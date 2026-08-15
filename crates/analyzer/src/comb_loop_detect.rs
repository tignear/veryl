//! Combinational loop detection on the analyzer IR (issue #931).
//!
//! The analysis pipeline is split by responsibility:
//!
//! 1. discover sparse bit and array regions used by each module;
//! 2. evaluate procedures in statement order and build dependency edges;
//! 3. detect compatible cycles in the graph;
//! 4. summarize module feedthrough bottom-up for parent instances.
//!
//! Under-detect by design: opaque constructs (SystemVerilog black
//! boxes, `inout` ports, recursive functions) add no edges; the
//! simulator's `analyze_dependency` is the backup safety net.

mod graph;
mod hierarchy;
mod model;
mod procedure;
mod region;
mod ssa;
mod summary;

#[cfg(test)]
thread_local! {
    static INSTANCE_REQUEST_EDGE_PROBES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static INSTANCE_FRAGMENT_PROBES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static GUARDED_EXPRESSION_PROBES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_instance_request_edge_probes() {
    INSTANCE_REQUEST_EDGE_PROBES.set(0);
}

#[cfg(test)]
pub(crate) fn instance_request_edge_probes() -> usize {
    INSTANCE_REQUEST_EDGE_PROBES.get()
}

#[cfg(test)]
pub(crate) fn reset_instance_fragment_probes() {
    INSTANCE_FRAGMENT_PROBES.set(0);
}

#[cfg(test)]
pub(crate) fn instance_fragment_probes() -> usize {
    INSTANCE_FRAGMENT_PROBES.get()
}

#[cfg(test)]
pub(crate) fn reset_guarded_expression_probes() {
    GUARDED_EXPRESSION_PROBES.set(0);
}

#[cfg(test)]
pub(crate) fn guarded_expression_probes() -> usize {
    GUARDED_EXPRESSION_PROBES.get()
}

#[cfg(test)]
pub(crate) use procedure::{
    expression_layout_visit_count, formal_output_region_probe_count,
    function_barrier_evaluation_count, function_evaluation_count,
    function_result_region_probe_count, function_result_version_count,
    function_summary_graph_node_count, function_summary_metadata_visits, module_context_entries,
    reset_function_evaluation_count, reset_module_context_entries,
    write_footprint_statement_visits,
};
#[cfg(test)]
pub(crate) use ssa::{
    flow_scaling_counters, reset_flow_scaling_counters, reset_source_summary_state_visits,
    source_summary_state_visits,
};

use graph::{
    DependencyGraph, GraphDependency, GraphNode, add_dependency_edge, add_region_dependency,
    check_graph, ensure_node, node_regions_overlap_with_dependency,
};
use hierarchy::{module_postorder, walk_insts};
use model::{BitDependency, ModuleCombSummary, SummaryNodeKind, SummaryRegion};
use region::{
    ArraySpan, BitPartition, IdxKey, NodeKey, PackedSpan, dst_writes, signed_difference,
    translate_position, var_reads,
};
use ssa::{BranchId, BranchRemapper, DependencyDagNode, PathCondition, PositionDomain};
use summary::compute_module_summary;

use crate::AnalyzerError;
use crate::HashMap;
use crate::HashSet;
use crate::conv::Context;
use crate::ir::VarId;
use crate::ir::{
    AssignDestination, Component, Declaration, Expression, Factor, FunctionCall,
    InstActualFragment, InstDeclaration, InstInterfaceBinding, Ir, MemberSelectDomain, Module, Op,
    Signature, Statement, SystemFunctionCall, SystemFunctionKind, VarSelect, VarSelectOp, Variable,
};
use crate::symbol::{Affiliation, Direction};
use daggy::petgraph::graph::NodeIndex;
use std::rc::Rc;
use veryl_parser::token_range::TokenRange;

pub fn check(ir: &Ir) -> Vec<AnalyzerError> {
    check_inner(ir).0
}

#[cfg(test)]
pub(crate) fn is_complete(ir: &Ir) -> bool {
    check_inner(ir).1
}

fn check_inner(ir: &Ir) -> (Vec<AnalyzerError>, bool) {
    let mut errors = Vec::new();
    let mut complete = true;
    let mut summaries: HashMap<Signature, ModuleCombSummary> = HashMap::default();

    for module in module_postorder(ir) {
        let (graph, _bit_part, module_complete) = build_module_graph(module, &summaries);
        check_graph(module, &graph, &mut errors);
        let mut summary = compute_module_summary(module, &graph);
        summary.complete = module_complete;
        summaries.insert(module.signature.clone(), summary);
        complete &= module_complete;
    }

    (errors, complete)
}

/// Split only at observed access endpoints. Runtime and storage depend on the
/// number of accesses, never on the highest referenced bit position.
fn atomic_ranges(spans: &[PackedSpan], endpoints: Option<&HashSet<usize>>) -> Vec<PackedSpan> {
    let mut events = Vec::with_capacity(spans.len() * 2 + endpoints.map_or(0, HashSet::len));
    for span in spans {
        events.push((span.start, 1isize));
        events.push((span.end(), -1isize));
    }
    if let Some(endpoints) = endpoints {
        events.extend(endpoints.iter().map(|endpoint| (*endpoint, 0)));
    }
    events.sort_unstable_by_key(|event| event.0);

    let mut atoms = Vec::new();
    let mut active = 0isize;
    let mut index = 0;
    while index < events.len() {
        let position = events[index].0;
        while index < events.len() && events[index].0 == position {
            active += events[index].1;
            index += 1;
        }
        if active > 0
            && let Some(next) = events.get(index).map(|event| event.0)
            && let Some(atom) = PackedSpan::new(position, next - position)
        {
            atoms.push(atom);
        }
    }
    atoms
}

fn build_bit_partition(
    module: &Module,
    summaries: &HashMap<Signature, ModuleCombSummary>,
    ctx: &mut Context,
) -> BitPartition {
    let mut accesses: HashMap<IdxKey, Vec<PackedSpan>> = HashMap::default();
    let mut visited_functions = HashSet::default();

    for declaration in &module.declarations {
        if let Declaration::Comb(comb) = declaration {
            collect_statement_spans(&comb.statements, &mut accesses, ctx);
            collect_called_function_statement_spans(
                &comb.statements,
                module,
                &mut accesses,
                &mut visited_functions,
                ctx,
            );
        }
    }

    // Inst input expressions are not represented by procedure statements.
    for inst in walk_insts(module) {
        for inp in &inst.inputs {
            if let Some(src) = &inp.range_src
                && let Some(packed) =
                    PackedSpan::new(src.parent_packed_start, src.parent_packed_length)
            {
                accesses
                    .entry((
                        src.parent,
                        ArraySpan {
                            start: src.parent_array_start,
                            length: src.parent_array_length,
                        },
                    ))
                    .or_default()
                    .push(packed);
            } else {
                for expr in &inp.exprs {
                    collect_expr_spans(expr, &mut accesses, ctx);
                    collect_called_function_expr_spans(
                        expr,
                        module,
                        &mut accesses,
                        &mut visited_functions,
                        ctx,
                    );
                }
            }
        }
        for out in &inst.outputs {
            if let Some(dst) = &out.range_dst
                && let Some(packed) =
                    PackedSpan::new(dst.parent_packed_start, dst.parent_packed_length)
            {
                accesses
                    .entry((
                        dst.parent,
                        ArraySpan {
                            start: dst.parent_array_start,
                            length: dst.parent_array_length,
                        },
                    ))
                    .or_default()
                    .push(packed);
            } else {
                for dst in &out.dst {
                    collect_destination_spans(dst, &mut accesses, ctx);
                    collect_called_function_destination_spans(
                        dst,
                        module,
                        &mut accesses,
                        &mut visited_functions,
                        ctx,
                    );
                }
            }
        }
    }

    collect_instance_summary_spans(module, summaries, &mut accesses, ctx);

    // Function-local regions are not represented by the caller's aggregate
    // reference table. They still need atoms because calls are lowered into
    // the same SSA version graph as their caller.
    for function in module.functions.values() {
        for body in &function.functions {
            for (path, id) in &body.arg_map {
                let r#type = module
                    .variables
                    .get(id)
                    .map(|variable| &variable.r#type)
                    .or_else(|| {
                        function
                            .args
                            .iter()
                            .flat_map(|argument| &argument.members)
                            .find_map(|(member, comptime, _)| {
                                (member == path).then_some(&comptime.r#type)
                            })
                    });
                if let Some(r#type) = r#type {
                    add_whole_type_access(&mut accesses, *id, r#type);
                }
            }
            if let Some(id) = body.ret {
                let r#type = module
                    .variables
                    .get(&id)
                    .map(|variable| &variable.r#type)
                    .unwrap_or(&function.r#type.r#type);
                add_whole_type_access(&mut accesses, id, r#type);
            }
            collect_statement_spans(&body.statements, &mut accesses, ctx);
        }
    }

    // SSA evaluation carries positional transfers on dependency edges. The
    // storage partition therefore needs only syntactically observed access
    // boundaries. Closing boundaries over the transfer graph can generate all
    // subset sums of independent shifts and silently devolve into bit-level
    // expansion.
    let endpoints = HashMap::default();
    let ranges = split_array_spans(accesses, &endpoints);

    BitPartition::new(ranges)
}

fn add_whole_type_access(
    accesses: &mut HashMap<IdxKey, Vec<PackedSpan>>,
    id: VarId,
    r#type: &crate::ir::Type,
) {
    let Some(array_length) = r#type.array.total() else {
        return;
    };
    let Some(packed) = r#type.total_width().and_then(PackedSpan::whole) else {
        return;
    };
    accesses
        .entry((
            id,
            ArraySpan {
                start: 0,
                length: array_length,
            },
        ))
        .or_default()
        .push(packed);
}

#[derive(Clone, Copy)]
struct PeriodicArrayFilter {
    period: usize,
    phase: usize,
    extent: usize,
}

/// Statically known coordinates of an otherwise dynamic unpacked access.
///
/// Each coordinate is represented as one periodic band in flattened storage,
/// so checking a sparse partition key is independent of the declared array
/// width. Size-one axes are omitted; consequently the number of meaningful
/// filters is bounded by the number of bits in a representable array size.
#[derive(Clone, Default)]
struct StaticArrayFilters {
    filters: Rc<Vec<PeriodicArrayFilter>>,
}

impl StaticArrayFilters {
    fn new(parent: VarId, index: &crate::ir::VarIndex, ctx: &mut Context) -> Self {
        let Some(shape) = ctx
            .variables
            .get(&parent)
            .map(|variable| variable.r#type.array.clone())
        else {
            return Self::default();
        };
        let filters = index
            .0
            .iter()
            .enumerate()
            .filter_map(|(position, expression)| {
                if !expression.comptime().is_const {
                    return None;
                }
                let dimension = shape.get(position).copied().flatten()?;
                if dimension == 1 {
                    return None;
                }
                let value = expression.eval_value(ctx)?.to_usize()?;
                if value >= dimension {
                    return None;
                }
                let stride = shape[position + 1..]
                    .iter()
                    .try_fold(1usize, |stride, dimension| {
                        stride.checked_mul((*dimension)?)
                    })?;
                Some(PeriodicArrayFilter {
                    period: dimension.checked_mul(stride)?,
                    phase: value.checked_mul(stride)?,
                    extent: stride,
                })
            })
            .collect();
        Self {
            filters: Rc::new(filters),
        }
    }

    fn may_select(&self, span: ArraySpan) -> bool {
        self.filters
            .iter()
            .all(|filter| periodic_array_filter_may_overlap(span, *filter))
    }
}

fn periodic_array_filter_may_overlap(span: ArraySpan, filter: PeriodicArrayFilter) -> bool {
    let Some(span_end) = span.end() else {
        return true;
    };
    let Some(phase_end) = filter.phase.checked_add(filter.extent) else {
        return true;
    };
    if filter.period == 0
        || filter.extent == 0
        || filter.phase >= filter.period
        || phase_end > filter.period
    {
        return true;
    }

    let residue = span.start % filter.period;
    let band_start = if residue < filter.phase {
        span.start.checked_add(filter.phase - residue)
    } else if residue < phase_end {
        span.start.checked_sub(residue - filter.phase)
    } else {
        span.start
            .checked_add(filter.period - residue)
            .and_then(|start| start.checked_add(filter.phase))
    };
    band_start.is_some_and(|band_start| band_start < span_end)
}

fn filtered_actual_keys(
    bit_part: &BitPartition,
    parent: VarId,
    array: ArraySpan,
    packed: PackedSpan,
    filters: &StaticArrayFilters,
) -> Vec<NodeKey> {
    bit_part
        .overlapping_access(parent, array, packed)
        .into_iter()
        .filter(|key| {
            key.1
                .intersection(array)
                .is_some_and(|span| filters.may_select(span))
        })
        .collect()
}

struct InstanceEndpointIndex {
    inputs: HashMap<VarId, usize>,
    outputs: HashMap<VarId, usize>,
    interface_bindings: HashMap<VarId, usize>,
    input_array_filters: HashMap<VarId, StaticArrayFilters>,
    output_array_filters: HashMap<VarId, StaticArrayFilters>,
    output_layouts: HashMap<VarId, Option<ActualFragmentLayout>>,
}

impl InstanceEndpointIndex {
    fn new(inst: &InstDeclaration, child: &Module, ctx: &mut Context) -> Self {
        let output_layouts = inst
            .outputs
            .iter()
            .filter_map(|output| {
                let variable = child
                    .variables
                    .get(&output.id)
                    .or_else(|| child.interface_members.get(&output.id))?;
                let fragments = if let Some(actual) = &output.range_dst {
                    coerced_contiguous_actual_fragments(variable, actual)
                } else {
                    actual_fragments(variable, &output.dst, ctx)
                };
                Some((output.id, fragments.map(ActualFragmentLayout::new)))
            })
            .collect();
        let input_array_filters = inst
            .inputs
            .iter()
            .filter_map(|input| {
                let Expression::Term(factor) = input.single()? else {
                    return None;
                };
                let Factor::Variable(parent, index, _, _) = factor.as_ref() else {
                    return None;
                };
                Some((input.id, StaticArrayFilters::new(*parent, index, ctx)))
            })
            .collect();
        let output_array_filters = inst
            .outputs
            .iter()
            .filter_map(|output| {
                let [destination] = output.dst.as_slice() else {
                    return None;
                };
                Some((
                    output.id,
                    StaticArrayFilters::new(destination.id, &destination.index, ctx),
                ))
            })
            .collect();
        Self {
            inputs: inst
                .inputs
                .iter()
                .enumerate()
                .map(|(index, input)| (input.id, index))
                .collect(),
            outputs: inst
                .outputs
                .iter()
                .enumerate()
                .map(|(index, output)| (output.id, index))
                .collect(),
            interface_bindings: inst
                .interface_bindings
                .iter()
                .enumerate()
                .map(|(index, binding)| (binding.child, index))
                .collect(),
            input_array_filters,
            output_array_filters,
            output_layouts,
        }
    }
}

fn collect_instance_summary_spans(
    module: &Module,
    summaries: &HashMap<Signature, ModuleCombSummary>,
    accesses: &mut HashMap<IdxKey, Vec<PackedSpan>>,
    ctx: &mut Context,
) {
    for inst in walk_insts(module) {
        let Component::Module(child) = inst.component.as_ref() else {
            continue;
        };
        let Some(summary) = summaries.get(&child.signature) else {
            continue;
        };
        let endpoints = InstanceEndpointIndex::new(inst, child, ctx);
        for node in &summary.nodes {
            let direction = match node.kind {
                SummaryNodeKind::Input | SummaryNodeKind::Interface => Direction::Input,
                SummaryNodeKind::Output => Direction::Output,
                SummaryNodeKind::Internal => continue,
            };
            for (parent, array, packed) in
                summary_parent_accesses(inst, &endpoints, child, node.region, direction, ctx)
            {
                accesses.entry((parent, array)).or_default().push(packed);
            }
        }
    }
}

fn summary_parent_accesses(
    inst: &InstDeclaration,
    endpoints: &InstanceEndpointIndex,
    child: &Module,
    region: SummaryRegion,
    direction: Direction,
    ctx: &mut Context,
) -> Vec<(VarId, ArraySpan, PackedSpan)> {
    let Some(variable) = child
        .variables
        .get(&region.id)
        .or_else(|| child.interface_members.get(&region.id))
    else {
        return Vec::new();
    };
    if let Some(binding) = endpoints
        .interface_bindings
        .get(&region.id)
        .map(|&index| &inst.interface_bindings[index])
        && let Some(accesses) = translated_interface_binding_accesses(region, variable, binding)
    {
        return accesses
            .into_iter()
            .map(|access| (access.parent, access.array, access.packed))
            .collect();
    }
    if direction == Direction::Output
        && let Some(output) = endpoints
            .outputs
            .get(&region.id)
            .map(|&index| &inst.outputs[index])
    {
        let accesses = endpoints
            .output_layouts
            .get(&output.id)
            .and_then(|layout| layout.as_ref())
            .and_then(|layout| layout.translate(region));
        if let Some(accesses) = accesses {
            return accesses
                .into_iter()
                .map(|access| (access.parent, access.array, access.packed))
                .collect();
        }
    }
    if direction == Direction::Input
        && let Some(input) = endpoints
            .inputs
            .get(&region.id)
            .map(|&index| &inst.inputs[index])
        && let Some(actual) = &input.range_src
        && let Some(accesses) = translated_coerced_input_contiguous_actual_accesses(
            region,
            variable,
            actual,
            actual.signed,
        )
    {
        return accesses
            .into_iter()
            .map(|access| (access.parent, access.array, access.packed))
            .collect();
    }
    if let Some((parent, index, select, member_select_domain, _)) =
        instance_port_region_actual(inst, endpoints, region.id, direction)
    {
        return translated_summary_access(
            region,
            variable,
            parent,
            index,
            select,
            member_select_domain,
            ctx,
        )
        .map(|(array, packed, _)| vec![(parent, array, packed)])
        .unwrap_or_default();
    }
    Vec::new()
}

fn split_array_spans(
    accesses_by_index: HashMap<IdxKey, Vec<PackedSpan>>,
    endpoints: &HashMap<VarId, HashSet<usize>>,
) -> HashMap<IdxKey, Vec<PackedSpan>> {
    let mut accesses: HashMap<VarId, Vec<(ArraySpan, PackedSpan)>> = HashMap::default();
    for ((id, span), packed_spans) in accesses_by_index {
        for packed in packed_spans {
            accesses.entry(id).or_default().push((span, packed));
        }
    }

    let mut ranges = HashMap::default();
    for (id, accesses) in accesses {
        let mut events = Vec::with_capacity(accesses.len() * 2);
        for (span, packed) in accesses {
            if span.length == 0 {
                continue;
            }
            let Some(end) = span.end() else {
                continue;
            };
            events.push((span.start, true, packed));
            events.push((end, false, packed));
        }
        events.sort_unstable_by_key(|(position, starts, packed)| {
            (*position, *starts, packed.start, packed.length)
        });

        let mut active: HashMap<PackedSpan, usize> = HashMap::default();
        let mut previous = events.first().map(|event| event.0);
        let mut cursor = 0;
        while cursor < events.len() {
            let position = events[cursor].0;
            if let Some(previous) = previous
                && previous < position
                && !active.is_empty()
            {
                let split = ArraySpan {
                    start: previous,
                    length: position - previous,
                };
                let split_spans = active.keys().copied().collect::<Vec<_>>();
                let parts = atomic_ranges(&split_spans, endpoints.get(&id));
                if !parts.is_empty() {
                    ranges.insert((id, split), parts);
                }
            }
            while cursor < events.len() && events[cursor].0 == position {
                let (_, starts, packed) = events[cursor];
                if starts {
                    *active.entry(packed).or_default() += 1;
                } else if let std::collections::hash_map::Entry::Occupied(mut entry) =
                    active.entry(packed)
                {
                    *entry.get_mut() -= 1;
                    if *entry.get() == 0 {
                        entry.remove();
                    }
                }
                cursor += 1;
            }
            previous = Some(position);
        }
    }
    ranges
}

fn collect_expr_spans(
    expr: &Expression,
    out: &mut HashMap<IdxKey, Vec<PackedSpan>>,
    ctx: &mut Context,
) {
    match expr {
        Expression::Term(t) => collect_factor_spans(t, out, ctx),
        Expression::Unary(_, e, _) => collect_expr_spans(e, out, ctx),
        Expression::Binary(a, _, b, _) => {
            collect_expr_spans(a, out, ctx);
            collect_expr_spans(b, out, ctx);
        }
        Expression::Ternary(a, b, c, _) => {
            collect_expr_spans(a, out, ctx);
            collect_expr_spans(b, out, ctx);
            collect_expr_spans(c, out, ctx);
        }
        Expression::Concatenation(parts, _) => {
            for (a, b) in parts {
                collect_expr_spans(a, out, ctx);
                if let Some(b) = b {
                    collect_expr_spans(b, out, ctx);
                }
            }
        }
        Expression::StructConstructor(_, fields, _) => {
            for (_, e) in fields {
                collect_expr_spans(e, out, ctx);
            }
        }
        Expression::ArrayLiteral(items, _) => {
            for item in items {
                match item {
                    crate::ir::ArrayLiteralItem::Value(value, repeat) => {
                        collect_expr_spans(value, out, ctx);
                        if let Some(repeat) = repeat {
                            collect_expr_spans(repeat, out, ctx);
                        }
                    }
                    crate::ir::ArrayLiteralItem::Defaul(value) => {
                        collect_expr_spans(value, out, ctx);
                    }
                }
            }
        }
    }
}

fn collect_factor_spans(
    factor: &Factor,
    out: &mut HashMap<IdxKey, Vec<PackedSpan>>,
    ctx: &mut Context,
) {
    match factor {
        Factor::Variable(id, index, select, comptime) => {
            for (idx, packed) in var_reads(*id, index, select, comptime.member_select_domain, ctx) {
                out.entry((*id, idx)).or_default().push(packed);
            }
            for coordinate in index
                .0
                .iter()
                .chain(select.0.iter())
                .chain(select.1.iter().map(|(_, expression)| expression))
            {
                collect_expr_spans(coordinate, out, ctx);
            }
        }
        Factor::HierVariable(variable) => {
            for coordinate in variable
                .index
                .0
                .iter()
                .chain(variable.select.0.iter())
                .chain(variable.select.1.iter().map(|(_, expression)| expression))
            {
                collect_expr_spans(coordinate, out, ctx);
            }
        }
        Factor::FunctionCall(call) => {
            for coordinate in &call.receiver_index.0 {
                collect_expr_spans(coordinate, out, ctx);
            }
            for input in call.inputs.values() {
                collect_expr_spans(input, out, ctx);
            }
            for outputs in call.outputs.values() {
                for destination in outputs {
                    collect_destination_spans(destination, out, ctx);
                }
            }
        }
        Factor::SystemFunctionCall(call) => {
            for_each_system_function_input(call, |expression| {
                collect_expr_spans(expression, out, ctx);
            });
            for destination in system_function_outputs(call) {
                collect_destination_spans(destination, out, ctx);
            }
        }
        _ => {}
    }
}

fn for_each_system_function_input(call: &SystemFunctionCall, mut visit: impl FnMut(&Expression)) {
    match &call.kind {
        SystemFunctionKind::Bits(input)
        | SystemFunctionKind::Size(input)
        | SystemFunctionKind::Clog2(input)
        | SystemFunctionKind::Onehot(input)
        | SystemFunctionKind::Signed(input)
        | SystemFunctionKind::Unsigned(input)
        | SystemFunctionKind::Readmemh(input, _) => visit(&input.0),
        SystemFunctionKind::Display(inputs) | SystemFunctionKind::Write(inputs) => {
            for input in inputs {
                visit(&input.0);
            }
        }
        SystemFunctionKind::Assert { cond, args, .. } => {
            visit(&cond.0);
            for input in args {
                visit(&input.0);
            }
        }
        SystemFunctionKind::Finish => {}
    }
}

fn system_function_outputs(call: &SystemFunctionCall) -> &[AssignDestination] {
    match &call.kind {
        SystemFunctionKind::Readmemh(_, output) => &output.0,
        _ => &[],
    }
}

fn collect_destination_spans(
    destination: &AssignDestination,
    out: &mut HashMap<IdxKey, Vec<PackedSpan>>,
    ctx: &mut Context,
) {
    for coordinate in destination
        .index
        .0
        .iter()
        .chain(destination.select.0.iter())
        .chain(
            destination
                .select
                .1
                .iter()
                .map(|(_, expression)| expression),
        )
    {
        collect_expr_spans(coordinate, out, ctx);
    }
    for (index, packed) in dst_writes(destination, ctx) {
        out.entry((destination.id, index)).or_default().push(packed);
    }
}

fn collect_statement_spans(
    statements: &[Statement],
    out: &mut HashMap<IdxKey, Vec<PackedSpan>>,
    ctx: &mut Context,
) {
    for statement in statements {
        match statement {
            Statement::Assign(assign) => {
                collect_expr_spans(&assign.expr, out, ctx);
                for destination in &assign.dst {
                    collect_destination_spans(destination, out, ctx);
                }
            }
            Statement::If(statement) => {
                collect_expr_spans(&statement.cond, out, ctx);
                collect_statement_spans(&statement.true_side, out, ctx);
                collect_statement_spans(&statement.false_side, out, ctx);
            }
            Statement::Case(statement) => {
                collect_expr_spans(&statement.case_target, out, ctx);
                for arm in &statement.arms {
                    for pattern in &arm.patterns {
                        match pattern {
                            crate::ir::CasePattern::Eq(expression) => {
                                collect_expr_spans(expression, out, ctx);
                            }
                            crate::ir::CasePattern::Range { lo, hi, .. } => {
                                collect_expr_spans(lo, out, ctx);
                                collect_expr_spans(hi, out, ctx);
                            }
                        }
                    }
                    collect_statement_spans(&arm.body, out, ctx);
                }
                collect_statement_spans(&statement.default, out, ctx);
            }
            Statement::For(statement) => {
                let (start, end) = match &statement.range {
                    crate::ir::ForRange::Forward { start, end, .. }
                    | crate::ir::ForRange::Reverse { start, end, .. }
                    | crate::ir::ForRange::Stepped { start, end, .. } => (start, end),
                };
                for bound in [start, end] {
                    if let crate::ir::ForBound::Expression(expression) = bound {
                        collect_expr_spans(expression, out, ctx);
                    }
                }
                collect_statement_spans(&statement.body, out, ctx);
            }
            Statement::FunctionCall(call) => {
                for coordinate in &call.receiver_index.0 {
                    collect_expr_spans(coordinate, out, ctx);
                }
                for input in call.inputs.values() {
                    collect_expr_spans(input, out, ctx);
                }
                for outputs in call.outputs.values() {
                    for destination in outputs {
                        collect_destination_spans(destination, out, ctx);
                    }
                }
            }
            Statement::SystemFunctionCall(call) => {
                for_each_system_function_input(call, |expression| {
                    collect_expr_spans(expression, out, ctx);
                });
                for destination in system_function_outputs(call) {
                    collect_destination_spans(destination, out, ctx);
                }
            }
            Statement::IfReset(statement) => {
                collect_statement_spans(&statement.true_side, out, ctx);
                collect_statement_spans(&statement.false_side, out, ctx);
            }
            Statement::TbMethodCall(_)
            | Statement::Break
            | Statement::Unsupported(_)
            | Statement::Null => {}
        }
    }
}

fn collect_called_function_expr_spans(
    expression: &Expression,
    module: &Module,
    out: &mut HashMap<IdxKey, Vec<PackedSpan>>,
    visited: &mut HashSet<CalledFunctionKey>,
    ctx: &mut Context,
) {
    match expression {
        Expression::Term(factor) => match factor.as_ref() {
            Factor::Variable(_, index, select, _) => {
                for expression in index
                    .0
                    .iter()
                    .chain(select.0.iter())
                    .chain(select.1.iter().map(|(_, expression)| expression))
                {
                    collect_called_function_expr_spans(expression, module, out, visited, ctx);
                }
            }
            Factor::HierVariable(variable) => {
                for expression in variable
                    .index
                    .0
                    .iter()
                    .chain(variable.select.0.iter())
                    .chain(variable.select.1.iter().map(|(_, expression)| expression))
                {
                    collect_called_function_expr_spans(expression, module, out, visited, ctx);
                }
            }
            Factor::FunctionCall(call) => {
                for coordinate in &call.receiver_index.0 {
                    collect_called_function_expr_spans(coordinate, module, out, visited, ctx);
                }
                for input in call.inputs.values() {
                    collect_called_function_expr_spans(input, module, out, visited, ctx);
                }
                for outputs in call.outputs.values() {
                    for destination in outputs {
                        collect_called_function_destination_spans(
                            destination,
                            module,
                            out,
                            visited,
                            ctx,
                        );
                    }
                }
                collect_called_function_body_spans(call, module, out, visited, ctx);
            }
            Factor::SystemFunctionCall(call) => {
                for_each_system_function_input(call, |expression| {
                    collect_called_function_expr_spans(expression, module, out, visited, ctx);
                });
                for destination in system_function_outputs(call) {
                    collect_called_function_destination_spans(
                        destination,
                        module,
                        out,
                        visited,
                        ctx,
                    );
                }
            }
            _ => {}
        },
        Expression::Unary(_, expression, _) => {
            collect_called_function_expr_spans(expression, module, out, visited, ctx);
        }
        Expression::Binary(left, _, right, _) => {
            collect_called_function_expr_spans(left, module, out, visited, ctx);
            collect_called_function_expr_spans(right, module, out, visited, ctx);
        }
        Expression::Ternary(condition, left, right, _) => {
            collect_called_function_expr_spans(condition, module, out, visited, ctx);
            collect_called_function_expr_spans(left, module, out, visited, ctx);
            collect_called_function_expr_spans(right, module, out, visited, ctx);
        }
        Expression::Concatenation(parts, _) => {
            for (value, repeat) in parts {
                collect_called_function_expr_spans(value, module, out, visited, ctx);
                if let Some(repeat) = repeat {
                    collect_called_function_expr_spans(repeat, module, out, visited, ctx);
                }
            }
        }
        Expression::StructConstructor(_, fields, _) => {
            for (_, value) in fields {
                collect_called_function_expr_spans(value, module, out, visited, ctx);
            }
        }
        Expression::ArrayLiteral(items, _) => {
            for item in items {
                match item {
                    crate::ir::ArrayLiteralItem::Value(value, repeat) => {
                        collect_called_function_expr_spans(value, module, out, visited, ctx);
                        if let Some(repeat) = repeat {
                            collect_called_function_expr_spans(repeat, module, out, visited, ctx);
                        }
                    }
                    crate::ir::ArrayLiteralItem::Defaul(value) => {
                        collect_called_function_expr_spans(value, module, out, visited, ctx);
                    }
                }
            }
        }
    }
}

fn collect_called_function_destination_spans(
    destination: &AssignDestination,
    module: &Module,
    out: &mut HashMap<IdxKey, Vec<PackedSpan>>,
    visited: &mut HashSet<CalledFunctionKey>,
    ctx: &mut Context,
) {
    for expression in destination
        .index
        .0
        .iter()
        .chain(destination.select.0.iter())
        .chain(
            destination
                .select
                .1
                .iter()
                .map(|(_, expression)| expression),
        )
    {
        collect_called_function_expr_spans(expression, module, out, visited, ctx);
    }
}

fn collect_called_function_for_range_spans(
    range: &crate::ir::ForRange,
    module: &Module,
    out: &mut HashMap<IdxKey, Vec<PackedSpan>>,
    visited: &mut HashSet<CalledFunctionKey>,
    ctx: &mut Context,
) {
    use crate::ir::{ForBound, ForRange};

    let (start, end) = match range {
        ForRange::Forward { start, end, .. }
        | ForRange::Reverse { start, end, .. }
        | ForRange::Stepped { start, end, .. } => (start, end),
    };
    for bound in [start, end] {
        if let ForBound::Expression(expression) = bound {
            collect_called_function_expr_spans(expression, module, out, visited, ctx);
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum ReceiverCoordinateKey {
    Constant(usize),
    Dynamic(TokenRange),
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct CalledFunctionKey {
    id: VarId,
    receiver: Vec<ReceiverCoordinateKey>,
}

fn called_function_key(call: &FunctionCall) -> CalledFunctionKey {
    let receiver = call
        .receiver_index
        .0
        .iter()
        .map(|expression| {
            expression
                .comptime()
                .get_value()
                .ok()
                .and_then(|value| value.to_usize())
                .map_or_else(
                    || ReceiverCoordinateKey::Dynamic(expression.token_range()),
                    ReceiverCoordinateKey::Constant,
                )
        })
        .collect();
    CalledFunctionKey {
        id: call.id,
        receiver,
    }
}

fn collect_called_function_body_spans(
    call: &crate::ir::FunctionCall,
    module: &Module,
    out: &mut HashMap<IdxKey, Vec<PackedSpan>>,
    visited: &mut HashSet<CalledFunctionKey>,
    ctx: &mut Context,
) {
    if !visited.insert(called_function_key(call)) {
        return;
    }
    let Some(body) = module
        .functions
        .get(&call.id)
        .and_then(|function| function.get_function_for_index(&call.receiver_index))
    else {
        return;
    };
    collect_statement_spans(&body.statements, out, ctx);
    collect_called_function_statement_spans(&body.statements, module, out, visited, ctx);
}

fn collect_called_function_statement_spans(
    statements: &[Statement],
    module: &Module,
    out: &mut HashMap<IdxKey, Vec<PackedSpan>>,
    visited: &mut HashSet<CalledFunctionKey>,
    ctx: &mut Context,
) {
    for statement in statements {
        match statement {
            Statement::Assign(assign) => {
                collect_called_function_expr_spans(&assign.expr, module, out, visited, ctx);
                for destination in &assign.dst {
                    collect_called_function_destination_spans(
                        destination,
                        module,
                        out,
                        visited,
                        ctx,
                    );
                }
            }
            Statement::If(statement) => {
                collect_called_function_expr_spans(&statement.cond, module, out, visited, ctx);
                collect_called_function_statement_spans(
                    &statement.true_side,
                    module,
                    out,
                    visited,
                    ctx,
                );
                collect_called_function_statement_spans(
                    &statement.false_side,
                    module,
                    out,
                    visited,
                    ctx,
                );
            }
            Statement::Case(statement) => {
                collect_called_function_expr_spans(
                    &statement.case_target,
                    module,
                    out,
                    visited,
                    ctx,
                );
                for arm in &statement.arms {
                    for pattern in &arm.patterns {
                        match pattern {
                            crate::ir::CasePattern::Eq(expression) => {
                                collect_called_function_expr_spans(
                                    expression, module, out, visited, ctx,
                                );
                            }
                            crate::ir::CasePattern::Range { lo, hi, .. } => {
                                collect_called_function_expr_spans(lo, module, out, visited, ctx);
                                collect_called_function_expr_spans(hi, module, out, visited, ctx);
                            }
                        }
                    }
                    collect_called_function_statement_spans(&arm.body, module, out, visited, ctx);
                }
                collect_called_function_statement_spans(
                    &statement.default,
                    module,
                    out,
                    visited,
                    ctx,
                );
            }
            Statement::For(statement) => {
                collect_called_function_for_range_spans(
                    &statement.range,
                    module,
                    out,
                    visited,
                    ctx,
                );
                collect_called_function_statement_spans(&statement.body, module, out, visited, ctx);
            }
            Statement::FunctionCall(call) => {
                for coordinate in &call.receiver_index.0 {
                    collect_called_function_expr_spans(coordinate, module, out, visited, ctx);
                }
                for input in call.inputs.values() {
                    collect_called_function_expr_spans(input, module, out, visited, ctx);
                }
                for outputs in call.outputs.values() {
                    for destination in outputs {
                        collect_called_function_destination_spans(
                            destination,
                            module,
                            out,
                            visited,
                            ctx,
                        );
                    }
                }
                collect_called_function_body_spans(call, module, out, visited, ctx);
            }
            Statement::SystemFunctionCall(call) => {
                for_each_system_function_input(call, |expression| {
                    collect_called_function_expr_spans(expression, module, out, visited, ctx);
                });
                for destination in system_function_outputs(call) {
                    collect_called_function_destination_spans(
                        destination,
                        module,
                        out,
                        visited,
                        ctx,
                    );
                }
            }
            Statement::IfReset(statement) => {
                collect_called_function_statement_spans(
                    &statement.true_side,
                    module,
                    out,
                    visited,
                    ctx,
                );
                collect_called_function_statement_spans(
                    &statement.false_side,
                    module,
                    out,
                    visited,
                    ctx,
                );
            }
            Statement::TbMethodCall(_)
            | Statement::Break
            | Statement::Unsupported(_)
            | Statement::Null => {}
        }
    }
}

fn build_module_graph(
    module: &Module,
    summaries: &HashMap<Signature, ModuleCombSummary>,
) -> (DependencyGraph, BitPartition, bool) {
    let mut ctx = Context::default();
    ctx.variables = module.variables.clone();
    ctx.variables.extend(module.interface_members.clone());
    ctx.functions = module.functions.clone();
    let bit_part = build_bit_partition(module, summaries, &mut ctx);
    let mut builder = ModuleGraphBuilder::new(module, &bit_part, ctx);

    for (declaration_index, declaration) in module.declarations.iter().enumerate() {
        let Declaration::Comb(comb) = declaration else {
            continue;
        };
        let analysis = procedure::analyze(
            &bit_part,
            &comb.statements,
            declaration_index + 1,
            &mut builder.procedure_context,
            &mut builder.function_summaries,
        );
        if !analysis.status.is_complete() {
            builder.complete = false;
        }
        builder.add_procedure_graph(module, analysis);
    }

    for inst in walk_insts(module) {
        match inst.component.as_ref() {
            Component::Module(child) => {
                let Some(summary) = summaries.get(&child.signature) else {
                    builder.complete = false;
                    continue;
                };
                builder.complete &= summary.complete;
                builder.add_instance_feedthrough(inst, child, summary);
            }
            // SV black box: under-detect.
            Component::SystemVerilog(_) => builder.complete = false,
            // Interface signals are already lifted into the parent.
            Component::Interface(_) => {}
        }
    }

    let (graph, complete) = builder.finish();
    (graph, bit_part, complete)
}

struct ModuleGraphBuilder<'a> {
    bit_part: &'a BitPartition,
    graph: DependencyGraph,
    node_map: HashMap<NodeKey, NodeIndex>,
    ctx: Context,
    procedure_context: procedure::ProcedureContext,
    function_summaries: procedure::FunctionSummaries<'a>,
    complete: bool,
}

impl<'a> ModuleGraphBuilder<'a> {
    fn new(module: &'a Module, bit_part: &'a BitPartition, ctx: Context) -> Self {
        Self {
            bit_part,
            graph: DependencyGraph::new(),
            node_map: HashMap::default(),
            ctx,
            procedure_context: procedure::ProcedureContext::new(module),
            function_summaries: procedure::FunctionSummaries::new(module, bit_part),
            complete: !module
                .variables
                .values()
                .any(|variable| matches!(variable.kind, crate::ir::VarKind::Inout)),
        }
    }

    fn finish(self) -> (DependencyGraph, bool) {
        (self.graph, self.complete)
    }

    fn add_procedure_graph(&mut self, module: &Module, analysis: procedure::ProcedureResult) {
        let destinations = analysis
            .destinations
            .into_iter()
            .filter_map(|(key, root)| {
                (is_module_scope_var(key.0, &module.variables)
                    && !is_inout(key.0, &module.variables))
                .then_some((key, root))
            })
            .collect::<Vec<_>>();
        let Some(internal_region) = destinations.iter().find_map(|(key, _)| {
            ensure_node(&mut self.graph, &mut self.node_map, self.bit_part, *key)
                .map(|node| self.graph[node].region)
        }) else {
            return;
        };

        let mapped = analysis
            .graph
            .nodes
            .iter()
            .enumerate()
            .map(|(index, node)| match node {
                DependencyDagNode::External(key)
                    if is_module_scope_var(key.0, &module.variables)
                        && !is_inout(key.0, &module.variables) =>
                {
                    ensure_node(&mut self.graph, &mut self.node_map, self.bit_part, *key)
                }
                DependencyDagNode::External(_) => None,
                DependencyDagNode::Internal | DependencyDagNode::RegularTransfer => {
                    Some(self.graph.add_node(GraphNode {
                        // Internal nodes carry no variable identity. The region is
                        // only a coordinate carrier; exact edge relations retain
                        // the positional semantics.
                        region: internal_region,
                        domains: analysis.graph.domains[index].clone(),
                        regular_transfer: matches!(node, DependencyDagNode::RegularTransfer),
                        diagnostic: None,
                    }))
                }
            })
            .collect::<Vec<_>>();

        for edge in analysis.graph.edges {
            let (Some(source), Some(destination)) = (mapped[edge.source], mapped[edge.destination])
            else {
                continue;
            };
            add_dependency_edge(
                &mut self.graph,
                source,
                destination,
                GraphDependency {
                    kind: BitDependency {
                        array: edge.relation.array,
                        packed: edge.relation.packed,
                    },
                    condition: edge.condition,
                    carrier: matches!(
                        analysis.graph.nodes[edge.source],
                        DependencyDagNode::RegularTransfer
                    ) && edge.source == edge.destination,
                },
            );
        }
        for (destination, root) in destinations {
            let (Some(root), Some(destination)) = (
                root.and_then(|root| mapped[root]),
                ensure_node(
                    &mut self.graph,
                    &mut self.node_map,
                    self.bit_part,
                    destination,
                ),
            ) else {
                continue;
            };
            add_dependency_edge(
                &mut self.graph,
                root,
                destination,
                GraphDependency::unconditional(BitDependency {
                    array: Some(0),
                    packed: Some(0),
                }),
            );
        }
    }

    fn add_instance_feedthrough(
        &mut self,
        inst: &InstDeclaration,
        child: &Module,
        summary: &ModuleCombSummary,
    ) {
        let bit_part = self.bit_part;
        let graph = &mut self.graph;
        let node_map = &mut self.node_map;
        let ctx = &mut self.ctx;
        let procedure_context = &mut self.procedure_context;
        let function_summaries = &mut self.function_summaries;
        let mut complete = true;
        let endpoints = InstanceEndpointIndex::new(inst, child, ctx);
        let (input_requests, positioned_inputs) =
            instance_input_region_requests(inst, &endpoints, child, summary, bit_part, ctx);
        let mut input_reads: HashMap<VarId, Vec<procedure::RegionSource>> = HashMap::default();
        let mut input_read_keys: HashMap<VarId, HashSet<NodeKey>> = HashMap::default();
        let mut input_region_mappings: HashMap<SummaryRegion, InstanceRegionMapping> =
            HashMap::default();
        for inp in &inst.inputs {
            if !is_pure_input_or_output(inp.id, &child.variables, Direction::Input) {
                continue;
            }
            let mut reads = Vec::new();
            let mut regions = Vec::new();
            let mut dependencies = Vec::new();
            let mut actual_complete = true;
            if let Some(src) = &inp.range_src {
                let range_reads: Vec<procedure::RegionSource> =
                    PackedSpan::new(src.parent_packed_start, src.parent_packed_length)
                        .into_iter()
                        .flat_map(|packed| {
                            bit_part.overlapping_access(
                                src.parent,
                                ArraySpan {
                                    start: src.parent_array_start,
                                    length: src.parent_array_length,
                                },
                                packed,
                            )
                        })
                        .map(|key| procedure::RegionSource {
                            key,
                            offset: None,
                            condition: PathCondition::default(),
                        })
                        .collect();
                reads.extend(range_reads);
            } else if let (Some(expression), Some((requests, context_width))) = (
                inp.single(),
                input_requests
                    .get(&inp.id)
                    .zip(child.variables.get(&inp.id).and_then(Variable::total_width)),
            ) {
                let analysis = analyze_instance_actual_regions(
                    bit_part,
                    expression,
                    requests,
                    context_width,
                    procedure_context,
                    function_summaries,
                );
                reads.extend(analysis.reads);
                regions.extend(analysis.mappings);
                dependencies.extend(analysis.dependencies);
                actual_complete &= analysis.complete;
            } else {
                for expression in &inp.exprs {
                    let (sources, expression_dependencies, expression_complete) =
                        analyze_instance_actual(
                            bit_part,
                            expression,
                            ctx,
                            procedure_context,
                            function_summaries,
                        );
                    actual_complete &= expression_complete;
                    reads.extend(sources);
                    dependencies.extend(expression_dependencies);
                }
            }
            input_region_mappings.extend(regions);
            complete &= actual_complete;
            for dependency in dependencies {
                add_region_dependency(
                    graph,
                    node_map,
                    bit_part,
                    dependency.source,
                    dependency.destination,
                    GraphDependency {
                        kind: dependency.kind,
                        condition: dependency.condition,
                        carrier: false,
                    },
                );
            }
            reads.sort_unstable_by_key(|source| {
                (source.key, source.offset, source.condition.clone())
            });
            reads.dedup_by(|left, right| {
                left.key == right.key
                    && left.offset == right.offset
                    && left.condition == right.condition
            });
            if !reads.is_empty() {
                input_read_keys.insert(inp.id, reads.iter().map(|source| source.key).collect());
                input_reads.insert(inp.id, reads);
            }
        }

        let mut output_dsts: HashMap<VarId, Vec<procedure::RegionSource>> = HashMap::default();
        for out in &inst.outputs {
            if !is_pure_input_or_output(out.id, &child.variables, Direction::Output) {
                continue;
            }
            let mut keys = Vec::new();
            if out.range_dst.is_none() {
                for dst in &out.dst {
                    let mut destination_keys = Vec::new();
                    collect_dst_node_keys(dst, bit_part, &mut destination_keys, ctx);
                    let (selector_reads, dependencies, selector_complete) =
                        analyze_instance_destination(
                            bit_part,
                            dst,
                            ctx,
                            procedure_context,
                            function_summaries,
                        );
                    complete &= selector_complete;
                    for dependency in dependencies {
                        add_region_dependency(
                            graph,
                            node_map,
                            bit_part,
                            dependency.source,
                            dependency.destination,
                            GraphDependency {
                                kind: dependency.kind,
                                condition: dependency.condition,
                                carrier: false,
                            },
                        );
                    }
                    for source in selector_reads {
                        for destination in &destination_keys {
                            add_region_dependency(
                                graph,
                                node_map,
                                bit_part,
                                source.key,
                                *destination,
                                GraphDependency {
                                    kind: BitDependency::WHOLE,
                                    condition: source.condition.clone(),
                                    carrier: false,
                                },
                            );
                        }
                    }
                    keys.extend(destination_keys);
                }
            }
            if let Some(dst) = &out.range_dst
                && let Some(packed) =
                    PackedSpan::new(dst.parent_packed_start, dst.parent_packed_length)
            {
                keys.extend(bit_part.overlapping_access(
                    dst.parent,
                    ArraySpan {
                        start: dst.parent_array_start,
                        length: dst.parent_array_length,
                    },
                    packed,
                ));
            }
            keys.sort_unstable();
            keys.dedup();
            if !keys.is_empty() {
                output_dsts.insert(
                    out.id,
                    keys.into_iter()
                        .map(|key| procedure::RegionSource {
                            key,
                            offset: None,
                            condition: PathCondition::default(),
                        })
                        .collect(),
                );
            }
        }

        let summary_branches = BranchRemapper::new(remap_module_summary_branches(summary, inst));
        let mut mapped_nodes = Vec::with_capacity(summary.nodes.len());
        let mut endpoint_mappings = Vec::with_capacity(summary.nodes.len());
        for (index, node) in summary.nodes.iter().enumerate() {
            let (mapping, endpoint_mapping) = match node.kind {
                SummaryNodeKind::Input => {
                    #[cfg(test)]
                    INSTANCE_REQUEST_EDGE_PROBES.set(INSTANCE_REQUEST_EDGE_PROBES.get() + 1);
                    let preserve_position = positioned_inputs.contains(&index);
                    let mapping = map_instance_source_region(
                        inst,
                        &endpoints,
                        child,
                        node.region,
                        preserve_position,
                        input_reads.get(&node.region.id).map(Vec::as_slice),
                        input_read_keys.get(&node.region.id),
                        &input_region_mappings,
                        bit_part,
                        ctx,
                    );
                    let resolved = resolve_instance_mapping(
                        graph,
                        node_map,
                        bit_part,
                        mapping.clone(),
                        BoundaryFlow::ParentToChild,
                    );
                    (resolved, Some(mapping))
                }
                SummaryNodeKind::Output => {
                    let mapping = instance_region_mapping(
                        inst,
                        &endpoints,
                        child,
                        node.region,
                        Direction::Output,
                        output_dsts.get(&node.region.id).map(Vec::as_slice),
                        bit_part,
                        ctx,
                    );
                    let resolved = resolve_instance_mapping(
                        graph,
                        node_map,
                        bit_part,
                        mapping.clone(),
                        BoundaryFlow::ChildToParent,
                    );
                    (resolved, Some(mapping))
                }
                SummaryNodeKind::Interface => {
                    let mapping = instance_region_mapping(
                        inst,
                        &endpoints,
                        child,
                        node.region,
                        Direction::Input,
                        None,
                        bit_part,
                        ctx,
                    );
                    let resolved = resolve_instance_mapping(
                        graph,
                        node_map,
                        bit_part,
                        mapping.clone(),
                        BoundaryFlow::ChildToParent,
                    );
                    (resolved, Some(mapping))
                }
                SummaryNodeKind::Internal => (
                    ResolvedInstanceRegionMapping {
                        nodes: vec![ResolvedMappedNode {
                            node: graph.add_node(GraphNode {
                                region: node.region,
                                domains: node.domains.clone(),
                                regular_transfer: node.regular_transfer,
                                diagnostic: None,
                            }),
                            offset: BitDependency::identity(),
                            condition: PathCondition::default(),
                        }],
                    },
                    None,
                ),
            };
            mapped_nodes.push(mapping);
            endpoint_mappings.push(endpoint_mapping);
        }

        for edge in &summary.edges {
            let condition = summary_branches.remap(&edge.condition);
            if summary.nodes[edge.source].kind == SummaryNodeKind::Input
                && let Some((array, packed)) = edge.kind.exact_offset()
                && let Some(destinations) = &endpoint_mappings[edge.destination]
            {
                let mut fallback_destinations = Vec::new();
                for destination in &destinations.nodes {
                    match child_source_region_for_destination(
                        summary.nodes[edge.source].region,
                        summary.nodes[edge.destination].region,
                        array,
                        packed,
                        destination,
                        bit_part,
                    ) {
                        RegionProjection::Exact(source_region) => {
                            let sources = map_instance_source_region(
                                inst,
                                &endpoints,
                                child,
                                source_region,
                                true,
                                input_reads
                                    .get(&summary.nodes[edge.source].region.id)
                                    .map(Vec::as_slice),
                                input_read_keys.get(&summary.nodes[edge.source].region.id),
                                &input_region_mappings,
                                bit_part,
                                ctx,
                            );
                            let sources = resolve_instance_mapping(
                                graph,
                                node_map,
                                bit_part,
                                sources,
                                BoundaryFlow::ParentToChild,
                            );
                            let destinations = resolve_instance_mapping(
                                graph,
                                node_map,
                                bit_part,
                                InstanceRegionMapping {
                                    nodes: vec![destination.clone()],
                                },
                                BoundaryFlow::ChildToParent,
                            );
                            add_resolved_dependency_edges(
                                graph,
                                &sources,
                                &destinations,
                                edge.kind,
                                &condition,
                                edge.carrier,
                            );
                        }
                        RegionProjection::Disjoint => {}
                        RegionProjection::Unknown => {
                            fallback_destinations.push(destination.clone())
                        }
                    }
                }
                if fallback_destinations.is_empty() {
                    continue;
                }
                let destinations = resolve_instance_mapping(
                    graph,
                    node_map,
                    bit_part,
                    InstanceRegionMapping {
                        nodes: fallback_destinations,
                    },
                    BoundaryFlow::ChildToParent,
                );
                add_resolved_dependency_edges(
                    graph,
                    &mapped_nodes[edge.source],
                    &destinations,
                    edge.kind,
                    &condition,
                    edge.carrier,
                );
                continue;
            }
            add_resolved_dependency_edges(
                graph,
                &mapped_nodes[edge.source],
                &mapped_nodes[edge.destination],
                edge.kind,
                &condition,
                edge.carrier,
            );
        }
        self.complete &= complete;
    }
}

#[allow(clippy::too_many_arguments)]
fn map_instance_source_region(
    inst: &InstDeclaration,
    endpoints: &InstanceEndpointIndex,
    child: &Module,
    region: SummaryRegion,
    preserve_position: bool,
    allowed: Option<&[procedure::RegionSource]>,
    allowed_keys: Option<&HashSet<NodeKey>>,
    evaluated: &HashMap<SummaryRegion, InstanceRegionMapping>,
    bit_part: &BitPartition,
    ctx: &mut Context,
) -> InstanceRegionMapping {
    let parent_sources = instance_region_mapping(
        inst,
        endpoints,
        child,
        region,
        Direction::Input,
        allowed,
        bit_part,
        ctx,
    );
    if !preserve_position
        || parent_sources
            .nodes
            .iter()
            .any(|source| source.offset.has_position())
        || endpoints
            .inputs
            .get(&region.id)
            .and_then(|&index| inst.inputs.get(index))
            .is_some_and(|input| input.range_src.is_some())
    {
        return parent_sources;
    }
    let Some(mut mapping) = evaluated.get(&region).cloned() else {
        return parent_sources;
    };
    mapping
        .nodes
        .retain(|source| allowed_keys.is_some_and(|allowed| allowed.contains(&source.key)));
    mapping
}

#[derive(Clone)]
struct InstanceRegionMapping {
    nodes: Vec<MappedNode>,
}

#[derive(Clone)]
struct MappedNode {
    key: NodeKey,
    offset: BitDependency,
    child_domain: Option<SummaryRegion>,
    condition: PathCondition,
}

struct ResolvedInstanceRegionMapping {
    nodes: Vec<ResolvedMappedNode>,
}

struct ResolvedMappedNode {
    node: NodeIndex,
    offset: BitDependency,
    condition: PathCondition,
}

#[derive(Clone, Copy)]
enum BoundaryFlow {
    ParentToChild,
    ChildToParent,
}

fn remap_module_summary_branches(
    summary: &ModuleCombSummary,
    inst: &InstDeclaration,
) -> HashMap<BranchId, BranchId> {
    let branches = PathCondition::collect_branches(
        summary.edges.iter().map(|dependency| &dependency.condition),
    );
    let namespace = std::ptr::from_ref(inst).addr();
    branches
        .into_iter()
        .enumerate()
        .map(|(local, branch)| (branch, BranchId::new(namespace, local, branch.arms())))
        .collect()
}

enum RegionProjection {
    Exact(SummaryRegion),
    Disjoint,
    Unknown,
}

fn instance_input_region_requests(
    inst: &InstDeclaration,
    endpoints: &InstanceEndpointIndex,
    child: &Module,
    summary: &ModuleCombSummary,
    bit_part: &BitPartition,
    ctx: &mut Context,
) -> (HashMap<VarId, Vec<SummaryRegion>>, HashSet<usize>) {
    let mut requests: HashMap<VarId, Vec<SummaryRegion>> = HashMap::default();
    let mut positioned_inputs = HashSet::default();
    for edge in &summary.edges {
        #[cfg(test)]
        INSTANCE_REQUEST_EDGE_PROBES.set(INSTANCE_REQUEST_EDGE_PROBES.get() + 1);
        if edge.kind.has_position() {
            positioned_inputs.insert(edge.source);
        }
    }
    for &index in &positioned_inputs {
        let Some(node) = summary.nodes.get(index) else {
            continue;
        };
        if node.kind == SummaryNodeKind::Input {
            requests
                .entry(node.region.id)
                .or_default()
                .push(node.region);
        }
    }

    // Endpoint translation is pure: it resolves only declared ranges and
    // compile-time selectors. Dynamic output selectors deliberately yield no
    // exact request and retain the conservative base-region mapping.
    let endpoint_mappings = summary
        .nodes
        .iter()
        .map(|node| match node.kind {
            SummaryNodeKind::Output => Some(instance_region_mapping(
                inst,
                endpoints,
                child,
                node.region,
                Direction::Output,
                None,
                bit_part,
                ctx,
            )),
            SummaryNodeKind::Interface => Some(instance_region_mapping(
                inst,
                endpoints,
                child,
                node.region,
                Direction::Input,
                None,
                bit_part,
                ctx,
            )),
            SummaryNodeKind::Input | SummaryNodeKind::Internal => None,
        })
        .collect::<Vec<_>>();
    for edge in &summary.edges {
        #[cfg(test)]
        INSTANCE_REQUEST_EDGE_PROBES.set(INSTANCE_REQUEST_EDGE_PROBES.get() + 1);
        if summary.nodes[edge.source].kind != SummaryNodeKind::Input {
            continue;
        }
        let Some((array, packed)) = edge.kind.exact_offset() else {
            continue;
        };
        let Some(destinations) = &endpoint_mappings[edge.destination] else {
            continue;
        };
        for destination in &destinations.nodes {
            if let RegionProjection::Exact(region) = child_source_region_for_destination(
                summary.nodes[edge.source].region,
                summary.nodes[edge.destination].region,
                array,
                packed,
                destination,
                bit_part,
            ) {
                requests.entry(region.id).or_default().push(region);
            }
        }
    }
    for regions in requests.values_mut() {
        regions.sort_unstable();
        regions.dedup();
    }
    (requests, positioned_inputs)
}

fn child_source_region_for_destination(
    child_source: SummaryRegion,
    child_destination: SummaryRegion,
    dependency_array: isize,
    dependency_packed: isize,
    destination: &MappedNode,
    bit_part: &BitPartition,
) -> RegionProjection {
    let destination_array_offset = destination.offset.array;
    let destination_packed_offset = destination.offset.packed;
    let Some(parent_packed) = bit_part
        .ranges_of((destination.key.0, destination.key.1))
        .get(destination.key.2)
        .copied()
    else {
        return RegionProjection::Unknown;
    };
    let child_destination_array = if let Some(offset) = destination_array_offset {
        let Some(offset) = offset.checked_neg() else {
            return RegionProjection::Unknown;
        };
        let Some(span) = translate_array_span(destination.key.1, offset) else {
            return RegionProjection::Unknown;
        };
        span
    } else if let Some(domain) = destination.child_domain {
        domain.array
    } else {
        return RegionProjection::Unknown;
    };
    let child_destination_packed = if let Some(offset) = destination_packed_offset {
        let Some(offset) = offset.checked_neg() else {
            return RegionProjection::Unknown;
        };
        let Some(span) = translate_packed_span(parent_packed, offset) else {
            return RegionProjection::Unknown;
        };
        span
    } else if let Some(domain) = destination.child_domain {
        domain.packed
    } else {
        return RegionProjection::Unknown;
    };
    let Some(child_destination_array) =
        child_destination_array.intersection(child_destination.array)
    else {
        return RegionProjection::Disjoint;
    };
    let Some(child_destination_packed) =
        child_destination_packed.intersection(child_destination.packed)
    else {
        return RegionProjection::Disjoint;
    };
    let Some(dependency_array) = dependency_array.checked_neg() else {
        return RegionProjection::Unknown;
    };
    let Some(dependency_packed) = dependency_packed.checked_neg() else {
        return RegionProjection::Unknown;
    };
    let Some(child_source_array) = translate_array_span(child_destination_array, dependency_array)
    else {
        return RegionProjection::Unknown;
    };
    let Some(child_source_packed) =
        translate_packed_span(child_destination_packed, dependency_packed)
    else {
        return RegionProjection::Unknown;
    };
    let Some(array) = child_source_array.intersection(child_source.array) else {
        return RegionProjection::Disjoint;
    };
    let Some(packed) = child_source_packed.intersection(child_source.packed) else {
        return RegionProjection::Disjoint;
    };
    RegionProjection::Exact(SummaryRegion {
        id: child_source.id,
        array,
        packed,
    })
}

fn translate_array_span(span: ArraySpan, offset: isize) -> Option<ArraySpan> {
    let start = translate_position(span.start, offset)?;
    (span.length != 0 && start.checked_add(span.length).is_some()).then_some(ArraySpan {
        start,
        length: span.length,
    })
}

fn translate_packed_span(span: PackedSpan, offset: isize) -> Option<PackedSpan> {
    PackedSpan::new(translate_position(span.start, offset)?, span.length)
}

#[allow(clippy::too_many_arguments)]
fn instance_region_mapping(
    inst: &InstDeclaration,
    endpoints: &InstanceEndpointIndex,
    child: &Module,
    region: SummaryRegion,
    direction: Direction,
    fallback: Option<&[procedure::RegionSource]>,
    bit_part: &BitPartition,
    ctx: &mut Context,
) -> InstanceRegionMapping {
    let variable = child
        .variables
        .get(&region.id)
        .or_else(|| child.interface_members.get(&region.id));
    if let (Some(variable), Some(binding)) = (
        variable,
        endpoints
            .interface_bindings
            .get(&region.id)
            .map(|&index| &inst.interface_bindings[index]),
    ) && let Some(mapping) =
        map_summary_region_to_interface_binding(region, variable, binding, bit_part)
    {
        return mapping;
    }

    if direction == Direction::Output
        && let (Some(_variable), Some(output)) = (
            variable,
            endpoints
                .outputs
                .get(&region.id)
                .map(|&index| &inst.outputs[index]),
        )
    {
        let mapping = endpoints
            .output_layouts
            .get(&output.id)
            .and_then(|layout| layout.as_ref())
            .and_then(|layout| layout.translate(region))
            .map(|accesses| map_translated_fragment_accesses(accesses, bit_part));
        if let Some(mapping) = mapping {
            return mapping;
        }
    }

    if direction == Direction::Input
        && let (Some(variable), Some(input)) = (
            variable,
            endpoints
                .inputs
                .get(&region.id)
                .map(|&index| &inst.inputs[index]),
        )
        && let Some(actual) = &input.range_src
        && let Some(mapping) = map_summary_region_to_coerced_input_contiguous_actual(
            region,
            variable,
            actual,
            actual.signed,
            bit_part,
        )
    {
        return mapping;
    }

    if let Some(variable) = variable
        && let Some((parent, index, select, member_select_domain, array_filters)) =
            instance_port_region_actual(inst, endpoints, region.id, direction)
    {
        return map_summary_region(
            region,
            variable,
            parent,
            index,
            select,
            member_select_domain,
            array_filters,
            bit_part,
            ctx,
        );
    }

    InstanceRegionMapping {
        nodes: fallback
            .into_iter()
            .flatten()
            .map(|source| MappedNode {
                key: source.key,
                offset: BitDependency::WHOLE,
                child_domain: None,
                condition: source.condition.clone(),
            })
            .collect(),
    }
}

fn instance_port_region_actual<'a>(
    inst: &'a InstDeclaration,
    endpoints: &'a InstanceEndpointIndex,
    child: VarId,
    direction: Direction,
) -> Option<(
    VarId,
    &'a crate::ir::VarIndex,
    &'a VarSelect,
    Option<MemberSelectDomain>,
    &'a StaticArrayFilters,
)> {
    match direction {
        Direction::Input => {
            let input = &inst.inputs[*endpoints.inputs.get(&child)?];
            let Expression::Term(factor) = input.single()? else {
                return None;
            };
            let Factor::Variable(parent, index, select, comptime) = factor.as_ref() else {
                return None;
            };
            Some((
                *parent,
                index,
                select,
                comptime.member_select_domain,
                endpoints.input_array_filters.get(&child)?,
            ))
        }
        Direction::Output => {
            let output = &inst.outputs[*endpoints.outputs.get(&child)?];
            let [destination] = output.dst.as_slice() else {
                return None;
            };
            Some((
                destination.id,
                &destination.index,
                &destination.select,
                destination.comptime.member_select_domain,
                endpoints.output_array_filters.get(&child)?,
            ))
        }
        Direction::Inout | Direction::Interface | Direction::Modport | Direction::Import => None,
    }
}

#[derive(Clone)]
struct ActualFragment {
    parent: VarId,
    child_array: ArraySpan,
    child_packed: PackedSpan,
    parent_array: ArraySpan,
    parent_packed: PackedSpan,
    array_filters: StaticArrayFilters,
    offset: BitDependency,
}

/// Cached output-actual geometry. Summary regions repeatedly query the same
/// endpoint, so rebuilding and linearly scanning a W-part concatenation for
/// each of W child regions would otherwise take quadratic work.
struct ActualFragmentLayout {
    fragments: Vec<ActualFragment>,
    array: FragmentIntervalOrder,
    packed: FragmentIntervalOrder,
}

struct FragmentIntervalOrder {
    indices: Vec<usize>,
    prefix_max_end: Vec<usize>,
}

impl FragmentIntervalOrder {
    fn new(fragments: &[ActualFragment], span: impl Fn(&ActualFragment) -> (usize, usize)) -> Self {
        let mut indices = (0..fragments.len()).collect::<Vec<_>>();
        indices.sort_unstable_by_key(|&index| span(&fragments[index]).0);
        let mut maximum = 0usize;
        let prefix_max_end = indices
            .iter()
            .map(|&index| {
                maximum = maximum.max(span(&fragments[index]).1);
                maximum
            })
            .collect();
        Self {
            indices,
            prefix_max_end,
        }
    }

    fn candidate_range(
        &self,
        fragments: &[ActualFragment],
        start: usize,
        end: usize,
        span: impl Fn(&ActualFragment) -> (usize, usize),
    ) -> std::ops::Range<usize> {
        let first = self
            .prefix_max_end
            .partition_point(|&maximum| maximum <= start);
        let last = self
            .indices
            .partition_point(|&index| span(&fragments[index]).0 < end);
        first.min(last)..last
    }
}

impl ActualFragmentLayout {
    fn new(fragments: Vec<ActualFragment>) -> Self {
        let array = FragmentIntervalOrder::new(&fragments, |fragment| {
            (
                fragment.child_array.start,
                fragment.child_array.end().unwrap_or(usize::MAX),
            )
        });
        let packed = FragmentIntervalOrder::new(&fragments, |fragment| {
            (fragment.child_packed.start, fragment.child_packed.end())
        });
        Self {
            fragments,
            array,
            packed,
        }
    }

    fn translate(&self, region: SummaryRegion) -> Option<Vec<TranslatedFragmentAccess>> {
        let array_end = region.array.end().unwrap_or(usize::MAX);
        let packed_end = region.packed.end();
        let array = self.array.candidate_range(
            &self.fragments,
            region.array.start,
            array_end,
            |fragment| {
                (
                    fragment.child_array.start,
                    fragment.child_array.end().unwrap_or(usize::MAX),
                )
            },
        );
        let packed = self.packed.candidate_range(
            &self.fragments,
            region.packed.start,
            packed_end,
            |fragment| (fragment.child_packed.start, fragment.child_packed.end()),
        );
        let order = if array.len() <= packed.len() {
            (&self.array, array)
        } else {
            (&self.packed, packed)
        };
        order.0.indices[order.1]
            .iter()
            .filter_map(|&index| {
                #[cfg(test)]
                INSTANCE_FRAGMENT_PROBES.set(INSTANCE_FRAGMENT_PROBES.get() + 1);
                let fragment = self.fragments[index].clone();
                let array = region.array.intersection(fragment.child_array)?;
                let packed = region.packed.intersection(fragment.child_packed)?;
                Some((fragment, array, packed))
            })
            .map(|(fragment, array, packed)| {
                translate_actual_fragment(region.id, fragment, array, packed)
            })
            .collect()
    }
}

#[derive(Clone)]
struct TranslatedFragmentAccess {
    parent: VarId,
    array: ArraySpan,
    packed: PackedSpan,
    array_filters: StaticArrayFilters,
    offset: BitDependency,
    child_domain: SummaryRegion,
}

#[allow(clippy::too_many_arguments)]
fn append_coerced_actual_fragments(
    fragments: &mut Vec<ActualFragment>,
    parent: VarId,
    child_array: ArraySpan,
    actual_packed: PackedSpan,
    parent_array: ArraySpan,
    parent_packed: PackedSpan,
    array_filters: &StaticArrayFilters,
    child_packed_width: usize,
    child_signed: bool,
) -> Option<()> {
    let array_offset = if parent_array.length == child_array.length {
        Some(signed_difference(parent_array.start, child_array.start)?)
    } else {
        None
    };

    let parent_segment = |actual: PackedSpan| -> Option<(PackedSpan, Option<isize>)> {
        if parent_packed.length == actual_packed.length {
            let relative = actual.start.checked_sub(actual_packed.start)?;
            let start = parent_packed.start.checked_add(relative)?;
            let parent = PackedSpan::new(start, actual.length)?;
            let offset = signed_difference(parent.start, actual.start)?;
            Some((parent, Some(offset)))
        } else {
            Some((parent_packed, None))
        }
    };

    let copied_width = child_packed_width.min(actual_packed.end());
    if let Some(copied) = actual_packed.intersection(PackedSpan::new(0, copied_width)?) {
        let (parent_packed, packed_offset) = parent_segment(copied)?;
        fragments.push(ActualFragment {
            parent,
            child_array,
            child_packed: copied,
            parent_array,
            parent_packed,
            array_filters: array_filters.clone(),
            offset: BitDependency {
                array: array_offset,
                packed: packed_offset,
            },
        });
    }

    if child_signed && child_packed_width != 0 {
        let actual_end = actual_packed.end();
        if actual_end > child_packed_width
            && let Some(extension) = actual_packed.intersection(PackedSpan::new(
                child_packed_width,
                actual_end.checked_sub(child_packed_width)?,
            )?)
        {
            let (parent_packed, _) = parent_segment(extension)?;
            fragments.push(ActualFragment {
                parent,
                child_array,
                child_packed: PackedSpan::new(child_packed_width - 1, 1)?,
                parent_array,
                parent_packed,
                array_filters: array_filters.clone(),
                offset: BitDependency {
                    array: array_offset,
                    packed: None,
                },
            });
        }
    }
    Some(())
}

fn destination_packed_width(destination: &AssignDestination, ctx: &mut Context) -> Option<usize> {
    if destination.select.is_empty() {
        return destination.comptime.r#type.total_width();
    }
    if let Some((op, width)) = &destination.select.1
        && matches!(
            op,
            VarSelectOp::PlusColon | VarSelectOp::MinusColon | VarSelectOp::Step
        )
    {
        let width = width.eval_value(ctx)?.to_usize()?;
        let dimension = destination.select.dimension();
        let shape = destination.comptime.r#type.width();
        if dimension == 0 || shape.dims() < dimension || width == 0 {
            return None;
        }
        return shape.as_slice()[dimension..]
            .iter()
            .try_fold(width, |total, inner| total.checked_mul((*inner)?));
    }
    destination
        .select
        .eval_comptime(ctx, &destination.comptime.r#type, false)?
        .total()
}

fn actual_fragments(
    child: &Variable,
    actual: &[AssignDestination],
    ctx: &mut Context,
) -> Option<Vec<ActualFragment>> {
    let child_array_length = child.r#type.array.total()?;
    let child_packed_width = child.total_width()?;
    let accesses = actual
        .iter()
        .map(|destination| {
            let array_length = destination.comptime.r#type.array.total()?;
            let packed_width = destination_packed_width(destination, ctx)?;
            let spans = var_reads(
                destination.id,
                &destination.index,
                &destination.select,
                destination.comptime.member_select_domain,
                ctx,
            );
            let [(parent_array, parent_packed)] = spans.as_slice() else {
                return None;
            };
            let array_filters = StaticArrayFilters::new(destination.id, &destination.index, ctx);
            Some((
                destination.id,
                *parent_array,
                *parent_packed,
                array_length,
                packed_width,
                array_filters,
            ))
        })
        .collect::<Option<Vec<_>>>()?;
    let array_length = accesses
        .iter()
        .try_fold(0usize, |total, (_, _, _, length, _, _)| {
            total.checked_add(*length)
        })?;
    if array_length == child_array_length {
        let mut child_start = 0usize;
        let mut fragments = Vec::new();
        for (parent, parent_array, parent_packed, array_length, packed_width, array_filters) in
            accesses
        {
            let child_array = ArraySpan {
                start: child_start,
                length: array_length,
            };
            child_start = child_start.checked_add(array_length)?;
            append_coerced_actual_fragments(
                &mut fragments,
                parent,
                child_array,
                PackedSpan::whole(packed_width)?,
                parent_array,
                parent_packed,
                &array_filters,
                child_packed_width,
                child.r#type.signed,
            )?;
        }
        return Some(fragments);
    }

    let packed_width = accesses
        .iter()
        .try_fold(0usize, |total, (_, _, _, _, width, _)| {
            total.checked_add(*width)
        })?;
    if child_array_length != 1
        || accesses
            .iter()
            .any(|(_, _, _, array_length, _, _)| *array_length != 1)
    {
        return None;
    }

    let mut actual_start = packed_width;
    let mut fragments = Vec::new();
    for (parent, parent_array, parent_packed, _, fragment_width, array_filters) in accesses {
        actual_start = actual_start.checked_sub(fragment_width)?;
        append_coerced_actual_fragments(
            &mut fragments,
            parent,
            ArraySpan {
                start: 0,
                length: 1,
            },
            PackedSpan::new(actual_start, fragment_width)?,
            parent_array,
            parent_packed,
            &array_filters,
            child_packed_width,
            child.r#type.signed,
        )?;
    }
    Some(fragments)
}

fn contiguous_actual_fragment(
    child: &Variable,
    actual: &InstActualFragment,
) -> Option<ActualFragment> {
    let child_array_length = child.r#type.array.total()?;
    let child_packed_width = child.total_width()?;
    if child_array_length != actual.parent_array_length
        || child_packed_width != actual.parent_packed_length
    {
        return None;
    }
    Some(ActualFragment {
        parent: actual.parent,
        child_array: ArraySpan {
            start: 0,
            length: child_array_length,
        },
        child_packed: PackedSpan::whole(child_packed_width)?,
        parent_array: ArraySpan {
            start: actual.parent_array_start,
            length: actual.parent_array_length,
        },
        parent_packed: PackedSpan::new(actual.parent_packed_start, actual.parent_packed_length)?,
        array_filters: StaticArrayFilters::default(),
        offset: BitDependency {
            array: Some(signed_difference(actual.parent_array_start, 0)?),
            packed: Some(signed_difference(actual.parent_packed_start, 0)?),
        },
    })
}

fn coerced_contiguous_actual_fragments(
    child: &Variable,
    actual: &InstActualFragment,
) -> Option<Vec<ActualFragment>> {
    let child_array_length = child.r#type.array.total()?;
    let child_packed_width = child.total_width()?;
    if child_array_length != actual.parent_array_length {
        return None;
    }
    let child_array = ArraySpan {
        start: 0,
        length: child_array_length,
    };
    let parent_array = ArraySpan {
        start: actual.parent_array_start,
        length: actual.parent_array_length,
    };
    let parent_packed = PackedSpan::new(actual.parent_packed_start, actual.parent_packed_length)?;
    let mut fragments = Vec::new();
    append_coerced_actual_fragments(
        &mut fragments,
        actual.parent,
        child_array,
        PackedSpan::whole(actual.parent_packed_length)?,
        parent_array,
        parent_packed,
        &StaticArrayFilters::default(),
        child_packed_width,
        child.r#type.signed,
    )?;
    Some(fragments)
}

fn coerced_input_contiguous_actual_fragments(
    child: &Variable,
    actual: &InstActualFragment,
    actual_signed: bool,
) -> Option<Vec<ActualFragment>> {
    let child_array_length = child.r#type.array.total()?;
    let child_packed_width = child.total_width()?;
    let actual_packed_width = actual.parent_packed_length;
    if child_array_length != actual.parent_array_length {
        return None;
    }

    let child_array = ArraySpan {
        start: 0,
        length: child_array_length,
    };
    let parent_array = ArraySpan {
        start: actual.parent_array_start,
        length: actual.parent_array_length,
    };
    let array_offset = Some(signed_difference(parent_array.start, child_array.start)?);
    let mut fragments = Vec::new();

    let copied_width = child_packed_width.min(actual_packed_width);
    if copied_width != 0 {
        let child_packed = PackedSpan::new(0, copied_width)?;
        let parent_packed = PackedSpan::new(actual.parent_packed_start, copied_width)?;
        fragments.push(ActualFragment {
            parent: actual.parent,
            child_array,
            child_packed,
            parent_array,
            parent_packed,
            array_filters: StaticArrayFilters::default(),
            offset: BitDependency {
                array: array_offset,
                packed: Some(signed_difference(parent_packed.start, child_packed.start)?),
            },
        });
    }

    if actual_signed && actual_packed_width != 0 && child_packed_width > actual_packed_width {
        fragments.push(ActualFragment {
            parent: actual.parent,
            child_array,
            child_packed: PackedSpan::new(
                actual_packed_width,
                child_packed_width.checked_sub(actual_packed_width)?,
            )?,
            parent_array,
            parent_packed: PackedSpan::new(
                actual
                    .parent_packed_start
                    .checked_add(actual_packed_width - 1)?,
                1,
            )?,
            array_filters: StaticArrayFilters::default(),
            offset: BitDependency {
                array: array_offset,
                packed: None,
            },
        });
    }
    Some(fragments)
}

fn translate_actual_fragments(
    region: SummaryRegion,
    fragments: impl IntoIterator<Item = ActualFragment>,
) -> Option<Vec<TranslatedFragmentAccess>> {
    fragments
        .into_iter()
        .filter_map(|fragment| {
            let array = region.array.intersection(fragment.child_array)?;
            let packed = region.packed.intersection(fragment.child_packed)?;
            Some((fragment, array, packed))
        })
        .map(|(fragment, array, packed)| {
            translate_actual_fragment(region.id, fragment, array, packed)
        })
        .collect()
}

fn translate_actual_fragment(
    child: VarId,
    fragment: ActualFragment,
    child_array: ArraySpan,
    child_packed: PackedSpan,
) -> Option<TranslatedFragmentAccess> {
    let array = if fragment.offset.array.is_some() {
        child_array.translated(fragment.child_array.start, fragment.parent_array.start)?
    } else {
        fragment.parent_array
    };
    let packed = if fragment.offset.packed.is_some() {
        child_packed.translated(fragment.child_packed.start, fragment.parent_packed.start)?
    } else {
        fragment.parent_packed
    };
    Some(TranslatedFragmentAccess {
        parent: fragment.parent,
        array,
        packed,
        array_filters: fragment.array_filters,
        offset: fragment.offset,
        child_domain: SummaryRegion {
            id: child,
            array: child_array,
            packed: child_packed,
        },
    })
}

fn translated_interface_binding_accesses(
    region: SummaryRegion,
    child: &Variable,
    binding: &InstInterfaceBinding,
) -> Option<Vec<TranslatedFragmentAccess>> {
    translate_actual_fragments(
        region,
        [contiguous_actual_fragment(child, &binding.actual)?],
    )
}

fn translated_coerced_input_contiguous_actual_accesses(
    region: SummaryRegion,
    child: &Variable,
    actual: &InstActualFragment,
    actual_signed: bool,
) -> Option<Vec<TranslatedFragmentAccess>> {
    translate_actual_fragments(
        region,
        coerced_input_contiguous_actual_fragments(child, actual, actual_signed)?,
    )
}

fn map_translated_fragment_accesses(
    accesses: Vec<TranslatedFragmentAccess>,
    bit_part: &BitPartition,
) -> InstanceRegionMapping {
    let mut nodes = Vec::new();
    for access in accesses {
        nodes.extend(
            filtered_actual_keys(
                bit_part,
                access.parent,
                access.array,
                access.packed,
                &access.array_filters,
            )
            .into_iter()
            .map(|key| MappedNode {
                key,
                offset: access.offset,
                child_domain: Some(access.child_domain),
                condition: PathCondition::default(),
            }),
        );
    }
    InstanceRegionMapping { nodes }
}

fn map_summary_region_to_interface_binding(
    region: SummaryRegion,
    child: &Variable,
    binding: &InstInterfaceBinding,
    bit_part: &BitPartition,
) -> Option<InstanceRegionMapping> {
    let accesses = translated_interface_binding_accesses(region, child, binding)?;
    Some(map_translated_fragment_accesses(accesses, bit_part))
}

fn map_summary_region_to_coerced_input_contiguous_actual(
    region: SummaryRegion,
    child: &Variable,
    actual: &InstActualFragment,
    actual_signed: bool,
    bit_part: &BitPartition,
) -> Option<InstanceRegionMapping> {
    let accesses =
        translated_coerced_input_contiguous_actual_accesses(region, child, actual, actual_signed)?;
    Some(map_translated_fragment_accesses(accesses, bit_part))
}

#[allow(clippy::too_many_arguments)]
fn map_summary_region(
    region: SummaryRegion,
    child: &Variable,
    parent: VarId,
    index: &crate::ir::VarIndex,
    select: &VarSelect,
    member_select_domain: Option<MemberSelectDomain>,
    array_filters: &StaticArrayFilters,
    bit_part: &BitPartition,
    ctx: &mut Context,
) -> InstanceRegionMapping {
    let mut keys = Vec::new();
    let offset = if let Some((array, packed, offset)) = translated_summary_access(
        region,
        child,
        parent,
        index,
        select,
        member_select_domain,
        ctx,
    ) {
        keys.extend(bit_part.overlapping_access(parent, array, packed));
        Some(offset)
    } else {
        for (array, packed) in var_reads(parent, index, select, member_select_domain, ctx) {
            keys.extend(filtered_actual_keys(
                bit_part,
                parent,
                array,
                packed,
                array_filters,
            ));
        }
        None
    };
    keys.sort_unstable();
    keys.dedup();
    InstanceRegionMapping {
        nodes: keys
            .into_iter()
            .map(|key| MappedNode {
                key,
                offset: offset.map_or(BitDependency::WHOLE, |(array, packed)| BitDependency {
                    array: Some(array),
                    packed: Some(packed),
                }),
                child_domain: None,
                condition: PathCondition::default(),
            })
            .collect(),
    }
}

fn translated_summary_access(
    region: SummaryRegion,
    child: &Variable,
    parent: VarId,
    index: &crate::ir::VarIndex,
    select: &VarSelect,
    member_select_domain: Option<MemberSelectDomain>,
    ctx: &mut Context,
) -> Option<(ArraySpan, PackedSpan, (isize, isize))> {
    let accesses = var_reads(parent, index, select, member_select_domain, ctx);
    let [(parent_array, parent_packed)] = accesses.as_slice() else {
        return None;
    };
    if !index
        .0
        .iter()
        .all(|expression| expression.comptime().is_const)
        || !select.is_const_with_range()
        || child.r#type.array.total() != Some(parent_array.length)
        || child.total_width() != Some(parent_packed.length)
    {
        return None;
    }
    let start = region.array.start.checked_add(parent_array.start)?;
    let array = (region.array.end()? <= parent_array.length).then_some(ArraySpan {
        start,
        length: region.array.length,
    })?;
    let packed = region
        .packed
        .translated(0, parent_packed.start)?
        .intersection(*parent_packed)?;
    let offset = (
        signed_difference(parent_array.start, 0)?,
        signed_difference(parent_packed.start, 0)?,
    );
    Some((array, packed, offset))
}

fn resolve_instance_mapping(
    graph: &mut DependencyGraph,
    node_map: &mut HashMap<NodeKey, NodeIndex>,
    bit_part: &BitPartition,
    mapping: InstanceRegionMapping,
    boundary_flow: BoundaryFlow,
) -> ResolvedInstanceRegionMapping {
    let nodes = mapping
        .nodes
        .into_iter()
        .filter_map(|mapped| {
            let parent = ensure_node(graph, node_map, bit_part, mapped.key)?;
            if let Some(child_domain) = mapped.child_domain
                && (mapped.offset.array.is_none() || mapped.offset.packed.is_none())
            {
                // Preserve the exact child endpoint until after the imported
                // summary edge. Otherwise a broadcast/dynamic boundary would
                // erase which child bit or element feeds the parent region.
                let boundary = graph.add_node(GraphNode {
                    region: child_domain,
                    domains: vec![PositionDomain {
                        array_start: child_domain.array.start,
                        array_length: child_domain.array.length,
                        packed_start: child_domain.packed.start,
                        packed_length: child_domain.packed.length,
                    }],
                    regular_transfer: false,
                    diagnostic: None,
                });
                let (source, destination) = match boundary_flow {
                    BoundaryFlow::ParentToChild => (parent, boundary),
                    BoundaryFlow::ChildToParent => (boundary, parent),
                };
                let kind = match boundary_flow {
                    BoundaryFlow::ParentToChild => BitDependency {
                        array: mapped.offset.array.map(|offset| {
                            offset
                                .checked_neg()
                                .expect("mapped array dependency offset must fit in isize")
                        }),
                        packed: mapped.offset.packed.map(|offset| {
                            offset
                                .checked_neg()
                                .expect("mapped packed dependency offset must fit in isize")
                        }),
                    },
                    BoundaryFlow::ChildToParent => mapped.offset,
                };
                add_dependency_edge(
                    graph,
                    source,
                    destination,
                    GraphDependency {
                        kind,
                        condition: mapped.condition,
                        carrier: false,
                    },
                );
                return Some(ResolvedMappedNode {
                    node: boundary,
                    offset: BitDependency::identity(),
                    condition: PathCondition::default(),
                });
            }
            Some(ResolvedMappedNode {
                node: parent,
                offset: mapped.offset,
                condition: mapped.condition,
            })
        })
        .collect();
    ResolvedInstanceRegionMapping { nodes }
}

fn add_resolved_dependency_edges(
    graph: &mut DependencyGraph,
    sources: &ResolvedInstanceRegionMapping,
    destinations: &ResolvedInstanceRegionMapping,
    dependency: BitDependency,
    condition: &PathCondition,
    carrier: bool,
) {
    for source in &sources.nodes {
        for destination in &destinations.nodes {
            let Some(edge_condition) = condition
                .conjoin_if_compatible(&source.condition)
                .and_then(|condition| condition.conjoin_if_compatible(&destination.condition))
            else {
                continue;
            };
            let kind = BitDependency {
                array: dependency
                    .array
                    .zip(source.offset.array)
                    .zip(destination.offset.array)
                    .map(|((dependency, source), destination)| {
                        dependency
                            .checked_add(destination)
                            .and_then(|offset| offset.checked_sub(source))
                            .expect("mapped array dependency offset must fit in isize")
                    }),
                packed: dependency
                    .packed
                    .zip(source.offset.packed)
                    .zip(destination.offset.packed)
                    .map(|((dependency, source), destination)| {
                        dependency
                            .checked_add(destination)
                            .and_then(|offset| offset.checked_sub(source))
                            .expect("mapped packed dependency offset must fit in isize")
                    }),
            };
            if graph[source.node].diagnostic.is_some()
                && graph[destination.node].diagnostic.is_some()
                && !node_regions_overlap_with_dependency(
                    &graph[source.node],
                    &graph[destination.node],
                    kind,
                )
            {
                continue;
            }
            add_dependency_edge(
                graph,
                source.node,
                destination.node,
                GraphDependency {
                    kind,
                    condition: edge_condition,
                    carrier,
                },
            );
        }
    }
}

fn is_pure_input_or_output(id: VarId, vars: &HashMap<VarId, Variable>, want: Direction) -> bool {
    let Some(v) = vars.get(&id) else { return false };
    use crate::ir::VarKind;
    let actual = match v.kind {
        VarKind::Input => Direction::Input,
        VarKind::Output => Direction::Output,
        _ => return false,
    };
    actual == want
}

fn analyze_instance_actual<'a>(
    bit_part: &'a BitPartition,
    expression: &Expression,
    ctx: &mut Context,
    procedure_context: &mut procedure::ProcedureContext,
    summaries: &mut procedure::FunctionSummaries<'a>,
) -> (
    Vec<procedure::RegionSource>,
    Vec<procedure::Dependency>,
    bool,
) {
    let mut analysis = InstanceActualAnalysis::new(bit_part, ctx, procedure_context, summaries);
    analysis.eval(expression);
    analysis.finish()
}

struct InstanceActualRegionAnalysis {
    reads: Vec<procedure::RegionSource>,
    mappings: Vec<(SummaryRegion, InstanceRegionMapping)>,
    dependencies: Vec<procedure::Dependency>,
    complete: bool,
}

fn analyze_instance_actual_regions<'a>(
    bit_part: &'a BitPartition,
    expression: &Expression,
    requests: &[SummaryRegion],
    context_width: usize,
    procedure_context: &mut procedure::ProcedureContext,
    summaries: &mut procedure::FunctionSummaries<'a>,
) -> InstanceActualRegionAnalysis {
    let mut analysis = procedure::ExpressionAnalysis::new(bit_part, procedure_context, summaries);
    let expression_requests = requests
        .iter()
        .map(|region| procedure::ExpressionRegion {
            array: region.array,
            packed: region.packed,
            context_width,
        })
        .collect::<Vec<_>>();
    let (reads, mapped) = analysis.eval_with_regions(expression, &expression_requests);
    let mappings = requests
        .iter()
        .copied()
        .zip(mapped)
        .map(|(region, (_, sources))| {
            (
                region,
                InstanceRegionMapping {
                    nodes: sources
                        .into_iter()
                        .map(|source| MappedNode {
                            key: source.key,
                            offset: source.offset.map_or(
                                BitDependency::WHOLE,
                                |(array, packed)| BitDependency {
                                    array: Some(array),
                                    packed: Some(packed),
                                },
                            ),
                            child_domain: None,
                            condition: source.condition,
                        })
                        .collect(),
                },
            )
        })
        .collect();
    let dependencies = analysis.dependencies();
    let complete = analysis.is_complete();
    let result = InstanceActualRegionAnalysis {
        reads,
        mappings,
        dependencies,
        complete,
    };
    analysis.restore(procedure_context);
    result
}

fn analyze_instance_destination<'a>(
    bit_part: &'a BitPartition,
    destination: &AssignDestination,
    ctx: &mut Context,
    procedure_context: &mut procedure::ProcedureContext,
    summaries: &mut procedure::FunctionSummaries<'a>,
) -> (
    Vec<procedure::RegionSource>,
    Vec<procedure::Dependency>,
    bool,
) {
    let mut analysis = InstanceActualAnalysis::new(bit_part, ctx, procedure_context, summaries);
    for expression in destination
        .index
        .0
        .iter()
        .chain(destination.select.0.iter())
    {
        analysis.eval(expression);
    }
    if let Some((_, expression)) = &destination.select.1 {
        analysis.eval(expression);
    }
    analysis.finish()
}

struct InstanceActualAnalysis<'a, 's, 'c> {
    bit_part: &'a BitPartition,
    ctx: &'c mut Context,
    procedure_context: &'c mut procedure::ProcedureContext,
    summaries: Option<&'s mut procedure::FunctionSummaries<'a>>,
    procedure: Option<procedure::ExpressionAnalysis<'a, 's>>,
    reads: Vec<procedure::RegionSource>,
}

impl<'a, 's, 'c> InstanceActualAnalysis<'a, 's, 'c> {
    fn new(
        bit_part: &'a BitPartition,
        ctx: &'c mut Context,
        procedure_context: &'c mut procedure::ProcedureContext,
        summaries: &'s mut procedure::FunctionSummaries<'a>,
    ) -> Self {
        Self {
            bit_part,
            ctx,
            procedure_context,
            summaries: Some(summaries),
            procedure: None,
            reads: Vec::new(),
        }
    }

    fn finish(
        mut self,
    ) -> (
        Vec<procedure::RegionSource>,
        Vec<procedure::Dependency>,
        bool,
    ) {
        self.reads
            .sort_unstable_by_key(|source| (source.key, source.condition.clone()));
        self.reads
            .dedup_by(|left, right| left.key == right.key && left.condition == right.condition);
        let complete = self
            .procedure
            .as_mut()
            .is_none_or(procedure::ExpressionAnalysis::is_complete);
        let dependencies = if let Some(mut procedure) = self.procedure.take() {
            let dependencies = procedure.dependencies();
            procedure.restore(self.procedure_context);
            dependencies
        } else {
            Vec::new()
        };
        (self.reads, dependencies, complete)
    }

    fn eval(&mut self, expression: &Expression) {
        if let Some(procedure) = &mut self.procedure {
            self.reads.extend(procedure.eval(expression));
            return;
        }
        // Once an actual needs guarded SSA, analyze its complete syntax tree.
        // Starting at the first nested conditional or call would give that
        // subtree a different branch namespace from later region projections
        // of the complete actual, so mutually exclusive paths could combine.
        if requires_guarded_expression_analysis(expression) {
            let summaries = self.summaries.take().expect("initialized once");
            let mut procedure = procedure::ExpressionAnalysis::new(
                self.bit_part,
                self.procedure_context,
                summaries,
            );
            self.reads.extend(procedure.eval(expression));
            self.procedure = Some(procedure);
            return;
        }
        self.eval_unguarded(expression);
    }

    /// Collect reads after `eval` has established that the complete
    /// expression contains no guarded construct. Descendants are therefore
    /// unguarded as well, so walking them must not repeat the whole-subtree
    /// classification at every level.
    fn eval_unguarded(&mut self, expression: &Expression) {
        match expression {
            Expression::Term(factor) => match factor.as_ref() {
                Factor::FunctionCall(_) => unreachable!("guarded expression checked above"),
                Factor::Variable(_, index, select, _) => {
                    for expression in index.0.iter().chain(select.0.iter()) {
                        self.eval_unguarded(expression);
                    }
                    if let Some((_, expression)) = &select.1 {
                        self.eval_unguarded(expression);
                    }
                    let mut reads = Vec::new();
                    collect_factor_node_keys(factor, self.bit_part, &mut reads, self.ctx);
                    self.reads
                        .extend(reads.into_iter().map(|key| procedure::RegionSource {
                            key,
                            offset: None,
                            condition: PathCondition::default(),
                        }));
                }
                Factor::SystemFunctionCall(call) => match &call.kind {
                    SystemFunctionKind::Onehot(input)
                    | SystemFunctionKind::Signed(input)
                    | SystemFunctionKind::Unsigned(input)
                    | SystemFunctionKind::Readmemh(input, _) => self.eval_unguarded(&input.0),
                    SystemFunctionKind::Bits(_)
                    | SystemFunctionKind::Size(_)
                    | SystemFunctionKind::Clog2(_)
                    | SystemFunctionKind::Display(_)
                    | SystemFunctionKind::Write(_)
                    | SystemFunctionKind::Assert { .. }
                    | SystemFunctionKind::Finish => {}
                },
                _ => {}
            },
            Expression::Unary(_, operand, _) => self.eval_unguarded(operand),
            Expression::Binary(left, _, right, _) => {
                self.eval_unguarded(left);
                self.eval_unguarded(right);
            }
            Expression::Ternary(_, _, _, _) => unreachable!("guarded expression checked above"),
            Expression::Concatenation(parts, _) => {
                for (part, repeat) in parts {
                    self.eval_unguarded(part);
                    if let Some(repeat) = repeat {
                        self.eval_unguarded(repeat);
                    }
                }
            }
            Expression::ArrayLiteral(items, _) => {
                for item in items {
                    match item {
                        crate::ir::ArrayLiteralItem::Value(value, repeat) => {
                            self.eval_unguarded(value);
                            if let Some(repeat) = repeat {
                                self.eval_unguarded(repeat);
                            }
                        }
                        crate::ir::ArrayLiteralItem::Defaul(value) => self.eval_unguarded(value),
                    }
                }
            }
            Expression::StructConstructor(_, fields, _) => {
                for (_, value) in fields {
                    self.eval_unguarded(value);
                }
            }
        }
    }
}

fn requires_guarded_expression_analysis(expression: &Expression) -> bool {
    #[cfg(test)]
    GUARDED_EXPRESSION_PROBES.set(GUARDED_EXPRESSION_PROBES.get() + 1);
    match expression {
        Expression::Term(factor) => match factor.as_ref() {
            Factor::FunctionCall(_) => true,
            Factor::Variable(_, index, select, _) => {
                var_access_requires_guarded_analysis(index, select)
            }
            Factor::SystemFunctionCall(call) => match &call.kind {
                SystemFunctionKind::Bits(input)
                | SystemFunctionKind::Size(input)
                | SystemFunctionKind::Clog2(input)
                | SystemFunctionKind::Onehot(input)
                | SystemFunctionKind::Signed(input)
                | SystemFunctionKind::Unsigned(input) => {
                    requires_guarded_expression_analysis(&input.0)
                }
                SystemFunctionKind::Readmemh(input, output) => {
                    requires_guarded_expression_analysis(&input.0)
                        || output.0.iter().any(|destination| {
                            var_access_requires_guarded_analysis(
                                &destination.index,
                                &destination.select,
                            )
                        })
                }
                SystemFunctionKind::Display(inputs) | SystemFunctionKind::Write(inputs) => inputs
                    .iter()
                    .any(|input| requires_guarded_expression_analysis(&input.0)),
                SystemFunctionKind::Assert { cond, args, .. } => {
                    requires_guarded_expression_analysis(&cond.0)
                        || args
                            .iter()
                            .any(|input| requires_guarded_expression_analysis(&input.0))
                }
                SystemFunctionKind::Finish => false,
            },
            _ => false,
        },
        Expression::Unary(_, operand, _) => requires_guarded_expression_analysis(operand),
        Expression::Binary(left, op, right, _) => {
            matches!(op, Op::LogicAnd | Op::LogicOr)
                || requires_guarded_expression_analysis(left)
                || requires_guarded_expression_analysis(right)
        }
        Expression::Ternary(_, _, _, _) => true,
        Expression::Concatenation(parts, _) => parts.iter().any(|(part, repeat)| {
            requires_guarded_expression_analysis(part)
                || repeat
                    .as_ref()
                    .is_some_and(requires_guarded_expression_analysis)
        }),
        Expression::ArrayLiteral(items, _) => items.iter().any(|item| match item {
            crate::ir::ArrayLiteralItem::Value(value, repeat) => {
                requires_guarded_expression_analysis(value)
                    || repeat
                        .as_ref()
                        .is_some_and(|repeat| requires_guarded_expression_analysis(repeat))
            }
            crate::ir::ArrayLiteralItem::Defaul(value) => {
                requires_guarded_expression_analysis(value)
            }
        }),
        Expression::StructConstructor(_, fields, _) => fields
            .iter()
            .any(|(_, value)| requires_guarded_expression_analysis(value)),
    }
}

fn var_access_requires_guarded_analysis(
    index: &crate::ir::VarIndex,
    select: &crate::ir::VarSelect,
) -> bool {
    index
        .0
        .iter()
        .chain(select.0.iter())
        .any(requires_guarded_expression_analysis)
        || select
            .1
            .as_ref()
            .is_some_and(|(_, expression)| requires_guarded_expression_analysis(expression))
}

fn collect_factor_node_keys(
    factor: &Factor,
    bit_part: &BitPartition,
    out: &mut Vec<NodeKey>,
    ctx: &mut Context,
) {
    match factor {
        Factor::Variable(id, index, select, comptime) => {
            let array_filters = StaticArrayFilters::new(*id, index, ctx);
            for (idx, span) in var_reads(*id, index, select, comptime.member_select_domain, ctx) {
                out.extend(filtered_actual_keys(
                    bit_part,
                    *id,
                    idx,
                    span,
                    &array_filters,
                ));
            }
        }
        Factor::FunctionCall(_) | Factor::SystemFunctionCall(_) => {
            // No caller LHS at an inst input -- under-detect.
        }
        _ => {}
    }
}

fn collect_dst_node_keys(
    dst: &AssignDestination,
    bit_part: &BitPartition,
    out: &mut Vec<NodeKey>,
    ctx: &mut Context,
) {
    let array_filters = StaticArrayFilters::new(dst.id, &dst.index, ctx);
    for (array, packed) in dst_writes(dst, ctx) {
        out.extend(filtered_actual_keys(
            bit_part,
            dst.id,
            array,
            packed,
            &array_filters,
        ));
    }
}

fn is_module_scope_var(id: VarId, variables: &HashMap<VarId, Variable>) -> bool {
    match variables.get(&id) {
        Some(v) => matches!(v.affiliation, Affiliation::Module | Affiliation::Interface),
        None => true,
    }
}

fn is_inout(id: VarId, variables: &HashMap<VarId, Variable>) -> bool {
    variables
        .get(&id)
        .is_some_and(|variable| matches!(variable.kind, crate::ir::VarKind::Inout))
}

#[cfg(test)]
mod partition_tests {
    use super::*;

    #[test]
    fn disjoint_array_point_queries_do_not_scan_every_partition() {
        const COUNT: usize = 16_384;

        let id = VarId::from_raw(0);
        let packed = PackedSpan {
            start: 0,
            length: 32,
        };
        let mut accesses = HashMap::default();
        for start in 0..COUNT {
            accesses.insert((id, ArraySpan { start, length: 1 }), vec![packed]);
        }

        let ranges = split_array_spans(accesses, &HashMap::default());
        let partition = BitPartition::new(ranges);
        assert_eq!(partition.array_spans(id).len(), COUNT);
        for start in 0..COUNT {
            assert_eq!(
                partition.overlapping_access(id, ArraySpan { start, length: 1 }, packed),
                vec![(id, ArraySpan { start, length: 1 }, 0)]
            );
        }
    }

    #[test]
    fn array_partition_sweep_keeps_an_access_active_until_its_own_end() {
        let id = VarId::from_raw(0);
        let packed = PackedSpan {
            start: 0,
            length: 1,
        };
        let mut accesses = HashMap::default();
        accesses.insert(
            (
                id,
                ArraySpan {
                    start: 0,
                    length: 2,
                },
            ),
            vec![packed],
        );
        accesses.insert(
            (
                id,
                ArraySpan {
                    start: 1,
                    length: 2,
                },
            ),
            vec![packed],
        );

        let ranges = split_array_spans(accesses, &HashMap::default());
        for start in 0..3 {
            assert_eq!(
                ranges
                    .get(&(id, ArraySpan { start, length: 1 }))
                    .map(Vec::as_slice),
                Some([packed].as_slice())
            );
        }
    }

    #[test]
    fn packed_partition_storage_depends_on_endpoints_not_declared_width() {
        let distant = 1_000_000_000;
        let spans = [
            PackedSpan {
                start: 0,
                length: 1,
            },
            PackedSpan {
                start: distant,
                length: 1,
            },
        ];

        assert_eq!(atomic_ranges(&spans, None), spans);
    }
}
