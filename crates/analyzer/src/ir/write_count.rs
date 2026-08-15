//! Self-references an always_ff element cannot make without a register.
//!
//! Dropping the register is sound only while a self-reference still sees the
//! value the block started with.  Statements write in place, so a write that
//! has already run is what the read gets: `s = s + 1; s = s + 1` would
//! increment twice, and `s[7:0] = a; s[15:8] = s[15:8] + s[7:0]` would take
//! the new `s[7:0]`.  Both the overlap and the order are needed —
//! `x = x + 1; if c { x = 0 }` reads nothing it has written, and a shift run
//! from the far end (`for i in rev 0..N { q[i + 1] = q[i] }`) reaches each
//! bit only after reading it.
//!
//! Branch arms are alternatives, so what leaves a branch is the union of what
//! its arms may have written.  Const bounds are walked per iteration, which is
//! what makes each index and select concrete; without them every write the
//! body holds counts as already done, since it runs again.

use crate::HashMap;
use crate::HashSet;
use crate::conv::Context;
use crate::ir::ff_table::PackedMask;
use crate::ir::variable::FlatIndexSet;
use crate::ir::{
    ArrayLiteralItem, AssignDestination, Declaration, Expression, Factor, FunctionCall, Statement,
    SystemFunctionCall, SystemFunctionKind, VarId, VarKind,
};
use crate::symbol::Affiliation;
use crate::value::Value;
use std::collections::BTreeMap;

#[cfg(test)]
thread_local! {
    static SCALING_COUNTERS: std::cell::Cell<(usize, usize, usize)> = const {
        std::cell::Cell::new((0, 0, 0))
    };
    static RANGE_ENTRY_WORK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static RUNTIME_FOOTPRINT_STATEMENT_VISITS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static DESTINATION_CANDIDATE_VISITS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static READ_GROUP_COMPARISONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(super) fn reset_scaling_counters() {
    SCALING_COUNTERS.set((0, 0, 0));
    RANGE_ENTRY_WORK.set(0);
    RUNTIME_FOOTPRINT_STATEMENT_VISITS.set(0);
    DESTINATION_CANDIDATE_VISITS.set(0);
    READ_GROUP_COMPARISONS.set(0);
}

#[cfg(test)]
pub(super) fn scaling_counters() -> (usize, usize, usize) {
    SCALING_COUNTERS.get()
}

#[cfg(test)]
pub(super) fn range_entry_work() -> usize {
    RANGE_ENTRY_WORK.get()
}

#[cfg(test)]
pub(super) fn runtime_footprint_statement_visits() -> usize {
    RUNTIME_FOOTPRINT_STATEMENT_VISITS.get()
}

#[cfg(test)]
pub(super) fn destination_candidate_visits() -> usize {
    DESTINATION_CANDIDATE_VISITS.get()
}

#[cfg(test)]
pub(super) fn read_group_comparisons() -> usize {
    READ_GROUP_COMPARISONS.get()
}

#[cfg(test)]
fn count_destination_candidate_visit() {
    DESTINATION_CANDIDATE_VISITS.set(DESTINATION_CANDIDATE_VISITS.get() + 1);
}

#[cfg(not(test))]
fn count_destination_candidate_visit() {}

#[cfg(test)]
fn count_read_group_comparison() {
    READ_GROUP_COMPARISONS.set(READ_GROUP_COMPARISONS.get() + 1);
}

#[cfg(not(test))]
fn count_read_group_comparison() {}

#[cfg(test)]
fn count_runtime_footprint_statement_visit() {
    RUNTIME_FOOTPRINT_STATEMENT_VISITS.set(RUNTIME_FOOTPRINT_STATEMENT_VISITS.get() + 1);
}

#[cfg(not(test))]
fn count_runtime_footprint_statement_visit() {}

#[cfg(test)]
fn count_range_entry_work(count: usize) {
    RANGE_ENTRY_WORK.set(RANGE_ENTRY_WORK.get() + count);
}

#[cfg(not(test))]
fn count_range_entry_work(_count: usize) {}

#[cfg(test)]
fn count_state_merge() {
    SCALING_COUNTERS.with(|counters| {
        let (state, ranges, arms) = counters.get();
        counters.set((state + 1, ranges, arms));
    });
}

#[cfg(not(test))]
fn count_state_merge() {}

#[cfg(test)]
fn count_range_insert() {
    SCALING_COUNTERS.with(|counters| {
        let (state, ranges, arms) = counters.get();
        counters.set((state, ranges + 1, arms));
    });
}

#[cfg(not(test))]
fn count_range_insert() {}

#[cfg(test)]
fn count_branch_arm() {
    SCALING_COUNTERS.with(|counters| {
        let (state, ranges, arms) = counters.get();
        counters.set((state, ranges, arms + 1));
    });
}

#[cfg(not(test))]
fn count_branch_arm() {}

/// Elements that must keep their register, as `(declaration index, VarId,
/// array element)`.
pub type UnsafeSelfReads = HashSet<(usize, VarId, usize)>;

type WrittenKey = (VarId, usize);

/// A token-independent set of array elements written with the same packed
/// mask. Keeping the geometry intact lets repeated dynamic destinations prove
/// that their candidate relation is already present without revisiting every
/// element.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct DestinationGroup {
    id: VarId,
    candidates: FlatIndexSet,
    mask: PackedMask,
}

impl DestinationGroup {
    fn for_each(&self, mut f: impl FnMut(WrittenKey, Mask)) {
        let mask = Mask::from(self.mask);
        for index in self.candidates.clone() {
            count_destination_candidate_visit();
            f((self.id, index), mask.clone());
        }
    }
}

/// Structural statement weights used to retain the largest branch in place.
/// Replaying only smaller sibling deltas gives the traversal a heavy/light
/// bound: each write can cross only O(log N) rolled-back branch boundaries.
struct StatementWeights(HashMap<usize, usize>);

impl StatementWeights {
    fn new(statements: &[Statement]) -> Self {
        let mut weights = HashMap::default();
        let mut stack = statements
            .iter()
            .rev()
            .map(|statement| (statement, false))
            .collect::<Vec<_>>();
        while let Some((statement, visited)) = stack.pop() {
            if visited {
                let mut weight = 1usize;
                for_each_child(statement, |child| {
                    weight = weight.saturating_add(weights[&statement_key(child)]);
                });
                weights.insert(statement_key(statement), weight);
            } else {
                stack.push((statement, true));
                for_each_child(statement, |child| stack.push((child, false)));
            }
        }
        Self(weights)
    }

    fn sequence(&self, statements: &[Statement]) -> usize {
        statements.iter().fold(0usize, |weight, statement| {
            weight.saturating_add(self.0[&statement_key(statement)])
        })
    }
}

fn statement_key(statement: &Statement) -> usize {
    std::ptr::from_ref(statement).addr()
}

fn for_each_child<'a>(statement: &'a Statement, mut f: impl FnMut(&'a Statement)) {
    match statement {
        Statement::If(statement) => {
            statement.true_side.iter().for_each(&mut f);
            statement.false_side.iter().for_each(&mut f);
        }
        Statement::IfReset(statement) => {
            statement.true_side.iter().for_each(&mut f);
            statement.false_side.iter().for_each(&mut f);
        }
        Statement::Case(statement) => {
            for arm in &statement.arms {
                arm.body.iter().for_each(&mut f);
            }
            statement.default.iter().for_each(&mut f);
        }
        Statement::For(statement) => statement.body.iter().for_each(f),
        _ => {}
    }
}

/// Sparse packed-bit coverage. The ranges are inclusive, disjoint, and
/// coalesced. `All` is the conservative result for a dynamic/unknown select.
#[derive(Clone, Debug)]
enum Mask {
    Ranges(BitRanges),
    All,
}

impl Default for Mask {
    fn default() -> Self {
        Self::Ranges(BitRanges::default())
    }
}

impl From<PackedMask> for Mask {
    fn from(value: PackedMask) -> Self {
        match value {
            PackedMask::Range { high, low } => {
                let mut ranges = BitRanges::default();
                let _ = ranges.insert(low.min(high), low.max(high));
                Self::Ranges(ranges)
            }
            PackedMask::Unknown => Self::All,
        }
    }
}

impl Mask {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Ranges(ranges) if ranges.0.is_empty())
    }

    fn overlaps(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::All, _) | (_, Self::All) => true,
            (Self::Ranges(left), Self::Ranges(right)) => left.overlaps(right),
        }
    }

    fn merge(&mut self, other: Self) {
        match other {
            Self::All => *self = Self::All,
            Self::Ranges(mut other) => match self {
                Self::All => {}
                Self::Ranges(ranges) => {
                    if other
                        .0
                        .iter()
                        .any(|(&low, &high)| ranges.merge_work_exceeds_limit(low, high))
                    {
                        *self = Self::All;
                        return;
                    }
                    if ranges.0.len() < other.0.len() {
                        std::mem::swap(ranges, &mut other);
                    }
                    for (low, high) in other.0 {
                        let _ = ranges.insert(low, high);
                    }
                }
            },
        }
    }
}

#[derive(Clone, Debug, Default)]
struct BitRanges(BTreeMap<usize, usize>);

struct RangeUndo {
    inserted: (usize, usize),
    removed: Vec<(usize, usize)>,
}

impl BitRanges {
    // Merging a broad branch delta through an arbitrarily fragmented prefix
    // can otherwise repeat quadratic removal/rollback work. Above this bound
    // the analysis deliberately widens to `Mask::All`: sound, but potentially
    // conservative for a later read outside the known packed ranges.
    const MERGE_WORK_LIMIT: usize = 8;

    fn merge_work_exceeds_limit(&self, low: usize, high: usize) -> bool {
        let mut touched = usize::from(
            self.0
                .range(..low)
                .next_back()
                .is_some_and(|(_, end)| end.saturating_add(1) >= low),
        );
        let limit = high.saturating_add(1);
        for (&start, _) in self.0.range(low..) {
            if start > limit {
                break;
            }
            touched += 1;
            if touched > Self::MERGE_WORK_LIMIT {
                return true;
            }
        }
        false
    }

    fn insert(&mut self, low: usize, high: usize) -> Option<RangeUndo> {
        count_range_insert();
        debug_assert!(low <= high);
        if self
            .0
            .range(..=low)
            .next_back()
            .is_some_and(|(_, end)| *end >= high)
        {
            return None;
        }

        let mut merged_low = low;
        let mut merged_high = high;
        let mut removed = Vec::new();
        if let Some((&start, &end)) = self.0.range(..=low).next_back()
            && end.saturating_add(1) >= low
        {
            self.0.remove(&start);
            removed.push((start, end));
            merged_low = start;
            merged_high = merged_high.max(end);
        }
        while let Some((&start, &end)) = self.0.range(merged_low..).next() {
            if start > merged_high.saturating_add(1) {
                break;
            }
            self.0.remove(&start);
            removed.push((start, end));
            merged_high = merged_high.max(end);
        }
        self.0.insert(merged_low, merged_high);
        count_range_entry_work(removed.len());
        Some(RangeUndo {
            inserted: (merged_low, merged_high),
            removed,
        })
    }

    fn rollback(&mut self, undo: RangeUndo) {
        self.0.remove(&undo.inserted.0);
        count_range_entry_work(undo.removed.len());
        self.0.extend(undo.removed);
    }

    fn overlaps(&self, other: &Self) -> bool {
        let (small, large) = if self.0.len() <= other.0.len() {
            (self, other)
        } else {
            (other, self)
        };
        small.0.iter().any(|(&low, &high)| {
            large
                .0
                .range(..=high)
                .next_back()
                .is_some_and(|(_, other_high)| *other_high >= low)
        })
    }
}

#[derive(Default)]
struct WrittenDelta {
    entries: HashMap<WrittenKey, Mask>,
    groups: HashSet<DestinationGroup>,
}

impl WrittenDelta {
    fn add(&mut self, key: WrittenKey, mask: Mask) {
        if mask.is_empty() {
            return;
        }
        self.entries.entry(key).or_default().merge(mask);
    }

    fn add_destination(&mut self, destination: DestinationGroup) {
        self.groups.insert(destination);
    }

    fn absorb(&mut self, mut other: Self) {
        if self.entries.len() < other.entries.len() {
            std::mem::swap(&mut self.entries, &mut other.entries);
        }
        for (key, mask) in other.entries {
            self.add(key, mask);
        }
        self.groups.extend(other.groups);
    }
}

enum WrittenUndo {
    Remove(WrittenKey),
    RestoreKnown(WrittenKey, BitRanges),
    Range(WrittenKey, RangeUndo),
    Group(DestinationGroup),
}

/// Current may-written state plus a sparse transaction journal. Branches
/// evaluate against the same entry state and roll back only keys/ranges they
/// changed; they never clone the growing prefix map.
#[derive(Default)]
struct Written {
    current: HashMap<WrittenKey, Mask>,
    groups: HashSet<DestinationGroup>,
    ids: HashMap<VarId, usize>,
    reported_groups: HashSet<(VarId, FlatIndexSet)>,
    undo: Vec<WrittenUndo>,
}

impl Written {
    fn checkpoint(&self) -> usize {
        self.undo.len()
    }

    fn rollback(&mut self, checkpoint: usize) {
        while self.undo.len() > checkpoint {
            match self.undo.pop().expect("checked length") {
                WrittenUndo::Remove(key) => {
                    if self.current.remove(&key).is_some() {
                        let remove_id = {
                            let count = self.ids.get_mut(&key.0).expect("tracked written id");
                            *count -= 1;
                            *count == 0
                        };
                        if remove_id {
                            self.ids.remove(&key.0);
                        }
                    }
                }
                WrittenUndo::RestoreKnown(key, ranges) => {
                    self.current.insert(key, Mask::Ranges(ranges));
                }
                WrittenUndo::Range(key, change) => {
                    let Some(Mask::Ranges(ranges)) = self.current.get_mut(&key) else {
                        unreachable!("range undo requires a known mask")
                    };
                    ranges.rollback(change);
                }
                WrittenUndo::Group(group) => {
                    self.groups.remove(&group);
                }
            }
        }
    }

    fn overlaps(&self, key: WrittenKey, read: &Mask) -> bool {
        self.current
            .get(&key)
            .is_some_and(|written| read.overlaps(written))
    }

    fn has_id(&self, id: VarId) -> bool {
        self.ids.contains_key(&id)
    }

    fn contains_group(&self, read: &DestinationGroup) -> bool {
        self.groups.contains(read)
    }

    fn group_was_reported(&self, group: &DestinationGroup) -> bool {
        self.reported_groups
            .contains(&(group.id, group.candidates.clone()))
    }

    fn report_group(&mut self, group: &DestinationGroup, decl: usize, out: &mut UnsafeSelfReads) {
        if !self
            .reported_groups
            .insert((group.id, group.candidates.clone()))
        {
            return;
        }
        group.for_each(|key, _| {
            out.insert((decl, key.0, key.1));
        });
    }

    fn apply(&mut self, key: WrittenKey, mask: Mask, delta: &mut WrittenDelta) {
        self.merge_tracked(key, &mask);
        delta.add(key, mask);
    }

    fn apply_destination(&mut self, destination: &DestinationGroup, delta: &mut WrittenDelta) {
        if !self.groups.insert(destination.clone()) {
            return;
        }
        self.undo.push(WrittenUndo::Group(destination.clone()));
        destination.for_each(|key, mask| self.merge_tracked(key, &mask));
        delta.add_destination(destination.clone());
    }

    fn apply_delta(&mut self, incoming: WrittenDelta, delta: &mut WrittenDelta) {
        for destination in incoming.groups {
            self.apply_destination(&destination, delta);
        }
        for (key, mask) in incoming.entries {
            self.apply(key, mask, delta);
        }
    }

    fn merge_tracked(&mut self, key: WrittenKey, incoming: &Mask) {
        count_state_merge();
        if incoming.is_empty() {
            return;
        }
        let Some(current) = self.current.get_mut(&key) else {
            self.current.insert(key, incoming.clone());
            *self.ids.entry(key.0).or_default() += 1;
            self.undo.push(WrittenUndo::Remove(key));
            return;
        };
        match incoming {
            Mask::All => {
                if let Mask::Ranges(_) = current {
                    let Mask::Ranges(previous) = std::mem::replace(current, Mask::All) else {
                        unreachable!()
                    };
                    self.undo.push(WrittenUndo::RestoreKnown(key, previous));
                }
            }
            Mask::Ranges(incoming) => {
                let should_widen = match current {
                    Mask::All => return,
                    Mask::Ranges(ranges) => incoming
                        .0
                        .iter()
                        .any(|(&low, &high)| ranges.merge_work_exceeds_limit(low, high)),
                };
                if should_widen {
                    let Mask::Ranges(previous) = std::mem::replace(current, Mask::All) else {
                        unreachable!()
                    };
                    self.undo.push(WrittenUndo::RestoreKnown(key, previous));
                    return;
                }
                let Mask::Ranges(current) = current else {
                    unreachable!()
                };
                for (&low, &high) in &incoming.0 {
                    if let Some(change) = current.insert(low, high) {
                        self.undo.push(WrittenUndo::Range(key, change));
                    }
                }
            }
        }
    }
}

pub fn unsafe_self_reads(decls: &[Declaration], context: &mut Context) -> UnsafeSelfReads {
    let mut result = UnsafeSelfReads::default();
    for (decl, x) in decls.iter().enumerate() {
        if let Declaration::Ff(ff) = x {
            let mut written = Written::default();
            let mut delta = WrittenDelta::default();
            let weights = StatementWeights::new(&ff.statements);
            walk_seq(
                &ff.statements,
                decl,
                context,
                &mut written,
                &mut delta,
                &weights,
                false,
                &mut result,
            );
        }
    }
    result
}

#[allow(clippy::too_many_arguments)]
fn walk_seq(
    stmts: &[Statement],
    decl: usize,
    context: &mut Context,
    written: &mut Written,
    delta: &mut WrittenDelta,
    weights: &StatementWeights,
    runtime_footprint_preapplied: bool,
    out: &mut UnsafeSelfReads,
) {
    for s in stmts {
        walk_one(
            s,
            decl,
            context,
            written,
            delta,
            weights,
            runtime_footprint_preapplied,
            out,
        );
    }
}

#[allow(clippy::too_many_arguments)]
fn walk_one(
    stmt: &Statement,
    decl: usize,
    context: &mut Context,
    written: &mut Written,
    delta: &mut WrittenDelta,
    weights: &StatementWeights,
    runtime_footprint_preapplied: bool,
    out: &mut UnsafeSelfReads,
) {
    match stmt {
        Statement::Assign(x) => {
            let mut dsts = Vec::new();
            for dst in &x.dst {
                add_dst(dst, context, &mut dsts);
            }
            // The source runs before the enclosing store. Function output
            // actuals copy back as the expression is evaluated, so they must
            // become visible to later operands and later statements.
            let expression_delta =
                ExpressionOrder::new(decl, context, written, out, &dsts).walk(&x.expr);
            delta.absorb(expression_delta);
            for destination in &x.dst {
                let coordinate_delta = ExpressionOrder::new(decl, context, written, out, &[])
                    .walk_destination(destination);
                delta.absorb(coordinate_delta);
            }
            for destination in dsts {
                written.apply_destination(&destination, delta);
            }
        }
        Statement::If(x) => {
            let expression_delta =
                ExpressionOrder::new(decl, context, written, out, &[]).walk(&x.cond);
            delta.absorb(expression_delta);
            walk_branches(
                &x.true_side,
                &x.false_side,
                decl,
                context,
                written,
                delta,
                weights,
                runtime_footprint_preapplied,
                out,
            );
        }
        Statement::IfReset(x) => walk_branches(
            &x.true_side,
            &x.false_side,
            decl,
            context,
            written,
            delta,
            weights,
            runtime_footprint_preapplied,
            out,
        ),
        Statement::Case(x) => {
            let expression_delta =
                ExpressionOrder::new(decl, context, written, out, &[]).walk(&x.case_target);
            delta.absorb(expression_delta);
            walk_alternatives(
                x.arms
                    .iter()
                    .map(|arm| arm.body.as_slice())
                    .chain(std::iter::once(x.default.as_slice())),
                decl,
                context,
                written,
                delta,
                weights,
                runtime_footprint_preapplied,
                out,
            );
        }
        Statement::For(x) => {
            if let Some(iter) = x.range.eval_iter(context) {
                for i in iter {
                    if let Some(var) = context.variable_mut(&x.var_id)
                        && let Some(total_width) = x.var_type.total_width()
                    {
                        let val = Value::new(i as u64, total_width, x.var_type.signed);
                        var.set_value(&[], val, None);
                    }
                    walk_seq(
                        &x.body,
                        decl,
                        context,
                        written,
                        delta,
                        weights,
                        runtime_footprint_preapplied,
                        out,
                    );
                }
            } else {
                // Without concrete iterations there is no order to walk, and
                // the body runs again.
                if !runtime_footprint_preapplied {
                    let mut body = WrittenDelta::default();
                    collect_writes(&x.body, context, &mut body);
                    written.apply_delta(body, delta);
                }
                walk_seq(&x.body, decl, context, written, delta, weights, true, out);
            }
        }
        Statement::FunctionCall(x) => {
            let expression_delta =
                ExpressionOrder::new(decl, context, written, out, &[]).walk_call(x);
            delta.absorb(expression_delta);
        }
        Statement::SystemFunctionCall(x) => {
            let expression_delta =
                ExpressionOrder::new(decl, context, written, out, &[]).walk_system_call(x);
            delta.absorb(expression_delta);
        }
        Statement::TbMethodCall(_)
        | Statement::Break
        | Statement::Unsupported(_)
        | Statement::Null => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn walk_branches(
    true_side: &[Statement],
    false_side: &[Statement],
    decl: usize,
    context: &mut Context,
    written: &mut Written,
    delta: &mut WrittenDelta,
    weights: &StatementWeights,
    runtime_footprint_preapplied: bool,
    out: &mut UnsafeSelfReads,
) {
    walk_alternatives(
        [true_side, false_side].into_iter(),
        decl,
        context,
        written,
        delta,
        weights,
        runtime_footprint_preapplied,
        out,
    );
}

#[allow(clippy::too_many_arguments)]
fn walk_alternatives<'s>(
    branches: impl Iterator<Item = &'s [Statement]>,
    decl: usize,
    context: &mut Context,
    written: &mut Written,
    delta: &mut WrittenDelta,
    weights: &StatementWeights,
    runtime_footprint_preapplied: bool,
    out: &mut UnsafeSelfReads,
) {
    let mut branches = branches.collect::<Vec<_>>();
    if let Some((largest, _)) = branches
        .iter()
        .enumerate()
        .max_by_key(|(_, branch)| weights.sequence(branch))
    {
        let last = branches.len() - 1;
        branches.swap(largest, last);
    }
    let Some((last, preceding)) = branches.split_last() else {
        return;
    };
    let mut joined = WrittenDelta::default();
    for branch in preceding {
        count_branch_arm();
        let checkpoint = written.checkpoint();
        let mut branch_delta = WrittenDelta::default();
        walk_seq(
            branch,
            decl,
            context,
            written,
            &mut branch_delta,
            weights,
            runtime_footprint_preapplied,
            out,
        );
        written.rollback(checkpoint);
        joined.absorb(branch_delta);
    }
    count_branch_arm();
    let mut last_delta = WrittenDelta::default();
    walk_seq(
        last,
        decl,
        context,
        written,
        &mut last_delta,
        weights,
        runtime_footprint_preapplied,
        out,
    );
    delta.absorb(last_delta);
    written.apply_delta(joined, delta);
}

/// Everything the statements may write, ignoring order.
fn collect_writes(stmts: &[Statement], context: &mut Context, out: &mut WrittenDelta) {
    for s in stmts {
        count_runtime_footprint_statement_visit();
        match s {
            Statement::Assign(x) => {
                collect_expression_writes(&x.expr, context, out);
                for dst in &x.dst {
                    collect_destination_writes(dst, context, out);
                }
            }
            Statement::If(x) => {
                collect_expression_writes(&x.cond, context, out);
                collect_writes(&x.true_side, context, out);
                collect_writes(&x.false_side, context, out);
            }
            Statement::IfReset(x) => {
                collect_writes(&x.true_side, context, out);
                collect_writes(&x.false_side, context, out);
            }
            Statement::Case(x) => {
                collect_expression_writes(&x.case_target, context, out);
                for arm in &x.arms {
                    collect_writes(&arm.body, context, out);
                }
                collect_writes(&x.default, context, out);
            }
            Statement::For(x) => collect_writes(&x.body, context, out),
            Statement::FunctionCall(x) => collect_call_writes(x, context, out),
            Statement::SystemFunctionCall(x) => collect_system_call_writes(x, context, out),
            Statement::TbMethodCall(_)
            | Statement::Break
            | Statement::Unsupported(_)
            | Statement::Null => {}
        }
    }
}

/// Ordered expression evaluation for the self-read check. Plain reads are
/// accumulated until a side effect creates an ordering boundary. Compact
/// candidate groups keep repeated dynamic reads from expanding again while a
/// function output remains visible to every operand evaluated after the call.
struct ExpressionOrder<'a> {
    decl: usize,
    context: &'a mut Context,
    written: &'a mut Written,
    out: &'a mut UnsafeSelfReads,
    targets: &'a [DestinationGroup],
    reads: HashSet<DestinationGroup>,
    effects: WrittenDelta,
}

impl<'a> ExpressionOrder<'a> {
    fn new(
        decl: usize,
        context: &'a mut Context,
        written: &'a mut Written,
        out: &'a mut UnsafeSelfReads,
        targets: &'a [DestinationGroup],
    ) -> Self {
        Self {
            decl,
            context,
            written,
            out,
            targets,
            reads: HashSet::default(),
            effects: WrittenDelta::default(),
        }
    }

    fn walk(mut self, expression: &Expression) -> WrittenDelta {
        self.expression(expression);
        self.flush_reads();
        self.effects
    }

    fn walk_call(mut self, call: &FunctionCall) -> WrittenDelta {
        self.function_call(call);
        self.flush_reads();
        self.effects
    }

    fn walk_system_call(mut self, call: &SystemFunctionCall) -> WrittenDelta {
        self.system_function_call(call);
        self.flush_reads();
        self.effects
    }

    fn walk_destination(mut self, destination: &AssignDestination) -> WrittenDelta {
        self.destination_coordinates(destination);
        self.flush_reads();
        self.effects
    }

    fn expression(&mut self, expression: &Expression) {
        match expression {
            Expression::Term(factor) => self.factor(factor),
            Expression::Unary(_, expression, _) => self.expression(expression),
            Expression::Binary(left, _, right, _) => {
                self.expression(left);
                self.expression(right);
            }
            Expression::Ternary(condition, true_value, false_value, _) => {
                self.expression(condition);
                self.flush_reads();
                self.alternatives(true_value, false_value);
            }
            Expression::Concatenation(items, _) => {
                for (value, repeat) in items {
                    self.expression(value);
                    if let Some(repeat) = repeat {
                        self.expression(repeat);
                    }
                }
            }
            Expression::ArrayLiteral(items, _) => {
                for item in items {
                    match item {
                        ArrayLiteralItem::Value(value, repeat) => {
                            self.expression(value);
                            if let Some(repeat) = repeat {
                                self.expression(repeat);
                            }
                        }
                        ArrayLiteralItem::Defaul(value) => self.expression(value),
                    }
                }
            }
            Expression::StructConstructor(_, members, _) => {
                for (_, value) in members {
                    self.expression(value);
                }
            }
        }
    }

    fn factor(&mut self, factor: &Factor) {
        match factor {
            Factor::Variable(id, index, select, comptime) => {
                for coordinate in &index.0 {
                    self.expression(coordinate);
                }
                for coordinate in &select.0 {
                    self.expression(coordinate);
                }
                if let Some((_, coordinate)) = &select.1 {
                    self.expression(coordinate);
                }
                let Some(variable) = self.context.get_variable_info(*id) else {
                    return;
                };
                let r#type = variable.r#type.clone();
                let mask = PackedMask::from_range(select.conservative_packed_range(
                    self.context,
                    &r#type,
                    comptime.member_select_domain,
                ));
                if let Some(candidates) = index.possible_flat_indices(self.context, &r#type.array) {
                    self.reads.insert(DestinationGroup {
                        id: *id,
                        candidates,
                        mask,
                    });
                }
            }
            Factor::FunctionCall(call) => self.function_call(call),
            Factor::SystemFunctionCall(call) => self.system_function_call(call),
            Factor::HierVariable(_)
            | Factor::Value(_)
            | Factor::Anonymous(_)
            | Factor::Unknown(_) => {}
        }
    }

    fn function_call(&mut self, call: &FunctionCall) {
        // Resolve the receiver before evaluating actual arguments, matching
        // `FunctionCall::eval_value`. Outputs copy back only after all inputs.
        for coordinate in &call.receiver_index.0 {
            self.expression(coordinate);
        }
        for input in call.inputs.values() {
            self.expression(input);
        }
        for outputs in call.outputs.values() {
            for destination in outputs {
                self.destination_coordinates(destination);
            }
        }
        self.flush_reads();
        for outputs in call.outputs.values() {
            self.apply_outputs(outputs);
        }
    }

    fn system_function_call(&mut self, call: &SystemFunctionCall) {
        let input = |expression: &Expression, this: &mut Self| this.expression(expression);
        match &call.kind {
            SystemFunctionKind::Bits(value)
            | SystemFunctionKind::Size(value)
            | SystemFunctionKind::Clog2(value)
            | SystemFunctionKind::Onehot(value)
            | SystemFunctionKind::Signed(value)
            | SystemFunctionKind::Unsigned(value) => input(&value.0, self),
            SystemFunctionKind::Readmemh(value, output) => {
                input(&value.0, self);
                for destination in &output.0 {
                    self.destination_coordinates(destination);
                }
                self.flush_reads();
                self.apply_outputs(&output.0);
            }
            SystemFunctionKind::Display(values) | SystemFunctionKind::Write(values) => {
                for value in values {
                    input(&value.0, self);
                }
            }
            SystemFunctionKind::Assert { cond, args, .. } => {
                input(&cond.0, self);
                for value in args {
                    input(&value.0, self);
                }
            }
            SystemFunctionKind::Finish => {}
        }
    }

    fn destination_coordinates(&mut self, destination: &AssignDestination) {
        for coordinate in &destination.index.0 {
            self.expression(coordinate);
        }
        for coordinate in &destination.select.0 {
            self.expression(coordinate);
        }
        if let Some((_, coordinate)) = &destination.select.1 {
            self.expression(coordinate);
        }
    }

    fn apply_outputs(&mut self, outputs: &[AssignDestination]) {
        // A function body is opaque here, so a copyback to bits already
        // written by this block remains conservatively register-resident.
        let mut destinations = Vec::new();
        for destination in outputs {
            add_dst(destination, self.context, &mut destinations);
        }
        for destination in destinations {
            destination.for_each(|key, mask| {
                if self.written.overlaps(key, &mask) {
                    self.out.insert((self.decl, key.0, key.1));
                }
            });
            self.written
                .apply_destination(&destination, &mut self.effects);
        }
    }

    fn flush_reads(&mut self) {
        if self.reads.is_empty() {
            return;
        }
        let reads = std::mem::take(&mut self.reads);
        let mut reads_by_id = HashMap::<VarId, Vec<DestinationGroup>>::default();
        for read in reads {
            reads_by_id.entry(read.id).or_default().push(read);
        }
        let mut expanded_reads = None;
        for target in self.targets {
            if self.written.group_was_reported(target) {
                continue;
            }
            let Some(matching) = reads_by_id.get(&target.id) else {
                continue;
            };
            if matching.iter().any(|read| {
                count_read_group_comparison();
                read.candidates == target.candidates && self.written.contains_group(read)
            }) {
                self.written.report_group(target, self.decl, self.out);
                continue;
            }
            if !self.written.has_id(target.id) {
                continue;
            }
            let expanded_reads = expanded_reads.get_or_insert_with(|| {
                let mut expanded = HashMap::<WrittenKey, Mask>::default();
                for reads in reads_by_id.values() {
                    for read in reads {
                        read.for_each(|key, mask| {
                            expanded.entry(key).or_default().merge(mask);
                        });
                    }
                }
                expanded
            });
            target.for_each(|key, _| {
                if let Some(read) = expanded_reads.get(&key)
                    && self.written.overlaps(key, read)
                {
                    self.out.insert((self.decl, key.0, key.1));
                }
            });
        }
    }

    fn alternatives(&mut self, true_value: &Expression, false_value: &Expression) {
        let checkpoint = self.written.checkpoint();
        let true_effects = ExpressionOrder::new(
            self.decl,
            self.context,
            self.written,
            self.out,
            self.targets,
        )
        .walk(true_value);
        self.written.rollback(checkpoint);

        let false_effects = ExpressionOrder::new(
            self.decl,
            self.context,
            self.written,
            self.out,
            self.targets,
        )
        .walk(false_value);
        self.effects.absorb(false_effects);
        self.written.apply_delta(true_effects, &mut self.effects);
    }
}

fn collect_expression_writes(
    expression: &Expression,
    context: &mut Context,
    out: &mut WrittenDelta,
) {
    match expression {
        Expression::Term(factor) => match factor.as_ref() {
            Factor::FunctionCall(call) => collect_call_writes(call, context, out),
            Factor::SystemFunctionCall(call) => collect_system_call_writes(call, context, out),
            _ => {}
        },
        Expression::Unary(_, expression, _) => {
            collect_expression_writes(expression, context, out);
        }
        Expression::Binary(left, _, right, _) => {
            collect_expression_writes(left, context, out);
            collect_expression_writes(right, context, out);
        }
        Expression::Ternary(condition, true_value, false_value, _) => {
            collect_expression_writes(condition, context, out);
            collect_expression_writes(true_value, context, out);
            collect_expression_writes(false_value, context, out);
        }
        Expression::Concatenation(items, _) => {
            for (value, repeat) in items {
                collect_expression_writes(value, context, out);
                if let Some(repeat) = repeat {
                    collect_expression_writes(repeat, context, out);
                }
            }
        }
        Expression::ArrayLiteral(items, _) => {
            for item in items {
                match item {
                    ArrayLiteralItem::Value(value, repeat) => {
                        collect_expression_writes(value, context, out);
                        if let Some(repeat) = repeat {
                            collect_expression_writes(repeat, context, out);
                        }
                    }
                    ArrayLiteralItem::Defaul(value) => {
                        collect_expression_writes(value, context, out);
                    }
                }
            }
        }
        Expression::StructConstructor(_, members, _) => {
            for (_, value) in members {
                collect_expression_writes(value, context, out);
            }
        }
    }
}

fn collect_call_writes(call: &FunctionCall, context: &mut Context, out: &mut WrittenDelta) {
    for coordinate in &call.receiver_index.0 {
        collect_expression_writes(coordinate, context, out);
    }
    for input in call.inputs.values() {
        collect_expression_writes(input, context, out);
    }
    for outputs in call.outputs.values() {
        for destination in outputs {
            collect_destination_writes(destination, context, out);
        }
    }
}

fn collect_destination_writes(
    destination: &AssignDestination,
    context: &mut Context,
    out: &mut WrittenDelta,
) {
    for coordinate in &destination.index.0 {
        collect_expression_writes(coordinate, context, out);
    }
    for coordinate in &destination.select.0 {
        collect_expression_writes(coordinate, context, out);
    }
    if let Some((_, coordinate)) = &destination.select.1 {
        collect_expression_writes(coordinate, context, out);
    }
    let mut destinations = Vec::new();
    add_dst(destination, context, &mut destinations);
    for destination in destinations {
        out.add_destination(destination);
    }
}

fn collect_system_call_writes(
    call: &SystemFunctionCall,
    context: &mut Context,
    out: &mut WrittenDelta,
) {
    match &call.kind {
        SystemFunctionKind::Bits(value)
        | SystemFunctionKind::Size(value)
        | SystemFunctionKind::Clog2(value)
        | SystemFunctionKind::Onehot(value)
        | SystemFunctionKind::Signed(value)
        | SystemFunctionKind::Unsigned(value) => {
            collect_expression_writes(&value.0, context, out);
        }
        SystemFunctionKind::Readmemh(value, output) => {
            collect_expression_writes(&value.0, context, out);
            for destination in &output.0 {
                collect_destination_writes(destination, context, out);
            }
        }
        SystemFunctionKind::Display(values) | SystemFunctionKind::Write(values) => {
            for value in values {
                collect_expression_writes(&value.0, context, out);
            }
        }
        SystemFunctionKind::Assert { cond, args, .. } => {
            collect_expression_writes(&cond.0, context, out);
            for value in args {
                collect_expression_writes(&value.0, context, out);
            }
        }
        SystemFunctionKind::Finish => {}
    }
}

/// Mirrors `AssignDestination`'s gather so a write always has a matching
/// table entry.
fn add_dst(dst: &AssignDestination, context: &mut Context, out: &mut Vec<DestinationGroup>) {
    let Some(variable) = context.get_variable_info(dst.id) else {
        return;
    };
    if variable.kind == VarKind::Let || variable.affiliation == Affiliation::AlwaysFf {
        return;
    }
    let r#type = variable.r#type.clone();
    let mask = PackedMask::from_range(dst.select.conservative_packed_range(
        context,
        &r#type,
        dst.comptime.member_select_domain,
    ));
    if let Some(indices) = dst.index.possible_flat_indices(context, &r#type.array) {
        out.push(DestinationGroup {
            id: dst.id,
            candidates: indices,
            mask,
        });
    }
}
