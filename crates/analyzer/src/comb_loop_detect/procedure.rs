//! Analyzer-IR procedure evaluation for combinational dependency extraction.

use super::model::BitDependency;
use super::region::{
    ArraySpan, BitPartition, NodeKey, PackedSpan, dst_writes, signed_difference,
    translate_position, var_reads,
};
use super::ssa::{
    BranchId, BranchState, Checkpoint, DependencyDag, DependencyDagNode, PathCondition,
    PositionDomain, PositionRelation, RepeatedTransfer, SourceCache, SsaStore, StateRevision,
    VersionId,
};
use crate::conv::Context;
use crate::ir::VarId;
use crate::ir::{
    ArrayLiteralItem, AssignDestination, CaseStatement, Expression, Factor, ForBound, ForRange,
    ForStatement, FunctionCall, IfStatement, MemberSelectDomain, Module, Op, Statement,
    SystemFunctionKind, TypeKind, VarIndex, VarPath, VarSelect,
};
use crate::value::Value;
use crate::{HashMap, HashSet};
use std::cell::OnceCell;
use std::collections::BTreeMap;
use std::rc::Rc;

fn translate_array_span(span: ArraySpan, offset: isize) -> Option<ArraySpan> {
    Some(ArraySpan {
        start: translate_position(span.start, offset)?,
        length: span.length,
    })
}

fn position_domain(array: ArraySpan, packed: PackedSpan) -> PositionDomain {
    PositionDomain {
        array_start: array.start,
        array_length: array.length,
        packed_start: packed.start,
        packed_length: packed.length,
    }
}

fn packed_mask_overlaps(mask: &crate::BigUint, span: PackedSpan) -> bool {
    let Ok(start) = u64::try_from(span.start) else {
        return false;
    };
    if mask.bits() <= start {
        return false;
    }
    if span.length == 1 {
        return mask.bit(start);
    }
    if span.start == 0 && u64::try_from(span.end()).is_ok_and(|end| end >= mask.bits()) {
        return mask.bits() != 0;
    }

    let first_word = span.start / u64::BITS as usize;
    let last_word = (span.end() - 1) / u64::BITS as usize;
    mask.iter_u64_digits()
        .enumerate()
        .skip(first_word)
        .take(last_word - first_word + 1)
        .any(|(word_index, mut word)| {
            if word_index == first_word {
                word &= u64::MAX << (span.start % u64::BITS as usize);
            }
            if word_index == last_word {
                let end_bit = span.end() % u64::BITS as usize;
                if end_bit != 0 {
                    word &= (1u64 << end_bit) - 1;
                }
            }
            word != 0
        })
}

fn translate_packed_span(span: PackedSpan, offset: isize) -> Option<PackedSpan> {
    PackedSpan::new(translate_position(span.start, offset)?, span.length)
}

/// Whether an inclusive interval is already contained in a normalized set of
/// disjoint inclusive intervals.
fn case_interval_is_covered(covered: &BTreeMap<usize, usize>, (low, high): (usize, usize)) -> bool {
    let mut cursor = low;
    if let Some((_, &end)) = covered.range(..=cursor).next_back()
        && end >= cursor
    {
        if end >= high {
            return true;
        }
        let Some(next) = end.checked_add(1) else {
            return true;
        };
        cursor = next;
    }

    for (&start, &end) in covered.range(cursor..=high) {
        if start > cursor {
            return false;
        }
        if end >= high {
            return true;
        }
        let Some(next) = end.checked_add(1) else {
            return true;
        };
        cursor = next;
    }
    false
}

/// Insert one inclusive interval while keeping the set normalized. Each old
/// interval is removed at most once, so a large flat `case` stays near
/// O(patterns log patterns) instead of repeatedly rescanning every arm.
fn insert_case_interval(covered: &mut BTreeMap<usize, usize>, (mut low, mut high): (usize, usize)) {
    if let Some((&start, &end)) = covered.range(..=low).next_back()
        && end.saturating_add(1) >= low
    {
        low = start;
        high = high.max(end);
        covered.remove(&start);
    }

    loop {
        let next = covered
            .range(low..)
            .next()
            .map(|(&start, &end)| (start, end));
        let Some((start, end)) = next else {
            break;
        };
        if start > high.saturating_add(1) {
            break;
        }
        high = high.max(end);
        covered.remove(&start);
    }
    covered.insert(low, high);
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct AffineIndex {
    terms: Vec<(VarId, isize)>,
    constant: isize,
}

#[derive(Clone, Copy)]
struct DestinationArrayProjection {
    destination: ArraySpan,
    source: ArraySpan,
    /// Translation from expression-local/formal array coordinates to this
    /// destination key. A key spanning more than one periodic candidate has
    /// no single exact translation.
    array_offset: Option<isize>,
}

#[derive(Clone, Copy)]
struct PeriodicArrayFilter {
    period: usize,
    phase: usize,
    extent: usize,
}

#[derive(Clone)]
struct DestinationArraySelection {
    dynamic: bool,
    /// Geometry of the statically selected suffix after the last dynamic
    /// index. Reachable storage intervals start at `phase` modulo `period`
    /// and have `extent` elements.
    period: Option<usize>,
    phase: usize,
    extent: Option<usize>,
    /// Constraints from every statically known coordinate, including a
    /// constant between two dynamic coordinates such as `a[i][0][j]`.
    static_filters: Vec<PeriodicArrayFilter>,
}

impl DestinationArrayProjection {
    fn position_offset(
        self,
        destination_packed: usize,
        source_packed: usize,
    ) -> Option<PositionRelation> {
        Some(PositionRelation {
            array: self.array_offset,
            packed: Some(signed_difference(destination_packed, source_packed)?),
        })
    }
}

enum PeriodicArrayProjection {
    Exact(Option<DestinationArrayProjection>),
    Unknown,
}

fn periodic_destination_array_projection(
    destination: ArraySpan,
    period: usize,
    phase: usize,
    extent: usize,
) -> PeriodicArrayProjection {
    let Some(phase_end) = phase.checked_add(extent) else {
        return PeriodicArrayProjection::Unknown;
    };
    if period == 0 || extent == 0 || phase >= period || phase_end > period {
        return PeriodicArrayProjection::Unknown;
    }
    let Some(destination_end) = destination.end() else {
        return PeriodicArrayProjection::Unknown;
    };

    let residue = destination.start % period;
    let band_start = if residue < phase {
        destination.start.checked_add(phase - residue)
    } else if residue < phase_end {
        destination.start.checked_sub(residue - phase)
    } else {
        destination
            .start
            .checked_add(period - residue)
            .and_then(|start| start.checked_add(phase))
    };
    let Some(band_start) = band_start else {
        // The next periodic interval lies beyond the address space, and the
        // input span itself was already known not to overflow.
        return PeriodicArrayProjection::Exact(None);
    };
    if band_start >= destination_end {
        return PeriodicArrayProjection::Exact(None);
    }
    let Some(band_end) = band_start.checked_add(extent) else {
        return PeriodicArrayProjection::Unknown;
    };
    let fragment_start = destination.start.max(band_start);
    let fragment_end = destination_end.min(band_end);
    if fragment_start >= fragment_end {
        return PeriodicArrayProjection::Exact(None);
    }

    let spans_multiple_bands = band_start
        .checked_add(period)
        .is_some_and(|next| next < destination_end);
    if spans_multiple_bands {
        return PeriodicArrayProjection::Exact(Some(DestinationArrayProjection {
            destination,
            source: ArraySpan {
                start: 0,
                length: extent,
            },
            array_offset: None,
        }));
    }

    PeriodicArrayProjection::Exact(Some(DestinationArrayProjection {
        destination: ArraySpan {
            start: fragment_start,
            length: fragment_end - fragment_start,
        },
        source: ArraySpan {
            start: fragment_start - band_start,
            length: fragment_end - fragment_start,
        },
        array_offset: isize::try_from(band_start).ok(),
    }))
}

fn destination_array_projection(
    key: ArraySpan,
    candidates: ArraySpan,
    selection: &DestinationArraySelection,
) -> Option<DestinationArrayProjection> {
    let destination = key.intersection(candidates)?;
    if !selection.dynamic {
        return Some(DestinationArrayProjection {
            destination,
            source: destination.translated(candidates.start, 0)?,
            array_offset: isize::try_from(candidates.start).ok(),
        });
    }

    for filter in &selection.static_filters {
        if matches!(
            periodic_destination_array_projection(
                destination,
                filter.period,
                filter.phase,
                filter.extent,
            ),
            PeriodicArrayProjection::Exact(None)
        ) {
            return None;
        }
    }

    if let (Some(period), Some(extent)) = (selection.period, selection.extent) {
        match periodic_destination_array_projection(destination, period, selection.phase, extent) {
            PeriodicArrayProjection::Exact(projection) => return projection,
            PeriodicArrayProjection::Unknown => {}
        }
    }

    let source = {
        // A dynamic unpacked index broadcasts the selected value to every
        // candidate below the statically resolved prefix. Preserve trailing
        // unpacked dimensions by projecting storage coordinates modulo the
        // extent selected by one dynamic-prefix value.
        if let Some(extent) = selection.extent.filter(|extent| *extent != 0) {
            let relative = destination.start.checked_sub(candidates.start)?;
            let start = relative % extent;
            if destination.length >= extent || start.checked_add(destination.length)? > extent {
                ArraySpan {
                    start: 0,
                    length: extent,
                }
            } else {
                ArraySpan {
                    start,
                    length: destination.length,
                }
            }
        } else {
            ArraySpan {
                start: 0,
                length: destination.length,
            }
        }
    };
    Some(DestinationArrayProjection {
        destination,
        source,
        array_offset: None,
    })
}

#[cfg(test)]
mod destination_array_projection_tests {
    use super::*;

    #[test]
    fn periodic_projection_is_constant_work_for_a_large_destination() {
        let selection = DestinationArraySelection {
            dynamic: true,
            period: Some(2),
            phase: 1,
            extent: Some(1),
            static_filters: Vec::new(),
        };
        let candidates = ArraySpan {
            start: 0,
            length: 1_000_000,
        };

        assert!(
            destination_array_projection(
                ArraySpan {
                    start: 999_998,
                    length: 1,
                },
                candidates,
                &selection,
            )
            .is_none()
        );
        let selected = destination_array_projection(
            ArraySpan {
                start: 999_999,
                length: 1,
            },
            candidates,
            &selection,
        )
        .expect("the odd static suffix is reachable");
        assert_eq!(
            selected.source,
            ArraySpan {
                start: 0,
                length: 1
            }
        );
        assert_eq!(selected.array_offset, Some(999_999));

        let broad = destination_array_projection(candidates, candidates, &selection)
            .expect("a broad key contains periodic candidates");
        assert_eq!(
            broad.source,
            ArraySpan {
                start: 0,
                length: 1
            }
        );
        assert_eq!(broad.array_offset, None);
    }

    #[test]
    fn unavailable_or_overflowed_periodic_geometry_falls_back_conservatively() {
        let key = ArraySpan {
            start: 0,
            length: 4,
        };
        for selection in [
            DestinationArraySelection {
                dynamic: true,
                period: None,
                phase: 0,
                extent: Some(1),
                static_filters: Vec::new(),
            },
            DestinationArraySelection {
                dynamic: true,
                period: Some(usize::MAX),
                phase: usize::MAX,
                extent: Some(1),
                static_filters: Vec::new(),
            },
        ] {
            let projection = destination_array_projection(key, key, &selection)
                .expect("unknown geometry must retain every possible candidate");
            assert_eq!(projection.destination, key);
            assert_eq!(projection.array_offset, None);
        }
    }
}

impl AffineIndex {
    fn variable(id: VarId) -> Self {
        Self {
            terms: vec![(id, 1)],
            constant: 0,
        }
    }

    fn add_scaled(&mut self, other: &Self, scale: isize) -> Option<()> {
        self.constant = self
            .constant
            .checked_add(other.constant.checked_mul(scale)?)?;
        for &(id, coefficient) in &other.terms {
            let coefficient = coefficient.checked_mul(scale)?;
            match self.terms.binary_search_by_key(&id, |(id, _)| *id) {
                Ok(index) => {
                    self.terms[index].1 = self.terms[index].1.checked_add(coefficient)?;
                }
                Err(index) => self.terms.insert(index, (id, coefficient)),
            }
        }
        self.terms.retain(|(_, coefficient)| *coefficient != 0);
        Some(())
    }

    fn scaled(mut self, scale: isize) -> Option<Self> {
        self.constant = self.constant.checked_mul(scale)?;
        for (_, coefficient) in &mut self.terms {
            *coefficient = coefficient.checked_mul(scale)?;
        }
        Some(self)
    }

    /// Destination position minus source position when both use the same
    /// symbolic coordinates.
    fn destination_offset_from(&self, source: &Self) -> Option<isize> {
        (self.terms == source.terms).then(|| self.constant.checked_sub(source.constant))?
    }
}

fn affine_constant(expression: &Expression, ctx: &mut Context) -> Option<AffineIndex> {
    let constant = expression
        .eval_value(ctx)
        .and_then(|value| value.to_usize())
        .and_then(|value| isize::try_from(value).ok())?;
    Some(AffineIndex {
        terms: Vec::new(),
        constant,
    })
}

fn affine_index(expression: &Expression, ctx: &mut Context) -> Option<AffineIndex> {
    match expression {
        Expression::Term(factor) => match factor.as_ref() {
            Factor::Variable(id, index, select, _) if index.0.is_empty() && select.is_empty() => {
                Some(AffineIndex::variable(*id))
            }
            Factor::Value(_) => affine_constant(expression, ctx),
            _ if expression.comptime().is_const => affine_constant(expression, ctx),
            _ => None,
        },
        Expression::Unary(Op::Add, expression, _) => affine_index(expression, ctx),
        Expression::Unary(Op::Sub, expression, _) => affine_index(expression, ctx)?.scaled(-1),
        Expression::Binary(left, Op::Add | Op::Sub, right, _) => {
            let mut result = affine_index(left, ctx)?;
            let right = affine_index(right, ctx)?;
            result.add_scaled(
                &right,
                if matches!(expression, Expression::Binary(_, Op::Sub, _, _)) {
                    -1
                } else {
                    1
                },
            )?;
            Some(result)
        }
        Expression::Binary(left, Op::Mul, right, _) => {
            let left = affine_index(left, ctx)?;
            let right = affine_index(right, ctx)?;
            if left.terms.is_empty() {
                right.scaled(left.constant)
            } else if right.terms.is_empty() {
                left.scaled(right.constant)
            } else {
                None
            }
        }
        Expression::Binary(left, Op::As, _, _) => affine_index(left, ctx),
        _ if expression.comptime().is_const => affine_constant(expression, ctx),
        _ => None,
    }
}

fn affine_bound(bound: &ForBound, ctx: &mut Context) -> Option<AffineIndex> {
    match bound {
        ForBound::Const(value) => Some(AffineIndex {
            terms: Vec::new(),
            constant: isize::try_from(*value).ok()?,
        }),
        ForBound::Expression(expression) => affine_index(expression, ctx),
    }
}

fn for_range_bounds(range: &ForRange) -> (&ForBound, &ForBound, bool) {
    match range {
        ForRange::Forward {
            start,
            end,
            inclusive,
            ..
        }
        | ForRange::Reverse {
            start,
            end,
            inclusive,
            ..
        }
        | ForRange::Stepped {
            start,
            end,
            inclusive,
            ..
        } => (start, end, *inclusive),
    }
}

fn for_range_has_dynamic_bounds(range: &ForRange) -> bool {
    let (start, end, _) = for_range_bounds(range);
    matches!(start, ForBound::Expression(_)) || matches!(end, ForBound::Expression(_))
}

#[derive(Clone, Copy)]
struct RepeatedFragment {
    local_start: usize,
    length: usize,
    output_start: usize,
}

enum RepeatedProjection {
    Empty,
    Exact {
        first: RepeatedFragment,
        second: Option<RepeatedFragment>,
    },
    Periodic,
}

fn project_repeated_span(
    requested_start: usize,
    requested_length: usize,
    output_start: usize,
    item_length: usize,
    repeat: usize,
) -> RepeatedProjection {
    let Some(output_length) = item_length.checked_mul(repeat) else {
        return RepeatedProjection::Periodic;
    };
    let Some(requested_end) = requested_start.checked_add(requested_length) else {
        return RepeatedProjection::Periodic;
    };
    let Some(output_end) = output_start.checked_add(output_length) else {
        return RepeatedProjection::Periodic;
    };
    let overlap_start = requested_start.max(output_start);
    let overlap_end = requested_end.min(output_end);
    if item_length == 0 || overlap_start >= overlap_end {
        return RepeatedProjection::Empty;
    }
    let relative_start = overlap_start - output_start;
    let relative_end = overlap_end - output_start;
    let first = relative_start / item_length;
    let last = (relative_end - 1) / item_length;
    let first_output_start = output_start + first * item_length;
    if first == last {
        return RepeatedProjection::Exact {
            first: RepeatedFragment {
                local_start: relative_start % item_length,
                length: overlap_end - overlap_start,
                output_start: first_output_start,
            },
            second: None,
        };
    }

    // A range touching exactly two copies has two exact translations whether
    // either fragment happens to cover a complete copy. Their number is
    // structurally bounded and independent of `repeat`.
    if last == first + 1 {
        let first_end = (first + 1) * item_length;
        let last_output_start = output_start + last * item_length;
        return RepeatedProjection::Exact {
            first: RepeatedFragment {
                local_start: relative_start % item_length,
                length: first_end - relative_start,
                output_start: first_output_start,
            },
            second: Some(RepeatedFragment {
                local_start: 0,
                length: relative_end - last * item_length,
                output_start: last_output_start,
            }),
        };
    }
    RepeatedProjection::Periodic
}

#[cfg(test)]
use std::cell::Cell;

#[cfg(test)]
thread_local! {
    static EXPRESSION_LAYOUT_VISITS: Cell<usize> = const { Cell::new(0) };
}

struct CallResult {
    region_groups: Vec<(ArraySpan, Vec<(PackedSpan, VersionId)>)>,
}

impl CallResult {
    fn for_each_region_group(
        &self,
        requested: Option<ArraySpan>,
        mut visit: impl FnMut(ArraySpan, &[(PackedSpan, VersionId)]),
    ) {
        let (first, requested_end) = requested
            .and_then(|requested| {
                Some((
                    self.region_groups.partition_point(|(array, _)| {
                        #[cfg(test)]
                        FUNCTION_RESULT_REGION_PROBES.set(FUNCTION_RESULT_REGION_PROBES.get() + 1);
                        array.end().is_some_and(|end| end <= requested.start)
                    }),
                    requested.end()?,
                ))
            })
            .unwrap_or((0, usize::MAX));
        for (array, regions) in &self.region_groups[first..] {
            #[cfg(test)]
            FUNCTION_RESULT_REGION_PROBES.set(FUNCTION_RESULT_REGION_PROBES.get() + 1);
            if array.start >= requested_end {
                break;
            }
            if requested.is_none_or(|requested| array.overlaps(requested)) {
                visit(*array, regions);
            }
        }
    }
}

struct FormalVersionLayout {
    groups: Vec<(ArraySpan, Vec<(PackedSpan, VersionId)>)>,
}

impl FormalVersionLayout {
    fn new(versions: &[(NodeKey, VersionId)], bit_part: &BitPartition) -> FormalVersionLayout {
        let mut groups: Vec<(ArraySpan, Vec<(PackedSpan, VersionId)>)> = Vec::new();
        for &(key, version) in versions {
            let Some(packed) = bit_part.ranges_of((key.0, key.1)).get(key.2).copied() else {
                continue;
            };
            if groups.last().is_none_or(|(array, _)| *array != key.1) {
                groups.push((key.1, Vec::new()));
            }
            groups
                .last_mut()
                .expect("formal version group was just inserted")
                .1
                .push((packed, version));
        }
        debug_assert!(
            groups
                .windows(2)
                .all(|pair| { pair[0].0.end().is_some_and(|end| end <= pair[1].0.start) })
        );
        debug_assert!(groups.iter().all(|(_, regions)| {
            regions
                .windows(2)
                .all(|pair| pair[0].0.end() <= pair[1].0.start)
        }));
        Self { groups }
    }

    fn overlapping(&self, array: ArraySpan, packed: PackedSpan) -> Vec<VersionId> {
        let Some(array_end) = array.end() else {
            return Vec::new();
        };
        let first = self.groups.partition_point(|(candidate, _)| {
            #[cfg(test)]
            FORMAL_OUTPUT_REGION_PROBES.set(FORMAL_OUTPUT_REGION_PROBES.get() + 1);
            candidate.end().is_some_and(|end| end <= array.start)
        });
        let mut result = Vec::new();
        for (candidate, regions) in &self.groups[first..] {
            #[cfg(test)]
            FORMAL_OUTPUT_REGION_PROBES.set(FORMAL_OUTPUT_REGION_PROBES.get() + 1);
            if candidate.start >= array_end {
                break;
            }
            if !candidate.overlaps(array) {
                continue;
            }
            let first = regions.partition_point(|(candidate, _)| {
                #[cfg(test)]
                FORMAL_OUTPUT_REGION_PROBES.set(FORMAL_OUTPUT_REGION_PROBES.get() + 1);
                candidate.end() <= packed.start
            });
            for (candidate, version) in &regions[first..] {
                #[cfg(test)]
                FORMAL_OUTPUT_REGION_PROBES.set(FORMAL_OUTPUT_REGION_PROBES.get() + 1);
                if candidate.start >= packed.end() {
                    break;
                }
                if candidate.overlaps(packed) {
                    result.push(*version);
                }
            }
        }
        result
    }
}

struct FrozenVariableRead {
    selectors: Vec<VersionId>,
    versions: Vec<(NodeKey, VersionId)>,
}

#[derive(Clone, Copy)]
struct PackedProjectionFragment {
    part: usize,
    output_start: usize,
    item_width: usize,
    repeat: usize,
}

impl PackedProjectionFragment {
    fn output_end(self) -> Option<usize> {
        self.item_width
            .checked_mul(self.repeat)?
            .checked_add(self.output_start)
    }
}

struct PackedProjectionLayout {
    fragments: Vec<PackedProjectionFragment>,
    controls: Vec<VersionId>,
}

#[derive(Clone, Copy)]
struct ArrayProjectionFragment {
    item: usize,
    output_start: usize,
    item_length: usize,
    repeat: usize,
    output_length: usize,
}

impl ArrayProjectionFragment {
    fn output_end(self) -> Option<usize> {
        self.output_start.checked_add(self.output_length)
    }
}

struct ArrayProjectionLayout {
    fragments: Vec<ArrayProjectionFragment>,
    controls: Vec<VersionId>,
    total: usize,
}

impl FrozenVariableRead {
    fn version(&self, key: NodeKey) -> Option<VersionId> {
        self.versions
            .binary_search_by_key(&key, |(key, _)| *key)
            .ok()
            .map(|index| self.versions[index].1)
    }
}

// Region-split writes query one RHS several times, but a function call in that
// RHS is one procedural evaluation. `None` is an invocation barrier: temporary
// call nodes in a cloned callee body must never enter the caller's cache.
#[derive(Default)]
struct EvaluationCache {
    calls: HashMap<*const FunctionCall, Rc<CallResult>>,
    expression_branches: HashMap<*const Expression, BranchId>,
    // These addresses identify occurrences in the immutable caller IR only
    // while `snapshot_expression` owns this cache. Callee evaluation pushes an
    // invocation barrier, so temporary/cloned body nodes never enter it, and
    // the cache is dropped before its caller expression can cease to exist.
    variable_reads: HashMap<*const Factor, Rc<FrozenVariableRead>>,
    packed_layouts: HashMap<*const Expression, Rc<PackedProjectionLayout>>,
    array_layouts: HashMap<*const Expression, Rc<ArrayProjectionLayout>>,
    struct_layouts: HashMap<*const Expression, Rc<PackedProjectionLayout>>,
}

#[cfg(test)]
mod evaluation_cache_tests {
    use super::*;
    use std::hash::Hash;
    use std::ptr::NonNull;

    const WIDTH: usize = 256;

    fn assert_shared_lookups<K, T>(cache: &HashMap<K, Rc<T>>, key: K, expected: &Rc<T>)
    where
        K: Copy + Eq + Hash,
    {
        for _ in 0..WIDTH {
            let cached = cache.get(&key).cloned().expect("cached large value");
            assert!(Rc::ptr_eq(&cached, expected));
        }
        assert_eq!(Rc::strong_count(expected), 2);
    }

    #[test]
    fn large_value_lookups_clone_only_shared_handles() {
        // W projected regions repeatedly query cache payloads containing W
        // elements. The payload types intentionally do not implement Clone;
        // every lookup below must therefore remain an O(1) Rc clone rather
        // than restoring the former W x W Vec-copy path.
        let call = Rc::new(CallResult {
            region_groups: (0..WIDTH)
                .map(|start| {
                    (
                        ArraySpan { start, length: 1 },
                        vec![(PackedSpan::new(0, 1).expect("unit span"), start)],
                    )
                })
                .collect(),
        });
        let variable = Rc::new(FrozenVariableRead {
            selectors: (0..WIDTH).collect(),
            versions: (0..WIDTH)
                .map(|start| {
                    (
                        (VarId::from_raw(0), ArraySpan { start, length: 1 }, 0),
                        start,
                    )
                })
                .collect(),
        });
        let packed = Rc::new(PackedProjectionLayout {
            fragments: (0..WIDTH)
                .map(|output_start| PackedProjectionFragment {
                    part: output_start,
                    output_start,
                    item_width: 1,
                    repeat: 1,
                })
                .collect(),
            controls: (0..WIDTH).collect(),
        });
        let array = Rc::new(ArrayProjectionLayout {
            fragments: (0..WIDTH)
                .map(|output_start| ArrayProjectionFragment {
                    item: output_start,
                    output_start,
                    item_length: 1,
                    repeat: 1,
                    output_length: 1,
                })
                .collect(),
            controls: (0..WIDTH).collect(),
            total: WIDTH,
        });
        let r#struct = Rc::new(PackedProjectionLayout {
            fragments: (0..WIDTH)
                .map(|output_start| PackedProjectionFragment {
                    part: output_start,
                    output_start,
                    item_width: 1,
                    repeat: 1,
                })
                .collect(),
            controls: Vec::new(),
        });

        let call_key = NonNull::<FunctionCall>::dangling().as_ptr().cast_const();
        let variable_key = NonNull::<Factor>::dangling().as_ptr().cast_const();
        let expression_key = NonNull::<Expression>::dangling().as_ptr().cast_const();
        let mut cache = EvaluationCache::default();
        cache.calls.insert(call_key, Rc::clone(&call));
        cache
            .variable_reads
            .insert(variable_key, Rc::clone(&variable));
        cache
            .packed_layouts
            .insert(expression_key, Rc::clone(&packed));
        cache
            .array_layouts
            .insert(expression_key, Rc::clone(&array));
        cache
            .struct_layouts
            .insert(expression_key, Rc::clone(&r#struct));

        assert_shared_lookups(&cache.calls, call_key, &call);
        assert_shared_lookups(&cache.variable_reads, variable_key, &variable);
        assert_shared_lookups(&cache.packed_layouts, expression_key, &packed);
        assert_shared_lookups(&cache.array_layouts, expression_key, &array);
        assert_shared_lookups(&cache.struct_layouts, expression_key, &r#struct);
    }

    #[test]
    fn unpacked_call_result_queries_do_not_scan_every_array_group() {
        let result = CallResult {
            region_groups: (0..WIDTH)
                .map(|start| {
                    (
                        ArraySpan { start, length: 1 },
                        vec![(PackedSpan::new(0, 1).expect("unit span"), start)],
                    )
                })
                .collect(),
        };

        FUNCTION_RESULT_REGION_PROBES.set(0);
        for start in 0..WIDTH {
            let mut found = Vec::new();
            result.for_each_region_group(Some(ArraySpan { start, length: 1 }), |array, regions| {
                found.push((array, regions.len()))
            });
            assert_eq!(found, vec![(ArraySpan { start, length: 1 }, 1)]);
        }
        assert!(FUNCTION_RESULT_REGION_PROBES.get() <= WIDTH * 12);
    }
}

type CallCache = Option<EvaluationCache>;

#[derive(Default)]
struct ExpressionBranchLayout {
    conditionals: Vec<*const Expression>,
    calls: Vec<*const FunctionCall>,
}

fn collect_expression_branch_layout(expression: &Expression, layout: &mut ExpressionBranchLayout) {
    #[cfg(test)]
    EXPRESSION_LAYOUT_VISITS.set(EXPRESSION_LAYOUT_VISITS.get() + 1);
    if matches!(expression, Expression::Ternary(..))
        || matches!(
            expression,
            Expression::Binary(_, Op::LogicAnd | Op::LogicOr, _, _)
        )
    {
        layout.conditionals.push(std::ptr::from_ref(expression));
    }

    match expression {
        Expression::Term(factor) => match factor.as_ref() {
            Factor::Variable(_, index, select, _) => {
                collect_var_access_expressions(index, select, layout);
            }
            Factor::HierVariable(reference) => {
                collect_var_access_expressions(&reference.index, &reference.select, layout);
            }
            Factor::FunctionCall(call) => {
                let call_key = std::ptr::from_ref(call);
                // The expression IR is an owned tree: a syntactic call
                // occurrence is reached exactly once by this preorder walk.
                layout.calls.push(call_key);
                for expression in &call.receiver_index.0 {
                    collect_expression_branch_layout(expression, layout);
                }
                for expression in call.inputs.values() {
                    collect_expression_branch_layout(expression, layout);
                }
                for destinations in call.outputs.values() {
                    for destination in destinations {
                        collect_var_access_expressions(
                            &destination.index,
                            &destination.select,
                            layout,
                        );
                    }
                }
            }
            Factor::SystemFunctionCall(call) => {
                collect_system_call_branch_layout(call, layout);
            }
            Factor::Value(_) | Factor::Anonymous(_) | Factor::Unknown(_) => {}
        },
        Expression::Unary(_, operand, _) => {
            collect_expression_branch_layout(operand, layout);
        }
        Expression::Binary(left, _, right, _) => {
            collect_expression_branch_layout(left, layout);
            collect_expression_branch_layout(right, layout);
        }
        Expression::Ternary(condition, left, right, _) => {
            collect_expression_branch_layout(condition, layout);
            collect_expression_branch_layout(left, layout);
            collect_expression_branch_layout(right, layout);
        }
        Expression::Concatenation(parts, _) => {
            for (part, repeat) in parts {
                collect_expression_branch_layout(part, layout);
                if let Some(repeat) = repeat {
                    collect_expression_branch_layout(repeat, layout);
                }
            }
        }
        Expression::ArrayLiteral(items, _) => {
            for item in items {
                match item {
                    ArrayLiteralItem::Value(value, repeat) => {
                        collect_expression_branch_layout(value, layout);
                        if let Some(repeat) = repeat {
                            collect_expression_branch_layout(repeat, layout);
                        }
                    }
                    ArrayLiteralItem::Defaul(value) => {
                        collect_expression_branch_layout(value, layout);
                    }
                }
            }
        }
        Expression::StructConstructor(_, fields, _) => {
            for (_, value) in fields {
                collect_expression_branch_layout(value, layout);
            }
        }
    }
}

fn collect_var_access_expressions(
    index: &VarIndex,
    select: &VarSelect,
    layout: &mut ExpressionBranchLayout,
) {
    for expression in index.0.iter().chain(select.0.iter()) {
        collect_expression_branch_layout(expression, layout);
    }
    if let Some((_, expression)) = &select.1 {
        collect_expression_branch_layout(expression, layout);
    }
}

fn collect_system_call_branch_layout(
    call: &crate::ir::SystemFunctionCall,
    layout: &mut ExpressionBranchLayout,
) {
    match &call.kind {
        SystemFunctionKind::Bits(input)
        | SystemFunctionKind::Size(input)
        | SystemFunctionKind::Clog2(input)
        | SystemFunctionKind::Onehot(input)
        | SystemFunctionKind::Signed(input)
        | SystemFunctionKind::Unsigned(input) => {
            collect_expression_branch_layout(&input.0, layout);
        }
        SystemFunctionKind::Readmemh(input, output) => {
            collect_expression_branch_layout(&input.0, layout);
            for destination in &output.0 {
                collect_var_access_expressions(&destination.index, &destination.select, layout);
            }
        }
        SystemFunctionKind::Display(inputs) | SystemFunctionKind::Write(inputs) => {
            for input in inputs {
                collect_expression_branch_layout(&input.0, layout);
            }
        }
        SystemFunctionKind::Assert { cond, args, .. } => {
            collect_expression_branch_layout(&cond.0, layout);
            for input in args {
                collect_expression_branch_layout(&input.0, layout);
            }
        }
        SystemFunctionKind::Finish => {}
    }
}

// Module and interface storage is shared by every call. Function-owned
// storage is automatic, so its SSA identity also includes the invocation.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct SsaKey {
    node: NodeKey,
    call_frame: Option<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ProcedureFlow {
    Continue,
    Break,
    Return,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct FlowPredicate {
    expression: PredicateExpression,
    controls: Vec<VersionId>,
}

impl FlowPredicate {
    fn expression(expression: &Expression, controls: &[VersionId]) -> Self {
        let mut controls = controls.to_vec();
        controls.sort_unstable();
        controls.dedup();
        Self {
            expression: PredicateExpression::from_expression(expression),
            controls,
        }
    }

    fn opaque(identity: usize, controls: &[VersionId]) -> Self {
        let mut controls = controls.to_vec();
        controls.sort_unstable();
        controls.dedup();
        Self {
            expression: PredicateExpression::Opaque(identity),
            controls,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum PredicateExpression {
    Variable {
        id: VarId,
        index: Vec<PredicateExpression>,
        select: Vec<PredicateExpression>,
        range: Option<(u8, Box<PredicateExpression>)>,
    },
    Value(crate::ir::ValueVariant),
    Unary(Op, Box<PredicateExpression>),
    Binary(Box<PredicateExpression>, Op, Box<PredicateExpression>),
    Ternary(
        Box<PredicateExpression>,
        Box<PredicateExpression>,
        Box<PredicateExpression>,
    ),
    Concatenation(Vec<(PredicateExpression, Option<PredicateExpression>)>),
    ArrayLiteral(Vec<(Option<PredicateExpression>, PredicateExpression)>),
    StructConstructor(Vec<(veryl_parser::resource_table::StrId, PredicateExpression)>),
    Opaque(usize),
}

impl PredicateExpression {
    fn from_expression(expression: &Expression) -> Self {
        match expression {
            Expression::Term(factor) => match factor.as_ref() {
                Factor::Variable(id, index, select, _) => Self::Variable {
                    id: *id,
                    index: index.0.iter().map(Self::from_expression).collect(),
                    select: select.0.iter().map(Self::from_expression).collect(),
                    range: select.1.as_ref().map(|(op, expression)| {
                        let op = match op {
                            crate::ir::VarSelectOp::Colon => 0,
                            crate::ir::VarSelectOp::PlusColon => 1,
                            crate::ir::VarSelectOp::MinusColon => 2,
                            crate::ir::VarSelectOp::Step => 3,
                        };
                        (op, Box::new(Self::from_expression(expression)))
                    }),
                },
                Factor::Value(comptime) => Self::Value(comptime.value.clone()),
                _ => Self::Opaque(std::ptr::from_ref(factor.as_ref()).addr()),
            },
            Expression::Unary(op, expression, _) => {
                Self::Unary(*op, Box::new(Self::from_expression(expression)))
            }
            Expression::Binary(left, op, right, _) => Self::Binary(
                Box::new(Self::from_expression(left)),
                *op,
                Box::new(Self::from_expression(right)),
            ),
            Expression::Ternary(condition, left, right, _) => Self::Ternary(
                Box::new(Self::from_expression(condition)),
                Box::new(Self::from_expression(left)),
                Box::new(Self::from_expression(right)),
            ),
            Expression::Concatenation(parts, _) => Self::Concatenation(
                parts
                    .iter()
                    .map(|(part, repeat)| {
                        (
                            Self::from_expression(part),
                            repeat.as_ref().map(Self::from_expression),
                        )
                    })
                    .collect(),
            ),
            Expression::ArrayLiteral(items, _) => Self::ArrayLiteral(
                items
                    .iter()
                    .map(|item| match item {
                        ArrayLiteralItem::Value(value, repeat) => (
                            repeat.as_ref().map(|repeat| Self::from_expression(repeat)),
                            Self::from_expression(value),
                        ),
                        ArrayLiteralItem::Defaul(value) => (None, Self::from_expression(value)),
                    })
                    .collect(),
            ),
            Expression::StructConstructor(_, fields, _) => Self::StructConstructor(
                fields
                    .iter()
                    .map(|(name, value)| (*name, Self::from_expression(value)))
                    .collect(),
            ),
        }
    }
}

type FlowSemanticId = usize;
type ContinuationSemanticId = usize;

#[derive(Clone, PartialEq, Eq, Hash)]
enum FlowSemanticKey {
    Outcome(ProcedureFlow),
    Decision {
        predicate: FlowPredicate,
        arms: Vec<FlowSemanticId>,
    },
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum ContinuationSemanticKey {
    Outcome(bool),
    Decision {
        predicate: FlowPredicate,
        arms: Vec<ContinuationSemanticId>,
    },
}

#[derive(Clone)]
struct FlowArm {
    condition: PathCondition,
    tree: FlowTree,
}

#[derive(Clone)]
enum FlowTreeNode {
    Outcome(ProcedureFlow),
    Decision {
        predicate: FlowPredicate,
        arms: Vec<FlowArm>,
    },
}

struct FlowTreeData {
    node: FlowTreeNode,
    semantic: FlowSemanticId,
    continuation: ContinuationSemanticId,
    outcomes: u8,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct FlowTree(usize);

#[derive(Default)]
struct FlowStore {
    trees: Vec<FlowTreeData>,
    semantics: Vec<FlowSemanticKey>,
    semantic_ids: HashMap<FlowSemanticKey, FlowSemanticId>,
    continuations: Vec<ContinuationSemanticKey>,
    continuation_ids: HashMap<ContinuationSemanticKey, ContinuationSemanticId>,
    bind_mapped: HashMap<FlowTree, FlowTree>,
    bind_work: Vec<(FlowTree, bool)>,
    #[cfg(test)]
    bind_visits: usize,
}

impl FlowStore {
    const CONTINUE: u8 = 1;
    const BREAK: u8 = 2;
    const RETURN: u8 = 4;

    fn intern_semantic(&mut self, key: FlowSemanticKey) -> FlowSemanticId {
        if let Some(id) = self.semantic_ids.get(&key) {
            return *id;
        }
        let id = self.semantics.len();
        self.semantics.push(key.clone());
        self.semantic_ids.insert(key, id);
        id
    }

    fn intern_continuation(&mut self, key: ContinuationSemanticKey) -> ContinuationSemanticId {
        if let Some(id) = self.continuation_ids.get(&key) {
            return *id;
        }
        let id = self.continuations.len();
        self.continuations.push(key.clone());
        self.continuation_ids.insert(key, id);
        id
    }

    fn push_tree(&mut self, data: FlowTreeData) -> FlowTree {
        let tree = FlowTree(self.trees.len());
        self.trees.push(data);
        tree
    }

    fn outcome(&mut self, flow: ProcedureFlow) -> FlowTree {
        let bit = Self::outcome_bit(flow);
        let semantic = self.intern_semantic(FlowSemanticKey::Outcome(flow));
        let continuation = self.intern_continuation(ContinuationSemanticKey::Outcome(
            flow == ProcedureFlow::Continue,
        ));
        self.push_tree(FlowTreeData {
            node: FlowTreeNode::Outcome(flow),
            semantic,
            continuation,
            outcomes: bit,
        })
    }

    fn decision(&mut self, predicate: FlowPredicate, arms: Vec<FlowArm>) -> FlowTree {
        debug_assert!(!arms.is_empty());
        let outcomes = arms
            .iter()
            .fold(0, |outcomes, arm| outcomes | self.data(arm.tree).outcomes);
        let semantic_arms = arms
            .iter()
            .map(|arm| self.data(arm.tree).semantic)
            .collect::<Vec<_>>();
        let continuation_arms = arms
            .iter()
            .map(|arm| self.data(arm.tree).continuation)
            .collect::<Vec<_>>();
        let semantic = if semantic_arms[1..]
            .iter()
            .all(|arm| *arm == semantic_arms[0])
        {
            semantic_arms[0]
        } else {
            self.intern_semantic(FlowSemanticKey::Decision {
                predicate: predicate.clone(),
                arms: semantic_arms,
            })
        };
        let continuation = if continuation_arms[1..]
            .iter()
            .all(|arm| *arm == continuation_arms[0])
        {
            continuation_arms[0]
        } else {
            self.intern_continuation(ContinuationSemanticKey::Decision {
                predicate: predicate.clone(),
                arms: continuation_arms,
            })
        };
        self.push_tree(FlowTreeData {
            node: FlowTreeNode::Decision { predicate, arms },
            semantic,
            continuation,
            outcomes,
        })
    }

    fn outcome_bit(flow: ProcedureFlow) -> u8 {
        match flow {
            ProcedureFlow::Continue => Self::CONTINUE,
            ProcedureFlow::Break => Self::BREAK,
            ProcedureFlow::Return => Self::RETURN,
        }
    }

    fn data(&self, tree: FlowTree) -> &FlowTreeData {
        &self.trees[tree.0]
    }

    fn contains(&self, tree: FlowTree, flow: ProcedureFlow) -> bool {
        self.data(tree).outcomes & Self::outcome_bit(flow) != 0
    }

    fn aggregate(&self, tree: FlowTree) -> ProcedureFlow {
        if self.contains(tree, ProcedureFlow::Continue) {
            ProcedureFlow::Continue
        } else if self.contains(tree, ProcedureFlow::Break) {
            ProcedureFlow::Break
        } else {
            ProcedureFlow::Return
        }
    }

    /// Substitute `next` for every continuing leaf in `tree`.
    ///
    /// `tree` is one source statement's plan. Blocks apply this from right to
    /// left, so a long sequential block never walks the prefix built so far.
    fn bind(&mut self, tree: FlowTree, next: FlowTree) -> FlowTree {
        if !self.contains(tree, ProcedureFlow::Continue) {
            return tree;
        }
        let mut mapped = std::mem::take(&mut self.bind_mapped);
        mapped.clear();
        let mut work = std::mem::take(&mut self.bind_work);
        work.clear();
        work.push((tree, false));
        while let Some((current, expanded)) = work.pop() {
            #[cfg(test)]
            {
                self.bind_visits += 1;
            }
            if mapped.contains_key(&current) {
                continue;
            }
            match self.data(current).node.clone() {
                FlowTreeNode::Outcome(ProcedureFlow::Continue) => {
                    mapped.insert(current, next);
                }
                FlowTreeNode::Outcome(_) => {
                    mapped.insert(current, current);
                }
                FlowTreeNode::Decision { predicate, arms } if expanded => {
                    let arms = arms
                        .into_iter()
                        .map(|arm| FlowArm {
                            condition: arm.condition,
                            tree: mapped[&arm.tree],
                        })
                        .collect();
                    let bound = self.decision(predicate, arms);
                    mapped.insert(current, bound);
                }
                FlowTreeNode::Decision { arms, .. } => {
                    work.push((current, true));
                    for arm in arms.into_iter().rev() {
                        if !mapped.contains_key(&arm.tree) {
                            work.push((arm.tree, false));
                        }
                    }
                }
            }
        }
        let bound = mapped[&tree];
        self.bind_mapped = mapped;
        self.bind_work = work;
        bound
    }

    fn leave_loop(&mut self, tree: FlowTree) -> FlowTree {
        let mut mapped = HashMap::default();
        let mut work = vec![(tree, false)];
        while let Some((current, expanded)) = work.pop() {
            if mapped.contains_key(&current) {
                continue;
            }
            match self.data(current).node.clone() {
                FlowTreeNode::Outcome(ProcedureFlow::Return) => {
                    mapped.insert(current, current);
                }
                FlowTreeNode::Outcome(_) => {
                    let continuing = self.outcome(ProcedureFlow::Continue);
                    mapped.insert(current, continuing);
                }
                FlowTreeNode::Decision { predicate, arms } if expanded => {
                    let arms = arms
                        .into_iter()
                        .map(|arm| FlowArm {
                            condition: arm.condition,
                            tree: mapped[&arm.tree],
                        })
                        .collect();
                    let outside = self.decision(predicate, arms);
                    mapped.insert(current, outside);
                }
                FlowTreeNode::Decision { arms, .. } => {
                    work.push((current, true));
                    for arm in arms.into_iter().rev() {
                        if !mapped.contains_key(&arm.tree) {
                            work.push((arm.tree, false));
                        }
                    }
                }
            }
        }
        mapped[&tree]
    }

    fn collect_continuation_controls(
        &self,
        tree: FlowTree,
        controls: &mut Vec<(Vec<VersionId>, PathCondition)>,
    ) {
        let mut work = vec![(tree, PathCondition::default())];
        while let Some((current, inherited)) = work.pop() {
            let FlowTreeNode::Decision { predicate, arms } = &self.data(current).node else {
                continue;
            };
            let decision_matters = arms[1..].iter().any(|arm| {
                self.data(arm.tree).continuation != self.data(arms[0].tree).continuation
            });
            for arm in arms.iter().rev() {
                let Some(condition) = inherited.conjoin_if_compatible(&arm.condition) else {
                    continue;
                };
                if decision_matters
                    && self.contains(arm.tree, ProcedureFlow::Continue)
                    && !predicate.controls.is_empty()
                {
                    controls.push((predicate.controls.clone(), condition.clone()));
                }
                work.push((arm.tree, condition));
            }
        }
    }
}

#[cfg(test)]
mod flow_store_tests {
    use super::*;

    #[test]
    fn sequential_early_exits_are_linear_and_do_not_use_the_native_stack() {
        const STATEMENTS: usize = 100_000;

        let mut store = FlowStore::default();
        let continuing = store.outcome(ProcedureFlow::Continue);
        let returning = store.outcome(ProcedureFlow::Return);
        let predicate = FlowPredicate {
            expression: PredicateExpression::Value(crate::ir::ValueVariant::Unknown),
            controls: Vec::new(),
        };
        let mut statements = Vec::with_capacity(STATEMENTS);
        for _ in 0..STATEMENTS {
            statements.push(store.decision(
                predicate.clone(),
                vec![
                    FlowArm {
                        condition: PathCondition::default(),
                        tree: returning,
                    },
                    FlowArm {
                        condition: PathCondition::default(),
                        tree: continuing,
                    },
                ],
            ));
        }

        // A block is composed from its tail. Each bind therefore visits only
        // that statement's plan, never the already-built sequential prefix.
        let mut tree = store.outcome(ProcedureFlow::Continue);
        for statement in statements.into_iter().rev() {
            tree = store.bind(statement, tree);
        }

        assert!(store.contains(tree, ProcedureFlow::Continue));
        assert!(store.contains(tree, ProcedureFlow::Return));
        assert!(store.trees.len() <= 2 * STATEMENTS + 3);
        assert!(store.bind_visits <= 4 * STATEMENTS);
        let mut controls = Vec::new();
        store.collect_continuation_controls(tree, &mut controls);
        assert!(controls.is_empty());
    }
}

struct FlowResult {
    flow: ProcedureFlow,
    continuation_controls: Vec<VersionId>,
    tree: FlowTree,
}

struct FunctionFlow {
    return_id: Option<VarId>,
    revision: StateRevision,
}

struct LoopFlow {
    checkpoint: Checkpoint,
    breaks: Vec<FlowState>,
    returns: Option<RuntimeReturnCapture>,
}

struct RuntimeReturnCapture {
    /// Runtime-loop returns are exits after zero or more continuing
    /// iterations. Delay recording them in the enclosing function until the
    /// loop transfer has been applied.
    revision: StateRevision,
    conditions: Vec<PathCondition>,
}

struct FlowState {
    state: BranchState<SsaKey>,
    condition: PathCondition,
}

struct RuntimeLoopBody {
    flow: FlowResult,
    continuing: BranchState<SsaKey>,
    breaks: Vec<FlowState>,
    returned: Option<FlowState>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct FunctionSummaryKey {
    id: VarId,
    index: Option<Vec<usize>>,
}

#[derive(Clone)]
struct FunctionSummary {
    arg_map: HashMap<VarPath, VarId>,
    graph: Rc<DependencyDag<SsaKey>>,
    /// Metadata derived from the immutable summary graph. Keep it with the
    /// summary so applying an N-node body at N call sites does not rescan the
    /// whole graph at every call.
    external_keys: Vec<SsaKey>,
    branches: Vec<BranchId>,
    result: FunctionResultSummary,
    writes: Vec<(NodeKey, Option<usize>)>,
    status: AnalysisStatus,
}

enum FunctionSummaryLookup {
    Ready(Rc<FunctionSummary>),
    Recursive,
    Missing,
}

type FunctionResultSummary = Vec<(ArraySpan, Vec<(PackedSpan, Option<usize>)>)>;

pub(super) struct FunctionSummaries<'a> {
    module: &'a Module,
    bit_part: &'a BitPartition,
    summaries: HashMap<FunctionSummaryKey, Option<Rc<FunctionSummary>>>,
    contexts: Vec<ProcedureContext>,
}

/// Reusable module-local evaluation context for independent procedural
/// declarations. Its large variable and function maps are built once per
/// active analysis context; SSA and control-flow state remain per analysis.
pub(super) struct ProcedureContext {
    ctx: Option<Context>,
    module_scope_ids: Rc<HashSet<VarId>>,
}

impl ProcedureContext {
    pub(super) fn new(module: &Module) -> Self {
        let mut ctx = Context::default();
        ctx.variables = module.variables.clone();
        ctx.variables.extend(module.interface_members.clone());
        ctx.functions = module.functions.clone();
        let module_scope_ids = ctx
            .variables
            .iter()
            .filter_map(|(&id, variable)| {
                matches!(
                    variable.affiliation,
                    crate::symbol::Affiliation::Module | crate::symbol::Affiliation::Interface
                )
                .then_some(id)
            })
            .collect::<HashSet<_>>();
        #[cfg(test)]
        MODULE_CONTEXT_ENTRIES
            .set(MODULE_CONTEXT_ENTRIES.get() + ctx.variables.len() + ctx.functions.len());
        Self {
            ctx: Some(ctx),
            module_scope_ids: Rc::new(module_scope_ids),
        }
    }

    fn take(&mut self) -> (Context, Rc<HashSet<VarId>>) {
        (
            self.ctx.take().expect("procedure context is not reentrant"),
            Rc::clone(&self.module_scope_ids),
        )
    }

    fn restore(&mut self, ctx: Context) {
        debug_assert!(self.ctx.is_none());
        self.ctx = Some(ctx);
    }
}

impl<'a> FunctionSummaries<'a> {
    pub(super) fn new(module: &'a Module, bit_part: &'a BitPartition) -> Self {
        Self {
            module,
            bit_part,
            summaries: HashMap::default(),
            contexts: Vec::new(),
        }
    }

    fn get(&mut self, call: &FunctionCall) -> FunctionSummaryLookup {
        let key = FunctionSummaryKey {
            id: call.id,
            index: call.index.clone(),
        };
        if let Some(summary) = self.summaries.get(&key).cloned() {
            return summary.map_or(
                FunctionSummaryLookup::Recursive,
                FunctionSummaryLookup::Ready,
            );
        }
        self.summaries.insert(key.clone(), None);
        let mut context = self
            .contexts
            .pop()
            .unwrap_or_else(|| ProcedureContext::new(self.module));
        let summary = ProcedureAnalysis::summarize_function(
            self.module,
            self.bit_part,
            call.id,
            &call.receiver_index,
            &mut context,
            self,
        )
        .map(Rc::new);
        self.contexts.push(context);
        if let Some(summary) = summary {
            // A dynamic receiver summary contains the selector expression of
            // this call site. Keep only the in-progress entry as a recursion
            // guard; reusing the completed graph at another call site would
            // reuse the wrong selector dependencies.
            if call.index.is_some() || call.receiver_index.0.is_empty() {
                self.summaries.insert(key, Some(summary.clone()));
            } else {
                self.summaries.remove(&key);
            }
            FunctionSummaryLookup::Ready(summary)
        } else {
            self.summaries.remove(&key);
            FunctionSummaryLookup::Missing
        }
    }
}

#[cfg(test)]
thread_local! {
    static FUNCTION_EVALUATIONS: Cell<usize> = const { Cell::new(0) };
    static FUNCTION_RESULT_VERSIONS: Cell<usize> = const { Cell::new(0) };
    static FUNCTION_RESULT_REGION_PROBES: Cell<usize> = const { Cell::new(0) };
    static FORMAL_OUTPUT_REGION_PROBES: Cell<usize> = const { Cell::new(0) };
    static FUNCTION_BARRIER_EVALUATIONS: Cell<usize> = const { Cell::new(0) };
    static FUNCTION_SUMMARY_GRAPH_NODES: Cell<usize> = const { Cell::new(0) };
    static MODULE_CONTEXT_ENTRIES: Cell<usize> = const { Cell::new(0) };
    static FUNCTION_SUMMARY_METADATA_VISITS: Cell<usize> = const { Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_function_evaluation_count() {
    FUNCTION_EVALUATIONS.set(0);
    FUNCTION_RESULT_VERSIONS.set(0);
    FUNCTION_RESULT_REGION_PROBES.set(0);
    FORMAL_OUTPUT_REGION_PROBES.set(0);
    FUNCTION_BARRIER_EVALUATIONS.set(0);
    FUNCTION_SUMMARY_GRAPH_NODES.set(0);
    MODULE_CONTEXT_ENTRIES.set(0);
    FUNCTION_SUMMARY_METADATA_VISITS.set(0);
    EXPRESSION_LAYOUT_VISITS.set(0);
}

#[cfg(test)]
pub(crate) fn function_evaluation_count() -> usize {
    FUNCTION_EVALUATIONS.get()
}

#[cfg(test)]
pub(crate) fn function_result_version_count() -> usize {
    FUNCTION_RESULT_VERSIONS.get()
}

#[cfg(test)]
pub(crate) fn function_result_region_probe_count() -> usize {
    FUNCTION_RESULT_REGION_PROBES.get()
}

#[cfg(test)]
pub(crate) fn formal_output_region_probe_count() -> usize {
    FORMAL_OUTPUT_REGION_PROBES.get()
}

#[cfg(test)]
pub(crate) fn function_barrier_evaluation_count() -> usize {
    FUNCTION_BARRIER_EVALUATIONS.get()
}

#[cfg(test)]
pub(crate) fn function_summary_graph_node_count() -> usize {
    FUNCTION_SUMMARY_GRAPH_NODES.get()
}

#[cfg(test)]
pub(crate) fn reset_module_context_entries() {
    MODULE_CONTEXT_ENTRIES.set(0);
}

#[cfg(test)]
pub(crate) fn module_context_entries() -> usize {
    MODULE_CONTEXT_ENTRIES.get()
}

#[cfg(test)]
pub(crate) fn function_summary_metadata_visits() -> usize {
    FUNCTION_SUMMARY_METADATA_VISITS.get()
}

#[cfg(test)]
pub(crate) fn expression_layout_visit_count() -> usize {
    EXPRESSION_LAYOUT_VISITS.get()
}

pub(super) fn analyze<'a>(
    module: &'a Module,
    bit_part: &'a BitPartition,
    statements: &[Statement],
    declaration_index: usize,
    branch_namespace: usize,
    context: &mut ProcedureContext,
    summaries: &mut FunctionSummaries<'a>,
) -> ProcedureResult {
    ProcedureAnalysis::analyze(
        module,
        bit_part,
        statements,
        declaration_index,
        branch_namespace,
        context,
        summaries,
    )
}

pub(super) struct ProcedureResult {
    pub(super) graph: DependencyDag<NodeKey>,
    pub(super) destinations: Vec<(NodeKey, Option<usize>)>,
    pub(super) status: AnalysisStatus,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum AnalysisStatus {
    #[default]
    Complete,
    Partial,
}

impl AnalysisStatus {
    pub(super) fn is_complete(self) -> bool {
        self == Self::Complete
    }
}

pub(super) struct Dependency {
    pub(super) source: NodeKey,
    pub(super) destination: NodeKey,
    pub(super) kind: BitDependency,
    pub(super) condition: PathCondition,
}

#[derive(Default)]
struct ExpressionSources {
    sources: Vec<(VersionId, PositionRelation)>,
}

struct DestinationSnapshot {
    key: NodeKey,
    sources: ExpressionSources,
    opaque: bool,
}

#[derive(Clone, Copy)]
struct FormalOutputCoercion {
    actual_width: usize,
    formal_width: usize,
    formal_signed: bool,
}

#[derive(Default)]
struct ProjectionContext {
    destination_index: Option<AffineIndex>,
    destination_array: Option<ArraySpan>,
    destination_array_offset: Option<isize>,
}

impl ExpressionSources {
    fn whole(versions: Vec<VersionId>) -> Self {
        Self {
            sources: versions
                .into_iter()
                .map(|version| (version, PositionRelation::whole()))
                .collect(),
        }
    }

    fn extend(&mut self, other: Self) {
        self.sources.extend(other.sources);
    }

    fn extend_whole(&mut self, versions: impl IntoIterator<Item = VersionId>) {
        self.sources.extend(
            versions
                .into_iter()
                .map(|version| (version, PositionRelation::whole())),
        );
    }

    fn push(&mut self, version: VersionId, relation: PositionRelation) {
        self.sources.push((version, relation));
    }

    fn is_empty(&self) -> bool {
        self.sources.is_empty()
    }

    fn translate(&mut self, offset: PositionRelation) {
        for (_, current) in &mut self.sources {
            *current = current.compose(offset);
        }
    }

    fn forget_array_position(&mut self) {
        for (_, relation) in &mut self.sources {
            relation.array = None;
        }
    }

    fn forget_packed_position(&mut self) {
        for (_, relation) in &mut self.sources {
            relation.packed = None;
        }
    }

    fn widen_all(&mut self) {
        for (_, relation) in &mut self.sources {
            *relation = PositionRelation::whole();
        }
    }

    fn normalize(&mut self) {
        self.sources.sort_unstable();
        self.sources.dedup();
    }
}

pub(super) struct ExpressionAnalysis<'a, 's> {
    inner: Option<ProcedureAnalysis<'a, 's>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct ExpressionRegion {
    pub(super) array: ArraySpan,
    pub(super) packed: PackedSpan,
    pub(super) context_width: usize,
}

impl<'a, 's> ExpressionAnalysis<'a, 's> {
    pub(super) fn new(
        bit_part: &'a BitPartition,
        context: &mut ProcedureContext,
        summaries: &'s mut FunctionSummaries<'a>,
    ) -> Self {
        let (mut ctx, module_scope_ids) = context.take();
        ctx.begin_analysis_transaction();
        let mut inner = ProcedureAnalysis::from_context(bit_part, ctx, module_scope_ids);
        inner.summaries = Some(summaries);
        Self { inner: Some(inner) }
    }

    fn inner(&mut self) -> &mut ProcedureAnalysis<'a, 's> {
        self.inner.as_mut().expect("expression analysis is active")
    }

    pub(super) fn eval(&mut self, expression: &Expression) -> Vec<RegionSource> {
        let inner = self.inner();
        inner.prepare_top_expression(expression);
        inner.eval_expression_sources(expression)
    }

    /// Evaluate an actual once in source order, then project every requested
    /// region from the variable versions and call results captured at each
    /// syntactic occurrence. The ordered effects are committed only once.
    pub(super) fn eval_with_regions(
        &mut self,
        expression: &Expression,
        requests: &[ExpressionRegion],
    ) -> (
        Vec<RegionSource>,
        Vec<(ExpressionRegion, Vec<RegionSource>)>,
    ) {
        let inner = self.inner();
        inner.prepare_top_expression(expression);
        inner.snapshot_expression(expression, |this| {
            let mut source_cache = SourceCache::default();
            let regions = requests
                .iter()
                .copied()
                .map(|request| {
                    let sources = this.eval_expr_requested(
                        expression,
                        request.array,
                        request.packed,
                        request.context_width,
                    );
                    (
                        request,
                        this.mapped_region_sources_cached(&mut source_cache, sources),
                    )
                })
                .collect();
            // Projected regions usually share the same SSA value DAG. Reuse
            // their source summaries for the whole-expression result too.
            let whole = this.eval_expression_sources_cached(expression, &mut source_cache);
            (whole, regions)
        })
    }

    pub(super) fn dependencies(&mut self) -> Vec<Dependency> {
        self.inner().dependencies()
    }

    pub(super) fn restore(mut self, context: &mut ProcedureContext) {
        let mut inner = self.inner.take().expect("expression analysis is active");
        inner.ctx.rollback_analysis_transaction();
        context.restore(inner.ctx);
    }

    pub(super) fn is_complete(&self) -> bool {
        self.inner
            .as_ref()
            .expect("expression analysis is active")
            .status
            .is_complete()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct RegionSource {
    pub(super) key: NodeKey,
    pub(super) offset: Option<(isize, isize)>,
    pub(super) condition: PathCondition,
}

struct ProcedureAnalysis<'a, 's> {
    bit_part: &'a BitPartition,
    ctx: Context,
    module_scope_ids: Rc<HashSet<VarId>>,
    ssa: SsaStore<SsaKey>,
    structural_dependency_cache: HashMap<VersionId, bool>,
    projection_source_cache: SourceCache<SsaKey>,
    flow_store: FlowStore,
    written: HashSet<NodeKey>,
    call_caches: Vec<CallCache>,
    call_frames: Vec<usize>,
    next_call_frame: usize,
    function_flows: Vec<FunctionFlow>,
    loop_flows: Vec<LoopFlow>,
    path_condition: PathCondition,
    effects_only: bool,
    projection_only: bool,
    causal_write_keys: Vec<NodeKey>,
    branch_namespace: usize,
    next_branch: usize,
    top_expression_branches: HashMap<*const Expression, BranchId>,
    top_expression_calls: HashMap<*const FunctionCall, usize>,
    status: AnalysisStatus,
    summaries: Option<&'s mut FunctionSummaries<'a>>,
}

impl<'a, 's> ProcedureAnalysis<'a, 's> {
    fn from_context(
        bit_part: &'a BitPartition,
        ctx: Context,
        module_scope_ids: Rc<HashSet<VarId>>,
    ) -> Self {
        Self {
            bit_part,
            ctx,
            module_scope_ids,
            ssa: SsaStore::default(),
            structural_dependency_cache: HashMap::default(),
            projection_source_cache: SourceCache::default(),
            flow_store: FlowStore::default(),
            written: HashSet::default(),
            call_caches: Vec::new(),
            call_frames: Vec::new(),
            next_call_frame: 0,
            function_flows: Vec::new(),
            loop_flows: Vec::new(),
            path_condition: PathCondition::default(),
            effects_only: false,
            projection_only: false,
            causal_write_keys: Vec::new(),
            branch_namespace: 0,
            next_branch: 0,
            top_expression_branches: HashMap::default(),
            top_expression_calls: HashMap::default(),
            status: AnalysisStatus::Complete,
            summaries: None,
        }
    }

    fn analyze(
        module: &'a Module,
        bit_part: &'a BitPartition,
        statements: &[Statement],
        declaration_index: usize,
        branch_namespace: usize,
        context: &mut ProcedureContext,
        summaries: &'s mut FunctionSummaries<'a>,
    ) -> ProcedureResult {
        let (mut ctx, module_scope_ids) = context.take();
        ctx.begin_analysis_transaction();
        let mut this = Self::from_context(bit_part, ctx, module_scope_ids);
        this.summaries = Some(summaries);
        this.causal_write_keys =
            this.process_write_footprint(module, declaration_index, statements);
        this.branch_namespace = branch_namespace;
        this.eval_block(statements, &[]);
        let (graph, destinations) = this.dependency_graph();
        let result = ProcedureResult {
            graph,
            destinations,
            status: this.status,
        };
        this.ctx.rollback_analysis_transaction();
        context.restore(this.ctx);
        result
    }

    fn eval_expression_sources(&mut self, expression: &Expression) -> Vec<RegionSource> {
        self.eval_expression_sources_cached(expression, &mut SourceCache::default())
    }

    fn eval_expression_sources_cached(
        &mut self,
        expression: &Expression,
        cache: &mut SourceCache<SsaKey>,
    ) -> Vec<RegionSource> {
        let versions = self.eval_reachable_expr(expression);
        let value = self.ssa.definition(versions);
        let mut sources = self
            .ssa
            .root_source_relations_guarded_cached(value, cache)
            .into_iter()
            .filter_map(|(source, _, condition)| {
                source.call_frame.is_none().then_some(RegionSource {
                    key: source.node,
                    offset: None,
                    condition,
                })
            })
            .filter(|source| self.is_module_scope_key(source.key))
            .collect::<Vec<_>>();
        sources.sort_unstable_by_key(|source| (source.key, source.condition.clone()));
        sources.dedup_by(|left, right| left.key == right.key && left.condition == right.condition);
        sources
    }

    fn mapped_region_sources_cached(
        &mut self,
        cache: &mut SourceCache<SsaKey>,
        mut sources: ExpressionSources,
    ) -> Vec<RegionSource> {
        sources.normalize();
        let mut mapped = Vec::new();
        for (version, expression_offset) in sources.sources {
            for (source, relation, condition) in self
                .ssa
                .root_source_relations_guarded_including_entry_cached(version, cache)
            {
                if source.call_frame.is_some() {
                    continue;
                }
                let relation = expression_offset.compose(relation).reversed();
                mapped.push(RegionSource {
                    key: source.node,
                    offset: relation.array.zip(relation.packed),
                    condition,
                });
            }
        }
        mapped.sort_unstable_by_key(|source| (source.key, source.offset, source.condition.clone()));
        mapped.dedup_by(|left, right| {
            left.key == right.key
                && left.offset == right.offset
                && left.condition == right.condition
        });
        mapped
    }

    fn summarize_function(
        module: &'a Module,
        bit_part: &'a BitPartition,
        id: VarId,
        receiver_index: &VarIndex,
        context: &mut ProcedureContext,
        summaries: &'s mut FunctionSummaries<'a>,
    ) -> Option<FunctionSummary> {
        let function = module.functions.get(&id)?;
        let body = function.get_function_for_index(receiver_index)?;
        let formal_ids = body.arg_map.values().copied().collect::<HashSet<_>>();
        let (mut ctx, module_scope_ids) = context.take();
        ctx.begin_analysis_transaction();
        let mut this = Self::from_context(bit_part, ctx, module_scope_ids);
        this.summaries = Some(summaries);
        this.call_caches.push(None);
        this.causal_write_keys = this.statement_write_footprint(&body.statements);
        this.eval_function_body(&body.statements, body.ret, &[]);
        this.call_caches.pop();

        let result_versions: Vec<(ArraySpan, Vec<(PackedSpan, VersionId)>)> = body
            .ret
            .map(|ret| this.current_function_return_region_groups(ret, None))
            .unwrap_or_default();

        let mut destinations = this
            .written
            .iter()
            .copied()
            .filter(|destination| {
                formal_ids.contains(&destination.0) || this.is_module_scope_key(*destination)
            })
            .collect::<Vec<_>>();

        destinations.sort_unstable();
        let write_versions = destinations
            .into_iter()
            .map(|destination| {
                let version = this.read_key(destination);
                (destination, version)
            })
            .collect::<Vec<_>>();

        // Only entry versions that were actually created can appear as DAG
        // sources. Enumerating every partition of every visible variable for
        // each procedure/function makes N sparse declarations cost N^2.
        // Take this snapshot after all result/write roots have been read.
        let allowed = this
            .ssa
            .entry_keys()
            .filter(|key| {
                key.call_frame.is_none()
                    && (formal_ids.contains(&key.node.0)
                        || this.module_scope_ids.contains(&key.node.0))
            })
            .collect::<HashSet<_>>();

        let mut roots = result_versions
            .iter()
            .flat_map(|(_, regions)| regions.iter().map(|(_, version)| *version))
            .collect::<Vec<_>>();
        roots.extend(write_versions.iter().map(|(_, version)| *version));
        let graph = this.ssa.dependency_dag(&roots, &allowed);
        let graph = Rc::new(graph);
        #[cfg(test)]
        FUNCTION_SUMMARY_GRAPH_NODES.set(FUNCTION_SUMMARY_GRAPH_NODES.get().max(graph.nodes.len()));
        let mut root = graph.roots.iter().copied();
        let result = result_versions
            .into_iter()
            .map(|(array, regions)| {
                let regions = regions
                    .into_iter()
                    .map(|(span, _)| {
                        (
                            span,
                            root.next().expect("every function result has a DAG root"),
                        )
                    })
                    .collect();
                (array, regions)
            })
            .collect();
        let writes = write_versions
            .into_iter()
            .map(|(destination, _)| {
                (
                    destination,
                    root.next().expect("every function write has a DAG root"),
                )
            })
            .collect();
        debug_assert!(root.next().is_none());

        let mut external_keys = Vec::new();
        let mut seen_external_keys = HashSet::default();
        for node in &graph.nodes {
            if let DependencyDagNode::External(key) = node
                && seen_external_keys.insert(*key)
            {
                external_keys.push(*key);
            }
        }
        let branches =
            PathCondition::collect_branches(graph.edges.iter().map(|edge| &edge.condition));

        let summary = FunctionSummary {
            arg_map: body.arg_map,
            graph,
            external_keys,
            branches,
            result,
            writes,
            status: this.status,
        };
        this.ctx.rollback_analysis_transaction();
        context.restore(this.ctx);
        Some(summary)
    }

    fn dependencies(&mut self) -> Vec<Dependency> {
        let mut dependencies = Vec::new();
        let destinations = self
            .written
            .iter()
            .copied()
            .filter(|key| self.is_module_scope_key(*key))
            .collect::<Vec<_>>();
        let destination_versions = destinations
            .into_iter()
            .map(|destination| (destination, self.read_key(destination)))
            .collect::<Vec<_>>();
        let mut source_cache =
            SourceCache::restricted(self.ssa.entry_keys().filter(|key| {
                key.call_frame.is_none() && self.module_scope_ids.contains(&key.node.0)
            }));
        for (destination, version) in destination_versions {
            let sources = self
                .ssa
                .root_source_relations_guarded_cached(version, &mut source_cache);
            dependencies.extend(
                sources
                    .into_iter()
                    .filter_map(|(source, source_kind, condition)| {
                        source
                            .call_frame
                            .is_none()
                            .then_some((source.node, source_kind, condition))
                    })
                    .filter(|(source, _, _)| self.is_module_scope_key(*source))
                    .map(|(source, source_kind, condition)| Dependency {
                        source,
                        destination,
                        kind: Self::dependency_kind(source_kind),
                        condition,
                    }),
            );
        }
        dependencies.sort_unstable_by_key(|dependency| {
            (
                dependency.source,
                dependency.destination,
                dependency.condition.clone(),
            )
        });
        dependencies
    }

    fn dependency_graph(&mut self) -> (DependencyDag<NodeKey>, Vec<(NodeKey, Option<usize>)>) {
        let mut destinations = self
            .written
            .iter()
            .copied()
            .filter(|key| self.is_module_scope_key(*key))
            .collect::<Vec<_>>();
        destinations.sort_unstable();
        let roots = destinations
            .iter()
            .map(|destination| self.read_key(*destination))
            .collect::<Vec<_>>();
        let allowed = self
            .ssa
            .entry_keys()
            .filter(|key| key.call_frame.is_none() && self.module_scope_ids.contains(&key.node.0))
            .map(|key| key.node)
            .collect::<HashSet<_>>();
        let graph = self.dependency_dag_for_nodes(&roots, allowed);
        let destinations = destinations
            .into_iter()
            .zip(graph.roots.iter().copied())
            .collect();
        (graph, destinations)
    }

    fn dependency_kind(source_kind: PositionRelation) -> BitDependency {
        BitDependency {
            array: source_kind.array,
            packed: source_kind.packed,
        }
    }

    fn regular_transfer(
        &mut self,
        sources: ExpressionSources,
        initial: PositionRelation,
        step: PositionRelation,
        domain: PositionDomain,
    ) -> ExpressionSources {
        ExpressionSources {
            sources: sources
                .sources
                .into_iter()
                .map(|(source, relation)| {
                    let repeated =
                        self.ssa
                            .repeated(source, relation.compose(initial), step, domain);
                    (repeated, PositionRelation::default())
                })
                .collect(),
        }
    }

    fn regular_packed_repeat(
        &mut self,
        mut sources: ExpressionSources,
        array: ArraySpan,
        output_start: usize,
        output_length: usize,
        item_length: usize,
    ) -> ExpressionSources {
        let (Ok(output_start_offset), Ok(step), Some(domain)) = (
            isize::try_from(output_start),
            isize::try_from(item_length),
            PackedSpan::new(output_start, output_length),
        ) else {
            sources.forget_packed_position();
            return sources;
        };
        self.regular_transfer(
            sources,
            PositionRelation {
                array: Some(0),
                packed: Some(output_start_offset),
            },
            PositionRelation {
                array: Some(0),
                packed: Some(step),
            },
            position_domain(array, domain),
        )
    }

    fn regular_array_repeat(
        &mut self,
        mut sources: ExpressionSources,
        packed: PackedSpan,
        output_start: usize,
        output_length: usize,
        item_length: usize,
    ) -> ExpressionSources {
        let (Ok(output_start_offset), Ok(step)) =
            (isize::try_from(output_start), isize::try_from(item_length))
        else {
            sources.forget_array_position();
            return sources;
        };
        self.regular_transfer(
            sources,
            PositionRelation {
                array: Some(output_start_offset),
                packed: Some(0),
            },
            PositionRelation {
                array: Some(step),
                packed: Some(0),
            },
            position_domain(
                ArraySpan {
                    start: output_start,
                    length: output_length,
                },
                packed,
            ),
        )
    }

    fn is_module_scope_key(&self, key: NodeKey) -> bool {
        self.module_scope_ids.contains(&key.0)
    }

    fn ssa_key(&self, node: NodeKey) -> SsaKey {
        let call_frame = self
            .ctx
            .variables
            .get(&node.0)
            .is_some_and(|variable| variable.affiliation == crate::symbol::Affiliation::Function)
            .then(|| self.call_frames.last().copied())
            .flatten();
        SsaKey { node, call_frame }
    }

    fn read_key(&mut self, node: NodeKey) -> VersionId {
        self.ssa.read(self.ssa_key(node))
    }

    fn bind_key(&mut self, node: NodeKey, version: VersionId) {
        self.ssa.bind(self.ssa_key(node), version);
    }

    fn dependency_dag_for_nodes(
        &self,
        roots: &[VersionId],
        allowed: impl IntoIterator<Item = NodeKey>,
    ) -> DependencyDag<NodeKey> {
        let allowed = allowed
            .into_iter()
            .map(|node| SsaKey {
                node,
                call_frame: None,
            })
            .collect::<HashSet<_>>();
        let graph = self.ssa.dependency_dag(roots, &allowed);
        DependencyDag {
            nodes: graph
                .nodes
                .into_iter()
                .map(|node| match node {
                    DependencyDagNode::External(SsaKey {
                        node,
                        call_frame: None,
                    }) => DependencyDagNode::External(node),
                    DependencyDagNode::External(SsaKey {
                        call_frame: Some(_),
                        ..
                    }) => unreachable!("call-frame storage is not a visible DAG source"),
                    DependencyDagNode::Internal => DependencyDagNode::Internal,
                    DependencyDagNode::RegularTransfer => DependencyDagNode::RegularTransfer,
                })
                .collect(),
            edges: graph.edges,
            roots: graph.roots,
            domains: graph.domains,
            incoming: OnceCell::new(),
        }
    }

    fn process_write_footprint(
        &mut self,
        module: &Module,
        declaration_index: usize,
        statements: &[Statement],
    ) -> Vec<NodeKey> {
        let mut keys = HashSet::default();

        // Prefer the sparse IR destinations. Besides covering ordinary writes
        // exactly, this avoids scanning a dense assignment mask merely to add
        // a NodeKey that is already known from the statement itself.
        let mut visited = HashSet::default();
        self.collect_statement_write_footprint(statements, &mut keys, &mut visited);

        // `per_decl_refs` is the authoritative, bit-precise ownership record
        // for writes that the IR cannot recover (for example an unsupported
        // statement). It prevents an incomplete boundary in one process from
        // erasing a disjoint bit driven by another process.
        if let Some(references) = module.per_decl_refs.get(&declaration_index) {
            for (&id, reference) in references {
                for key in self.keys_for_id(id) {
                    if keys.contains(&key) {
                        continue;
                    }
                    let Some(packed) = self.key_span(key) else {
                        continue;
                    };
                    let Some(array_end) = key.1.end() else {
                        continue;
                    };
                    let start = key.1.start.min(reference.mask_assign.len());
                    let end = array_end.min(reference.mask_assign.len());
                    if reference.mask_assign[start..end]
                        .iter()
                        .any(|mask| packed_mask_overlaps(mask, packed))
                    {
                        keys.insert(key);
                    }
                }
            }
        }
        let mut keys = keys.into_iter().collect::<Vec<_>>();
        keys.sort_unstable();
        keys
    }

    fn statement_write_footprint(&mut self, statements: &[Statement]) -> Vec<NodeKey> {
        let mut keys = HashSet::default();
        let mut visited = HashSet::default();
        self.collect_statement_write_footprint(statements, &mut keys, &mut visited);
        let mut keys = keys.into_iter().collect::<Vec<_>>();
        keys.sort_unstable();
        keys
    }

    fn function_call_write_footprint(&mut self, call: &FunctionCall) -> Vec<NodeKey> {
        let mut keys = HashSet::default();
        let mut visited = HashSet::default();
        self.collect_function_call_write_footprint(call, &mut keys, &mut visited);
        let mut keys = keys.into_iter().collect::<Vec<_>>();
        keys.sort_unstable();
        keys
    }

    fn collect_statement_write_footprint(
        &mut self,
        statements: &[Statement],
        keys: &mut HashSet<NodeKey>,
        visited: &mut HashSet<FunctionSummaryKey>,
    ) {
        for statement in statements {
            match statement {
                Statement::Assign(assign) => {
                    self.collect_expression_write_footprint(&assign.expr, keys, visited);
                    for destination in &assign.dst {
                        self.collect_destination_write_footprint(destination, keys, visited);
                    }
                }
                Statement::If(statement) => {
                    self.collect_expression_write_footprint(&statement.cond, keys, visited);
                    self.collect_statement_write_footprint(&statement.true_side, keys, visited);
                    self.collect_statement_write_footprint(&statement.false_side, keys, visited);
                }
                Statement::IfReset(statement) => {
                    self.collect_statement_write_footprint(&statement.true_side, keys, visited);
                    self.collect_statement_write_footprint(&statement.false_side, keys, visited);
                }
                Statement::Case(statement) => {
                    self.collect_expression_write_footprint(&statement.case_target, keys, visited);
                    for arm in &statement.arms {
                        for pattern in &arm.patterns {
                            match pattern {
                                crate::ir::CasePattern::Eq(expression) => self
                                    .collect_expression_write_footprint(expression, keys, visited),
                                crate::ir::CasePattern::Range { lo, hi, .. } => {
                                    self.collect_expression_write_footprint(lo, keys, visited);
                                    self.collect_expression_write_footprint(hi, keys, visited);
                                }
                            }
                        }
                        self.collect_statement_write_footprint(&arm.body, keys, visited);
                    }
                    self.collect_statement_write_footprint(&statement.default, keys, visited);
                }
                Statement::For(statement) => {
                    let (start, end, _) = for_range_bounds(&statement.range);
                    for bound in [start, end] {
                        if let ForBound::Expression(expression) = bound {
                            self.collect_expression_write_footprint(expression, keys, visited);
                        }
                    }
                    self.collect_statement_write_footprint(&statement.body, keys, visited);
                }
                Statement::FunctionCall(call) => {
                    self.collect_function_call_write_footprint(call, keys, visited);
                }
                Statement::SystemFunctionCall(call) => {
                    self.collect_system_call_write_footprint(call, keys, visited);
                }
                Statement::TbMethodCall(_)
                | Statement::Break
                | Statement::Unsupported(_)
                | Statement::Null => {}
            }
        }
    }

    fn collect_destination_write_footprint(
        &mut self,
        destination: &AssignDestination,
        keys: &mut HashSet<NodeKey>,
        visited: &mut HashSet<FunctionSummaryKey>,
    ) {
        let mut resolved = destination.clone();
        resolved.index = self.receiver_index(resolved.id, &resolved.index);
        for (array, packed) in dst_writes(&resolved, &mut self.ctx) {
            keys.extend(self.bit_part.overlapping_access(resolved.id, array, packed));
        }
        for expression in destination
            .index
            .0
            .iter()
            .chain(destination.select.0.iter())
        {
            self.collect_expression_write_footprint(expression, keys, visited);
        }
        if let Some((_, expression)) = &destination.select.1 {
            self.collect_expression_write_footprint(expression, keys, visited);
        }
    }

    fn collect_expression_write_footprint(
        &mut self,
        expression: &Expression,
        keys: &mut HashSet<NodeKey>,
        visited: &mut HashSet<FunctionSummaryKey>,
    ) {
        match expression {
            Expression::Term(factor) => match factor.as_ref() {
                Factor::Variable(_, index, select, _) => {
                    for expression in index.0.iter().chain(select.0.iter()) {
                        self.collect_expression_write_footprint(expression, keys, visited);
                    }
                    if let Some((_, expression)) = &select.1 {
                        self.collect_expression_write_footprint(expression, keys, visited);
                    }
                }
                Factor::FunctionCall(call) => {
                    self.collect_function_call_write_footprint(call, keys, visited);
                }
                Factor::SystemFunctionCall(call) => {
                    self.collect_system_call_write_footprint(call, keys, visited);
                }
                Factor::Unknown(_)
                | Factor::HierVariable(_)
                | Factor::Value(_)
                | Factor::Anonymous(_) => {}
            },
            Expression::Unary(_, expression, _) => {
                self.collect_expression_write_footprint(expression, keys, visited);
            }
            Expression::Binary(left, _, right, _) => {
                self.collect_expression_write_footprint(left, keys, visited);
                self.collect_expression_write_footprint(right, keys, visited);
            }
            Expression::Ternary(condition, left, right, _) => {
                self.collect_expression_write_footprint(condition, keys, visited);
                self.collect_expression_write_footprint(left, keys, visited);
                self.collect_expression_write_footprint(right, keys, visited);
            }
            Expression::Concatenation(parts, _) => {
                for (expression, repeat) in parts {
                    self.collect_expression_write_footprint(expression, keys, visited);
                    if let Some(repeat) = repeat {
                        self.collect_expression_write_footprint(repeat, keys, visited);
                    }
                }
            }
            Expression::ArrayLiteral(items, _) => {
                for item in items {
                    match item {
                        ArrayLiteralItem::Value(expression, repeat) => {
                            self.collect_expression_write_footprint(expression, keys, visited);
                            if let Some(repeat) = repeat {
                                self.collect_expression_write_footprint(repeat, keys, visited);
                            }
                        }
                        ArrayLiteralItem::Defaul(expression) => {
                            self.collect_expression_write_footprint(expression, keys, visited);
                        }
                    }
                }
            }
            Expression::StructConstructor(_, fields, _) => {
                for (_, expression) in fields {
                    self.collect_expression_write_footprint(expression, keys, visited);
                }
            }
        }
    }

    fn collect_function_call_write_footprint(
        &mut self,
        call: &FunctionCall,
        keys: &mut HashSet<NodeKey>,
        visited: &mut HashSet<FunctionSummaryKey>,
    ) {
        for actual in call.inputs.values() {
            self.collect_expression_write_footprint(actual, keys, visited);
        }
        for destinations in call.outputs.values() {
            for destination in destinations {
                self.collect_destination_write_footprint(destination, keys, visited);
            }
        }

        let summary_key = FunctionSummaryKey {
            id: call.id,
            index: call.index.clone(),
        };
        if !visited.insert(summary_key) {
            return;
        }
        let Some(statements) = self
            .ctx
            .functions
            .get(&call.id)
            .and_then(|function| function.get_function_for_index(&call.receiver_index))
            .map(|body| body.statements)
        else {
            return;
        };
        self.collect_statement_write_footprint(&statements, keys, visited);
    }

    fn collect_system_call_write_footprint(
        &mut self,
        call: &crate::ir::SystemFunctionCall,
        keys: &mut HashSet<NodeKey>,
        visited: &mut HashSet<FunctionSummaryKey>,
    ) {
        match &call.kind {
            SystemFunctionKind::Bits(input)
            | SystemFunctionKind::Size(input)
            | SystemFunctionKind::Clog2(input)
            | SystemFunctionKind::Onehot(input)
            | SystemFunctionKind::Signed(input)
            | SystemFunctionKind::Unsigned(input) => {
                self.collect_expression_write_footprint(&input.0, keys, visited);
            }
            SystemFunctionKind::Readmemh(input, output) => {
                self.collect_expression_write_footprint(&input.0, keys, visited);
                for destination in &output.0 {
                    self.collect_destination_write_footprint(destination, keys, visited);
                }
            }
            SystemFunctionKind::Display(inputs) | SystemFunctionKind::Write(inputs) => {
                for input in inputs {
                    self.collect_expression_write_footprint(&input.0, keys, visited);
                }
            }
            SystemFunctionKind::Assert { cond, args, .. } => {
                self.collect_expression_write_footprint(&cond.0, keys, visited);
                for input in args {
                    self.collect_expression_write_footprint(&input.0, keys, visited);
                }
            }
            SystemFunctionKind::Finish => {}
        }
    }

    fn opaque_value(&mut self) -> VersionId {
        self.status = self.status.max(AnalysisStatus::Partial);
        self.ssa.definition(Vec::new())
    }

    fn opaque_kill_keys(&mut self, keys: Vec<NodeKey>, weak: bool) {
        self.status = self.status.max(AnalysisStatus::Partial);
        self.bind_opaque_keys(keys, weak);
    }

    fn bind_opaque_keys(&mut self, keys: Vec<NodeKey>, weak: bool) {
        for key in keys {
            let opaque = self.ssa.definition(Vec::new());
            self.bind_destination(key, opaque, weak);
        }
    }

    fn opaque_causal_boundary(&mut self) {
        self.opaque_kill_keys(self.causal_write_keys.clone(), false);
    }

    fn opaque_function_call_boundary(&mut self, call: &FunctionCall) {
        for input in call.inputs.values() {
            self.eval_expr(input);
        }
        let mut keys = self.function_call_write_footprint(call);
        // This helper is used only when the callee effect summary is missing
        // or recursive. Its hidden writes may target any key owned by the
        // current unit, but never a continuous/other-process-only source.
        keys.extend_from_slice(&self.causal_write_keys);
        keys.sort_unstable();
        keys.dedup();
        self.opaque_kill_keys(keys, false);
        for destinations in call.outputs.values() {
            for destination in destinations {
                // Output lvalue selectors still execute, but an unresolved
                // callee supplies no proven value or control dependency.
                self.write_destination(destination, &[], &[]);
            }
        }
    }

    fn read_keys(
        &mut self,
        id: VarId,
        index: &VarIndex,
        select: &VarSelect,
        member_select_domain: Option<MemberSelectDomain>,
    ) -> Vec<NodeKey> {
        if !self.ctx.variables.contains_key(&id) && index.0.is_empty() && select.is_empty() {
            return self.keys_for_id(id);
        }
        let mut keys = Vec::new();
        let index = self.receiver_index(id, index);
        let selection = self.destination_array_selection(id, &index);
        let accesses = var_reads(id, &index, select, member_select_domain, &mut self.ctx);
        if accesses.is_empty() {
            self.status = self.status.max(AnalysisStatus::Partial);
        }
        for (idx, span) in accesses {
            keys.extend(
                self.bit_part
                    .overlapping_access(id, idx, span)
                    .into_iter()
                    .filter(|key| destination_array_projection(key.1, idx, &selection).is_some()),
            );
        }
        keys.sort_unstable();
        keys.dedup();
        keys
    }

    fn write_keys(&mut self, destination: &AssignDestination) -> (Vec<NodeKey>, bool) {
        if !self.ctx.variables.contains_key(&destination.id)
            && destination.index.0.is_empty()
            && destination.select.is_empty()
        {
            return (self.keys_for_id(destination.id), true);
        }
        let mut keys = Vec::new();
        let mut destination = destination.clone();
        destination.index = self.receiver_index(destination.id, &destination.index);
        let accesses = dst_writes(&destination, &mut self.ctx);
        if accesses.is_empty() {
            self.status = self.status.max(AnalysisStatus::Partial);
            keys = if self.module_scope_ids.contains(&destination.id) {
                self.causal_write_keys
                    .iter()
                    .copied()
                    .filter(|key| key.0 == destination.id)
                    .collect()
            } else {
                self.keys_for_id(destination.id)
            };
            keys.sort_unstable();
            keys.dedup();
            return (keys, false);
        }
        for (idx, span) in accesses {
            keys.extend(self.bit_part.overlapping_access(destination.id, idx, span));
        }
        keys.sort_unstable();
        keys.dedup();
        (keys, true)
    }

    fn destination_is_dynamic(&self, destination: &AssignDestination) -> bool {
        let index = self.receiver_index(destination.id, &destination.index);
        !index.is_const() || !destination.select.is_const_with_range()
    }

    fn flattened_affine_index(&mut self, id: VarId, index: &VarIndex) -> Option<AffineIndex> {
        let index = self.receiver_index(id, index);
        let variable = self.ctx.variables.get(&id)?;
        if index.dimension() != variable.r#type.array.dims() {
            return None;
        }
        let flattened = variable.r#type.array.calc_index_expr(&index.0)?;
        affine_index(&flattened, &mut self.ctx)
    }

    fn destination_array_selection(
        &mut self,
        id: VarId,
        index: &VarIndex,
    ) -> DestinationArraySelection {
        let index = self.receiver_index(id, index);
        let last_dynamic = index
            .0
            .iter()
            .rposition(|expression| !expression.comptime().is_const);
        let dynamic = last_dynamic.is_some();
        let Some(shape) = self
            .ctx
            .variables
            .get(&id)
            .map(|variable| variable.r#type.array.clone())
        else {
            return DestinationArraySelection {
                dynamic,
                period: None,
                phase: 0,
                extent: None,
                static_filters: Vec::new(),
            };
        };
        let extent = (index.dimension() <= shape.dims())
            .then(|| {
                shape[index.dimension()..]
                    .iter()
                    .try_fold(1usize, |extent, dimension| {
                        extent.checked_mul((*dimension)?)
                    })
            })
            .flatten();
        let periodic = last_dynamic.and_then(|last_dynamic| {
            let extent = extent?;
            let period = shape[last_dynamic + 1..]
                .iter()
                .try_fold(1usize, |period, dimension| {
                    period.checked_mul((*dimension)?)
                })?;
            let mut phase = 0usize;
            for (position, expression) in index.0.iter().enumerate().skip(last_dynamic + 1) {
                let dimension = shape.get(position).copied().flatten()?;
                let value = expression.eval_value(&mut self.ctx)?.to_usize()?;
                if value >= dimension {
                    return None;
                }
                phase = phase.checked_mul(dimension)?.checked_add(value)?;
            }
            phase = phase.checked_mul(extent)?;
            Some((period, phase))
        });
        let static_filters = index
            .0
            .iter()
            .enumerate()
            .filter_map(|(position, expression)| {
                if !expression.comptime().is_const {
                    return None;
                }
                let dimension = shape.get(position).copied().flatten()?;
                // A size-one axis constrains no storage coordinate. Skipping
                // it also bounds meaningful periodic filters by the number of
                // bits in the flattened array size, rather than by an
                // arbitrarily long list of singleton dimensions.
                if dimension == 1 {
                    return None;
                }
                let value = expression.eval_value(&mut self.ctx)?.to_usize()?;
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
        DestinationArraySelection {
            dynamic,
            period: periodic.map(|(period, _)| period),
            phase: periodic.map_or(0, |(_, phase)| phase),
            extent,
            static_filters,
        }
    }

    fn aggregate_destination_controls(
        &mut self,
        mut controls: Vec<VersionId>,
    ) -> Option<VersionId> {
        controls.sort_unstable();
        controls.dedup();
        match controls.len() {
            0 => None,
            1 => controls.first().copied(),
            _ => Some(self.ssa.definition(controls)),
        }
    }

    fn bind_destination(&mut self, key: NodeKey, version: VersionId, dynamic: bool) {
        if dynamic {
            let key = self.ssa_key(key);
            self.ssa.weak_bind(key, version);
        } else {
            self.bind_key(key, version);
        }
        self.written.insert(key);
    }

    fn receiver_index(&self, _id: VarId, index: &VarIndex) -> VarIndex {
        index.clone()
    }

    fn read_variable(
        &mut self,
        id: VarId,
        index: &VarIndex,
        select: &VarSelect,
        member_select_domain: Option<MemberSelectDomain>,
    ) -> Vec<VersionId> {
        self.read_keys(id, index, select, member_select_domain)
            .into_iter()
            .map(|key| self.read_key(key))
            .collect()
    }

    fn write_destination(
        &mut self,
        destination: &AssignDestination,
        sources: &[VersionId],
        controls: &[VersionId],
    ) {
        let mut dependencies = sources.to_vec();
        dependencies.extend_from_slice(controls);
        for expression in destination
            .index
            .0
            .iter()
            .chain(destination.select.0.iter())
        {
            dependencies.extend(self.eval_expr(expression));
        }
        if let Some((_, expression)) = &destination.select.1 {
            dependencies.extend(self.eval_expr(expression));
        }
        let (keys, resolved) = self.write_keys(destination);
        let dynamic = !resolved || self.destination_is_dynamic(destination);
        let version = if resolved {
            self.ssa
                .definition_guarded(dependencies, &self.path_condition)
        } else {
            self.ssa.definition(Vec::new())
        };
        for key in keys {
            self.bind_destination(key, version, dynamic);
        }
    }

    fn destination_width(&mut self, destination: &AssignDestination) -> Option<usize> {
        let variable = self.ctx.variables.get(&destination.id)?.clone();
        let (high, low) = destination
            .select
            .eval_value(&mut self.ctx, &variable.r#type, false)?;
        high.checked_sub(low)?.checked_add(1)
    }

    fn key_span(&self, key: NodeKey) -> Option<PackedSpan> {
        self.bit_part.ranges_of((key.0, key.1)).get(key.2).copied()
    }

    fn snapshot_assignment_destination(
        &mut self,
        destination: &AssignDestination,
        expression: &Expression,
        expression_offset: usize,
        expression_context_width: usize,
    ) -> Vec<DestinationSnapshot> {
        let variable = self.ctx.variables.get(&destination.id).cloned();
        let selected = if destination.select.is_const_with_range() {
            variable.as_ref().and_then(|variable| {
                destination
                    .select
                    .eval_value(&mut self.ctx, &variable.r#type, false)
            })
        } else {
            None
        };
        let destination_array = dst_writes(destination, &mut self.ctx)
            .into_iter()
            .map(|(array, _)| array)
            .next();
        let destination_index = self.flattened_affine_index(destination.id, &destination.index);
        let destination_array_selection =
            self.destination_array_selection(destination.id, &destination.index);
        let (keys, resolved) = self.write_keys(destination);
        let whole_sources = if resolved && (destination_array.is_none() || selected.is_none()) {
            Some(self.eval_speculatively(|this| this.eval_expr(expression)))
        } else {
            None
        };
        let mut snapshots = Vec::with_capacity(keys.len());
        for key in keys {
            let mut destination_offset = None;
            let array = if !resolved {
                None
            } else if let Some(destination_array) = destination_array {
                let Some(array) = destination_array_projection(
                    key.1,
                    destination_array,
                    &destination_array_selection,
                ) else {
                    // The partition key lies in a statically impossible gap
                    // between periodic dynamic-index candidates.
                    continue;
                };
                Some(array)
            } else {
                None
            };
            let mut sources = if !resolved {
                ExpressionSources::default()
            } else if let (Some(array), Some((_, low)), Some(key_span)) =
                (array, selected, self.key_span(key))
            {
                if let Some(packed) = key_span.translated(low, expression_offset) {
                    destination_offset = array.position_offset(low, expression_offset);
                    self.eval_speculatively(|this| {
                        this.eval_expr_requested_in(
                            expression,
                            array.source,
                            packed,
                            expression_context_width,
                            &ProjectionContext {
                                destination_index: destination_index.clone(),
                                destination_array: Some(array.destination),
                                destination_array_offset: array.array_offset,
                            },
                        )
                    })
                } else {
                    ExpressionSources::default()
                }
            } else {
                ExpressionSources::whole(whole_sources.clone().unwrap_or_default())
            };
            for (_, relation) in &mut sources.sources {
                *relation = destination_offset
                    .map(|base| relation.compose(base))
                    .unwrap_or_else(PositionRelation::whole);
            }
            snapshots.push(DestinationSnapshot {
                key,
                sources,
                opaque: !resolved,
            });
        }
        snapshots
    }

    fn write_assignment_destination(
        &mut self,
        destination: &AssignDestination,
        snapshots: Vec<DestinationSnapshot>,
        controls: &[VersionId],
    ) {
        let destination_dynamic = self.destination_is_dynamic(destination);
        let mut destination_controls = controls.to_vec();
        // Destination coordinates are one syntactic evaluation, independent
        // of how many sparse partition keys may be written. Freeze their
        // effects/dependencies once instead of re-running a selector per key.
        for selector in destination
            .index
            .0
            .iter()
            .chain(destination.select.0.iter())
        {
            destination_controls.extend(self.eval_expr(selector));
        }
        if let Some((_, selector)) = &destination.select.1 {
            destination_controls.extend(self.eval_expr(selector));
        }
        let destination_control = self.aggregate_destination_controls(destination_controls);
        for DestinationSnapshot {
            key,
            mut sources,
            opaque,
        } in snapshots
        {
            let whole = if opaque {
                Vec::new()
            } else {
                destination_control.into_iter().collect()
            };
            sources.extend_whole(whole);
            sources.normalize();
            let version = if opaque {
                self.ssa.definition(Vec::new())
            } else {
                self.ssa
                    .related_definition_guarded(sources.sources, &self.path_condition)
            };
            self.bind_destination(key, version, opaque || destination_dynamic);
        }
    }

    /// Evaluate an expression once for its procedural effects, then obtain
    /// positional views of that value from the same pre-evaluation SSA state.
    /// Versions survive rollback, so cached call results and projected reads
    /// remain valid when the captured effects are committed afterwards.
    fn snapshot_expression<T>(
        &mut self,
        expression: &Expression,
        snapshot: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let owns_cache = !matches!(self.call_caches.last(), Some(Some(_)));
        if owns_cache {
            self.call_caches.push(Some(EvaluationCache::default()));
        }

        let checkpoint = self.ssa.checkpoint();
        let parent_effects_only = self.effects_only;
        self.effects_only = true;
        self.eval_expr(expression);
        let effects = self.ssa.capture_and_rollback(checkpoint);
        self.effects_only = false;
        let parent_projection_only = self.projection_only;
        self.projection_only = true;
        let value = snapshot(self);
        self.projection_only = parent_projection_only;
        self.ssa.merge([&effects]);
        self.effects_only = parent_effects_only;

        if owns_cache {
            self.call_caches.pop();
        }
        value
    }

    fn eval_speculatively<T>(&mut self, eval: impl FnOnce(&mut Self) -> T) -> T {
        let checkpoint = self.ssa.checkpoint();
        let value = eval(self);
        self.ssa.capture_and_rollback(checkpoint);
        value
    }

    fn eval_function_body(
        &mut self,
        statements: &[Statement],
        return_id: Option<VarId>,
        controls: &[VersionId],
    ) {
        let caller_condition = self.path_condition.clone();
        let checkpoint = self.ssa.checkpoint();
        let revision = self.ssa.begin_state_revision(checkpoint);
        self.function_flows.push(FunctionFlow {
            return_id,
            revision,
        });
        let flow = self.eval_block(statements, controls);
        let function = self
            .function_flows
            .pop()
            .expect("function flow was pushed above");
        if flow.flow != ProcedureFlow::Return {
            self.ssa.record_state_revision_exit(function.revision);
        }
        let exits = self.ssa.finish_state_revision(function.revision);
        let _ = self.ssa.capture_and_rollback(checkpoint);
        self.ssa.merge([&exits]);
        self.path_condition = caller_condition;
    }

    fn record_return(&mut self) {
        self.record_return_marker(self.path_condition.clone());
    }

    fn record_return_marker(&mut self, condition: PathCondition) {
        if let Some(index) = self
            .loop_flows
            .iter()
            .rposition(|r#loop| r#loop.returns.is_some())
        {
            let returns = self.loop_flows[index]
                .returns
                .as_mut()
                .expect("selected a runtime-loop return capture");
            self.ssa.record_state_revision_exit(returns.revision);
            returns.conditions.push(condition);
            return;
        }
        let Some(revision) = self.function_flows.last().map(|function| function.revision) else {
            return;
        };
        self.ssa.record_state_revision_exit(revision);
    }

    fn record_deferred_return(&mut self, state: BranchState<SsaKey>, condition: PathCondition) {
        let checkpoint = self.ssa.checkpoint();
        self.ssa.merge([&state]);
        self.record_return_marker(condition);
        let _ = self.ssa.capture_and_rollback(checkpoint);
    }

    fn record_break(&mut self) {
        let Some(r#loop) = self.loop_flows.last() else {
            return;
        };
        let state = FlowState {
            state: self.ssa.snapshot_since(r#loop.checkpoint),
            condition: self.path_condition.clone(),
        };
        self.loop_flows
            .last_mut()
            .expect("checked above")
            .breaks
            .push(state);
    }

    fn next_branch_id(&mut self, arms: usize) -> BranchId {
        let branch = BranchId::new(self.branch_namespace, self.next_branch, arms);
        self.next_branch += 1;
        branch
    }

    fn flow_result_from_tree(&mut self, tree: FlowTree) -> FlowResult {
        let mut controls = Vec::new();
        self.flow_store
            .collect_continuation_controls(tree, &mut controls);
        controls.sort_unstable();
        controls.dedup();
        let continuation_controls = controls
            .into_iter()
            .map(|(sources, condition)| self.ssa.definition_guarded(sources, &condition))
            .collect();
        FlowResult {
            flow: self.flow_store.aggregate(tree),
            continuation_controls,
            tree,
        }
    }

    fn simple_flow_result(&mut self, flow: ProcedureFlow) -> FlowResult {
        FlowResult {
            flow,
            continuation_controls: Vec::new(),
            tree: self.flow_store.outcome(flow),
        }
    }

    fn prepare_top_expression(&mut self, expression: &Expression) {
        // Instance actuals are immutable IR objects for the complete module
        // graph build. Their addresses therefore give all region analyses of
        // one actual a shared namespace while keeping cloned actuals distinct.
        let namespace = std::ptr::from_ref(expression).addr();
        let mut layout = ExpressionBranchLayout::default();
        collect_expression_branch_layout(expression, &mut layout);
        self.branch_namespace = namespace;
        self.next_branch = layout.conditionals.len();
        self.top_expression_branches.clear();
        self.top_expression_branches.extend(
            layout
                .conditionals
                .into_iter()
                .enumerate()
                .map(|(local, expression)| (expression, BranchId::expression(namespace, local, 2))),
        );
        self.top_expression_calls = layout
            .calls
            .into_iter()
            .enumerate()
            .map(|(ordinal, call)| (call, ordinal))
            .collect();
    }

    fn expression_branch_id(&mut self, expression: &Expression) -> BranchId {
        let key = std::ptr::from_ref(expression);
        if let Some(branch) = self.top_expression_branches.get(&key) {
            return *branch;
        }
        if let Some(branch) = self
            .call_caches
            .last()
            .and_then(Option::as_ref)
            .and_then(|cache| cache.expression_branches.get(&key))
        {
            return *branch;
        }
        let branch = self.next_branch_id(2);
        if let Some(Some(cache)) = self.call_caches.last_mut() {
            cache.expression_branches.insert(key, branch);
        }
        branch
    }

    fn merge_flow_states(&mut self, states: &[FlowState]) {
        self.ssa.merge(states.iter().map(|state| &state.state));
        self.path_condition =
            PathCondition::disjoin_all(states.iter().map(|state| &state.condition));
    }

    fn is_return_assignment(&self, destinations: &[AssignDestination]) -> bool {
        self.function_flows
            .last()
            .and_then(|function| function.return_id)
            .is_some_and(|return_id| {
                destinations
                    .iter()
                    .any(|destination| destination.id == return_id)
            })
    }

    fn eval_block(&mut self, statements: &[Statement], controls: &[VersionId]) -> FlowResult {
        let base_controls = controls.to_vec();
        let mut active_controls = base_controls.clone();
        let mut continuation_control = None;
        let mut statement_trees = Vec::with_capacity(statements.len());
        for statement in statements {
            let result = self.eval_statement(statement, &active_controls);
            statement_trees.push(result.tree);
            if !result.continuation_controls.is_empty() {
                let mut sources = result.continuation_controls;
                if let Some(previous) = continuation_control {
                    sources.push(previous);
                }
                sources.sort_unstable();
                sources.dedup();
                let control = self.ssa.definition(sources);
                continuation_control = Some(control);
                active_controls.clone_from(&base_controls);
                active_controls.push(control);
            }
            if !self
                .flow_store
                .contains(result.tree, ProcedureFlow::Continue)
            {
                break;
            }
        }
        let mut tree = self.flow_store.outcome(ProcedureFlow::Continue);
        for statement in statement_trees.into_iter().rev() {
            tree = self.flow_store.bind(statement, tree);
        }
        FlowResult {
            flow: self.flow_store.aggregate(tree),
            continuation_controls: continuation_control.into_iter().collect(),
            tree,
        }
    }

    fn eval_statement(&mut self, statement: &Statement, controls: &[VersionId]) -> FlowResult {
        match statement {
            Statement::Assign(assign) => {
                self.call_caches.push(Some(EvaluationCache::default()));
                let widths: Vec<_> = assign
                    .dst
                    .iter()
                    .map(|destination| self.destination_width(destination))
                    .collect();
                if widths.iter().all(Option::is_some) {
                    let total_width = widths.iter().flatten().sum();
                    let snapshots = self.snapshot_expression(&assign.expr, |this| {
                        let mut offset = total_width;
                        assign
                            .dst
                            .iter()
                            .zip(&widths)
                            .map(|(destination, width)| {
                                let width = width.expect("checked above");
                                offset -= width;
                                this.snapshot_assignment_destination(
                                    destination,
                                    &assign.expr,
                                    offset,
                                    total_width,
                                )
                            })
                            .collect::<Vec<_>>()
                    });
                    for (destination, snapshots) in assign.dst.iter().zip(snapshots) {
                        self.write_assignment_destination(destination, snapshots, controls);
                    }
                } else {
                    let sources = self.eval_expr(&assign.expr);
                    for destination in &assign.dst {
                        self.write_destination(destination, &sources, controls);
                    }
                }
                self.call_caches.pop();
                if self.is_return_assignment(&assign.dst) {
                    self.record_return();
                    self.simple_flow_result(ProcedureFlow::Return)
                } else {
                    self.simple_flow_result(ProcedureFlow::Continue)
                }
            }
            Statement::If(statement) => self.eval_if(statement, controls),
            Statement::Case(statement) => self.eval_case(statement, controls),
            Statement::For(statement) => self.eval_for(statement, controls),
            Statement::FunctionCall(call) => {
                self.eval_call(call, controls);
                self.simple_flow_result(ProcedureFlow::Continue)
            }
            Statement::SystemFunctionCall(call) => {
                self.eval_system_call(call, controls, false);
                self.simple_flow_result(ProcedureFlow::Continue)
            }
            Statement::Break => {
                self.record_break();
                self.simple_flow_result(ProcedureFlow::Break)
            }
            Statement::IfReset(_) | Statement::TbMethodCall(_) | Statement::Null => {
                self.simple_flow_result(ProcedureFlow::Continue)
            }
            Statement::Unsupported(_) => {
                self.opaque_causal_boundary();
                self.simple_flow_result(ProcedureFlow::Continue)
            }
        }
    }

    fn merge_branches(
        &mut self,
        branches: Vec<(FlowResult, BranchState<SsaKey>, PathCondition)>,
        predicate: FlowPredicate,
        parent_condition: &PathCondition,
    ) -> FlowResult {
        let mut continuation = Vec::new();
        let mut continuation_conditions = Vec::new();
        let mut continuation_controls = Vec::new();
        let continuation_shape = branches
            .first()
            .map(|(result, _, _)| self.flow_store.data(result.tree).continuation);
        let decision_matters = continuation_shape.is_some_and(|first| {
            branches[1..]
                .iter()
                .any(|(result, _, _)| self.flow_store.data(result.tree).continuation != first)
        });
        let mut arms = Vec::with_capacity(branches.len());
        for (result, state, condition) in branches {
            let continues = self
                .flow_store
                .contains(result.tree, ProcedureFlow::Continue);
            if continues {
                continuation.push(state);
                let mut controls = result.continuation_controls;
                if decision_matters {
                    controls.extend_from_slice(&predicate.controls);
                }
                controls.sort_unstable();
                controls.dedup();
                if !controls.is_empty() {
                    // `controls` already includes the continuation token from
                    // the enclosing block. Guard this new token only by the
                    // choice introduced at this decision; retaining the full
                    // execution prefix in every sequential token would
                    // duplicate an N-deep path N times.
                    let local_condition = condition.relative_to(parent_condition);
                    continuation_controls
                        .push(self.ssa.definition_guarded(controls, &local_condition));
                }
                continuation_conditions.push(condition.clone());
            }
            arms.push(FlowArm {
                condition,
                tree: result.tree,
            });
        }
        let tree = self.flow_store.decision(predicate, arms);
        self.ssa.merge(&continuation);
        if self.flow_store.contains(tree, ProcedureFlow::Continue) {
            self.path_condition = PathCondition::disjoin_all(&continuation_conditions);
            FlowResult {
                flow: self.flow_store.aggregate(tree),
                continuation_controls,
                tree,
            }
        } else {
            FlowResult {
                flow: self.flow_store.aggregate(tree),
                continuation_controls: Vec::new(),
                tree,
            }
        }
    }

    fn eval_if(&mut self, statement: &IfStatement, controls: &[VersionId]) -> FlowResult {
        let condition = self.eval_expr(&statement.cond);
        let predicate = FlowPredicate::expression(&statement.cond, &condition);
        let mut nested_controls = controls.to_vec();
        nested_controls.extend_from_slice(&condition);
        match self.constant_truth(&statement.cond) {
            Some(true) => return self.eval_block(&statement.true_side, &nested_controls),
            Some(false) => return self.eval_block(&statement.false_side, &nested_controls),
            None => {}
        }

        let branch = self.next_branch_id(2);
        let parent_condition = self.path_condition.clone();
        self.path_condition = parent_condition.with_choice(branch, 0);
        let checkpoint = self.ssa.checkpoint();
        let true_flow = self.eval_block(&statement.true_side, &nested_controls);
        let true_state = self.ssa.capture_and_rollback(checkpoint);
        let true_condition = self.path_condition.clone();

        self.path_condition = parent_condition.with_choice(branch, 1);
        let checkpoint = self.ssa.checkpoint();
        let false_flow = self.eval_block(&statement.false_side, &nested_controls);
        let false_state = self.ssa.capture_and_rollback(checkpoint);
        let false_condition = self.path_condition.clone();

        self.path_condition = parent_condition.clone();
        self.merge_branches(
            vec![
                (true_flow, true_state, true_condition),
                (false_flow, false_state, false_condition),
            ],
            predicate,
            &parent_condition,
        )
    }

    fn eval_case(&mut self, statement: &CaseStatement, controls: &[VersionId]) -> FlowResult {
        let mut condition = self.eval_expr(&statement.case_target);
        for arm in &statement.arms {
            for pattern in &arm.patterns {
                match pattern {
                    crate::ir::CasePattern::Eq(expression) => {
                        condition.extend(self.eval_expr(expression));
                    }
                    crate::ir::CasePattern::Range { lo, hi, .. } => {
                        condition.extend(self.eval_expr(lo));
                        condition.extend(self.eval_expr(hi));
                    }
                }
            }
        }
        let predicate = FlowPredicate::opaque(std::ptr::from_ref(statement).addr(), &condition);
        let mut nested_controls = controls.to_vec();
        nested_controls.extend_from_slice(&condition);

        if let Some(target) = statement.case_target.eval_value(&mut self.ctx)
            && target.to_usize().is_some()
        {
            let mut possible = Vec::new();
            let mut has_definite_match = false;
            for (index, arm) in statement.arms.iter().enumerate() {
                let mut uncertain = false;
                let mut matched = false;
                for pattern in &arm.patterns {
                    match pattern.matches(&target, &mut self.ctx) {
                        Some(true) => {
                            matched = true;
                            break;
                        }
                        Some(false) => {}
                        None => uncertain = true,
                    }
                }
                if matched {
                    possible.push(index);
                    has_definite_match = true;
                    break;
                }
                if uncertain {
                    possible.push(index);
                }
            }

            if possible.is_empty() {
                return self.eval_block(&statement.default, &nested_controls);
            }
            if possible.len() == 1 && has_definite_match {
                return self.eval_block(&statement.arms[possible[0]].body, &nested_controls);
            }

            let branch = self.next_branch_id(statement.arms.len() + 1);
            let parent_condition = self.path_condition.clone();
            let mut states = Vec::with_capacity(possible.len() + usize::from(!has_definite_match));
            for index in possible {
                self.path_condition = parent_condition.with_choice(branch, index);
                let checkpoint = self.ssa.checkpoint();
                let flow = self.eval_block(&statement.arms[index].body, &nested_controls);
                let state = self.ssa.capture_and_rollback(checkpoint);
                states.push((flow, state, self.path_condition.clone()));
            }
            if !has_definite_match {
                self.path_condition = parent_condition.with_choice(branch, statement.arms.len());
                let checkpoint = self.ssa.checkpoint();
                let flow = self.eval_block(&statement.default, &nested_controls);
                let state = self.ssa.capture_and_rollback(checkpoint);
                states.push((flow, state, self.path_condition.clone()));
            }
            self.path_condition = parent_condition.clone();
            return self.merge_branches(states, predicate, &parent_condition);
        }

        let (reachable_arms, default_reachable) = self
            .ordered_case_reachability(statement)
            .unwrap_or_else(|| ((0..statement.arms.len()).collect(), true));
        let branch = self.next_branch_id(statement.arms.len() + 1);
        let parent_condition = self.path_condition.clone();
        let mut states = Vec::with_capacity(reachable_arms.len() + usize::from(default_reachable));
        for index in reachable_arms {
            self.path_condition = parent_condition.with_choice(branch, index);
            let checkpoint = self.ssa.checkpoint();
            let flow = self.eval_block(&statement.arms[index].body, &nested_controls);
            let state = self.ssa.capture_and_rollback(checkpoint);
            states.push((flow, state, self.path_condition.clone()));
        }
        if default_reachable {
            self.path_condition = parent_condition.with_choice(branch, statement.arms.len());
            let checkpoint = self.ssa.checkpoint();
            let flow = self.eval_block(&statement.default, &nested_controls);
            let state = self.ssa.capture_and_rollback(checkpoint);
            states.push((flow, state, self.path_condition.clone()));
        }
        self.path_condition = parent_condition.clone();
        self.merge_branches(states, predicate, &parent_condition)
    }

    /// Return the arms that can win an ordered `case`, plus whether its
    /// default remains reachable. Keep the general path conservative: this
    /// finite interval model applies only to a scalar, 2-state selector and
    /// constant, non-X/Z bounds. Signed selectors accept only equal-width
    /// equality patterns, whose raw bit-pattern comparison is unambiguous;
    /// signed ranges and context-sized equalities keep the general fallback.
    fn ordered_case_reachability(
        &mut self,
        statement: &CaseStatement,
    ) -> Option<(Vec<usize>, bool)> {
        let target_type = &statement.case_target.comptime().r#type;
        if !matches!(target_type.kind, TypeKind::Bit)
            || !target_type.array.is_empty()
            || !target_type.is_2state()
        {
            return None;
        }
        let width = target_type.total_width()?;
        if width == 0 || width > usize::BITS as usize {
            return None;
        }
        let domain_high = if width == usize::BITS as usize {
            usize::MAX
        } else {
            (1usize << width) - 1
        };

        let mut covered = BTreeMap::<usize, usize>::new();
        let mut reachable = Vec::new();
        for (index, arm) in statement.arms.iter().enumerate() {
            let mut intervals = Vec::with_capacity(arm.patterns.len());
            for pattern in &arm.patterns {
                if let Some(interval) =
                    self.case_pattern_interval(pattern, domain_high, width, target_type.signed)?
                {
                    intervals.push(interval);
                }
            }
            if intervals
                .iter()
                .any(|&interval| !case_interval_is_covered(&covered, interval))
            {
                reachable.push(index);
            }
            for interval in intervals {
                insert_case_interval(&mut covered, interval);
            }
        }

        let default_reachable = !case_interval_is_covered(&covered, (0, domain_high));
        Some((reachable, default_reachable))
    }

    fn case_pattern_interval(
        &mut self,
        pattern: &crate::ir::CasePattern,
        domain_high: usize,
        target_width: usize,
        target_signed: bool,
    ) -> Option<Option<(usize, usize)>> {
        if target_signed {
            let crate::ir::CasePattern::Eq(expression) = pattern else {
                return None;
            };
            let value = expression.eval_value(&mut self.ctx)?;
            if value.is_xz() || value.width() == 0 || value.width() != target_width {
                return None;
            }
            let value = value.to_usize()?;
            return Some(Some((value, value)));
        }

        let constant = |this: &mut Self, expression: &Expression| {
            let value = expression.eval_value(&mut this.ctx)?;
            // Width-zero values are the unbased all-bit literals (`'0`,
            // `'1`, ...). Their concrete value comes from the selector width,
            // so the context-free payload is not an interval endpoint.
            if value.is_xz() || value.width() == 0 {
                return None;
            }
            if value.signed()
                && u64::try_from(value.width() - 1)
                    .ok()
                    .is_some_and(|sign| value.payload().bit(sign))
            {
                return None;
            }
            value.to_usize()
        };

        match pattern {
            crate::ir::CasePattern::Eq(expression) => {
                let value = constant(self, expression)?;
                Some((value <= domain_high).then_some((value, value)))
            }
            crate::ir::CasePattern::Range { lo, hi, inclusive } => {
                let lo = constant(self, lo)?;
                let hi = constant(self, hi)?;
                let Some(hi) = (if *inclusive {
                    Some(hi)
                } else {
                    hi.checked_sub(1)
                }) else {
                    return Some(None);
                };
                if lo > hi || lo > domain_high {
                    return Some(None);
                }
                Some(Some((lo, hi.min(domain_high))))
            }
        }
    }

    fn eval_for(&mut self, statement: &ForStatement, controls: &[VersionId]) -> FlowResult {
        let (range_controls, bound_controls) =
            self.eval_for_range_controls(&statement.range, controls);
        if self.for_range_is_proven_empty(&statement.range) {
            return self.simple_flow_result(ProcedureFlow::Continue);
        }

        if let Some(iterations) = statement.range.eval_iter(&mut self.ctx) {
            self.eval_known_for_iterations(statement, &range_controls, iterations)
        } else if statement.range.is_over_size_limit(&mut self.ctx) {
            // Preserve exact analysis after the resource boundary. The body
            // may change only its own transitive write footprint; an unknown
            // result replaces those definitions without inventing data edges.
            let mut keys = self.statement_write_footprint(&statement.body);
            if statements_have_unsupported(&statement.body) {
                keys.extend_from_slice(&self.causal_write_keys);
                keys.sort_unstable();
                keys.dedup();
            }
            let may_skip = !self.for_range_is_proven_nonempty(&statement.range);
            self.opaque_kill_keys(keys, may_skip);
            self.simple_flow_result(ProcedureFlow::Continue)
        } else {
            self.eval_runtime_for(statement, &range_controls, &bound_controls)
        }
    }

    fn eval_for_range_controls(
        &mut self,
        range: &ForRange,
        controls: &[VersionId],
    ) -> (Vec<VersionId>, Vec<VersionId>) {
        let mut bound_controls = Vec::new();
        let (start, end, _) = for_range_bounds(range);
        for bound in [start, end] {
            if let ForBound::Expression(expression) = bound {
                bound_controls.extend(self.eval_expr(expression));
            }
        }
        bound_controls.sort_unstable();
        bound_controls.dedup();
        let mut range_controls = controls.to_vec();
        range_controls.extend_from_slice(&bound_controls);
        range_controls.sort_unstable();
        range_controls.dedup();
        (range_controls, bound_controls)
    }

    fn for_range_is_proven_empty(&mut self, range: &ForRange) -> bool {
        let (start, end, inclusive) = for_range_bounds(range);
        !inclusive
            && affine_bound(start, &mut self.ctx)
                .zip(affine_bound(end, &mut self.ctx))
                .is_some_and(|(start, end)| start == end)
    }

    fn for_range_is_proven_nonempty(&mut self, range: &ForRange) -> bool {
        let (start, end, inclusive) = for_range_bounds(range);
        start
            .eval_value(&mut self.ctx)
            .zip(end.eval_value(&mut self.ctx))
            .is_some_and(
                |(start, end)| {
                    if inclusive { start <= end } else { start < end }
                },
            )
    }

    fn set_known_iterator_value(&mut self, statement: &ForStatement, value: usize) {
        let Some(variable) = self.ctx.variables.get_mut(&statement.var_id) else {
            return;
        };
        let Some(width) = statement.var_type.total_width() else {
            return;
        };
        variable.set_value(
            &[],
            Value::new(value as u64, width, statement.var_type.signed),
            None,
        );
    }

    fn forget_runtime_iterator_value(&mut self, iterator: VarId) {
        if let Some(variable) = self.ctx.variables.get_mut(&iterator) {
            // Conversion may leave the range's initial value in the shared
            // compile-time store. It is not a constant in a runtime loop and
            // must not prune iterator-dependent branches.
            variable.value.clear();
        }
    }

    fn eval_known_for_iterations(
        &mut self,
        statement: &ForStatement,
        range_controls: &[VersionId],
        iterations: Vec<usize>,
    ) -> FlowResult {
        let parent_condition = self.path_condition.clone();
        let checkpoint = self.ssa.checkpoint();
        self.loop_flows.push(LoopFlow {
            checkpoint,
            breaks: Vec::new(),
            returns: None,
        });
        let mut iteration_trees = Vec::with_capacity(iterations.len());
        let mut iteration_controls = range_controls.to_vec();
        for value in iterations {
            self.set_known_iterator_value(statement, value);
            let result = self.eval_block(&statement.body, &iteration_controls);
            iteration_trees.push(result.tree);
            for control in result.continuation_controls {
                if !iteration_controls.contains(&control) {
                    iteration_controls.push(control);
                }
            }
            if !self
                .flow_store
                .contains(result.tree, ProcedureFlow::Continue)
            {
                break;
            }
        }
        let mut tree = self.flow_store.outcome(ProcedureFlow::Continue);
        for iteration in iteration_trees.into_iter().rev() {
            tree = self.flow_store.bind(iteration, tree);
        }
        let mut loop_flow = self.loop_flows.pop().expect("loop flow was pushed above");
        let fallthrough = self.ssa.capture_and_rollback(checkpoint);
        if self.flow_store.contains(tree, ProcedureFlow::Continue) {
            loop_flow.breaks.push(FlowState {
                state: fallthrough,
                condition: self.path_condition.clone(),
            });
        }
        let tree = self.flow_store.leave_loop(tree);
        if !self.flow_store.contains(tree, ProcedureFlow::Continue) {
            self.path_condition = parent_condition;
            return self.flow_result_from_tree(tree);
        }
        self.merge_flow_states(&loop_flow.breaks);
        self.flow_result_from_tree(tree)
    }

    fn eval_runtime_for(
        &mut self,
        statement: &ForStatement,
        range_controls: &[VersionId],
        bound_controls: &[VersionId],
    ) -> FlowResult {
        // A runtime iterator is not part of a static prefix. Consequently
        // accesses such as x[i], x[i + 1], and x[j] all may address the same
        // LSP region. Evaluate the body once without binding the iterator so
        // the ordinary dynamic-access rules conservatively retain that alias.
        self.forget_runtime_iterator_value(statement.var_id);
        let parent_condition = self.path_condition.clone();
        let may_execute_zero_times = for_range_has_dynamic_bounds(&statement.range);
        let execution_branch = may_execute_zero_times.then(|| self.next_branch_id(2));
        if let Some(branch) = execution_branch {
            self.path_condition = parent_condition.with_choice(branch, 1);
        }
        let checkpoint = self.ssa.checkpoint();
        let mut body = self.capture_runtime_loop_body(statement, range_controls, checkpoint);
        self.path_condition = parent_condition.clone();
        let transfer = self
            .ssa
            .prepare_repeated_transfer(&body.continuing, checkpoint);
        self.lift_runtime_loop_exits(&transfer, &mut body);
        let normal = self.capture_runtime_normal_exit(
            &transfer,
            self.flow_store
                .contains(body.flow.tree, ProcedureFlow::Continue),
            may_execute_zero_times,
        );
        self.ssa.merge(
            body.breaks
                .iter()
                .map(|state| &state.state)
                .chain(normal.iter()),
        );
        let mut tree = self.flow_store.leave_loop(body.flow.tree);
        if may_execute_zero_times {
            let branch = execution_branch.expect("created for a possibly empty runtime loop");
            let zero = self.flow_store.outcome(ProcedureFlow::Continue);
            tree = self.flow_store.decision(
                FlowPredicate::opaque(std::ptr::from_ref(statement).addr(), bound_controls),
                vec![
                    FlowArm {
                        condition: parent_condition.with_choice(branch, 0),
                        tree: zero,
                    },
                    FlowArm {
                        condition: parent_condition.with_choice(branch, 1),
                        tree,
                    },
                ],
            );
        }
        self.flow_result_from_tree(tree)
    }

    fn capture_runtime_loop_body(
        &mut self,
        statement: &ForStatement,
        range_controls: &[VersionId],
        checkpoint: Checkpoint,
    ) -> RuntimeLoopBody {
        let return_revision =
            (!self.function_flows.is_empty()).then(|| self.ssa.begin_state_revision(checkpoint));
        self.loop_flows.push(LoopFlow {
            checkpoint,
            breaks: Vec::new(),
            returns: return_revision.map(|revision| RuntimeReturnCapture {
                revision,
                conditions: Vec::new(),
            }),
        });
        let flow = self.eval_block(&statement.body, range_controls);
        let loop_flow = self.loop_flows.pop().expect("loop flow was pushed above");
        let return_state = return_revision
            .map(|revision| self.ssa.finish_optional_state_revision(revision))
            .unwrap_or_else(BranchState::empty);
        let body_state = self.ssa.capture_and_rollback(checkpoint);
        let continuing = if self.flow_store.contains(flow.tree, ProcedureFlow::Continue) {
            body_state
        } else {
            BranchState::empty()
        };
        let returned = loop_flow.returns.and_then(|returns| {
            (!returns.conditions.is_empty()).then(|| FlowState {
                state: return_state,
                condition: PathCondition::disjoin_all(&returns.conditions),
            })
        });
        RuntimeLoopBody {
            flow,
            continuing,
            breaks: loop_flow.breaks,
            returned,
        }
    }

    fn lift_runtime_loop_exits(
        &mut self,
        transfer: &RepeatedTransfer<SsaKey>,
        body: &mut RuntimeLoopBody,
    ) {
        self.ssa.lift_repeated_exit_states(
            transfer,
            body.breaks
                .iter_mut()
                .chain(body.returned.iter_mut())
                .map(|state| (&mut state.state, &state.condition)),
        );
        if let Some(returned) = body.returned.take() {
            self.record_deferred_return(returned.state, returned.condition);
        }
    }

    fn capture_runtime_normal_exit(
        &mut self,
        transfer: &RepeatedTransfer<SsaKey>,
        continues: bool,
        may_execute_zero_times: bool,
    ) -> Option<BranchState<SsaKey>> {
        if continues {
            let checkpoint = self.ssa.checkpoint();
            self.ssa
                .apply_repeated_transfer(transfer, may_execute_zero_times);
            Some(self.ssa.capture_and_rollback(checkpoint))
        } else {
            may_execute_zero_times.then(BranchState::empty)
        }
    }

    fn eval_expr_requested(
        &mut self,
        expression: &Expression,
        requested_array: ArraySpan,
        requested: PackedSpan,
        context_width: usize,
    ) -> ExpressionSources {
        self.eval_expr_requested_in(
            expression,
            requested_array,
            requested,
            context_width,
            &ProjectionContext::default(),
        )
    }

    fn packed_projection_layout(
        &mut self,
        expression: &Expression,
        parts: &[(Expression, Option<Expression>)],
    ) -> Option<Rc<PackedProjectionLayout>> {
        let key = std::ptr::from_ref(expression);
        if let Some(layout) = self
            .call_caches
            .last()
            .and_then(Option::as_ref)
            .and_then(|cache| cache.packed_layouts.get(&key))
            .cloned()
        {
            return Some(layout);
        }

        let mut output_start = 0usize;
        let mut fragments = Vec::with_capacity(parts.len());
        let mut controls = Vec::new();
        for (part_index, (part, repeat)) in parts.iter().enumerate().rev() {
            let item_width = part.comptime().r#type.total_width()?;
            let repeat_count = if let Some(repeat) = repeat {
                let count = repeat
                    .eval_value(&mut self.ctx)
                    .and_then(|value| value.to_usize())?;
                controls.extend(self.eval_expr_inner(repeat, true));
                count
            } else {
                1
            };
            fragments.push(PackedProjectionFragment {
                part: part_index,
                output_start,
                item_width,
                repeat: repeat_count,
            });
            output_start = item_width
                .checked_mul(repeat_count)?
                .checked_add(output_start)?;
        }
        controls.sort_unstable();
        controls.dedup();
        let layout = Rc::new(PackedProjectionLayout {
            fragments,
            controls,
        });
        if let Some(Some(cache)) = self.call_caches.last_mut() {
            cache.packed_layouts.insert(key, Rc::clone(&layout));
        }
        Some(layout)
    }

    fn array_projection_layout(
        &mut self,
        expression: &Expression,
        items: &[ArrayLiteralItem],
    ) -> Option<Rc<ArrayProjectionLayout>> {
        let key = std::ptr::from_ref(expression);
        if let Some(layout) = self
            .call_caches
            .last()
            .and_then(Option::as_ref)
            .and_then(|cache| cache.array_layouts.get(&key))
            .cloned()
        {
            return Some(layout);
        }

        let total = self.expression_array_extent(expression)?;
        let mut output_start = 0usize;
        let mut fragments = Vec::with_capacity(items.len());
        let mut controls = Vec::new();
        let mut default = None;
        for (item_index, item) in items.iter().enumerate() {
            let ArrayLiteralItem::Value(value, repeat) = item else {
                default = Some(item_index);
                continue;
            };
            let item_length = self.expression_array_extent(value)?;
            if item_length == 0 {
                return None;
            }
            let repeat_count = if let Some(repeat) = repeat {
                let count = repeat
                    .eval_value(&mut self.ctx)
                    .and_then(|value| value.to_usize())?;
                controls.extend(self.eval_expr_inner(repeat, true));
                count
            } else {
                1
            };
            let output_length = item_length.checked_mul(repeat_count)?;
            fragments.push(ArrayProjectionFragment {
                item: item_index,
                output_start,
                item_length,
                repeat: repeat_count,
                output_length,
            });
            output_start = output_start.checked_add(output_length)?;
        }
        if let Some(item) = default
            && output_start < total
        {
            let ArrayLiteralItem::Defaul(value) = &items[item] else {
                unreachable!("default index was collected from a default item")
            };
            let item_length = self.expression_array_extent(value)?;
            if item_length == 0 {
                return None;
            }
            let output_length = total - output_start;
            fragments.push(ArrayProjectionFragment {
                item,
                output_start,
                item_length,
                repeat: output_length.div_ceil(item_length),
                output_length,
            });
        }
        controls.sort_unstable();
        controls.dedup();
        let layout = Rc::new(ArrayProjectionLayout {
            fragments,
            controls,
            total,
        });
        if let Some(Some(cache)) = self.call_caches.last_mut() {
            cache.array_layouts.insert(key, Rc::clone(&layout));
        }
        Some(layout)
    }

    fn struct_projection_layout(
        &mut self,
        expression: &Expression,
        r#type: &crate::ir::Type,
        fields: &[(veryl_parser::resource_table::StrId, Expression)],
    ) -> Option<Rc<PackedProjectionLayout>> {
        let key = std::ptr::from_ref(expression);
        if let Some(layout) = self
            .call_caches
            .last()
            .and_then(Option::as_ref)
            .and_then(|cache| cache.struct_layouts.get(&key))
            .cloned()
        {
            return Some(layout);
        }
        let mut output_start = 0usize;
        let mut fragments = Vec::with_capacity(fields.len());
        for (field, (name, _)) in fields.iter().enumerate().rev() {
            let item_width = r#type.get_member_type(*name)?.total_width()?;
            fragments.push(PackedProjectionFragment {
                part: field,
                output_start,
                item_width,
                repeat: 1,
            });
            output_start = output_start.checked_add(item_width)?;
        }
        let layout = Rc::new(PackedProjectionLayout {
            fragments,
            controls: Vec::new(),
        });
        if let Some(Some(cache)) = self.call_caches.last_mut() {
            cache.struct_layouts.insert(key, Rc::clone(&layout));
        }
        Some(layout)
    }

    fn eval_expr_requested_in(
        &mut self,
        expression: &Expression,
        requested_array: ArraySpan,
        requested: PackedSpan,
        context_width: usize,
        projection: &ProjectionContext,
    ) -> ExpressionSources {
        let requested_array = if matches!(expression, Expression::ArrayLiteral(_, _)) {
            requested_array
        } else {
            let expression_array = expression.comptime().r#type.array.total().unwrap_or(1);
            let Some(requested_array) = requested_array.intersection(ArraySpan {
                start: 0,
                length: expression_array,
            }) else {
                return ExpressionSources::default();
            };
            requested_array
        };
        let expression_width = expression
            .comptime()
            .r#type
            .total_width()
            .unwrap_or(context_width);
        let mut reads = PackedSpan::whole(expression_width)
            .and_then(|width| requested.intersection(width))
            .map(|span| self.eval_expr_bits_in(expression, requested_array, span, projection))
            .unwrap_or_default();
        if context_width > expression_width
            && expression.comptime().r#type.signed
            && requested.end() > expression_width
            && expression_width != 0
        {
            let mut sign = self.eval_expr_bits_in(
                expression,
                requested_array,
                PackedSpan {
                    start: expression_width - 1,
                    length: 1,
                },
                projection,
            );
            // Sign extension broadcasts only along the packed axis. Keep the
            // unpacked-element relation so sibling array elements stay
            // independent across context-sized expression boundaries.
            sign.forget_packed_position();
            reads.extend(sign);
        }
        reads.normalize();
        reads
    }

    fn eval_expr_bits_in(
        &mut self,
        expression: &Expression,
        requested_array: ArraySpan,
        requested: PackedSpan,
        projection: &ProjectionContext,
    ) -> ExpressionSources {
        match expression {
            Expression::Term(factor) => match factor.as_ref() {
                Factor::Variable(id, index, select, comptime) => {
                    let frozen = self
                        .call_caches
                        .last()
                        .and_then(Option::as_ref)
                        .and_then(|cache| {
                            cache
                                .variable_reads
                                .get(&std::ptr::from_ref(factor.as_ref()))
                        })
                        .cloned();
                    if self.projection_only && frozen.is_none() {
                        self.status = self.status.max(AnalysisStatus::Partial);
                        return ExpressionSources::default();
                    }
                    let mut selector_sources = frozen
                        .as_ref()
                        .map(|frozen| frozen.selectors.clone())
                        .unwrap_or_else(|| {
                            let mut selectors = Vec::new();
                            for expression in index.0.iter().chain(select.0.iter()) {
                                selectors.extend(self.eval_expr(expression));
                            }
                            if let Some((_, expression)) = &select.1 {
                                selectors.extend(self.eval_expr(expression));
                            }
                            selectors
                        });
                    let variable = self.ctx.variables.get(id).cloned();
                    let selected = if select.is_const_with_range() {
                        variable.as_ref().and_then(|variable| {
                            select.eval_value(&mut self.ctx, &variable.r#type, false)
                        })
                    } else {
                        None
                    };
                    if let Some((_, low)) = selected {
                        let mut reads = Vec::new();
                        let accesses = var_reads(
                            *id,
                            index,
                            select,
                            comptime.member_select_domain,
                            &mut self.ctx,
                        );
                        let absolute_dynamic_array_offset = projection
                            .destination_index
                            .clone()
                            .filter(|destination| !destination.terms.is_empty())
                            .and_then(|destination| {
                                let source = self.flattened_affine_index(*id, index)?;
                                destination.destination_offset_from(&source)
                            });
                        // Affine comparison produces an absolute
                        // source-to-destination translation. Expression
                        // projection first maps the source into expression-local
                        // coordinates; the key-specific destination translation
                        // is composed by the caller.
                        let local_dynamic_array_offset = absolute_dynamic_array_offset
                            .zip(projection.destination_array_offset)
                            .and_then(|(absolute, destination)| absolute.checked_sub(destination));
                        let position_preserving =
                            index.0.iter().all(|index| index.comptime().is_const)
                                && accesses.len() == 1;
                        if let Some(source_span) = requested.translated(0, low) {
                            for (idx, access) in &accesses {
                                let source_array =
                                    if let Some(offset) = absolute_dynamic_array_offset {
                                        offset
                                            .checked_neg()
                                            .and_then(|offset| {
                                                translate_array_span(
                                                    projection
                                                        .destination_array
                                                        .unwrap_or(requested_array),
                                                    offset,
                                                )
                                            })
                                            .and_then(|requested| requested.intersection(*idx))
                                    } else if position_preserving {
                                        requested_array
                                            .translated(0, idx.start)
                                            .and_then(|requested| requested.intersection(*idx))
                                    } else {
                                        Some(*idx)
                                    };
                                if let (Some(source_array), Some(source_span)) =
                                    (source_array, source_span.intersection(*access))
                                {
                                    for key in self.bit_part.overlapping_access(
                                        *id,
                                        source_array,
                                        source_span,
                                    ) {
                                        if let Some(frozen) = &frozen {
                                            if let Some(version) = frozen.version(key) {
                                                reads.push(version);
                                            }
                                        } else {
                                            reads.push(self.read_key(key));
                                        }
                                    }
                                }
                            }
                        }
                        let offset = local_dynamic_array_offset
                            .and_then(|array| {
                                Some(PositionRelation {
                                    array: Some(array),
                                    packed: Some(isize::try_from(low).ok()?.checked_neg()?),
                                })
                            })
                            .or_else(|| {
                                position_preserving
                                    .then(|| {
                                        Some(PositionRelation {
                                            array: Some(
                                                isize::try_from(accesses[0].0.start)
                                                    .ok()?
                                                    .checked_neg()?,
                                            ),
                                            packed: Some(isize::try_from(low).ok()?.checked_neg()?),
                                        })
                                    })
                                    .flatten()
                            });
                        if let Some(offset) = offset {
                            let mut sources = ExpressionSources {
                                sources: reads
                                    .into_iter()
                                    .map(|version| (version, offset))
                                    .collect(),
                            };
                            sources.extend_whole(selector_sources);
                            sources
                        } else {
                            selector_sources.extend(reads);
                            ExpressionSources::whole(selector_sources)
                        }
                    } else {
                        if let Some(frozen) = &frozen {
                            selector_sources
                                .extend(frozen.versions.iter().map(|(_, version)| *version));
                        } else {
                            selector_sources.extend(self.read_variable(
                                *id,
                                index,
                                select,
                                comptime.member_select_domain,
                            ));
                        }
                        ExpressionSources::whole(selector_sources)
                    }
                }
                Factor::SystemFunctionCall(call) => match &call.kind {
                    SystemFunctionKind::Signed(input) | SystemFunctionKind::Unsigned(input) => {
                        self.eval_expr_bits_in(&input.0, requested_array, requested, projection)
                    }
                    _ => ExpressionSources::whole(self.eval_system_call(call, &[], true)),
                },
                Factor::FunctionCall(call) => ExpressionSources {
                    sources: self
                        .eval_call_requested(call, &[], Some((requested_array, requested)))
                        .into_iter()
                        .map(|version| (version, PositionRelation::default()))
                        .collect(),
                },
                Factor::Unknown(_) => {
                    let opaque = self.opaque_value();
                    ExpressionSources::whole(vec![opaque])
                }
                Factor::HierVariable(_) | Factor::Value(_) | Factor::Anonymous(_) => {
                    ExpressionSources::default()
                }
            },
            Expression::Unary(op, operand, _) => match op {
                Op::BitNot | Op::Add => {
                    self.eval_expr_bits_in(operand, requested_array, requested, projection)
                }
                _ => ExpressionSources::whole(self.eval_expr(operand)),
            },
            Expression::Binary(left, op, right, comptime) => match op {
                Op::As => {
                    let context_width = comptime.r#type.total_width().unwrap_or(requested.end());
                    self.eval_expr_requested_in(
                        left,
                        requested_array,
                        requested,
                        context_width,
                        projection,
                    )
                }
                Op::LogicShiftL | Op::ArithShiftL => {
                    let shift = right
                        .eval_value(&mut self.ctx)
                        .and_then(|value| value.to_usize());
                    let mut reads = ExpressionSources::whole(self.eval_expr(right));
                    if let Some(shift) = shift {
                        let start = requested.start.max(shift);
                        if let Some(length) = requested.end().checked_sub(start)
                            && let Some(input) = PackedSpan::new(start - shift, length)
                        {
                            let mut input =
                                self.eval_expr_bits_in(left, requested_array, input, projection);
                            if let Ok(shift) = isize::try_from(shift) {
                                input.translate(PositionRelation {
                                    array: Some(0),
                                    packed: Some(shift),
                                });
                            } else {
                                input.widen_all();
                            }
                            reads.extend(input);
                        }
                    } else {
                        reads.extend_whole(self.eval_expr(left));
                    }
                    reads
                }
                Op::LogicShiftR | Op::ArithShiftR => {
                    let shift = right
                        .eval_value(&mut self.ctx)
                        .and_then(|value| value.to_usize());
                    let mut reads = ExpressionSources::whole(self.eval_expr(right));
                    if let Some(shift) = shift {
                        let width = left.comptime().r#type.total_width().unwrap_or(0);
                        let shifted = requested.translated(0, shift);
                        if let Some(input) = shifted
                            .and_then(|shifted| PackedSpan::whole(width)?.intersection(shifted))
                        {
                            let mut input =
                                self.eval_expr_bits_in(left, requested_array, input, projection);
                            if let Ok(shift) = isize::try_from(shift) {
                                input.translate(PositionRelation {
                                    array: Some(0),
                                    packed: Some(-shift),
                                });
                            } else {
                                input.widen_all();
                            }
                            reads.extend(input);
                        }
                        if *op == Op::ArithShiftR
                            && left.comptime().r#type.signed
                            && width != 0
                            && shifted.is_some_and(|shifted| shifted.end() > width)
                        {
                            let mut sign = self.eval_expr_bits_in(
                                left,
                                requested_array,
                                PackedSpan {
                                    start: width - 1,
                                    length: 1,
                                },
                                projection,
                            );
                            sign.widen_all();
                            reads.extend(sign);
                        }
                    } else {
                        reads.extend_whole(self.eval_expr(left));
                    }
                    reads
                }
                Op::BitAnd | Op::BitOr | Op::BitXor | Op::BitXnor => {
                    let context_width = comptime.r#type.total_width().unwrap_or(requested.end());
                    let mut reads = self.eval_expr_requested_in(
                        left,
                        requested_array,
                        requested,
                        context_width,
                        projection,
                    );
                    reads.extend(self.eval_expr_requested_in(
                        right,
                        requested_array,
                        requested,
                        context_width,
                        projection,
                    ));
                    reads
                }
                Op::LogicAnd | Op::LogicOr => {
                    let mut reads = ExpressionSources::whole(self.eval_expr(left));
                    let execute_right = match (op, self.constant_truth(left)) {
                        (Op::LogicAnd, Some(false)) | (Op::LogicOr, Some(true)) => Some(false),
                        (Op::LogicAnd, Some(true)) | (Op::LogicOr, Some(false)) => Some(true),
                        _ => None,
                    };
                    match execute_right {
                        Some(false) => {}
                        Some(true) => reads.extend_whole(self.eval_expr(right)),
                        None => {
                            let branch = self.expression_branch_id(expression);
                            let parent_condition = self.path_condition.clone();

                            let checkpoint = self.ssa.checkpoint();
                            self.path_condition = parent_condition.with_choice(branch, 0);
                            let right = self.eval_expr(right);
                            let right = self.ssa.definition_guarded(right, &self.path_condition);
                            let evaluated_state = self.ssa.capture_and_rollback(checkpoint);

                            let checkpoint = self.ssa.checkpoint();
                            self.path_condition = parent_condition.with_choice(branch, 1);
                            let skipped_state = self.ssa.capture_and_rollback(checkpoint);

                            self.ssa.merge([&evaluated_state, &skipped_state]);
                            self.path_condition = parent_condition;
                            reads.push(right, PositionRelation::whole());
                        }
                    }
                    reads
                }
                _ => ExpressionSources::whole(self.eval_expr(expression)),
            },
            Expression::Ternary(condition, left, right, comptime) => {
                let context_width = comptime.r#type.total_width().unwrap_or(requested.end());
                let mut reads = ExpressionSources::whole(self.eval_expr(condition));
                match self.constant_truth(condition) {
                    Some(true) => reads.extend(self.eval_expr_requested_in(
                        left,
                        requested_array,
                        requested,
                        context_width,
                        projection,
                    )),
                    Some(false) => reads.extend(self.eval_expr_requested_in(
                        right,
                        requested_array,
                        requested,
                        context_width,
                        projection,
                    )),
                    None => {
                        let branch = self.expression_branch_id(expression);
                        let parent_condition = self.path_condition.clone();

                        let checkpoint = self.ssa.checkpoint();
                        self.path_condition = parent_condition.with_choice(branch, 0);
                        let left = self.eval_expr_requested_in(
                            left,
                            requested_array,
                            requested,
                            context_width,
                            projection,
                        );
                        let left = self.guard_expression_sources(left);
                        let left_state = self.ssa.capture_and_rollback(checkpoint);

                        let checkpoint = self.ssa.checkpoint();
                        self.path_condition = parent_condition.with_choice(branch, 1);
                        let right = self.eval_expr_requested_in(
                            right,
                            requested_array,
                            requested,
                            context_width,
                            projection,
                        );
                        let right = self.guard_expression_sources(right);
                        let right_state = self.ssa.capture_and_rollback(checkpoint);

                        self.ssa.merge([&left_state, &right_state]);
                        self.path_condition = parent_condition;
                        reads.extend(left);
                        reads.extend(right);
                    }
                }
                reads
            }
            Expression::Concatenation(parts, _) => {
                let Some(layout) = self.packed_projection_layout(expression, parts) else {
                    return ExpressionSources::whole(self.eval_expr(expression));
                };
                let mut reads = ExpressionSources::default();
                reads.extend_whole(layout.controls.iter().copied());
                let first = layout.fragments.partition_point(|fragment| {
                    fragment
                        .output_end()
                        .is_some_and(|end| end <= requested.start)
                });
                for fragment in &layout.fragments[first..] {
                    if fragment.output_start >= requested.end() {
                        break;
                    }
                    let part = &parts[fragment.part].0;
                    match project_repeated_span(
                        requested.start,
                        requested.length,
                        fragment.output_start,
                        fragment.item_width,
                        fragment.repeat,
                    ) {
                        RepeatedProjection::Empty => {}
                        RepeatedProjection::Exact { first, second } => {
                            for fragment in [Some(first), second].into_iter().flatten() {
                                let Some(local) =
                                    PackedSpan::new(fragment.local_start, fragment.length)
                                else {
                                    continue;
                                };
                                let mut part = self.eval_expr_bits_in(
                                    part,
                                    requested_array,
                                    local,
                                    projection,
                                );
                                if let Ok(output_start) = isize::try_from(fragment.output_start) {
                                    part.translate(PositionRelation {
                                        array: Some(0),
                                        packed: Some(output_start),
                                    });
                                } else {
                                    part.widen_all();
                                }
                                reads.extend(part);
                            }
                        }
                        RepeatedProjection::Periodic => {
                            let Some(local) = PackedSpan::whole(fragment.item_width) else {
                                reads.extend_whole(self.eval_expr(part));
                                continue;
                            };
                            let part =
                                self.eval_expr_bits_in(part, requested_array, local, projection);
                            if let Some(output_length) =
                                fragment.item_width.checked_mul(fragment.repeat)
                            {
                                let part = self.regular_packed_repeat(
                                    part,
                                    requested_array,
                                    fragment.output_start,
                                    output_length,
                                    fragment.item_width,
                                );
                                reads.extend(part);
                            } else {
                                let mut part = part;
                                part.forget_packed_position();
                                reads.extend(part);
                            }
                        }
                    }
                }
                reads
            }
            Expression::ArrayLiteral(items, _) => {
                let Some(requested_end) = requested_array.end() else {
                    return ExpressionSources::whole(self.eval_expr(expression));
                };
                if let Some(layout) = self.array_projection_layout(expression, items)
                    && requested_end <= layout.total
                {
                    let mut reads = ExpressionSources::default();
                    reads.extend_whole(layout.controls.iter().copied());
                    let first = layout.fragments.partition_point(|fragment| {
                        fragment
                            .output_end()
                            .is_some_and(|end| end <= requested_array.start)
                    });
                    for fragment in &layout.fragments[first..] {
                        if fragment.output_start >= requested_end {
                            break;
                        }
                        let value = match &items[fragment.item] {
                            ArrayLiteralItem::Value(value, _) | ArrayLiteralItem::Defaul(value) => {
                                value
                            }
                        };
                        match project_repeated_span(
                            requested_array.start,
                            requested_array.length,
                            fragment.output_start,
                            fragment.item_length,
                            fragment.repeat,
                        ) {
                            RepeatedProjection::Empty => {}
                            RepeatedProjection::Exact { first, second } => {
                                for projected in [Some(first), second].into_iter().flatten() {
                                    let mut item = self.eval_expr_requested_in(
                                        value,
                                        ArraySpan {
                                            start: projected.local_start,
                                            length: projected.length,
                                        },
                                        requested,
                                        value
                                            .comptime()
                                            .r#type
                                            .total_width()
                                            .unwrap_or(requested.length),
                                        projection,
                                    );
                                    if let Ok(output_start) =
                                        isize::try_from(projected.output_start)
                                    {
                                        item.translate(PositionRelation {
                                            array: Some(output_start),
                                            packed: Some(0),
                                        });
                                    } else {
                                        item.widen_all();
                                    }
                                    reads.extend(item);
                                }
                            }
                            RepeatedProjection::Periodic => {
                                let item = self.eval_expr_requested_in(
                                    value,
                                    ArraySpan {
                                        start: 0,
                                        length: fragment.item_length,
                                    },
                                    requested,
                                    value
                                        .comptime()
                                        .r#type
                                        .total_width()
                                        .unwrap_or(requested.length),
                                    projection,
                                );
                                reads.extend(self.regular_array_repeat(
                                    item,
                                    requested,
                                    fragment.output_start,
                                    fragment.output_length,
                                    fragment.item_length,
                                ));
                            }
                        }
                    }
                    return reads;
                }
                let total = self
                    .expression_array_extent(expression)
                    .unwrap_or(1)
                    .max(requested_end);
                let mut cursor = 0usize;
                let mut default = None;
                let mut reads = ExpressionSources::default();
                for item in items {
                    let ArrayLiteralItem::Value(value, repeat) = item else {
                        let ArrayLiteralItem::Defaul(value) = item else {
                            unreachable!();
                        };
                        default = Some(value.as_ref());
                        continue;
                    };
                    let item_length = self.expression_array_extent(value).unwrap_or(1);
                    let count = if let Some(repeat) = repeat {
                        let Some(count) = repeat
                            .eval_value(&mut self.ctx)
                            .and_then(|value| value.to_usize())
                        else {
                            return ExpressionSources::whole(self.eval_expr(expression));
                        };
                        reads.extend_whole(self.eval_expr_inner(repeat, false));
                        count
                    } else {
                        1
                    };
                    match project_repeated_span(
                        requested_array.start,
                        requested_array.length,
                        cursor,
                        item_length,
                        count,
                    ) {
                        RepeatedProjection::Empty => {}
                        RepeatedProjection::Exact { first, second } => {
                            for fragment in [Some(first), second].into_iter().flatten() {
                                let mut item = self.eval_expr_requested_in(
                                    value,
                                    ArraySpan {
                                        start: fragment.local_start,
                                        length: fragment.length,
                                    },
                                    requested,
                                    value
                                        .comptime()
                                        .r#type
                                        .total_width()
                                        .unwrap_or(requested.length),
                                    projection,
                                );
                                if let Ok(output_start) = isize::try_from(fragment.output_start) {
                                    item.translate(PositionRelation {
                                        array: Some(output_start),
                                        packed: Some(0),
                                    });
                                } else {
                                    item.widen_all();
                                }
                                reads.extend(item);
                            }
                        }
                        RepeatedProjection::Periodic => {
                            let item = self.eval_expr_requested_in(
                                value,
                                ArraySpan {
                                    start: 0,
                                    length: item_length,
                                },
                                requested,
                                value
                                    .comptime()
                                    .r#type
                                    .total_width()
                                    .unwrap_or(requested.length),
                                projection,
                            );
                            if let Some(output_length) = item_length.checked_mul(count) {
                                let item = self.regular_array_repeat(
                                    item,
                                    requested,
                                    cursor,
                                    output_length,
                                    item_length,
                                );
                                reads.extend(item);
                            } else {
                                let mut item = item;
                                item.forget_array_position();
                                reads.extend(item);
                            }
                        }
                    }
                    let Some(item_extent) = item_length.checked_mul(count) else {
                        return ExpressionSources::whole(self.eval_expr(expression));
                    };
                    let Some(next) = cursor.checked_add(item_extent) else {
                        return ExpressionSources::whole(self.eval_expr(expression));
                    };
                    cursor = next;
                }
                if let Some(default) = default
                    && cursor < total
                {
                    let item_length = self.expression_array_extent(default).unwrap_or(1);
                    let remaining = total - cursor;
                    let count = remaining.div_ceil(item_length);
                    match project_repeated_span(
                        requested_array.start,
                        requested_array.length,
                        cursor,
                        item_length,
                        count,
                    ) {
                        RepeatedProjection::Empty => {}
                        RepeatedProjection::Exact { first, second } => {
                            for fragment in [Some(first), second].into_iter().flatten() {
                                let mut item = self.eval_expr_requested_in(
                                    default,
                                    ArraySpan {
                                        start: fragment.local_start,
                                        length: fragment.length,
                                    },
                                    requested,
                                    default
                                        .comptime()
                                        .r#type
                                        .total_width()
                                        .unwrap_or(requested.length),
                                    projection,
                                );
                                if let Ok(output_start) = isize::try_from(fragment.output_start) {
                                    item.translate(PositionRelation {
                                        array: Some(output_start),
                                        packed: Some(0),
                                    });
                                } else {
                                    item.widen_all();
                                }
                                reads.extend(item);
                            }
                        }
                        RepeatedProjection::Periodic => {
                            let item = self.eval_expr_requested_in(
                                default,
                                ArraySpan {
                                    start: 0,
                                    length: item_length,
                                },
                                requested,
                                default
                                    .comptime()
                                    .r#type
                                    .total_width()
                                    .unwrap_or(requested.length),
                                projection,
                            );
                            if let Some(output_length) = item_length
                                .checked_mul(count)
                                .map(|length| length.min(remaining))
                            {
                                let item = self.regular_array_repeat(
                                    item,
                                    requested,
                                    cursor,
                                    output_length,
                                    item_length,
                                );
                                reads.extend(item);
                            } else {
                                let mut item = item;
                                item.forget_array_position();
                                reads.extend(item);
                            }
                        }
                    }
                }
                reads
            }
            Expression::StructConstructor(r#type, fields, _) => {
                if let Some(layout) = self.struct_projection_layout(expression, r#type, fields) {
                    let mut reads = ExpressionSources::default();
                    let first = layout.fragments.partition_point(|fragment| {
                        fragment
                            .output_end()
                            .is_some_and(|end| end <= requested.start)
                    });
                    for fragment in &layout.fragments[first..] {
                        if fragment.output_start >= requested.end() {
                            break;
                        }
                        let Some(window) =
                            PackedSpan::new(fragment.output_start, fragment.item_width)
                        else {
                            continue;
                        };
                        let Some(local) = requested
                            .intersection(window)
                            .and_then(|span| span.translated(fragment.output_start, 0))
                        else {
                            continue;
                        };
                        let value = &fields[fragment.part].1;
                        let mut field = self.eval_expr_requested_in(
                            value,
                            requested_array,
                            local,
                            fragment.item_width,
                            projection,
                        );
                        if let Ok(output_start) = isize::try_from(fragment.output_start) {
                            field.translate(PositionRelation {
                                array: Some(0),
                                packed: Some(output_start),
                            });
                        } else {
                            field.widen_all();
                        }
                        reads.extend(field);
                    }
                    return reads;
                }
                let mut low = 0usize;
                let mut reads = ExpressionSources::default();
                for (name, value) in fields.iter().rev() {
                    let Some(member) = r#type.get_member_type(*name) else {
                        return ExpressionSources::whole(self.eval_expr(expression));
                    };
                    let Some(width) = member.total_width() else {
                        return ExpressionSources::whole(self.eval_expr(expression));
                    };
                    if let Some(window) = PackedSpan::new(low, width)
                        && let Some(local) = requested
                            .intersection(window)
                            .and_then(|span| span.translated(low, 0))
                    {
                        let mut field = self.eval_expr_requested_in(
                            value,
                            requested_array,
                            local,
                            width,
                            projection,
                        );
                        if let Ok(low) = isize::try_from(low) {
                            field.translate(PositionRelation {
                                array: Some(0),
                                packed: Some(low),
                            });
                        } else {
                            field.widen_all();
                        }
                        reads.extend(field);
                    }
                    let Some(next) = low.checked_add(width) else {
                        return ExpressionSources::whole(self.eval_expr(expression));
                    };
                    low = next;
                }
                reads
            }
        }
    }

    fn expression_array_extent(&mut self, expression: &Expression) -> Option<usize> {
        match expression {
            Expression::ArrayLiteral(items, _) if !items.is_empty() => {
                let mut total = 0usize;
                for item in items {
                    let ArrayLiteralItem::Value(value, repeat) = item else {
                        return expression.comptime().r#type.array.total();
                    };
                    let value_extent = self.expression_array_extent(value)?;
                    let repeat = repeat
                        .as_ref()
                        .map(|repeat| {
                            repeat
                                .eval_value(&mut self.ctx)
                                .and_then(|value| value.to_usize())
                        })
                        .unwrap_or(Some(1))?;
                    total = total.checked_add(value_extent.checked_mul(repeat)?)?;
                }
                Some(total)
            }
            _ => expression.comptime().r#type.array.total().or(Some(1)),
        }
    }

    fn eval_expr(&mut self, expression: &Expression) -> Vec<VersionId> {
        self.eval_expr_inner(expression, true)
    }

    fn guard_expression_sources(&mut self, mut sources: ExpressionSources) -> ExpressionSources {
        sources.normalize();
        if sources.is_empty() {
            return sources;
        }
        let version = self
            .ssa
            .related_definition_guarded(sources.sources, &self.path_condition);
        ExpressionSources {
            sources: vec![(version, PositionRelation::default())],
        }
    }

    fn eval_reachable_expr(&mut self, expression: &Expression) -> Vec<VersionId> {
        self.eval_expr_inner(expression, true)
    }

    fn eval_expr_inner(
        &mut self,
        expression: &Expression,
        prune_constant_branches: bool,
    ) -> Vec<VersionId> {
        let mut reads = Vec::new();
        match expression {
            Expression::Term(factor) => self.eval_factor(factor, &mut reads),
            Expression::Unary(_, expression, _) => {
                reads.extend(self.eval_expr_inner(expression, prune_constant_branches));
            }
            Expression::Binary(left, op, right, _) => {
                reads.extend(self.eval_expr_inner(left, prune_constant_branches));
                let execute_right = match (prune_constant_branches, op) {
                    (true, Op::LogicAnd) => match self.constant_truth(left) {
                        Some(false) => Some(false),
                        Some(true) => Some(true),
                        None => None,
                    },
                    (true, Op::LogicOr) => match self.constant_truth(left) {
                        Some(true) => Some(false),
                        Some(false) => Some(true),
                        None => None,
                    },
                    _ => Some(true),
                };
                match execute_right {
                    Some(false) => {}
                    Some(true) => {
                        reads.extend(self.eval_expr_inner(right, prune_constant_branches));
                    }
                    None => {
                        let branch = self.expression_branch_id(expression);
                        let parent_condition = self.path_condition.clone();

                        let checkpoint = self.ssa.checkpoint();
                        self.path_condition = parent_condition.with_choice(branch, 0);
                        let right = self.eval_expr_inner(right, prune_constant_branches);
                        let right = self.ssa.definition_guarded(right, &self.path_condition);
                        let evaluated_state = self.ssa.capture_and_rollback(checkpoint);

                        let checkpoint = self.ssa.checkpoint();
                        self.path_condition = parent_condition.with_choice(branch, 1);
                        let skipped_state = self.ssa.capture_and_rollback(checkpoint);

                        self.ssa.merge([&evaluated_state, &skipped_state]);
                        self.path_condition = parent_condition;
                        reads.push(right);
                    }
                }
            }
            Expression::Ternary(condition, left, right, _) => {
                reads.extend(self.eval_expr_inner(condition, prune_constant_branches));
                match prune_constant_branches
                    .then(|| self.constant_truth(condition))
                    .flatten()
                {
                    Some(true) => {
                        reads.extend(self.eval_expr_inner(left, prune_constant_branches));
                    }
                    Some(false) => {
                        reads.extend(self.eval_expr_inner(right, prune_constant_branches));
                    }
                    None => {
                        let branch = self.expression_branch_id(expression);
                        let parent_condition = self.path_condition.clone();

                        let checkpoint = self.ssa.checkpoint();
                        self.path_condition = parent_condition.with_choice(branch, 0);
                        let left = self.eval_expr_inner(left, prune_constant_branches);
                        let left = self.ssa.definition_guarded(left, &self.path_condition);
                        let left_state = self.ssa.capture_and_rollback(checkpoint);

                        let checkpoint = self.ssa.checkpoint();
                        self.path_condition = parent_condition.with_choice(branch, 1);
                        let right = self.eval_expr_inner(right, prune_constant_branches);
                        let right = self.ssa.definition_guarded(right, &self.path_condition);
                        let right_state = self.ssa.capture_and_rollback(checkpoint);

                        self.ssa.merge([&left_state, &right_state]);
                        self.path_condition = parent_condition;
                        reads.push(left);
                        reads.push(right);
                    }
                }
            }
            Expression::Concatenation(parts, _) => {
                for (part, repeat) in parts {
                    reads.extend(self.eval_expr_inner(part, prune_constant_branches));
                    if let Some(repeat) = repeat {
                        reads.extend(self.eval_expr_inner(repeat, prune_constant_branches));
                    }
                }
            }
            Expression::ArrayLiteral(items, _) => {
                for item in items {
                    match item {
                        ArrayLiteralItem::Value(value, repeat) => {
                            reads.extend(self.eval_expr_inner(value, prune_constant_branches));
                            if let Some(repeat) = repeat {
                                reads.extend(self.eval_expr_inner(repeat, prune_constant_branches));
                            }
                        }
                        ArrayLiteralItem::Defaul(value) => {
                            reads.extend(self.eval_expr_inner(value, prune_constant_branches));
                        }
                    }
                }
            }
            Expression::StructConstructor(_, fields, _) => {
                for (_, value) in fields {
                    reads.extend(self.eval_expr_inner(value, prune_constant_branches));
                }
            }
        }
        reads.sort_unstable();
        reads.dedup();
        reads
    }

    fn constant_truth(&mut self, expression: &Expression) -> Option<bool> {
        expression
            .eval_value(&mut self.ctx)
            .and_then(|value| value.to_usize())
            .map(|value| value != 0)
    }

    fn eval_factor(&mut self, factor: &Factor, reads: &mut Vec<VersionId>) {
        match factor {
            Factor::Variable(id, index, select, comptime) => {
                if let Some(frozen) = self
                    .call_caches
                    .last()
                    .and_then(Option::as_ref)
                    .and_then(|cache| cache.variable_reads.get(&std::ptr::from_ref(factor)))
                    .cloned()
                {
                    reads.extend(frozen.selectors.iter().copied());
                    reads.extend(frozen.versions.iter().map(|(_, version)| *version));
                    return;
                }
                if self.projection_only {
                    self.status = self.status.max(AnalysisStatus::Partial);
                    return;
                }
                let mut selectors = Vec::new();
                for expression in index.0.iter().chain(select.0.iter()) {
                    selectors.extend(self.eval_expr(expression));
                }
                if let Some((_, expression)) = &select.1 {
                    selectors.extend(self.eval_expr(expression));
                }
                selectors.sort_unstable();
                selectors.dedup();
                reads.extend(selectors.iter().copied());

                let versions = self
                    .read_keys(*id, index, select, comptime.member_select_domain)
                    .into_iter()
                    .map(|key| (key, self.read_key(key)))
                    .collect::<Vec<_>>();
                reads.extend(versions.iter().map(|(_, version)| *version));
                if let Some(Some(cache)) = self.call_caches.last_mut() {
                    cache.variable_reads.insert(
                        std::ptr::from_ref(factor),
                        Rc::new(FrozenVariableRead {
                            selectors,
                            versions,
                        }),
                    );
                }
            }
            Factor::FunctionCall(call) => reads.extend(self.eval_call(call, &[])),
            Factor::SystemFunctionCall(call) => {
                reads.extend(self.eval_system_call(call, &[], true));
            }
            Factor::Unknown(_) => {
                let opaque = self.opaque_value();
                reads.push(opaque);
            }
            Factor::HierVariable(_) | Factor::Value(_) | Factor::Anonymous(_) => {}
        }
    }

    fn eval_call(&mut self, call: &FunctionCall, controls: &[VersionId]) -> Vec<VersionId> {
        self.eval_call_requested(call, controls, None)
    }

    fn eval_call_requested(
        &mut self,
        call: &FunctionCall,
        controls: &[VersionId],
        requested: Option<(ArraySpan, PackedSpan)>,
    ) -> Vec<VersionId> {
        #[cfg(test)]
        if matches!(self.call_caches.last(), Some(None)) {
            FUNCTION_BARRIER_EVALUATIONS.set(FUNCTION_BARRIER_EVALUATIONS.get() + 1);
        }
        let cache_key = std::ptr::from_ref(call);
        if let Some(cached) = self
            .call_caches
            .last()
            .and_then(Option::as_ref)
            .and_then(|cache| cache.calls.get(&cache_key))
            .cloned()
        {
            if self.effects_only {
                return Vec::new();
            }
            let result = self.select_call_result(&cached, requested);
            #[cfg(test)]
            FUNCTION_RESULT_VERSIONS.set(FUNCTION_RESULT_VERSIONS.get() + result.len());
            return result;
        }

        // Region projection is a pure query over the ordered evaluation
        // trace. Every reachable caller-side invocation was cached by that
        // evaluation; a miss therefore cannot be repaired by executing a call
        // here without duplicating or inventing procedural effects.
        if self.projection_only {
            self.status = self.status.max(AnalysisStatus::Partial);
            return Vec::new();
        }

        // The enclosing expression may need only this call's effects, but the
        // call body still needs ordinary value evaluation: its return value or
        // writes can depend on nested calls. Suppress only the result selected
        // at this boundary, not results used while constructing `CallResult`.
        let discard_result = self.effects_only;
        self.effects_only = false;
        let evaluated = Rc::new(self.eval_call_uncached(call, controls));
        self.effects_only = discard_result;
        if let Some(Some(cache)) = self.call_caches.last_mut() {
            cache.calls.insert(cache_key, Rc::clone(&evaluated));
        }
        if discard_result {
            return Vec::new();
        }
        let result = self.select_call_result(&evaluated, requested);
        #[cfg(test)]
        FUNCTION_RESULT_VERSIONS.set(FUNCTION_RESULT_VERSIONS.get() + result.len());
        result
    }

    fn select_call_result(
        &mut self,
        evaluated: &CallResult,
        requested: Option<(ArraySpan, PackedSpan)>,
    ) -> Vec<VersionId> {
        let mut result = Vec::new();
        evaluated.for_each_region_group(requested.map(|(array, _)| array), |array, regions| {
            let requested_packed = requested.map(|(_, packed)| packed);
            let first = requested_packed.map_or(0, |requested| {
                regions.partition_point(|(span, _)| {
                    #[cfg(test)]
                    FUNCTION_RESULT_REGION_PROBES.set(FUNCTION_RESULT_REGION_PROBES.get() + 1);
                    span.end() <= requested.start
                })
            });
            for (span, version) in &regions[first..] {
                #[cfg(test)]
                FUNCTION_RESULT_REGION_PROBES.set(FUNCTION_RESULT_REGION_PROBES.get() + 1);
                if requested_packed.is_some_and(|requested| span.start >= requested.end()) {
                    break;
                }
                if let Some((requested_array, requested_packed)) = requested {
                    if requested_array.intersection(array) == Some(array)
                        && requested_packed.intersection(*span) == Some(*span)
                    {
                        result.push(*version);
                    } else {
                        result.extend(self.project_version_sources(
                            *version,
                            requested_array,
                            requested_packed,
                        ));
                    }
                } else {
                    result.push(*version);
                }
            }
        });
        result.sort_unstable();
        result.dedup();
        result
    }

    fn eval_call_uncached(&mut self, call: &FunctionCall, controls: &[VersionId]) -> CallResult {
        #[cfg(test)]
        FUNCTION_EVALUATIONS.set(FUNCTION_EVALUATIONS.get() + 1);

        let summary = self
            .summaries
            .as_deref_mut()
            .map(|summaries| summaries.get(call));
        match summary {
            Some(FunctionSummaryLookup::Ready(summary)) => {
                return self.apply_function_summary(call, controls, summary.as_ref());
            }
            Some(FunctionSummaryLookup::Recursive) => {
                self.opaque_function_call_boundary(call);
                return CallResult {
                    region_groups: Vec::new(),
                };
            }
            Some(FunctionSummaryLookup::Missing) | None => {}
        }

        let body = self
            .ctx
            .functions
            .get(&call.id)
            .and_then(|function| function.get_function_for_index(&call.receiver_index));
        let Some(body) = body else {
            self.opaque_function_call_boundary(call);
            return CallResult {
                region_groups: Vec::new(),
            };
        };
        let mut input_bindings = Vec::new();

        for (path, actual) in &call.inputs {
            let formal = body.arg_map.get(path).copied();
            let (_, snapshots) = self.snapshot_function_actual(actual, formal);
            for (key, mut sources) in snapshots {
                sources.normalize();
                input_bindings.push((key, sources));
            }
        }

        let call_frame = self.next_call_frame;
        self.next_call_frame += 1;
        self.call_frames.push(call_frame);

        let mut formal_ids = body.arg_map.values().copied().collect::<Vec<_>>();
        formal_ids.extend(body.ret);
        formal_ids.sort_unstable();
        formal_ids.dedup();
        for formal in formal_ids {
            for key in self.keys_for_id(formal) {
                let version = self.ssa.definition(Vec::new());
                self.bind_key(key, version);
            }
        }
        for (key, sources) in input_bindings {
            let version = self.ssa.related_definition(sources.sources);
            self.bind_key(key, version);
        }

        self.call_caches.push(None);
        self.eval_function_body(&body.statements, body.ret, controls);
        self.call_caches.pop();

        let mut formal_outputs = HashMap::default();
        for (path, _) in &call.outputs {
            let Some(&formal) = body.arg_map.get(path) else {
                continue;
            };
            formal_outputs
                .entry(formal)
                .or_insert_with(|| self.current_key_versions_for_id(formal));
        }
        let region_groups = body
            .ret
            .map(|ret| self.current_function_return_region_groups(ret, None))
            .unwrap_or_default();

        assert_eq!(self.call_frames.pop(), Some(call_frame));

        for (path, destinations) in &call.outputs {
            let Some(&formal) = body.arg_map.get(path) else {
                continue;
            };
            let formal_coercion = self.ctx.variables.get(&formal).and_then(|variable| {
                Some((variable.r#type.total_width()?, variable.r#type.signed))
            });
            let formal_versions = formal_outputs
                .get(&formal)
                .map(Vec::as_slice)
                .unwrap_or_default();
            let formal_layout = FormalVersionLayout::new(formal_versions, self.bit_part);
            let widths: Vec<_> = destinations
                .iter()
                .map(|destination| self.destination_width(destination))
                .collect();
            if let Some((formal_width, formal_signed)) = formal_coercion
                && widths.iter().all(Option::is_some)
            {
                let total_width = widths.iter().flatten().sum();
                let coercion = FormalOutputCoercion {
                    actual_width: total_width,
                    formal_width,
                    formal_signed,
                };
                let mut offset = total_width;
                for (destination, width) in destinations.iter().zip(widths) {
                    let width = width.expect("checked above");
                    offset -= width;
                    self.write_formal_output(
                        destination,
                        formal_versions,
                        &formal_layout,
                        offset,
                        coercion,
                        controls,
                    );
                }
            } else {
                self.status = self.status.max(AnalysisStatus::Partial);
                let sources = formal_versions
                    .iter()
                    .map(|(_, version)| *version)
                    .collect::<Vec<_>>();
                for destination in destinations {
                    self.write_destination(destination, &sources, controls);
                }
            }
        }

        CallResult { region_groups }
    }

    fn apply_function_summary(
        &mut self,
        call: &FunctionCall,
        controls: &[VersionId],
        summary: &FunctionSummary,
    ) -> CallResult {
        self.status = self.status.max(summary.status);
        self.call_caches.push(Some(EvaluationCache::default()));
        let mut actual_bindings = HashMap::default();
        for (path, actual) in &call.inputs {
            let formal = summary.arg_map.get(path).copied();
            let (_, snapshots) = self.snapshot_function_actual(actual, formal);
            for (key, mut sources) in snapshots {
                sources.normalize();
                actual_bindings.insert(key, sources.sources);
            }
        }
        let branch_map = self.instantiate_summary_branches(call, summary);
        let branch_remapper = SsaStore::<SsaKey>::branch_remapper(branch_map);
        let mut bindings = HashMap::default();
        for key in &summary.external_keys {
            #[cfg(test)]
            FUNCTION_SUMMARY_METADATA_VISITS.set(FUNCTION_SUMMARY_METADATA_VISITS.get() + 1);
            bindings.insert(
                *key,
                self.map_summary_node_source(&actual_bindings, key.node)
                    .sources,
            );
        }
        let bindings = Rc::new(bindings);

        for (destination, root) in &summary.writes {
            let imported = self.ssa.imported_shared(
                summary.graph.clone(),
                *root,
                Rc::clone(&bindings),
                branch_remapper.clone(),
            );
            let mut sources = ExpressionSources {
                sources: vec![(imported, PositionRelation::default())],
            };
            sources.extend_whole(controls.iter().copied());
            let version = self
                .ssa
                .related_definition_guarded(sources.sources, &self.path_condition);
            self.bind_destination(*destination, version, false);
        }

        for (path, destinations) in &call.outputs {
            let Some(&formal) = summary.arg_map.get(path) else {
                continue;
            };
            let formal_coercion = self.ctx.variables.get(&formal).and_then(|variable| {
                Some((variable.r#type.total_width()?, variable.r#type.signed))
            });
            let widths: Vec<_> = destinations
                .iter()
                .map(|destination| self.destination_width(destination))
                .collect();
            if let Some((formal_width, formal_signed)) = formal_coercion
                && widths.iter().all(Option::is_some)
            {
                let formal_versions = self.current_key_versions_for_id(formal);
                let formal_layout = FormalVersionLayout::new(&formal_versions, self.bit_part);
                let total_width = widths.iter().flatten().sum();
                let coercion = FormalOutputCoercion {
                    actual_width: total_width,
                    formal_width,
                    formal_signed,
                };
                let mut offset = total_width;
                for (destination, width) in destinations.iter().zip(widths) {
                    let width = width.expect("checked above");
                    offset -= width;
                    self.write_formal_output(
                        destination,
                        &formal_versions,
                        &formal_layout,
                        offset,
                        coercion,
                        controls,
                    );
                }
            } else {
                self.status = self.status.max(AnalysisStatus::Partial);
                let sources = self
                    .current_key_versions_for_id(formal)
                    .into_iter()
                    .map(|(_, version)| version)
                    .collect::<Vec<_>>();
                for destination in destinations {
                    self.write_destination(destination, &sources, controls);
                }
            }
        }

        let region_groups = summary
            .result
            .iter()
            .map(|(array, regions)| {
                let regions = regions
                    .iter()
                    .map(|(span, root)| {
                        let imported = self.ssa.imported_shared(
                            summary.graph.clone(),
                            *root,
                            Rc::clone(&bindings),
                            branch_remapper.clone(),
                        );
                        let version = if self.path_condition.is_unconditional() {
                            imported
                        } else {
                            self.ssa.related_definition_guarded(
                                vec![(imported, PositionRelation::default())],
                                &self.path_condition,
                            )
                        };
                        (*span, version)
                    })
                    .collect();
                (*array, regions)
            })
            .collect();
        self.call_caches.pop();
        CallResult { region_groups }
    }

    fn map_summary_node_source(
        &mut self,
        actual_bindings: &HashMap<NodeKey, Vec<(VersionId, PositionRelation)>>,
        source: NodeKey,
    ) -> ExpressionSources {
        if self.is_module_scope_key(source) {
            return ExpressionSources {
                sources: vec![(self.read_key(source), PositionRelation::default())],
            };
        }
        ExpressionSources {
            sources: actual_bindings.get(&source).cloned().unwrap_or_default(),
        }
    }

    fn instantiate_summary_branches(
        &mut self,
        call: &FunctionCall,
        summary: &FunctionSummary,
    ) -> HashMap<BranchId, BranchId> {
        #[cfg(test)]
        FUNCTION_SUMMARY_METADATA_VISITS
            .set(FUNCTION_SUMMARY_METADATA_VISITS.get() + summary.branches.len());
        if let Some(&call) = self.top_expression_calls.get(&std::ptr::from_ref(call)) {
            summary
                .branches
                .iter()
                .copied()
                .enumerate()
                .map(|(local, branch)| {
                    (
                        branch,
                        BranchId::expression_call(
                            self.branch_namespace,
                            call,
                            local,
                            branch.arms(),
                        ),
                    )
                })
                .collect()
        } else {
            summary
                .branches
                .iter()
                .copied()
                .map(|branch| (branch, self.next_branch_id(branch.arms())))
                .collect()
        }
    }

    fn keys_for_id(&self, id: VarId) -> Vec<NodeKey> {
        let mut keys = self
            .bit_part
            .array_spans(id)
            .iter()
            .flat_map(|index| {
                let ranges = self.bit_part.ranges_of((id, *index));
                (0..ranges.len()).map(move |range| (id, *index, range))
            })
            .collect::<Vec<_>>();
        keys.sort_unstable();
        keys
    }

    fn current_key_versions_for_id(&mut self, id: VarId) -> Vec<(NodeKey, VersionId)> {
        self.keys_for_id(id)
            .into_iter()
            .map(|key| (key, self.read_key(key)))
            .collect()
    }

    fn project_version_sources(
        &mut self,
        version: VersionId,
        requested_array: ArraySpan,
        requested_packed: PackedSpan,
    ) -> Vec<VersionId> {
        if self
            .ssa
            .has_structural_dependency_cached(version, &mut self.structural_dependency_cache)
        {
            return vec![
                self.ssa
                    .projected(version, position_domain(requested_array, requested_packed)),
            ];
        }
        let sources = self
            .ssa
            .root_source_relations_guarded_cached(version, &mut self.projection_source_cache);
        if sources.is_empty() {
            return vec![version];
        }
        let mut projected = Vec::new();
        for (key, relation, condition) in sources {
            let array_matches = relation.array.is_none_or(|offset| {
                translate_array_span(key.node.1, offset)
                    .is_some_and(|span| span.overlaps(requested_array))
            });
            let packed_matches = relation.packed.is_none_or(|offset| {
                self.key_span(key.node)
                    .and_then(|span| translate_packed_span(span, offset))
                    .is_some_and(|span| span.overlaps(requested_packed))
            });
            if array_matches && packed_matches {
                let source = self.ssa.read(key);
                projected.push(
                    self.ssa
                        .related_definition_guarded(vec![(source, relation)], &condition),
                );
            }
        }
        projected.sort_unstable();
        projected.dedup();
        projected
    }

    fn current_region_groups_for_id(
        &mut self,
        id: VarId,
    ) -> Vec<(ArraySpan, Vec<(PackedSpan, VersionId)>)> {
        let mut groups = Vec::<(ArraySpan, Vec<(PackedSpan, VersionId)>)>::new();
        let mut previous_array_span = None;
        for key in self.keys_for_id(id) {
            let Some(span) = self.key_span(key) else {
                continue;
            };
            if previous_array_span != Some(key.1) {
                groups.push((key.1, Vec::new()));
                previous_array_span = Some(key.1);
            }
            let group = &mut groups.last_mut().expect("pushed above").1;
            debug_assert!(group.last().is_none_or(|(previous, _)| {
                previous.start <= span.start && previous.end() <= span.start
            }));
            group.push((span, self.read_key(key)));
        }
        groups
    }

    fn current_function_return_region_groups(
        &mut self,
        id: VarId,
        storage_span: Option<ArraySpan>,
    ) -> Vec<(ArraySpan, Vec<(PackedSpan, VersionId)>)> {
        let groups = self.current_region_groups_for_id(id);
        let Some(storage_span) = storage_span else {
            return groups;
        };
        let array_offset = isize::try_from(storage_span.start)
            .ok()
            .and_then(isize::checked_neg);
        let mut selected = Vec::new();
        for (array, regions) in groups {
            let Some(array) = array
                .intersection(storage_span)
                .and_then(|array| array.translated(storage_span.start, 0))
            else {
                continue;
            };
            let regions = regions
                .into_iter()
                .map(|(packed, version)| {
                    let version = self.ssa.related_definition(vec![(
                        version,
                        PositionRelation {
                            array: array_offset,
                            packed: Some(0),
                        },
                    )]);
                    (packed, version)
                })
                .collect();
            selected.push((array, regions));
        }
        selected
    }

    fn eval_actual_for_formal_key(
        &mut self,
        actual: &Expression,
        formal_key: NodeKey,
    ) -> ExpressionSources {
        let Some(span) = self.key_span(formal_key) else {
            return ExpressionSources::whole(self.eval_expr(actual));
        };
        let formal_width = self
            .ctx
            .variables
            .get(&formal_key.0)
            .and_then(|variable| variable.r#type.total_width());
        if actual.comptime().r#type.total_width().is_none() || formal_width.is_none() {
            self.status = self.status.max(AnalysisStatus::Partial);
            return ExpressionSources::whole(self.eval_expr(actual));
        }
        self.eval_expr_requested(
            actual,
            formal_key.1,
            span,
            formal_width.expect("checked above"),
        )
    }

    fn snapshot_function_actual(
        &mut self,
        actual: &Expression,
        formal: Option<VarId>,
    ) -> (Vec<VersionId>, Vec<(NodeKey, ExpressionSources)>) {
        let formal_keys = formal.map_or_else(Vec::new, |formal| self.keys_for_id(formal));
        let snapshots: Vec<(NodeKey, ExpressionSources)> =
            self.snapshot_expression(actual, |this| {
                formal_keys
                    .into_iter()
                    .map(|key| {
                        let sources = this.eval_speculatively(|this| {
                            this.eval_actual_for_formal_key(actual, key)
                        });
                        (key, sources)
                    })
                    .collect()
            });
        let mut whole_sources = snapshots
            .iter()
            .flat_map(|(_, sources)| sources.sources.iter().map(|(version, _)| *version))
            .collect::<Vec<_>>();
        whole_sources.sort_unstable();
        whole_sources.dedup();
        (whole_sources, snapshots)
    }

    fn write_formal_output(
        &mut self,
        destination: &AssignDestination,
        formal_versions: &[(NodeKey, VersionId)],
        formal_layout: &FormalVersionLayout,
        formal_offset: usize,
        coercion: FormalOutputCoercion,
        controls: &[VersionId],
    ) {
        let FormalOutputCoercion {
            actual_width,
            formal_width,
            formal_signed,
        } = coercion;
        // An output actual is an assignment destination evaluated at copy-out.
        // Its array/packed coordinates therefore control every candidate key,
        // just as they do for an ordinary procedural assignment. Evaluate each
        // syntactic coordinate once here; omitting these dependencies loses
        // real loops such as `set(value[index])` where `index` depends on
        // `value` itself.
        let mut destination_controls = controls.to_vec();
        for selector in destination
            .index
            .0
            .iter()
            .chain(destination.select.0.iter())
        {
            destination_controls.extend(self.eval_expr(selector));
        }
        if let Some((_, selector)) = &destination.select.1 {
            destination_controls.extend(self.eval_expr(selector));
        }
        let destination_control = self.aggregate_destination_controls(destination_controls);
        let variable = self.ctx.variables.get(&destination.id).cloned();
        let selected = if destination.select.is_const_with_range() {
            variable.as_ref().and_then(|variable| {
                destination
                    .select
                    .eval_value(&mut self.ctx, &variable.r#type, false)
            })
        } else {
            None
        };
        let destination_array = dst_writes(destination, &mut self.ctx)
            .into_iter()
            .map(|(array, _)| array)
            .next();
        let destination_array_selection =
            self.destination_array_selection(destination.id, &destination.index);
        let (keys, resolved) = self.write_keys(destination);
        let dynamic = !resolved || self.destination_is_dynamic(destination);
        for key in keys {
            if !resolved {
                let opaque = self.ssa.definition(Vec::new());
                self.bind_destination(key, opaque, true);
                continue;
            }
            let array = if let Some(destination_array) = destination_array {
                let Some(array) = destination_array_projection(
                    key.1,
                    destination_array,
                    &destination_array_selection,
                ) else {
                    // Exact periodic gap: this key is not a possible output
                    // destination and must retain its previous value.
                    continue;
                };
                Some(array)
            } else {
                None
            };
            let mut positional = Vec::new();
            let mut whole = destination_control.into_iter().collect::<Vec<_>>();
            if let (Some(array), Some((_, low)), Some(span)) = (array, selected, self.key_span(key))
            {
                if let Some(position_offset) = array.position_offset(low, formal_offset) {
                    if let Some(requested) = span
                        .translated(low, formal_offset)
                        .and_then(|span| PackedSpan::whole(actual_width)?.intersection(span))
                    {
                        let requested_array = array.source;
                        if let Some(copied) = PackedSpan::whole(formal_width)
                            .and_then(|formal| formal.intersection(requested))
                        {
                            for version in formal_layout.overlapping(requested_array, copied) {
                                positional.extend(
                                    self.project_version_sources(version, requested_array, copied)
                                        .into_iter()
                                        .map(|version| (version, position_offset)),
                                );
                            }
                        }
                        if formal_signed
                            && formal_width != 0
                            && actual_width > formal_width
                            && requested.end() > formal_width
                        {
                            let sign = PackedSpan {
                                start: formal_width - 1,
                                length: 1,
                            };
                            let sign_relation = PositionRelation {
                                array: position_offset.array,
                                packed: None,
                            };
                            for version in formal_layout.overlapping(requested_array, sign) {
                                positional.extend(
                                    self.project_version_sources(version, requested_array, sign)
                                        .into_iter()
                                        .map(|version| (version, sign_relation)),
                                );
                            }
                        }
                    }
                } else {
                    whole.extend(formal_versions.iter().map(|(_, version)| *version));
                }
            } else {
                whole.extend(formal_versions.iter().map(|(_, version)| *version));
            }
            positional.extend(
                whole
                    .into_iter()
                    .map(|version| (version, PositionRelation::whole())),
            );
            let version = self
                .ssa
                .related_definition_guarded(positional, &self.path_condition);
            self.bind_destination(key, version, dynamic);
        }
    }

    fn eval_system_call(
        &mut self,
        call: &crate::ir::SystemFunctionCall,
        controls: &[VersionId],
        _value_position: bool,
    ) -> Vec<VersionId> {
        if self.projection_only {
            return match &call.kind {
                SystemFunctionKind::Onehot(input)
                | SystemFunctionKind::Signed(input)
                | SystemFunctionKind::Unsigned(input) => self.eval_expr(&input.0),
                SystemFunctionKind::Bits(_)
                | SystemFunctionKind::Size(_)
                | SystemFunctionKind::Clog2(_)
                | SystemFunctionKind::Readmemh(_, _)
                | SystemFunctionKind::Display(_)
                | SystemFunctionKind::Write(_)
                | SystemFunctionKind::Assert { .. }
                | SystemFunctionKind::Finish => Vec::new(),
            };
        }
        match &call.kind {
            SystemFunctionKind::Bits(_)
            | SystemFunctionKind::Size(_)
            | SystemFunctionKind::Clog2(_)
            | SystemFunctionKind::Finish => Vec::new(),
            SystemFunctionKind::Onehot(input)
            | SystemFunctionKind::Signed(input)
            | SystemFunctionKind::Unsigned(input) => self.eval_expr(&input.0),
            SystemFunctionKind::Readmemh(input, output) => {
                let sources = self.eval_expr(&input.0);
                for destination in &output.0 {
                    self.write_destination(destination, &sources, controls);
                }
                Vec::new()
            }
            SystemFunctionKind::Display(inputs) | SystemFunctionKind::Write(inputs) => {
                for input in inputs {
                    self.eval_expr(&input.0);
                }
                Vec::new()
            }
            SystemFunctionKind::Assert { cond, args, .. } => {
                self.eval_expr(&cond.0);
                for input in args {
                    self.eval_expr(&input.0);
                }
                Vec::new()
            }
        }
    }
}

fn statements_have_unsupported(statements: &[Statement]) -> bool {
    statements.iter().any(|statement| match statement {
        Statement::If(statement) => {
            statements_have_unsupported(&statement.true_side)
                || statements_have_unsupported(&statement.false_side)
        }
        Statement::IfReset(statement) => {
            statements_have_unsupported(&statement.true_side)
                || statements_have_unsupported(&statement.false_side)
        }
        Statement::Case(statement) => {
            statement
                .arms
                .iter()
                .any(|arm| statements_have_unsupported(&arm.body))
                || statements_have_unsupported(&statement.default)
        }
        Statement::For(statement) => statements_have_unsupported(&statement.body),
        Statement::Unsupported(_) => true,
        _ => false,
    })
}
