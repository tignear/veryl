//! IR-independent statement-ordered SSA state.

use crate::{HashMap, HashSet};
use std::cell::{OnceCell, RefCell};
use std::collections::VecDeque;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::rc::Rc;

#[cfg(test)]
thread_local! {
    static PATH_CONSTRAINT_MATERIALIZATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static SNAPSHOT_KEY_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static REVISION_EVENT_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static REVISION_CANDIDATE_INPUTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static SOURCE_SUMMARY_STATE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static INLINE_DEPENDENCY_EDGE_PROBES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static INLINE_DEPENDENCY_NODE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static IMPORTED_BINDING_PROBES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static STRUCTURAL_DEPENDENCY_VERSION_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_source_summary_state_visits() {
    SOURCE_SUMMARY_STATE_VISITS.set(0);
}

#[cfg(test)]
pub(crate) fn source_summary_state_visits() -> usize {
    SOURCE_SUMMARY_STATE_VISITS.get()
}

#[cfg(test)]
pub(crate) fn reset_flow_scaling_counters() {
    PATH_CONSTRAINT_MATERIALIZATIONS.set(0);
    SNAPSHOT_KEY_VISITS.set(0);
    REVISION_EVENT_VISITS.set(0);
    REVISION_CANDIDATE_INPUTS.set(0);
}

#[cfg(test)]
pub(crate) fn flow_scaling_counters() -> (usize, usize, usize, usize) {
    (
        PATH_CONSTRAINT_MATERIALIZATIONS.get(),
        SNAPSHOT_KEY_VISITS.get(),
        REVISION_EVENT_VISITS.get(),
        REVISION_CANDIDATE_INPUTS.get(),
    )
}

pub(super) type VersionId = usize;

type SourceMap<K> = HashMap<(K, PositionRelation), PathCondition>;

pub(super) struct BranchRemapper {
    mapping: HashMap<BranchId, BranchId>,
    cache: RefCell<HashMap<ConditionNodeKey, PathCondition>>,
    // Cache keys use the arena address, while this map keeps every referenced
    // arena alive for the lifetime of the cache. This prevents address reuse
    // without putting an interior-mutable `Rc<RefCell<_>>` in a hash key.
    source_arenas: RefCell<HashMap<usize, Rc<RefCell<PathConditionArena>>>>,
}

impl BranchRemapper {
    pub(super) fn new(mapping: HashMap<BranchId, BranchId>) -> Self {
        Self {
            mapping,
            cache: RefCell::new(HashMap::default()),
            source_arenas: RefCell::new(HashMap::default()),
        }
    }

    pub(super) fn remap(&self, condition: &PathCondition) -> PathCondition {
        let arena = Rc::as_ptr(&condition.arena) as usize;
        self.source_arenas
            .borrow_mut()
            .entry(arena)
            .or_insert_with(|| condition.arena.clone());
        condition.remapped_cached(&self.mapping, arena, &mut self.cache.borrow_mut())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ConditionNodeKey {
    arena: usize,
    node: usize,
}

pub(super) struct SourceCache<K> {
    summaries: HashMap<(VersionId, bool), Rc<SourceMap<K>>>,
    allowed: Option<HashSet<K>>,
}

impl<K> Default for SourceCache<K> {
    fn default() -> Self {
        Self {
            summaries: HashMap::default(),
            allowed: None,
        }
    }
}

impl<K> SourceCache<K>
where
    K: Eq + Hash,
{
    pub(super) fn restricted(allowed: impl IntoIterator<Item = K>) -> Self {
        Self {
            summaries: HashMap::default(),
            allowed: Some(allowed.into_iter().collect()),
        }
    }
}

#[derive(Clone)]
enum Version<K> {
    Entry(K),
    Definition {
        sources: Vec<(VersionId, PositionRelation)>,
        condition: PathCondition,
    },
    Phi(Vec<VersionId>),
    Imported {
        graph: Rc<DependencyDag<K>>,
        root: Option<usize>,
        bindings: Rc<HashMap<K, Vec<(VersionId, PositionRelation)>>>,
        branches: Rc<BranchRemapper>,
    },
    Projected {
        source: VersionId,
        domain: PositionDomain,
    },
    /// A finite regular transfer. The dependency DAG lowers this to one
    /// domain-bearing node reached by `initial`, with a self-edge `step`.
    /// The node domain bounds the number of legal repetitions without
    /// materializing one edge per repeated element.
    Repeated {
        source: VersionId,
        initial: PositionRelation,
        step: PositionRelation,
        domain: PositionDomain,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct BranchId {
    namespace: BranchNamespace,
    local: usize,
    arms: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum BranchNamespace {
    Procedure(usize),
    Expression(usize),
    ExpressionCall { root: usize, call: usize },
}

impl BranchId {
    pub(super) const fn new(procedure: usize, local: usize, arms: usize) -> Self {
        Self {
            namespace: BranchNamespace::Procedure(procedure),
            local,
            arms,
        }
    }

    pub(super) const fn expression(root: usize, local: usize, arms: usize) -> Self {
        Self {
            namespace: BranchNamespace::Expression(root),
            local,
            arms,
        }
    }

    pub(super) const fn expression_call(
        root: usize,
        call: usize,
        local: usize,
        arms: usize,
    ) -> Self {
        Self {
            namespace: BranchNamespace::ExpressionCall { root, call },
            local,
            arms,
        }
    }

    pub(super) const fn arms(self) -> usize {
        self.arms
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct BranchConstraint {
    branch: BranchId,
    allowed: ArmSet,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct ArmSet {
    ranges: Vec<(usize, usize)>,
}

impl ArmSet {
    fn range(start: usize, end: usize) -> Self {
        Self {
            ranges: (start < end).then_some((start, end)).into_iter().collect(),
        }
    }

    fn intersection(&self, other: &Self) -> Self {
        let mut ranges = Vec::new();
        let mut left = 0;
        let mut right = 0;
        while left < self.ranges.len() && right < other.ranges.len() {
            let a = self.ranges[left];
            let b = other.ranges[right];
            let start = a.0.max(b.0);
            let end = a.1.min(b.1);
            if start < end {
                ranges.push((start, end));
            }
            if a.1 < b.1 {
                left += 1;
            } else {
                right += 1;
            }
        }
        Self { ranges }
    }

    fn union(&self, other: &Self) -> Self {
        let mut ranges = self
            .ranges
            .iter()
            .chain(&other.ranges)
            .copied()
            .collect::<Vec<_>>();
        ranges.sort_unstable();
        let mut merged: Vec<(usize, usize)> = Vec::with_capacity(ranges.len());
        for range in ranges {
            if let Some(previous) = merged.last_mut()
                && range.0 <= previous.1
            {
                previous.1 = previous.1.max(range.1);
            } else {
                merged.push(range);
            }
        }
        Self { ranges: merged }
    }

    fn is_empty(&self) -> bool {
        self.ranges.is_empty()
    }

    fn is_all(&self, arms: usize) -> bool {
        self.ranges.as_slice() == [(0, arms)]
    }

    fn is_subset_of(&self, other: &Self) -> bool {
        self.intersection(other) == *self
    }
}

/// A compact Cartesian over-approximation of feasible branch choices.
///
/// Correlations between distinct syntactic branches are intentionally not
/// retained. Choices of the same branch remain exact, which is sufficient to
/// reject cycles assembled from mutually exclusive arms without enumerating
/// every combination of independent conditions.
#[derive(Clone)]
pub(super) struct PathCondition {
    arena: Rc<RefCell<PathConditionArena>>,
    node: usize,
}

#[derive(Default)]
struct PathConditionArena {
    nodes: Vec<PathConditionNode>,
}

struct PathConditionNode {
    kind: PathConditionNodeKind,
    length: usize,
    base_length: usize,
    fingerprint: u64,
    jumps: Vec<usize>,
    materialized: OnceCell<Rc<Vec<BranchConstraint>>>,
}

enum PathConditionNodeKind {
    Empty,
    Append {
        parent: usize,
        constraint: BranchConstraint,
    },
    Materialized,
}

impl Default for PathCondition {
    fn default() -> Self {
        let mut arena = PathConditionArena::default();
        arena.nodes.push(PathConditionNode {
            kind: PathConditionNodeKind::Empty,
            length: 0,
            base_length: 0,
            fingerprint: 0,
            jumps: Vec::new(),
            materialized: OnceCell::from(Rc::new(Vec::new())),
        });
        Self {
            arena: Rc::new(RefCell::new(arena)),
            node: 0,
        }
    }
}

impl std::fmt::Debug for PathCondition {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("PathCondition")
            .field("constraints", &self.constraints())
            .finish()
    }
}

impl PartialEq for PathCondition {
    fn eq(&self, other: &Self) -> bool {
        if Rc::ptr_eq(&self.arena, &other.arena) && self.node == other.node {
            return true;
        }
        let (left_length, left_fingerprint) = self.metadata();
        let (right_length, right_fingerprint) = other.metadata();
        left_length == right_length
            && left_fingerprint == right_fingerprint
            && self.constraints() == other.constraints()
    }
}

impl Eq for PathCondition {}

impl Hash for PathCondition {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.metadata().hash(state);
    }
}

impl PartialOrd for PathCondition {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PathCondition {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if Rc::ptr_eq(&self.arena, &other.arena) && self.node == other.node {
            return std::cmp::Ordering::Equal;
        }
        self.metadata()
            .cmp(&other.metadata())
            .then_with(|| self.constraints().cmp(&other.constraints()))
    }
}

impl PathCondition {
    fn metadata(&self) -> (usize, u64) {
        let arena = self.arena.borrow();
        let node = &arena.nodes[self.node];
        (node.length, node.fingerprint)
    }

    fn fingerprint(constraints: &[BranchConstraint]) -> u64 {
        constraints.iter().fold(0, |fingerprint, constraint| {
            let mut hasher = DefaultHasher::new();
            constraint.hash(&mut hasher);
            fingerprint.rotate_left(7) ^ hasher.finish()
        })
    }

    fn from_constraints(constraints: Vec<BranchConstraint>) -> Self {
        if constraints.is_empty() {
            return Self::default();
        }
        let fingerprint = Self::fingerprint(&constraints);
        let length = constraints.len();
        let materialized = OnceCell::from(Rc::new(constraints));
        let node = PathConditionNode {
            kind: PathConditionNodeKind::Materialized,
            length,
            base_length: length,
            fingerprint,
            jumps: Vec::new(),
            materialized,
        };
        let mut arena = PathConditionArena::default();
        arena.nodes.push(node);
        Self {
            arena: Rc::new(RefCell::new(arena)),
            node: 0,
        }
    }

    fn constraints(&self) -> Rc<Vec<BranchConstraint>> {
        if let Some(constraints) = self.arena.borrow().nodes[self.node].materialized.get() {
            return constraints.clone();
        }

        let mut suffix = Vec::new();
        let base = {
            let arena = self.arena.borrow();
            let mut current = self.node;
            loop {
                let node = &arena.nodes[current];
                if let Some(constraints) = node.materialized.get() {
                    break constraints.clone();
                }
                match &node.kind {
                    PathConditionNodeKind::Append { parent, constraint } => {
                        suffix.push(constraint.clone());
                        current = *parent;
                    }
                    PathConditionNodeKind::Empty | PathConditionNodeKind::Materialized => {
                        break Rc::new(Vec::new());
                    }
                }
            }
        };
        let mut constraints = Vec::with_capacity(base.len() + suffix.len());
        constraints.extend(base.iter().cloned());
        constraints.extend(suffix.into_iter().rev());
        let constraints = Rc::new(constraints);
        #[cfg(test)]
        PATH_CONSTRAINT_MATERIALIZATIONS
            .set(PATH_CONSTRAINT_MATERIALIZATIONS.get() + constraints.len());
        let arena = self.arena.borrow();
        let _ = arena.nodes[self.node].materialized.set(constraints.clone());
        constraints
    }

    fn immediate_append(&self) -> Option<(usize, BranchConstraint)> {
        let arena = self.arena.borrow();
        match &arena.nodes[self.node].kind {
            PathConditionNodeKind::Append { parent, constraint } => {
                Some((*parent, constraint.clone()))
            }
            PathConditionNodeKind::Empty | PathConditionNodeKind::Materialized => None,
        }
    }

    fn single_constraint(&self) -> Option<BranchConstraint> {
        if self.metadata().0 != 1 {
            return None;
        }
        if let Some((_, constraint)) = self.immediate_append() {
            return Some(constraint);
        }
        self.arena.borrow().nodes[self.node]
            .materialized
            .get()
            .and_then(|constraints| constraints.first().cloned())
    }

    fn appended_node_at_length(&self, target: usize) -> Option<usize> {
        let arena = self.arena.borrow();
        let root = &arena.nodes[self.node];
        if target <= root.base_length || target > root.length {
            return None;
        }
        let mut current = self.node;
        while arena.nodes[current].length > target {
            let difference = arena.nodes[current].length - target;
            let jump = (usize::BITS - 1 - difference.leading_zeros()) as usize;
            current = *arena.nodes[current].jumps.get(jump)?;
        }
        (arena.nodes[current].length == target).then_some(current)
    }

    fn constraint_for(&self, branch: BranchId) -> Option<BranchConstraint> {
        let (length, _) = self.metadata();
        let base_length = self.arena.borrow().nodes[self.node].base_length;
        let mut low = base_length + 1;
        let mut high = length + 1;
        while low < high {
            let middle = low + (high - low) / 2;
            let node = self.appended_node_at_length(middle)?;
            let arena = self.arena.borrow();
            let PathConditionNodeKind::Append { constraint, .. } = &arena.nodes[node].kind else {
                return None;
            };
            match constraint.branch.cmp(&branch) {
                std::cmp::Ordering::Less => low = middle + 1,
                std::cmp::Ordering::Greater => high = middle,
                std::cmp::Ordering::Equal => return Some(constraint.clone()),
            }
        }

        let arena = self.arena.borrow();
        let mut base = self.node;
        while let PathConditionNodeKind::Append { parent, .. } = &arena.nodes[base].kind {
            base = *parent;
        }
        arena.nodes[base]
            .materialized
            .get()
            .and_then(|constraints| {
                constraints
                    .binary_search_by_key(&branch, |constraint| constraint.branch)
                    .ok()
                    .map(|index| constraints[index].clone())
            })
    }

    fn ancestor_node(&self, descendant: &Self) -> Option<bool> {
        if !Rc::ptr_eq(&self.arena, &descendant.arena) {
            return None;
        }
        let (ancestor_length, _) = self.metadata();
        let (mut descendant_length, _) = descendant.metadata();
        if ancestor_length > descendant_length {
            return Some(false);
        }
        let arena = self.arena.borrow();
        let mut current = descendant.node;
        while descendant_length > ancestor_length {
            let PathConditionNodeKind::Append { parent, .. } = &arena.nodes[current].kind else {
                return Some(false);
            };
            current = *parent;
            descendant_length -= 1;
        }
        Some(current == self.node)
    }

    /// Keep only choices introduced after `ancestor`. The fast path walks the
    /// persistent suffix and is proportional to the newly introduced nesting,
    /// not to the complete enclosing procedural path.
    pub(super) fn relative_to(&self, ancestor: &Self) -> Self {
        if Rc::ptr_eq(&self.arena, &ancestor.arena) && ancestor.ancestor_node(self) == Some(true) {
            let mut suffix = Vec::new();
            let arena = self.arena.borrow();
            let mut current = self.node;
            while current != ancestor.node {
                let PathConditionNodeKind::Append { parent, constraint } =
                    &arena.nodes[current].kind
                else {
                    break;
                };
                suffix.push(constraint.clone());
                current = *parent;
            }
            suffix.reverse();
            return Self::from_constraints(suffix);
        }

        let constraints = self.constraints();
        let ancestor = ancestor.constraints();
        let mut relative = Vec::new();
        for constraint in constraints.iter() {
            let same = ancestor
                .binary_search_by_key(&constraint.branch, |entry| entry.branch)
                .is_ok_and(|index| ancestor[index] == *constraint);
            if !same {
                relative.push(constraint.clone());
            }
        }
        Self::from_constraints(relative)
    }

    pub(super) fn is_unconditional(&self) -> bool {
        self.metadata().0 == 0
    }

    pub(super) fn with_choice(&self, branch: BranchId, arm: usize) -> Self {
        self.with_choice_range(branch, arm, arm.saturating_add(1))
    }

    pub(super) fn with_choice_range(&self, branch: BranchId, start: usize, end: usize) -> Self {
        debug_assert!(start < end && end <= branch.arms);
        let constraint = BranchConstraint {
            branch,
            allowed: ArmSet::range(start, end),
        };
        let append = {
            let arena = self.arena.borrow();
            let node = &arena.nodes[self.node];
            if node.length == 0 {
                true
            } else {
                match &node.kind {
                    PathConditionNodeKind::Append {
                        constraint: last, ..
                    } => last.branch < branch,
                    PathConditionNodeKind::Materialized => node
                        .materialized
                        .get()
                        .and_then(|constraints| constraints.last())
                        .is_some_and(|last| last.branch < branch),
                    PathConditionNodeKind::Empty => true,
                }
            }
        };
        if append {
            let (length, fingerprint) = self.metadata();
            let mut hasher = DefaultHasher::new();
            constraint.hash(&mut hasher);
            let mut arena = self.arena.borrow_mut();
            let mut jumps = vec![self.node];
            let mut power = 1;
            while let Some(&previous) = jumps.get(power - 1) {
                let Some(&ancestor) = arena.nodes[previous].jumps.get(power - 1) else {
                    break;
                };
                jumps.push(ancestor);
                power += 1;
            }
            let node = PathConditionNode {
                kind: PathConditionNodeKind::Append {
                    parent: self.node,
                    constraint,
                },
                length: length + 1,
                base_length: arena.nodes[self.node].base_length,
                fingerprint: fingerprint.rotate_left(7) ^ hasher.finish(),
                jumps,
                materialized: OnceCell::new(),
            };
            let node_id = arena.nodes.len();
            arena.nodes.push(node);
            return Self {
                arena: self.arena.clone(),
                node: node_id,
            };
        }

        let mut constraints = self.constraints().as_ref().clone();
        match constraints.binary_search_by_key(&branch, |constraint| constraint.branch) {
            Ok(index) => constraints[index] = constraint,
            Err(index) => constraints.insert(index, constraint),
        }
        Self::from_constraints(constraints)
    }

    /// Joins alternative paths into the least Cartesian condition that covers
    /// every input condition.
    pub(super) fn disjoin_all<'a>(conditions: impl IntoIterator<Item = &'a Self>) -> Self {
        let mut conditions = conditions.into_iter();
        let Some(first) = conditions.next() else {
            return Self::default();
        };
        let mut combined = first.clone();
        for condition in conditions {
            combined = combined.disjoin(condition);
        }
        combined
    }

    pub(super) fn conjoin_if_compatible(&self, other: &Self) -> Option<Self> {
        if self.is_unconditional() {
            return Some(other.clone());
        }
        if other.is_unconditional() {
            return Some(self.clone());
        }
        if self.ancestor_node(other) == Some(true) {
            return Some(other.clone());
        }
        if other.ancestor_node(self) == Some(true) {
            return Some(self.clone());
        }
        if let Some(constraint) = self.single_constraint()
            && let Some(existing) = other.constraint_for(constraint.branch)
        {
            let allowed = existing.allowed.intersection(&constraint.allowed);
            if allowed.is_empty() {
                return None;
            }
            if existing.allowed.is_subset_of(&constraint.allowed) {
                return Some(other.clone());
            }
        }
        if let Some(constraint) = other.single_constraint()
            && let Some(existing) = self.constraint_for(constraint.branch)
        {
            let allowed = existing.allowed.intersection(&constraint.allowed);
            if allowed.is_empty() {
                return None;
            }
            if existing.allowed.is_subset_of(&constraint.allowed) {
                return Some(self.clone());
            }
        }
        if Rc::ptr_eq(&self.arena, &other.arena)
            && let (Some((left_parent, left)), Some((right_parent, right))) =
                (self.immediate_append(), other.immediate_append())
            && left_parent == right_parent
            && left.branch == right.branch
        {
            let allowed = left.allowed.intersection(&right.allowed);
            if allowed.is_empty() {
                return None;
            }
        }
        let left_constraints = self.constraints();
        let right_constraints = other.constraints();
        let mut constraints = Vec::with_capacity(left_constraints.len() + right_constraints.len());
        let mut left = left_constraints.iter().peekable();
        let mut right = right_constraints.iter().peekable();
        loop {
            match (left.peek(), right.peek()) {
                (Some(a), Some(b)) if a.branch == b.branch => {
                    let allowed = a.allowed.intersection(&b.allowed);
                    if allowed.is_empty() {
                        return None;
                    }
                    constraints.push(BranchConstraint {
                        branch: a.branch,
                        allowed,
                    });
                    left.next();
                    right.next();
                }
                (Some(a), Some(b)) if a.branch < b.branch => {
                    constraints.push((*a).clone());
                    left.next();
                }
                (Some(_), Some(b)) => {
                    constraints.push((*b).clone());
                    right.next();
                }
                (Some(a), None) => {
                    constraints.push((*a).clone());
                    left.next();
                }
                (None, Some(b)) => {
                    constraints.push((*b).clone());
                    right.next();
                }
                (None, None) => break,
            }
        }
        Some(Self::from_constraints(constraints))
    }

    /// Returns true when every branch valuation admitted by `other` is also
    /// admitted by `self`.
    pub(super) fn covers(&self, other: &Self) -> bool {
        if self.is_unconditional() || self.ancestor_node(other) == Some(true) {
            return true;
        }
        let constraints = self.constraints();
        let other = other.constraints();
        constraints.iter().all(|constraint| {
            other
                .binary_search_by_key(&constraint.branch, |other| other.branch)
                .ok()
                .is_some_and(|index| other[index].allowed.is_subset_of(&constraint.allowed))
        })
    }

    /// Collect branch identities from persistent paths without materializing
    /// every prefix. Nodes shared by multiple conditions are visited once.
    pub(super) fn collect_branches<'a>(
        conditions: impl IntoIterator<Item = &'a Self>,
    ) -> Vec<BranchId> {
        let mut branches = HashSet::default();
        let mut visited = HashSet::default();
        for condition in conditions {
            let mut current = condition.node;
            loop {
                let arena_id = Rc::as_ptr(&condition.arena) as usize;
                if !visited.insert((arena_id, current)) {
                    break;
                }
                let arena = condition.arena.borrow();
                let node = &arena.nodes[current];
                match &node.kind {
                    PathConditionNodeKind::Append { parent, constraint } => {
                        branches.insert(constraint.branch);
                        current = *parent;
                    }
                    PathConditionNodeKind::Empty => break,
                    PathConditionNodeKind::Materialized => {
                        if let Some(constraints) = node.materialized.get() {
                            branches.extend(constraints.iter().map(|constraint| constraint.branch));
                        }
                        break;
                    }
                }
            }
        }
        let mut branches = branches.into_iter().collect::<Vec<_>>();
        branches.sort_unstable();
        branches
    }

    fn remapped_cached(
        &self,
        branches: &HashMap<BranchId, BranchId>,
        arena: usize,
        cache: &mut HashMap<ConditionNodeKey, Self>,
    ) -> Self {
        let key_for = |node| ConditionNodeKey { arena, node };
        let root_key = key_for(self.node);
        if let Some(remapped) = cache.get(&root_key) {
            return remapped.clone();
        }

        let mut suffix = Vec::new();
        let mut current = self.node;
        let (base_key, base) = loop {
            let key = key_for(current);
            if let Some(remapped) = cache.get(&key) {
                break (key, remapped.clone());
            }
            let arena = self.arena.borrow();
            match &arena.nodes[current].kind {
                PathConditionNodeKind::Append { parent, constraint } => {
                    suffix.push((current, constraint.clone()));
                    current = *parent;
                }
                PathConditionNodeKind::Empty => break (key, Self::default()),
                PathConditionNodeKind::Materialized => {
                    let constraints = arena.nodes[current]
                        .materialized
                        .get()
                        .expect("materialized node contains its constraints")
                        .iter()
                        .map(|constraint| BranchConstraint {
                            branch: branches
                                .get(&constraint.branch)
                                .copied()
                                .unwrap_or(constraint.branch),
                            allowed: constraint.allowed.clone(),
                        })
                        .collect();
                    break (key, Self::from_constraints(constraints));
                }
            }
        };
        cache.entry(base_key).or_insert_with(|| base.clone());
        let mut remapped = base;
        for (source, mut constraint) in suffix.into_iter().rev() {
            constraint.branch = branches
                .get(&constraint.branch)
                .copied()
                .unwrap_or(constraint.branch);
            remapped = remapped.append_constraint(constraint);
            cache.insert(key_for(source), remapped.clone());
        }
        cache.insert(root_key, remapped.clone());
        remapped
    }

    fn append_constraint(&self, constraint: BranchConstraint) -> Self {
        let (length, fingerprint) = self.metadata();
        let mut hasher = DefaultHasher::new();
        constraint.hash(&mut hasher);
        let mut arena = self.arena.borrow_mut();
        let mut jumps = vec![self.node];
        let mut power = 1;
        while let Some(&previous) = jumps.get(power - 1) {
            let Some(&ancestor) = arena.nodes[previous].jumps.get(power - 1) else {
                break;
            };
            jumps.push(ancestor);
            power += 1;
        }
        let node = PathConditionNode {
            kind: PathConditionNodeKind::Append {
                parent: self.node,
                constraint,
            },
            length: length + 1,
            base_length: arena.nodes[self.node].base_length,
            fingerprint: fingerprint.rotate_left(7) ^ hasher.finish(),
            jumps,
            materialized: OnceCell::new(),
        };
        let node_id = arena.nodes.len();
        arena.nodes.push(node);
        Self {
            arena: self.arena.clone(),
            node: node_id,
        }
    }

    /// Returns the least Cartesian condition covering either input.
    pub(super) fn disjoin(&self, other: &Self) -> Self {
        if self.is_unconditional() || other.is_unconditional() {
            return Self::default();
        }
        if self.ancestor_node(other) == Some(true) {
            return self.clone();
        }
        if other.ancestor_node(self) == Some(true) {
            return other.clone();
        }
        if Rc::ptr_eq(&self.arena, &other.arena)
            && let (Some((left_parent, left)), Some((right_parent, right))) =
                (self.immediate_append(), other.immediate_append())
            && left_parent == right_parent
            && left.branch == right.branch
        {
            let allowed = left.allowed.union(&right.allowed);
            let parent = Self {
                arena: self.arena.clone(),
                node: left_parent,
            };
            if allowed.is_all(left.branch.arms) {
                return parent;
            }
            let Some(&(start, end)) = allowed.ranges.first() else {
                return parent;
            };
            if allowed.ranges.len() == 1 {
                return parent.with_choice_range(left.branch, start, end);
            }
        }
        let self_constraints = self.constraints();
        let other_constraints = other.constraints();
        let mut constraints = Vec::new();
        for constraint in self_constraints.iter() {
            let Ok(index) =
                other_constraints.binary_search_by_key(&constraint.branch, |other| other.branch)
            else {
                continue;
            };
            let allowed = constraint.allowed.union(&other_constraints[index].allowed);
            if !allowed.is_all(constraint.branch.arms) {
                constraints.push(BranchConstraint {
                    branch: constraint.branch,
                    allowed,
                });
            }
        }
        Self::from_constraints(constraints)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct PositionRelation {
    pub(super) array: Option<isize>,
    pub(super) packed: Option<isize>,
}

#[derive(Clone)]
pub(super) enum DependencyDagNode<K> {
    External(K),
    Internal,
    /// A finite regular transfer whose self-edge denotes repetition rather
    /// than an independently authored dependency.
    RegularTransfer,
}

#[derive(Clone)]
pub(super) struct DependencyDagEdge {
    pub(super) source: usize,
    pub(super) destination: usize,
    pub(super) relation: PositionRelation,
    pub(super) condition: PathCondition,
}

#[derive(Clone)]
pub(super) struct DependencyDag<K> {
    pub(super) nodes: Vec<DependencyDagNode<K>>,
    pub(super) edges: Vec<DependencyDagEdge>,
    pub(super) roots: Vec<Option<usize>>,
    pub(super) domains: Vec<Vec<PositionDomain>>,
    pub(super) incoming: OnceCell<Rc<Vec<Vec<usize>>>>,
}

impl<K> DependencyDag<K> {
    fn incoming(&self) -> Rc<Vec<Vec<usize>>> {
        self.incoming
            .get_or_init(|| {
                let mut incoming = vec![Vec::new(); self.nodes.len()];
                for (index, edge) in self.edges.iter().enumerate() {
                    #[cfg(test)]
                    INLINE_DEPENDENCY_EDGE_PROBES.set(INLINE_DEPENDENCY_EDGE_PROBES.get() + 1);
                    if let Some(edges) = incoming.get_mut(edge.destination) {
                        edges.push(index);
                    }
                }
                Rc::new(incoming)
            })
            .clone()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct PositionDomain {
    pub(super) array_start: usize,
    pub(super) array_length: usize,
    pub(super) packed_start: usize,
    pub(super) packed_length: usize,
}

impl Default for PositionRelation {
    fn default() -> Self {
        Self {
            array: Some(0),
            packed: Some(0),
        }
    }
}

impl PositionRelation {
    pub(super) const fn whole() -> Self {
        Self {
            array: None,
            packed: None,
        }
    }

    pub(super) fn compose(self, other: Self) -> Self {
        Self {
            array: compose_axis(self.array, other.array),
            packed: compose_axis(self.packed, other.packed),
        }
    }

    pub(super) fn reversed(self) -> Self {
        Self {
            array: self.array.map(|offset| {
                offset
                    .checked_neg()
                    .expect("reversed array position offset must fit in isize")
            }),
            packed: self.packed.map(|offset| {
                offset
                    .checked_neg()
                    .expect("reversed packed position offset must fit in isize")
            }),
        }
    }

    #[cfg(test)]
    pub(super) fn union(self, other: Self) -> Self {
        Self {
            array: (self.array == other.array).then_some(self.array).flatten(),
            packed: (self.packed == other.packed)
                .then_some(self.packed)
                .flatten(),
        }
    }
}

fn compose_axis(left: Option<isize>, right: Option<isize>) -> Option<isize> {
    match (left, right) {
        (Some(left), Some(right)) => Some(
            left.checked_add(right)
                .expect("composed position offset must fit in isize"),
        ),
        _ => None,
    }
}

fn widen_repeated_axis(mut relation: PositionRelation, step: PositionRelation) -> PositionRelation {
    if step.array.is_some_and(|step| step != 0) {
        relation.array = None;
    }
    if step.packed.is_some_and(|step| step != 0) {
        relation.packed = None;
    }
    relation
}

fn reachable_versions(
    direct: &HashSet<VersionId>,
    successors: &HashMap<VersionId, HashSet<VersionId>>,
) -> HashSet<VersionId> {
    let mut reached = direct.clone();
    let mut queue = VecDeque::from_iter(direct.iter().copied());
    while let Some(version) = queue.pop_front() {
        let Some(next) = successors.get(&version) else {
            continue;
        };
        for &next in next {
            if reached.insert(next) {
                queue.push_back(next);
            }
        }
    }
    reached
}

#[derive(Clone, Copy)]
pub(super) struct Checkpoint {
    undo_start: usize,
    depth: usize,
    version_start: usize,
}

pub(super) struct BranchState<K> {
    bindings: HashMap<K, VersionId>,
}

pub(super) struct RepeatedTransfer<K> {
    entry_version_by_key: HashMap<K, VersionId>,
    reachable_by_entry: HashMap<VersionId, HashSet<VersionId>>,
    version_start: usize,
}

impl<K> BranchState<K> {
    pub(super) fn empty() -> Self {
        Self {
            bindings: HashMap::default(),
        }
    }

    #[cfg(test)]
    pub(super) fn unchanged() -> Self {
        Self::empty()
    }
}

struct Undo<K> {
    key: K,
    previous: Option<VersionId>,
}

#[derive(Clone, Copy)]
pub(super) struct StateRevision {
    id: usize,
    event_start: usize,
    checkpoint_depth: usize,
}

#[derive(Clone, Copy)]
enum StateRevisionEvent<K> {
    Change {
        key: K,
        previous: Option<VersionId>,
        current: Option<VersionId>,
    },
    Exit(usize),
}

struct RevisionValue {
    baseline: Option<VersionId>,
    current: Option<VersionId>,
    current_since_exit: usize,
    inputs: HashSet<VersionId>,
    needs_entry: bool,
}

pub(super) struct SsaStore<K> {
    versions: Vec<Version<K>>,
    entries: HashMap<K, VersionId>,
    current: HashMap<K, VersionId>,
    undo: Vec<Undo<K>>,
    checkpoints: Vec<usize>,
    checkpoint_dirty: Vec<HashSet<K>>,
    revision_events: Vec<StateRevisionEvent<K>>,
    active_revisions: Vec<usize>,
    next_revision_id: usize,
}

impl<K> Default for SsaStore<K> {
    fn default() -> Self {
        Self {
            versions: Vec::new(),
            entries: HashMap::default(),
            current: HashMap::default(),
            undo: Vec::new(),
            checkpoints: Vec::new(),
            checkpoint_dirty: Vec::new(),
            revision_events: Vec::new(),
            active_revisions: Vec::new(),
            next_revision_id: 0,
        }
    }
}

impl<K> SsaStore<K>
where
    K: Copy + Eq + Hash,
{
    pub(super) fn entry_keys(&self) -> impl Iterator<Item = K> + '_ {
        self.entries.keys().copied()
    }

    fn entry(&mut self, key: K) -> VersionId {
        if let Some(version) = self.entries.get(&key) {
            return *version;
        }
        let version = self.versions.len();
        self.versions.push(Version::Entry(key));
        self.entries.insert(key, version);
        version
    }

    pub(super) fn read(&mut self, key: K) -> VersionId {
        if let Some(version) = self.current.get(&key) {
            *version
        } else {
            self.entry(key)
        }
    }

    pub(super) fn definition(&mut self, sources: Vec<VersionId>) -> VersionId {
        self.definition_guarded(sources, &PathCondition::default())
    }

    pub(super) fn definition_guarded(
        &mut self,
        sources: Vec<VersionId>,
        condition: &PathCondition,
    ) -> VersionId {
        self.related_definition_guarded(
            sources
                .into_iter()
                .map(|source| (source, PositionRelation::whole()))
                .collect(),
            condition,
        )
    }

    pub(super) fn related_definition(
        &mut self,
        sources: Vec<(VersionId, PositionRelation)>,
    ) -> VersionId {
        self.related_definition_guarded(sources, &PathCondition::default())
    }

    pub(super) fn related_definition_guarded(
        &mut self,
        sources: Vec<(VersionId, PositionRelation)>,
        condition: &PathCondition,
    ) -> VersionId {
        let mut sources = sources;
        sources.sort_unstable();
        sources.dedup();
        let version = self.versions.len();
        self.versions.push(Version::Definition {
            sources,
            condition: condition.clone(),
        });
        version
    }

    pub(super) fn imported(
        &mut self,
        graph: Rc<DependencyDag<K>>,
        root: Option<usize>,
        bindings: HashMap<K, Vec<(VersionId, PositionRelation)>>,
        branches: Rc<BranchRemapper>,
    ) -> VersionId {
        self.imported_shared(graph, root, Rc::new(bindings), branches)
    }

    pub(super) fn imported_shared(
        &mut self,
        graph: Rc<DependencyDag<K>>,
        root: Option<usize>,
        bindings: Rc<HashMap<K, Vec<(VersionId, PositionRelation)>>>,
        branches: Rc<BranchRemapper>,
    ) -> VersionId {
        let version = self.versions.len();
        self.versions.push(Version::Imported {
            graph,
            root,
            bindings,
            branches,
        });
        version
    }

    pub(super) fn branch_remapper(branches: HashMap<BranchId, BranchId>) -> Rc<BranchRemapper> {
        Rc::new(BranchRemapper::new(branches))
    }

    pub(super) fn projected(&mut self, source: VersionId, domain: PositionDomain) -> VersionId {
        let version = self.versions.len();
        self.versions.push(Version::Projected { source, domain });
        version
    }

    pub(super) fn repeated(
        &mut self,
        source: VersionId,
        initial: PositionRelation,
        step: PositionRelation,
        domain: PositionDomain,
    ) -> VersionId {
        debug_assert!(
            (step.array == Some(0) && step.packed.is_some_and(|step| step != 0))
                || (step.packed == Some(0) && step.array.is_some_and(|step| step != 0)),
            "a regular transfer advances exactly one position axis"
        );
        let version = self.versions.len();
        self.versions.push(Version::Repeated {
            source,
            initial,
            step,
            domain,
        });
        version
    }

    #[cfg(test)]
    pub(super) fn has_structural_dependency(&self, version: VersionId) -> bool {
        let mut visited = HashSet::default();
        let mut queue = VecDeque::from([version]);
        while let Some(version) = queue.pop_front() {
            if !visited.insert(version) {
                continue;
            }
            match &self.versions[version] {
                Version::Imported { .. } | Version::Projected { .. } | Version::Repeated { .. } => {
                    return true;
                }
                Version::Definition { sources, .. } => {
                    queue.extend(sources.iter().map(|(source, _)| *source));
                }
                Version::Phi(inputs) => queue.extend(inputs.iter().copied()),
                Version::Entry(_) => {}
            }
        }
        false
    }

    pub(super) fn has_structural_dependency_cached(
        &self,
        version: VersionId,
        cache: &mut HashMap<VersionId, bool>,
    ) -> bool {
        if let Some(&result) = cache.get(&version) {
            return result;
        }
        let mut stack = vec![(version, false)];
        while let Some((current, expanded)) = stack.pop() {
            if cache.contains_key(&current) {
                continue;
            }
            match &self.versions[current] {
                Version::Imported { .. } | Version::Projected { .. } | Version::Repeated { .. } => {
                    #[cfg(test)]
                    STRUCTURAL_DEPENDENCY_VERSION_VISITS
                        .set(STRUCTURAL_DEPENDENCY_VERSION_VISITS.get() + 1);
                    cache.insert(current, true);
                }
                Version::Definition { sources, .. } => {
                    if expanded {
                        #[cfg(test)]
                        STRUCTURAL_DEPENDENCY_VERSION_VISITS
                            .set(STRUCTURAL_DEPENDENCY_VERSION_VISITS.get() + 1);
                        cache.insert(current, sources.iter().any(|(source, _)| cache[source]));
                    } else {
                        stack.push((current, true));
                        stack.extend(
                            sources
                                .iter()
                                .filter(|(source, _)| !cache.contains_key(source))
                                .map(|(source, _)| (*source, false)),
                        );
                    }
                }
                Version::Phi(inputs) => {
                    if expanded {
                        #[cfg(test)]
                        STRUCTURAL_DEPENDENCY_VERSION_VISITS
                            .set(STRUCTURAL_DEPENDENCY_VERSION_VISITS.get() + 1);
                        cache.insert(current, inputs.iter().any(|input| cache[input]));
                    } else {
                        stack.push((current, true));
                        stack.extend(
                            inputs
                                .iter()
                                .filter(|input| !cache.contains_key(input))
                                .map(|input| (*input, false)),
                        );
                    }
                }
                Version::Entry(_) => {
                    #[cfg(test)]
                    STRUCTURAL_DEPENDENCY_VERSION_VISITS
                        .set(STRUCTURAL_DEPENDENCY_VERSION_VISITS.get() + 1);
                    cache.insert(current, false);
                }
            }
        }
        cache[&version]
    }

    pub(super) fn bind(&mut self, key: K, version: VersionId) {
        let previous = self.current.insert(key, version);
        self.record_revision_change(key, previous, Some(version));
        if !self.checkpoints.is_empty() {
            self.undo.push(Undo { key, previous });
            if let Some(dirty) = self.checkpoint_dirty.last_mut() {
                dirty.insert(key);
            }
        }
    }

    pub(super) fn weak_bind(&mut self, key: K, version: VersionId) {
        let previous = self.read(key);
        let version = self.phi(vec![previous, version]);
        self.bind(key, version);
    }

    pub(super) fn checkpoint(&mut self) -> Checkpoint {
        let checkpoint = Checkpoint {
            undo_start: self.undo.len(),
            depth: self.checkpoints.len(),
            version_start: self.versions.len(),
        };
        self.checkpoints.push(checkpoint.undo_start);
        self.checkpoint_dirty.push(HashSet::default());
        checkpoint
    }

    /// Start recording the SSA state changes and exits of one function body.
    /// Nested recorders share the append-only event stream; their exit markers
    /// are distinguished by `id`, while their state changes remain visible to
    /// an enclosing call exactly as ordinary SSA changes are.
    pub(super) fn begin_state_revision(&mut self, checkpoint: Checkpoint) -> StateRevision {
        assert!(checkpoint.depth < self.checkpoints.len());
        assert_eq!(self.checkpoints[checkpoint.depth], checkpoint.undo_start);
        if self.active_revisions.is_empty() {
            self.revision_events.clear();
        }
        let revision = StateRevision {
            id: self.next_revision_id,
            event_start: self.revision_events.len(),
            checkpoint_depth: checkpoint.depth,
        };
        self.next_revision_id += 1;
        self.active_revisions.push(revision.id);
        revision
    }

    /// Mark the current state as one feasible exit of `revision`.
    pub(super) fn record_state_revision_exit(&mut self, revision: StateRevision) {
        assert!(self.active_revisions.contains(&revision.id));
        self.revision_events
            .push(StateRevisionEvent::Exit(revision.id));
    }

    /// Merge all values observed at exits of `revision` without taking a full
    /// state snapshot at every exit. Rollbacks are state-change events too, so
    /// one linear replay recovers the same per-key phi inputs as merging those
    /// snapshots would.
    pub(super) fn finish_state_revision(&mut self, revision: StateRevision) -> BranchState<K> {
        self.finish_state_revision_inner(revision, true)
    }

    /// Finish a speculative exit recorder. Runtime-loop bodies may contain no
    /// return at all, in which case the recorded state is intentionally empty.
    pub(super) fn finish_optional_state_revision(
        &mut self,
        revision: StateRevision,
    ) -> BranchState<K> {
        self.finish_state_revision_inner(revision, false)
    }

    fn finish_state_revision_inner(
        &mut self,
        revision: StateRevision,
        require_exit: bool,
    ) -> BranchState<K> {
        assert_eq!(self.active_revisions.last(), Some(&revision.id));
        assert!(revision.checkpoint_depth < self.checkpoints.len());

        let mut exit_count = 0;
        let mut values: HashMap<K, RevisionValue> = HashMap::default();
        for event in &self.revision_events[revision.event_start..] {
            #[cfg(test)]
            REVISION_EVENT_VISITS.set(REVISION_EVENT_VISITS.get() + 1);
            match *event {
                StateRevisionEvent::Exit(id) if id == revision.id => exit_count += 1,
                StateRevisionEvent::Exit(_) => {}
                StateRevisionEvent::Change {
                    key,
                    previous,
                    current,
                } => {
                    let value = values.entry(key).or_insert_with(|| RevisionValue {
                        baseline: previous,
                        current: previous,
                        current_since_exit: 0,
                        inputs: HashSet::default(),
                        needs_entry: false,
                    });
                    if value.current_since_exit < exit_count {
                        if let Some(version) = value.current {
                            value.inputs.insert(version);
                        } else {
                            value.needs_entry = true;
                        }
                    }
                    value.current = current;
                    value.current_since_exit = exit_count;
                }
            }
        }
        assert!(
            !require_exit || exit_count != 0,
            "a completed function has at least one exit"
        );
        let mut bindings = HashMap::default();
        for (key, mut value) in values {
            if value.current_since_exit < exit_count {
                if let Some(version) = value.current {
                    value.inputs.insert(version);
                } else {
                    value.needs_entry = true;
                }
            }
            let only_baseline = match value.baseline {
                Some(baseline) => {
                    !value.needs_entry
                        && value.inputs.len() == 1
                        && value.inputs.contains(&baseline)
                }
                None => value.needs_entry && value.inputs.is_empty(),
            };
            if only_baseline {
                continue;
            }
            if value.needs_entry {
                value.inputs.insert(self.entry(key));
            }
            if value.inputs.is_empty() {
                continue;
            }
            #[cfg(test)]
            REVISION_CANDIDATE_INPUTS.set(REVISION_CANDIDATE_INPUTS.get() + value.inputs.len());
            bindings.insert(key, self.phi(value.inputs.into_iter().collect()));
        }

        assert_eq!(self.active_revisions.pop(), Some(revision.id));
        if self.active_revisions.is_empty() {
            self.revision_events.clear();
        }
        BranchState { bindings }
    }

    pub(super) fn capture_and_rollback(&mut self, checkpoint: Checkpoint) -> BranchState<K> {
        assert_eq!(checkpoint.depth + 1, self.checkpoints.len());
        assert_eq!(self.checkpoints.pop(), Some(checkpoint.undo_start));
        let dirty = self
            .checkpoint_dirty
            .pop()
            .expect("checkpoint dirty set was pushed together");

        let mut bindings = HashMap::default();
        for key in dirty {
            let version = self
                .current
                .get(&key)
                .copied()
                .expect("a branch binding must exist until rollback");
            bindings.insert(key, version);
        }

        while self.undo.len() > checkpoint.undo_start {
            let undo = self.undo.pop().expect("undo length checked above");
            let current = self.current.get(&undo.key).copied();
            if let Some(previous) = undo.previous {
                self.current.insert(undo.key, previous);
            } else {
                self.current.remove(&undo.key);
            }
            self.record_revision_change(undo.key, current, undo.previous);
        }
        bindings.retain(|key, version| self.current.get(key).copied() != Some(*version));
        BranchState { bindings }
    }

    fn record_revision_change(
        &mut self,
        key: K,
        previous: Option<VersionId>,
        current: Option<VersionId>,
    ) {
        if previous != current && !self.active_revisions.is_empty() {
            self.revision_events.push(StateRevisionEvent::Change {
                key,
                previous,
                current,
            });
        }
    }

    /// Capture bindings changed since an enclosing checkpoint without
    /// disturbing the current transaction. This records an early-exit path
    /// before its nearer branch checkpoint rolls back.
    pub(super) fn snapshot_since(&self, checkpoint: Checkpoint) -> BranchState<K> {
        assert!(checkpoint.depth < self.checkpoints.len());
        assert_eq!(self.checkpoints[checkpoint.depth], checkpoint.undo_start);

        let mut bindings = HashMap::default();
        for dirty in &self.checkpoint_dirty[checkpoint.depth..] {
            for key in dirty {
                #[cfg(test)]
                SNAPSHOT_KEY_VISITS.set(SNAPSHOT_KEY_VISITS.get() + 1);
                if let Some(version) = self.current.get(key) {
                    bindings.insert(*key, *version);
                }
            }
        }
        BranchState { bindings }
    }

    pub(super) fn merge<'b>(&mut self, states: impl IntoIterator<Item = &'b BranchState<K>>)
    where
        K: 'b,
    {
        let mut inputs_by_key: HashMap<K, (Vec<VersionId>, usize)> = HashMap::default();
        let mut state_count = 0;
        for state in states {
            state_count += 1;
            for (&key, &version) in &state.bindings {
                let (inputs, bound_branches) =
                    inputs_by_key.entry(key).or_insert_with(|| (Vec::new(), 0));
                inputs.push(version);
                *bound_branches += 1;
            }
        }
        for (key, (mut inputs, bound_branches)) in inputs_by_key {
            let fallback = self
                .current
                .get(&key)
                .copied()
                .unwrap_or_else(|| self.entry(key));
            if bound_branches < state_count {
                inputs.push(fallback);
            }
            let version = self.phi(inputs);
            self.bind(key, version);
        }
    }

    /// Prepare the transitive closure of a runtime loop's may-dependency
    /// transfer without enumerating runtime iterator values or iterations.
    ///
    /// `single_iteration` maps each written key to its output after one
    /// abstract iteration. Versions that predate `iteration_checkpoint` are
    /// that iteration's inputs, so they form the nodes of a finite transfer
    /// graph. The prepared reachability relation is shared by normal and early
    /// exits from the same runtime loop.
    pub(super) fn prepare_repeated_transfer(
        &mut self,
        single_iteration: &BranchState<K>,
        iteration_checkpoint: Checkpoint,
    ) -> RepeatedTransfer<K> {
        let mut entry_version_by_key = HashMap::default();
        let mut direct_inputs_by_key = HashMap::default();
        for (&key, &output) in &single_iteration.bindings {
            entry_version_by_key.insert(key, self.read(key));
            direct_inputs_by_key.insert(
                key,
                self.iteration_input_versions(output, iteration_checkpoint.version_start),
            );
        }
        let mut next_inputs_by_input: HashMap<VersionId, HashSet<VersionId>> = HashMap::default();
        for (&key, direct_inputs) in &direct_inputs_by_key {
            next_inputs_by_input
                .entry(entry_version_by_key[&key])
                .or_default()
                .extend(direct_inputs);
        }
        let reachable_by_entry = entry_version_by_key
            .values()
            .copied()
            .map(|entry| {
                let direct = next_inputs_by_input
                    .get(&entry)
                    .cloned()
                    .unwrap_or_default();
                (entry, reachable_versions(&direct, &next_inputs_by_input))
            })
            .collect();
        RepeatedTransfer {
            entry_version_by_key,
            reachable_by_entry,
            version_start: iteration_checkpoint.version_start,
        }
    }

    /// Apply a prepared transfer for any positive number of iterations.
    ///
    /// When `may_skip` is true, a root phi keeps the loop-entry version as a
    /// separate zero-iteration alternative. This distinction matters for a
    /// raw live-on-entry value: dependency DAG roots intentionally suppress
    /// that implicit latch input, while a concrete definition made before the
    /// loop remains visible through the phi.
    pub(super) fn apply_repeated_transfer(
        &mut self,
        transfer: &RepeatedTransfer<K>,
        may_skip: bool,
    ) {
        for (&key, &entry) in &transfer.entry_version_by_key {
            let reached = &transfer.reachable_by_entry[&entry];
            let positive_closure = self.related_definition(
                reached
                    .iter()
                    .copied()
                    .map(|version| (version, PositionRelation::whole()))
                    .collect(),
            );
            let output = if may_skip {
                self.phi(vec![entry, positive_closure])
            } else {
                positive_closure
            };
            self.bind(key, output);
        }
    }

    pub(super) fn lift_repeated_exit_states<'b>(
        &mut self,
        transfer: &RepeatedTransfer<K>,
        exits: impl IntoIterator<Item = (&'b mut BranchState<K>, &'b PathCondition)>,
    ) where
        K: 'b,
    {
        let mut exits = exits.into_iter().peekable();
        if exits.peek().is_none() {
            return;
        }
        let substitutions = transfer
            .entry_version_by_key
            .values()
            .copied()
            .map(|entry| {
                let reached = &transfer.reachable_by_entry[&entry];
                let positive = self.related_definition(
                    reached
                        .iter()
                        .copied()
                        .map(|version| (version, PositionRelation::whole()))
                        .collect(),
                );
                // Keep the zero-prior-iteration entry as a phi alternative.
                // At a retained-state root it remains an implicit latch input;
                // when a break assignment explicitly reads it, the enclosing
                // definition still turns that read into an ordinary source.
                (entry, self.phi(vec![entry, positive]))
            })
            .collect::<HashMap<_, _>>();
        let mut mapped = HashMap::default();
        for (state, condition) in exits {
            for (key, exit) in state.bindings.clone() {
                let output = self.substitute_iteration_inputs(
                    exit,
                    &substitutions,
                    transfer.version_start,
                    &mut mapped,
                );
                state.bindings.insert(key, output);
            }
            for (&key, &entry) in &transfer.entry_version_by_key {
                if state.bindings.contains_key(&key) {
                    continue;
                }
                let reached = &transfer.reachable_by_entry[&entry];
                let positive = self.related_definition(
                    reached
                        .iter()
                        .copied()
                        .map(|version| (version, PositionRelation::whole()))
                        .collect(),
                );
                let positive = self.related_definition_guarded(
                    vec![(positive, PositionRelation::default())],
                    condition,
                );
                state.bindings.insert(key, self.phi(vec![entry, positive]));
            }
        }
    }

    fn substitute_iteration_inputs(
        &mut self,
        root: VersionId,
        substitutions: &HashMap<VersionId, VersionId>,
        version_start: usize,
        mapped: &mut HashMap<VersionId, VersionId>,
    ) -> VersionId {
        let mut work = vec![(root, false)];
        while let Some((version, expanded)) = work.pop() {
            if mapped.contains_key(&version) {
                continue;
            }
            if version < version_start || matches!(self.versions[version], Version::Entry(_)) {
                mapped.insert(
                    version,
                    substitutions.get(&version).copied().unwrap_or(version),
                );
                continue;
            }
            let data = self.versions[version].clone();
            if !expanded {
                work.push((version, true));
                match data {
                    Version::Definition { sources, .. } => {
                        work.extend(sources.into_iter().map(|(source, _)| (source, false)));
                    }
                    Version::Phi(inputs) => {
                        work.extend(inputs.into_iter().map(|input| (input, false)));
                    }
                    Version::Imported { bindings, .. } => {
                        for sources in bindings.values() {
                            work.extend(sources.iter().map(|(source, _)| (*source, false)));
                        }
                    }
                    Version::Projected { source, .. } | Version::Repeated { source, .. } => {
                        work.push((source, false));
                    }
                    Version::Entry(_) => unreachable!("entries are handled above"),
                }
                continue;
            }
            let replacement = match data {
                Version::Definition { sources, condition } => self.related_definition_guarded(
                    sources
                        .into_iter()
                        .map(|(source, relation)| (mapped[&source], relation))
                        .collect(),
                    &condition,
                ),
                Version::Phi(inputs) => {
                    self.phi(inputs.into_iter().map(|input| mapped[&input]).collect())
                }
                Version::Imported {
                    graph,
                    root,
                    bindings,
                    branches,
                } => {
                    let bindings = bindings
                        .iter()
                        .map(|(&key, sources)| {
                            (
                                key,
                                sources
                                    .iter()
                                    .map(|(source, relation)| (mapped[source], *relation))
                                    .collect(),
                            )
                        })
                        .collect();
                    self.imported(graph, root, bindings, branches)
                }
                Version::Projected { source, domain } => self.projected(mapped[&source], domain),
                Version::Repeated {
                    source,
                    initial,
                    step,
                    domain,
                } => self.repeated(mapped[&source], initial, step, domain),
                Version::Entry(_) => unreachable!("entries are handled above"),
            };
            mapped.insert(version, replacement);
        }
        mapped[&root]
    }

    fn iteration_input_versions(
        &self,
        version: VersionId,
        version_start: usize,
    ) -> HashSet<VersionId> {
        let mut reached = HashSet::default();
        let mut visited = HashSet::default();
        let mut queue = VecDeque::from([version]);
        visited.insert(version);
        while let Some(current) = queue.pop_front() {
            if current < version_start || matches!(self.versions[current], Version::Entry(_)) {
                reached.insert(current);
                continue;
            }
            match &self.versions[current] {
                Version::Entry(_) => unreachable!("entries are handled above"),
                Version::Definition { sources, .. } => {
                    for (source, _) in sources {
                        if visited.insert(*source) {
                            queue.push_back(*source);
                        }
                    }
                }
                Version::Phi(inputs) => {
                    for input in inputs {
                        if visited.insert(*input) {
                            queue.push_back(*input);
                        }
                    }
                }
                Version::Imported {
                    graph,
                    root,
                    bindings,
                    ..
                } => {
                    for key in dependency_dag_external_keys(graph, *root) {
                        let Some(sources) = bindings.get(&key) else {
                            continue;
                        };
                        for (input, _) in sources {
                            if visited.insert(*input) {
                                queue.push_back(*input);
                            }
                        }
                    }
                }
                Version::Projected { source, .. } => {
                    if visited.insert(*source) {
                        queue.push_back(*source);
                    }
                }
                Version::Repeated { source, .. } => {
                    if visited.insert(*source) {
                        queue.push_back(*source);
                    }
                }
            }
        }
        reached
    }

    #[cfg(test)]
    pub(super) fn root_sources(&self, version: VersionId) -> HashSet<K> {
        self.root_source_relations(version).into_keys().collect()
    }

    #[cfg(test)]
    pub(super) fn root_source_relations(&self, version: VersionId) -> HashMap<K, PositionRelation> {
        let mut sources: HashMap<K, PositionRelation> = HashMap::default();
        for (source, relation, _) in self.root_source_relations_guarded(version) {
            sources
                .entry(source)
                .and_modify(|existing| *existing = existing.union(relation))
                .or_insert(relation);
        }
        sources
    }

    #[cfg(test)]
    pub(super) fn root_source_relations_guarded(
        &self,
        version: VersionId,
    ) -> Vec<(K, PositionRelation, PathCondition)> {
        self.root_source_relations_guarded_cached(version, &mut SourceCache::default())
    }

    pub(super) fn root_source_relations_guarded_cached(
        &self,
        version: VersionId,
        cache: &mut SourceCache<K>,
    ) -> Vec<(K, PositionRelation, PathCondition)> {
        // SSA versions form a DAG. Summarize each (version, relation) once and
        // combine branch alternatives at the join instead of re-walking the
        // same suffix for every feasible path.
        let sources = self.source_summary(version, false, cache);
        sources
            .iter()
            .map(|(&(source, relation), condition)| (source, relation, condition.clone()))
            .collect()
    }

    pub(super) fn root_source_relations_guarded_including_entry_cached(
        &self,
        version: VersionId,
        cache: &mut SourceCache<K>,
    ) -> Vec<(K, PositionRelation, PathCondition)> {
        let sources = self.source_summary(version, true, cache);
        sources
            .iter()
            .map(|(&(source, relation), condition)| (source, relation, condition.clone()))
            .collect()
    }

    pub(super) fn dependency_dag(
        &self,
        roots: &[VersionId],
        allowed: &HashSet<K>,
    ) -> DependencyDag<K>
    where
        K: Ord,
    {
        type ImportBindingIdentityKey = (usize, usize);
        let mut import_reachable_nodes: HashMap<ImportBindingIdentityKey, HashSet<usize>> =
            HashMap::default();
        let mut import_reachable_keys: HashMap<ImportBindingIdentityKey, HashSet<K>> =
            HashMap::default();
        let mut states = HashSet::default();
        let mut queue = VecDeque::new();
        for &root in roots {
            if states.insert((root, false)) {
                queue.push_back((root, false));
            }
        }
        while let Some((version, include_entry)) = queue.pop_front() {
            let mut enqueue = |state| {
                if states.insert(state) {
                    queue.push_back(state);
                }
            };
            match &self.versions[version] {
                Version::Entry(_) => {}
                Version::Definition { sources, .. } => {
                    for (source, _) in sources {
                        enqueue((*source, true));
                    }
                }
                Version::Phi(inputs) => {
                    for input in inputs {
                        enqueue((*input, include_entry));
                    }
                }
                Version::Imported {
                    graph,
                    root,
                    bindings,
                    ..
                } => {
                    let Some(root) = *root else {
                        continue;
                    };
                    let identity = (Rc::as_ptr(graph) as usize, Rc::as_ptr(bindings) as usize);
                    let visited = import_reachable_nodes.entry(identity).or_default();
                    if !visited.insert(root) {
                        continue;
                    }
                    let reachable_keys = import_reachable_keys.entry(identity).or_default();
                    let incoming = graph.incoming();
                    let mut import_queue = VecDeque::from([root]);
                    while let Some(node) = import_queue.pop_front() {
                        if let DependencyDagNode::External(key) = graph.nodes[node]
                            && reachable_keys.insert(key)
                        {
                            #[cfg(test)]
                            IMPORTED_BINDING_PROBES.set(IMPORTED_BINDING_PROBES.get() + 1);
                            for (source, _) in bindings.get(&key).into_iter().flatten() {
                                enqueue((*source, true));
                            }
                        }
                        for &edge in incoming.get(node).into_iter().flatten() {
                            let source = graph.edges[edge].source;
                            if visited.insert(source) {
                                import_queue.push_back(source);
                            }
                        }
                    }
                }
                Version::Projected { source, .. } => enqueue((*source, true)),
                Version::Repeated { source, .. } => enqueue((*source, true)),
            }
        }

        let mut nodes = Vec::new();
        let mut edges = Vec::new();
        let mut domains = Vec::new();
        let mut mapped: HashMap<(VersionId, bool), Option<usize>> = HashMap::default();
        type ImportInlineIdentityKey = (usize, usize, usize);
        type ImportInlineValueKey<K> = (
            usize,
            MappedDependencyBindingKey<K>,
            Vec<(BranchId, BranchId)>,
        );
        let mut mapped_bindings_by_identity: HashMap<
            ImportBindingIdentityKey,
            MappedDependencyBindingGroup<K>,
        > = HashMap::default();
        let mut imports_by_identity: HashMap<
            ImportInlineIdentityKey,
            Rc<RefCell<InlineDependencyDagCache>>,
        > = HashMap::default();
        let mut imports_by_value: HashMap<
            ImportInlineValueKey<K>,
            Rc<RefCell<InlineDependencyDagCache>>,
        > = HashMap::default();

        let mut ordered = states.into_iter().collect::<Vec<_>>();
        ordered.sort_unstable();
        for state @ (version, include_entry) in ordered {
            let node = match &self.versions[version] {
                Version::Entry(key) => (include_entry && allowed.contains(key)).then(|| {
                    let node = nodes.len();
                    nodes.push(DependencyDagNode::External(*key));
                    domains.push(Vec::new());
                    node
                }),
                Version::Definition { sources, condition } => {
                    let node = nodes.len();
                    nodes.push(DependencyDagNode::Internal);
                    domains.push(Vec::new());
                    for (source, relation) in sources {
                        if let Some(source) = mapped[&(*source, true)] {
                            edges.push(DependencyDagEdge {
                                source,
                                destination: node,
                                relation: *relation,
                                condition: condition.clone(),
                            });
                        }
                    }
                    Some(node)
                }
                Version::Phi(inputs) => {
                    let node = nodes.len();
                    nodes.push(DependencyDagNode::Internal);
                    domains.push(Vec::new());
                    for input in inputs {
                        if let Some(source) = mapped[&(*input, include_entry)] {
                            edges.push(DependencyDagEdge {
                                source,
                                destination: node,
                                relation: PositionRelation::default(),
                                condition: PathCondition::default(),
                            });
                        }
                    }
                    Some(node)
                }
                Version::Imported {
                    graph,
                    root,
                    bindings,
                    branches,
                } => {
                    let binding_identity =
                        (Rc::as_ptr(graph) as usize, Rc::as_ptr(bindings) as usize);
                    let mapped_binding_group = mapped_bindings_by_identity
                        .entry(binding_identity)
                        .or_insert_with(|| {
                            let mapped_bindings = import_reachable_keys
                                .get(&binding_identity)
                                .into_iter()
                                .flatten()
                                .filter_map(|&key| {
                                    #[cfg(test)]
                                    IMPORTED_BINDING_PROBES.set(IMPORTED_BINDING_PROBES.get() + 1);
                                    let sources = bindings.get(&key)?;
                                    let mut sources = sources
                                        .iter()
                                        .filter_map(|(source, relation)| {
                                            mapped
                                                .get(&(*source, true))
                                                .copied()
                                                .flatten()
                                                .map(|source| (source, *relation))
                                        })
                                        .collect::<Vec<_>>();
                                    sources.sort_unstable();
                                    Some((key, sources))
                                })
                                .collect::<MappedDependencyBindings<_>>();
                            let mut value_key = mapped_bindings
                                .iter()
                                .map(|(&key, sources)| (key, sources.clone()))
                                .collect::<MappedDependencyBindingKey<_>>();
                            value_key.sort_unstable_by_key(|(key, _)| *key);
                            MappedDependencyBindingGroup {
                                bindings: Rc::new(mapped_bindings),
                                value_key: Rc::new(value_key),
                            }
                        });
                    let mapped_bindings = Rc::clone(&mapped_binding_group.bindings);
                    let binding_value_key = Rc::clone(&mapped_binding_group.value_key);
                    let identity_key = (
                        Rc::as_ptr(graph) as usize,
                        Rc::as_ptr(bindings) as usize,
                        Rc::as_ptr(branches) as usize,
                    );
                    let inline_cache = if let Some(cache) = imports_by_identity.get(&identity_key) {
                        Rc::clone(cache)
                    } else {
                        let mut branch_key = branches
                            .mapping
                            .iter()
                            .map(|(&source, &destination)| (source, destination))
                            .collect::<Vec<_>>();
                        branch_key.sort_unstable();
                        let value_key = (
                            Rc::as_ptr(graph) as usize,
                            binding_value_key.as_ref().clone(),
                            branch_key,
                        );
                        let cache = imports_by_value
                            .entry(value_key)
                            .or_insert_with(|| {
                                Rc::new(RefCell::new(InlineDependencyDagCache::default()))
                            })
                            .clone();
                        imports_by_identity.insert(identity_key, Rc::clone(&cache));
                        cache
                    };
                    inline_dependency_dag_cached(
                        graph,
                        *root,
                        &mapped_bindings,
                        branches,
                        &mut inline_cache.borrow_mut(),
                        &mut nodes,
                        &mut edges,
                        &mut domains,
                    )
                }
                Version::Projected { source, domain } => {
                    let node = nodes.len();
                    nodes.push(DependencyDagNode::Internal);
                    domains.push(vec![*domain]);
                    if let Some(source) = mapped[&(*source, true)] {
                        edges.push(DependencyDagEdge {
                            source,
                            destination: node,
                            relation: PositionRelation::default(),
                            condition: PathCondition::default(),
                        });
                    }
                    Some(node)
                }
                Version::Repeated {
                    source,
                    initial,
                    step,
                    domain,
                } => {
                    let node = nodes.len();
                    nodes.push(DependencyDagNode::RegularTransfer);
                    domains.push(vec![*domain]);
                    if let Some(source) = mapped[&(*source, true)] {
                        edges.push(DependencyDagEdge {
                            source,
                            destination: node,
                            relation: *initial,
                            condition: PathCondition::default(),
                        });
                    }
                    edges.push(DependencyDagEdge {
                        source: node,
                        destination: node,
                        relation: *step,
                        condition: PathCondition::default(),
                    });
                    Some(node)
                }
            };
            mapped.insert(state, node);
        }

        DependencyDag {
            nodes,
            edges,
            roots: roots.iter().map(|root| mapped[&(*root, false)]).collect(),
            domains,
            incoming: OnceCell::new(),
        }
    }

    fn phi(&mut self, mut inputs: Vec<VersionId>) -> VersionId {
        inputs.sort_unstable();
        inputs.dedup();
        if inputs.len() == 1 {
            return inputs[0];
        }
        let version = self.versions.len();
        self.versions.push(Version::Phi(inputs));
        version
    }

    fn source_summary(
        &self,
        version: VersionId,
        include_entry: bool,
        cache: &mut SourceCache<K>,
    ) -> Rc<SourceMap<K>> {
        let cache_key = (version, include_entry);
        if let Some(sources) = cache.summaries.get(&cache_key) {
            return sources.clone();
        }

        let mut sources = HashMap::default();
        let start = (version, include_entry, PositionRelation::default());
        let mut reached = HashMap::default();
        reached.insert(start, PathCondition::default());
        let mut queued = HashSet::default();
        queued.insert(start);
        let mut queue = VecDeque::from([start]);

        while let Some(state @ (current, include_entry, relation)) = queue.pop_front() {
            #[cfg(test)]
            SOURCE_SUMMARY_STATE_VISITS.set(SOURCE_SUMMARY_STATE_VISITS.get() + 1);
            queued.remove(&state);
            let condition = reached[&state].clone();

            if current != version
                && let Some(cached) = cache.summaries.get(&(current, include_entry))
            {
                merge_source_summaries(&mut sources, cached, Some(&condition), Some(relation));
                continue;
            }

            let mut enqueue = |next: (VersionId, bool, PositionRelation),
                               condition: PathCondition| {
                let changed = if let Some(existing) = reached.get_mut(&next) {
                    let widened = existing.disjoin(&condition);
                    if *existing == widened {
                        false
                    } else {
                        *existing = widened;
                        true
                    }
                } else {
                    reached.insert(next, condition);
                    true
                };
                if changed && queued.insert(next) {
                    queue.push_back(next);
                }
            };

            match &self.versions[current] {
                Version::Entry(key) => {
                    if include_entry
                        && cache
                            .allowed
                            .as_ref()
                            .is_none_or(|allowed| allowed.contains(key))
                    {
                        merge_source(&mut sources, (*key, relation), condition);
                    }
                }
                Version::Definition {
                    sources,
                    condition: definition_condition,
                } => {
                    let Some(condition) = condition.conjoin_if_compatible(definition_condition)
                    else {
                        continue;
                    };
                    for (input, offset) in sources {
                        enqueue((*input, true, relation.compose(*offset)), condition.clone());
                    }
                }
                Version::Phi(inputs) => {
                    for input in inputs {
                        enqueue((*input, include_entry, relation), condition.clone());
                    }
                }
                Version::Imported {
                    graph,
                    root,
                    bindings,
                    branches,
                } => {
                    for (key, imported_relation, imported_condition) in
                        dependency_dag_external_sources(graph, *root)
                    {
                        let imported_condition = branches.remap(&imported_condition);
                        let Some(condition) = condition.conjoin_if_compatible(&imported_condition)
                        else {
                            continue;
                        };
                        for (source, binding_relation) in bindings.get(&key).into_iter().flatten() {
                            enqueue(
                                (
                                    *source,
                                    true,
                                    relation
                                        .compose(*binding_relation)
                                        .compose(imported_relation),
                                ),
                                condition.clone(),
                            );
                        }
                    }
                }
                Version::Projected { source, .. } => {
                    enqueue((*source, true, relation), condition);
                }
                Version::Repeated {
                    source,
                    initial,
                    step,
                    ..
                } => {
                    let relation = widen_repeated_axis(relation.compose(*initial), *step);
                    enqueue((*source, true, relation), condition);
                }
            }
        }
        let sources = Rc::new(sources);
        cache.summaries.insert(cache_key, sources.clone());
        sources
    }
}

fn dependency_dag_external_sources<K>(
    graph: &DependencyDag<K>,
    root: Option<usize>,
) -> Vec<(K, PositionRelation, PathCondition)>
where
    K: Copy + Eq + Hash,
{
    let Some(root) = root else {
        return Vec::new();
    };
    let incoming = graph.incoming();
    let mut reached = HashMap::default();
    let start = (root, PositionRelation::default());
    reached.insert(start, PathCondition::default());
    let mut queue = VecDeque::from([start]);
    let mut queued = [start].into_iter().collect::<HashSet<_>>();
    let mut sources: HashMap<(K, PositionRelation), PathCondition> = HashMap::default();
    while let Some(state @ (node, relation)) = queue.pop_front() {
        queued.remove(&state);
        let condition = reached[&state].clone();
        // A regular-transfer self-edge denotes any finite number of strides
        // admitted by this node's domain. Flat source summaries cannot retain
        // that arithmetic progression, so widen only the repeated axis and
        // traverse every non-self edge once. Positional consumers import the
        // graph itself and therefore never take this fallback. Arbitrary
        // self-edges retain their ordinary graph semantics.
        let regular_transfer = matches!(graph.nodes[node], DependencyDagNode::RegularTransfer);
        let relation = if regular_transfer {
            incoming
                .get(node)
                .into_iter()
                .flatten()
                .filter_map(|&edge| graph.edges.get(edge))
                .filter(|edge| edge.source == node)
                .fold(relation, |relation, edge| {
                    widen_repeated_axis(relation, edge.relation)
                })
        } else {
            relation
        };
        if let DependencyDagNode::External(key) = graph.nodes[node] {
            merge_source(&mut sources, (key, relation), condition);
            continue;
        }
        for edge in incoming
            .get(node)
            .into_iter()
            .flatten()
            .filter_map(|&edge| graph.edges.get(edge))
        {
            if regular_transfer && edge.source == node {
                continue;
            }
            let Some(next_condition) = condition.conjoin_if_compatible(&edge.condition) else {
                continue;
            };
            let next = (edge.source, relation.compose(edge.relation));
            let changed = if let Some(existing) = reached.get_mut(&next) {
                let merged = existing.disjoin(&next_condition);
                if *existing == merged {
                    false
                } else {
                    *existing = merged;
                    true
                }
            } else {
                reached.insert(next, next_condition);
                true
            };
            if changed && queued.insert(next) {
                queue.push_back(next);
            }
        }
    }
    sources
        .into_iter()
        .map(|((key, relation), condition)| (key, relation, condition))
        .collect()
}

fn dependency_dag_external_keys<K>(graph: &DependencyDag<K>, root: Option<usize>) -> HashSet<K>
where
    K: Copy + Eq + Hash,
{
    let Some(root) = root else {
        return HashSet::default();
    };
    let incoming = graph.incoming();
    let mut visited = HashSet::from_iter([root]);
    let mut queue = VecDeque::from([root]);
    let mut keys = HashSet::default();
    while let Some(node) = queue.pop_front() {
        if let DependencyDagNode::External(key) = graph.nodes[node] {
            keys.insert(key);
        }
        for &edge in incoming.get(node).into_iter().flatten() {
            let source = graph.edges[edge].source;
            if visited.insert(source) {
                queue.push_back(source);
            }
        }
    }
    keys
}

type MappedDependencyBindings<K> = HashMap<K, Vec<(usize, PositionRelation)>>;
type MappedDependencyBindingKey<K> = Vec<(K, Vec<(usize, PositionRelation)>)>;

struct MappedDependencyBindingGroup<K> {
    bindings: Rc<MappedDependencyBindings<K>>,
    value_key: Rc<MappedDependencyBindingKey<K>>,
}

#[derive(Default)]
struct InlineDependencyDagCache {
    mapped: HashMap<usize, usize>,
}

#[cfg(test)]
fn inline_dependency_dag<K>(
    graph: &DependencyDag<K>,
    root: Option<usize>,
    bindings: &HashMap<K, Vec<(usize, PositionRelation)>>,
    branches: &BranchRemapper,
    nodes: &mut Vec<DependencyDagNode<K>>,
    edges: &mut Vec<DependencyDagEdge>,
    domains: &mut Vec<Vec<PositionDomain>>,
) -> Option<usize>
where
    K: Copy + Eq + Hash,
{
    inline_dependency_dag_cached(
        graph,
        root,
        bindings,
        branches,
        &mut InlineDependencyDagCache::default(),
        nodes,
        edges,
        domains,
    )
}

#[allow(clippy::too_many_arguments)]
fn inline_dependency_dag_cached<K>(
    graph: &DependencyDag<K>,
    root: Option<usize>,
    bindings: &HashMap<K, Vec<(usize, PositionRelation)>>,
    branches: &BranchRemapper,
    cache: &mut InlineDependencyDagCache,
    nodes: &mut Vec<DependencyDagNode<K>>,
    edges: &mut Vec<DependencyDagEdge>,
    domains: &mut Vec<Vec<PositionDomain>>,
) -> Option<usize>
where
    K: Copy + Eq + Hash,
{
    let root = root?;
    if let Some(&root) = cache.mapped.get(&root) {
        return Some(root);
    }
    let incoming = graph.incoming();
    let mut retained = HashSet::default();
    let mut queue = VecDeque::from([root]);
    let mut retained_nodes = vec![root];
    retained.insert(root);
    while let Some(node) = queue.pop_front() {
        #[cfg(test)]
        INLINE_DEPENDENCY_NODE_VISITS.set(INLINE_DEPENDENCY_NODE_VISITS.get() + 1);
        for &edge in incoming.get(node).into_iter().flatten() {
            let source = graph.edges[edge].source;
            if !cache.mapped.contains_key(&source) && retained.insert(source) {
                queue.push_back(source);
                retained_nodes.push(source);
            }
        }
    }
    retained_nodes.sort_unstable();

    for &child in &retained_nodes {
        let child_node = &graph.nodes[child];
        let node = nodes.len();
        nodes.push(match child_node {
            DependencyDagNode::RegularTransfer => DependencyDagNode::RegularTransfer,
            DependencyDagNode::External(_) | DependencyDagNode::Internal => {
                DependencyDagNode::Internal
            }
        });
        domains.push(graph.domains[child].clone());
        cache.mapped.insert(child, node);
        if let DependencyDagNode::External(key) = child_node {
            for &(source, relation) in bindings.get(key).into_iter().flatten() {
                edges.push(DependencyDagEdge {
                    source,
                    destination: node,
                    relation,
                    condition: PathCondition::default(),
                });
            }
        }
    }
    for &child in &retained_nodes {
        for &edge in incoming.get(child).into_iter().flatten() {
            let edge = &graph.edges[edge];
            let (Some(&source), Some(&destination)) = (
                cache.mapped.get(&edge.source),
                cache.mapped.get(&edge.destination),
            ) else {
                continue;
            };
            edges.push(DependencyDagEdge {
                source,
                destination,
                relation: edge.relation,
                condition: branches.remap(&edge.condition),
            });
        }
    }
    cache.mapped.get(&root).copied()
}

fn merge_source<K>(
    destination: &mut SourceMap<K>,
    key: (K, PositionRelation),
    condition: PathCondition,
) where
    K: Copy + Eq + Hash,
{
    destination
        .entry(key)
        .and_modify(|existing| *existing = existing.disjoin(&condition))
        .or_insert(condition);
}

fn merge_source_summaries<K>(
    destination: &mut SourceMap<K>,
    sources: &SourceMap<K>,
    guard: Option<&PathCondition>,
    prefix: Option<PositionRelation>,
) where
    K: Copy + Eq + Hash,
{
    for (&(source, relation), condition) in sources {
        let key = (
            source,
            prefix.map_or(relation, |prefix| prefix.compose(relation)),
        );
        let condition = if let Some(guard) = guard {
            let Some(condition) = condition.conjoin_if_compatible(guard) else {
                continue;
            };
            condition
        } else {
            condition.clone()
        };
        merge_source(destination, key, condition);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn imported_roots_visit_only_their_reachable_bindings() {
        const COUNT: usize = 256;
        let graph = Rc::new(DependencyDag::<u32> {
            nodes: (0..COUNT as u32).map(DependencyDagNode::External).collect(),
            edges: Vec::new(),
            roots: (0..COUNT).map(Some).collect(),
            domains: vec![Vec::new(); COUNT],
            incoming: OnceCell::new(),
        });
        let mut ssa = SsaStore::default();
        let bindings = Rc::new(
            (0..COUNT as u32)
                .map(|key| (key, vec![(ssa.read(key), PositionRelation::default())]))
                .collect::<HashMap<_, _>>(),
        );
        let branches = SsaStore::<u32>::branch_remapper(HashMap::default());
        let roots = (0..COUNT)
            .map(|root| {
                ssa.imported_shared(
                    Rc::clone(&graph),
                    Some(root),
                    Rc::clone(&bindings),
                    Rc::clone(&branches),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(Rc::strong_count(&bindings), COUNT + 1);
        let allowed = (0..COUNT as u32).collect::<HashSet<_>>();

        IMPORTED_BINDING_PROBES.set(0);
        let dependency = ssa.dependency_dag(&roots, &allowed);
        assert_eq!(dependency.roots.len(), COUNT);
        assert!(
            IMPORTED_BINDING_PROBES.get() <= COUNT * 4,
            "each independent imported root should inspect only its own binding"
        );
    }

    #[test]
    fn inline_dependency_dag_indexes_incoming_edges_once() {
        const COUNT: usize = 4_096;
        let graph = DependencyDag::<u32> {
            nodes: vec![DependencyDagNode::Internal; COUNT],
            edges: (0..COUNT - 1)
                .map(|source| DependencyDagEdge {
                    source,
                    destination: source + 1,
                    relation: PositionRelation::default(),
                    condition: PathCondition::default(),
                })
                .collect(),
            roots: vec![Some(COUNT - 1)],
            domains: vec![Vec::new(); COUNT],
            incoming: OnceCell::new(),
        };
        let bindings: HashMap<u32, Vec<(usize, PositionRelation)>> = HashMap::default();
        let branches = BranchRemapper::new(HashMap::default());
        let mut nodes = Vec::new();
        let mut edges = Vec::new();
        let mut domains = Vec::new();

        INLINE_DEPENDENCY_EDGE_PROBES.set(0);
        let root = inline_dependency_dag(
            &graph,
            graph.roots[0],
            &bindings,
            &branches,
            &mut nodes,
            &mut edges,
            &mut domains,
        );

        assert_eq!(root, Some(COUNT - 1));
        assert_eq!(nodes.len(), COUNT);
        assert_eq!(edges.len(), COUNT - 1);
        // The former full-edge scan examined every edge once per retained node.
        // Building the incoming index must examine each edge exactly once.
        assert_eq!(INLINE_DEPENDENCY_EDGE_PROBES.get(), COUNT - 1);
    }

    #[test]
    fn imported_shared_chain_roots_inline_each_prefix_once() {
        const COUNT: usize = 256;
        let graph = Rc::new(DependencyDag::<u32> {
            nodes: std::iter::once(DependencyDagNode::External(0))
                .chain(std::iter::repeat_n(DependencyDagNode::Internal, COUNT - 1))
                .collect(),
            edges: (0..COUNT - 1)
                .map(|source| DependencyDagEdge {
                    source,
                    destination: source + 1,
                    relation: PositionRelation::default(),
                    condition: PathCondition::default(),
                })
                .collect(),
            roots: (0..COUNT).map(Some).collect(),
            domains: vec![Vec::new(); COUNT],
            incoming: OnceCell::new(),
        });
        let mut ssa = SsaStore::default();
        let source = ssa.read(0);
        let bindings = Rc::new(
            [(0, vec![(source, PositionRelation::default())])]
                .into_iter()
                .collect(),
        );
        let branches = SsaStore::<u32>::branch_remapper(HashMap::default());
        let roots = (0..COUNT)
            .map(|root| {
                ssa.imported_shared(
                    Rc::clone(&graph),
                    Some(root),
                    Rc::clone(&bindings),
                    Rc::clone(&branches),
                )
            })
            .collect::<Vec<_>>();

        INLINE_DEPENDENCY_NODE_VISITS.set(0);
        let allowed = [0].into_iter().collect();
        let dependency = ssa.dependency_dag(&roots, &allowed);

        assert_eq!(dependency.roots.len(), COUNT);
        assert_eq!(dependency.nodes.len(), COUNT + 1);
        assert_eq!(dependency.edges.len(), COUNT);
        assert!(
            INLINE_DEPENDENCY_NODE_VISITS.get() <= COUNT * 2,
            "shared prefixes should be visited at most once plus one root lookup each"
        );
    }

    #[test]
    fn structural_dependency_cache_visits_a_shared_chain_once() {
        const COUNT: usize = 4_096;
        let mut ssa = SsaStore::default();
        let mut current = ssa.read(0_u32);
        let mut versions = vec![current];
        for _ in 1..COUNT {
            current = ssa.definition(vec![current]);
            versions.push(current);
        }
        assert!(!ssa.has_structural_dependency(current));

        STRUCTURAL_DEPENDENCY_VERSION_VISITS.set(0);
        let mut cache = HashMap::default();
        for &version in versions.iter().rev() {
            assert!(!ssa.has_structural_dependency_cached(version, &mut cache));
        }
        assert_eq!(cache.len(), COUNT);
        assert_eq!(STRUCTURAL_DEPENDENCY_VERSION_VISITS.get(), COUNT);

        let projected = ssa.projected(
            current,
            PositionDomain {
                array_start: 0,
                array_length: 1,
                packed_start: 0,
                packed_length: 1,
            },
        );
        assert!(ssa.has_structural_dependency_cached(projected, &mut cache));
        assert_eq!(STRUCTURAL_DEPENDENCY_VERSION_VISITS.get(), COUNT + 1);
    }

    #[test]
    fn persistent_paths_and_remap_caches_are_linear_and_isolated() {
        const COUNT: usize = 100_000;
        let mut condition = PathCondition::default();
        let mut source_branches = Vec::with_capacity(COUNT);
        for local in 0..COUNT {
            let branch = BranchId::new(1, local, 2);
            source_branches.push(branch);
            condition = condition.with_choice(branch, local % 2);
        }
        assert_eq!(condition.arena.borrow().nodes.len(), COUNT + 1);
        assert!(
            condition.arena.borrow().nodes[condition.node]
                .materialized
                .get()
                .is_none()
        );

        let first_mapping = source_branches
            .iter()
            .enumerate()
            .map(|(local, branch)| (*branch, BranchId::new(2, local, 2)))
            .collect();
        let second_mapping = source_branches
            .iter()
            .enumerate()
            .map(|(local, branch)| (*branch, BranchId::new(3, local, 2)))
            .collect();
        let first = BranchRemapper::new(first_mapping);
        let second = BranchRemapper::new(second_mapping);
        let first_remapped = first.remap(&condition);
        let first_again = first.remap(&condition);
        let second_remapped = second.remap(&condition);

        assert!(Rc::ptr_eq(&first_remapped.arena, &first_again.arena));
        assert_eq!(first_remapped.node, first_again.node);
        assert!(!Rc::ptr_eq(&first_remapped.arena, &second_remapped.arena));
        assert_eq!(first.cache.borrow().len(), COUNT + 1);
        assert_eq!(second.cache.borrow().len(), COUNT + 1);
        assert!(
            condition.arena.borrow().nodes[condition.node]
                .materialized
                .get()
                .is_none()
        );
    }

    #[test]
    fn remap_cache_retains_the_source_arena_identity() {
        let source = BranchId::new(1, 0, 2);
        let destination = BranchId::new(2, 0, 2);
        let condition = PathCondition::default().with_choice(source, 1);
        let source_arena = Rc::downgrade(&condition.arena);
        let remapper = BranchRemapper::new([(source, destination)].into_iter().collect());

        remapper.remap(&condition);
        drop(condition);
        assert!(source_arena.upgrade().is_some());

        drop(remapper);
        assert!(source_arena.upgrade().is_none());
    }

    #[test]
    fn partially_overlapping_arm_sets_are_intersected_exactly() {
        let branch = BranchId::new(1, 0, 4);
        let extra = BranchId::new(1, 1, 2);
        let left = PathCondition::default().with_choice_range(branch, 0, 2);
        let right = PathCondition::default()
            .with_choice_range(branch, 1, 3)
            .with_choice(extra, 1);
        let expected = PathCondition::default()
            .with_choice_range(branch, 1, 2)
            .with_choice(extra, 1);

        assert_eq!(left.conjoin_if_compatible(&right), Some(expected));
    }

    #[test]
    fn imported_roots_share_one_branch_remap_cache() {
        let source = BranchId::new(1, 0, 2);
        let destination = BranchId::new(2, 0, 2);
        let remapper =
            SsaStore::<u8>::branch_remapper([(source, destination)].into_iter().collect());
        let graph = Rc::new(DependencyDag::<u8> {
            nodes: Vec::new(),
            edges: Vec::new(),
            roots: vec![None, None],
            domains: Vec::new(),
            incoming: OnceCell::new(),
        });
        let mut ssa = SsaStore::default();
        let first = ssa.imported(graph.clone(), None, HashMap::default(), remapper.clone());
        let second = ssa.imported(graph, None, HashMap::default(), remapper);
        let (
            Version::Imported {
                branches: first, ..
            },
            Version::Imported {
                branches: second, ..
            },
        ) = (&ssa.versions[first], &ssa.versions[second])
        else {
            panic!("both versions are imported roots");
        };
        assert!(Rc::ptr_eq(first, second));

        let condition = PathCondition::default().with_choice(source, 1);
        first.remap(&condition);
        let cached = first.cache.borrow().len();
        second.remap(&condition);
        assert_eq!(second.cache.borrow().len(), cached);
    }

    #[test]
    fn remap_cache_maps_a_shared_materialized_prefix_once() {
        let prefix_source = BranchId::new(1, 0, 2);
        let suffix_a_source = BranchId::new(1, 1, 2);
        let suffix_b_source = BranchId::new(1, 2, 2);
        let prefix_destination = BranchId::new(2, 0, 2);
        let suffix_a_destination = BranchId::new(2, 1, 2);
        let suffix_b_destination = BranchId::new(2, 2, 2);
        let prefix = PathCondition::from_constraints(vec![BranchConstraint {
            branch: prefix_source,
            allowed: ArmSet::range(0, 1),
        }]);
        let suffix_a = prefix.with_choice(suffix_a_source, 1);
        let suffix_b = prefix.with_choice(suffix_b_source, 0);
        let remapper = BranchRemapper::new(
            [
                (prefix_source, prefix_destination),
                (suffix_a_source, suffix_a_destination),
                (suffix_b_source, suffix_b_destination),
            ]
            .into_iter()
            .collect(),
        );

        let remapped_a = remapper.remap(&suffix_a);
        let cached_after_a = remapper.cache.borrow().len();
        let remapped_b = remapper.remap(&suffix_b);
        assert_eq!(cached_after_a + 1, remapper.cache.borrow().len());
        assert_eq!(
            PathCondition::collect_branches([&remapped_a, &remapped_b]),
            vec![
                prefix_destination,
                suffix_a_destination,
                suffix_b_destination,
            ]
        );
    }

    #[test]
    fn definition_reports_live_on_entry_source() {
        let mut ssa = SsaStore::default();
        let source = ssa.read("source");
        let destination = ssa.definition(vec![source]);

        let expected = ["source"].into_iter().collect::<HashSet<_>>();
        assert_eq!(ssa.root_sources(destination), expected);
    }

    #[test]
    fn related_definition_preserves_source_relation() {
        let mut ssa = SsaStore::default();
        let source = ssa.read("source");
        let destination = ssa.related_definition(vec![(source, PositionRelation::default())]);

        assert_eq!(
            ssa.root_source_relations(destination).get("source"),
            Some(&PositionRelation::default())
        );
    }

    #[test]
    fn positional_offsets_compose_through_definitions() {
        let mut ssa = SsaStore::default();
        let source = ssa.read("source");
        let first = ssa.related_definition(vec![(
            source,
            PositionRelation {
                array: Some(3),
                packed: Some(-2),
            },
        )]);
        let destination = ssa.related_definition(vec![(
            first,
            PositionRelation {
                array: Some(-1),
                packed: Some(5),
            },
        )]);

        assert_eq!(
            ssa.root_source_relations(destination).get("source"),
            Some(&PositionRelation {
                array: Some(2),
                packed: Some(3),
            })
        );
    }

    #[test]
    fn regular_transfer_is_constant_size_and_flattening_widens_only_its_axis() {
        let mut ssa = SsaStore::default();
        let source = ssa.read("source");
        let repeated = ssa.repeated(
            source,
            PositionRelation::default(),
            PositionRelation {
                array: Some(0),
                packed: Some(4),
            },
            PositionDomain {
                array_start: 0,
                array_length: 1,
                packed_start: 0,
                packed_length: 800_000,
            },
        );

        let allowed = ["source"].into_iter().collect::<HashSet<_>>();
        let graph = ssa.dependency_dag(&[repeated], &allowed);
        assert_eq!(graph.nodes.len(), 2);
        assert_eq!(graph.edges.len(), 2);
        assert!(graph.edges.iter().any(|edge| {
            edge.source == edge.destination
                && edge.relation
                    == PositionRelation {
                        array: Some(0),
                        packed: Some(4),
                    }
        }));
        assert_eq!(
            ssa.root_source_relations(repeated).get("source"),
            Some(&PositionRelation {
                array: Some(0),
                packed: None,
            })
        );
    }

    #[test]
    fn flat_summary_does_not_discard_an_arbitrary_self_loop() {
        let graph = DependencyDag {
            nodes: vec![
                DependencyDagNode::External("source"),
                DependencyDagNode::Internal,
            ],
            edges: vec![
                DependencyDagEdge {
                    source: 0,
                    destination: 1,
                    relation: PositionRelation::default(),
                    condition: PathCondition::default(),
                },
                DependencyDagEdge {
                    source: 1,
                    destination: 1,
                    relation: PositionRelation::whole(),
                    condition: PathCondition::default(),
                },
            ],
            roots: vec![Some(1)],
            domains: vec![Vec::new(), Vec::new()],
            incoming: OnceCell::new(),
        };

        let sources = dependency_dag_external_sources(&graph, Some(1));
        assert!(sources.iter().any(|(key, relation, _)| {
            *key == "source" && *relation == PositionRelation::default()
        }));
        assert!(sources.iter().any(|(key, relation, _)| {
            *key == "source" && *relation == PositionRelation::whole()
        }));
    }

    #[test]
    fn conflicting_offsets_only_widen_the_conflicting_axis() {
        let mut ssa = SsaStore::default();
        let source = ssa.read("source");
        let destination = ssa.related_definition(vec![
            (source, PositionRelation::default()),
            (
                source,
                PositionRelation {
                    array: Some(0),
                    packed: Some(1),
                },
            ),
        ]);

        assert_eq!(
            ssa.root_source_relations(destination).get("source"),
            Some(&PositionRelation {
                array: Some(0),
                packed: None,
            })
        );
    }

    #[test]
    fn whole_dependency_dominates_a_positional_path() {
        let mut ssa = SsaStore::default();
        let source = ssa.read("source");
        let destination = ssa.related_definition(vec![
            (source, PositionRelation::default()),
            (source, PositionRelation::whole()),
        ]);

        assert_eq!(
            ssa.root_source_relations(destination).get("source"),
            Some(&PositionRelation::whole())
        );
    }

    #[test]
    fn retained_live_on_entry_is_not_a_combinational_read() {
        let mut ssa = SsaStore::default();
        let retained = ssa.read("destination");
        let checkpoint = ssa.checkpoint();
        let assigned = ssa.definition(Vec::new());
        ssa.bind("destination", assigned);
        let branch = ssa.capture_and_rollback(checkpoint);

        ssa.merge(&[BranchState::unchanged(), branch]);

        let merged = ssa.read("destination");
        assert_ne!(merged, retained);
        assert!(ssa.root_sources(merged).is_empty());
    }

    #[test]
    fn weak_bind_retains_entry_until_a_later_explicit_read() {
        let mut ssa = SsaStore::<u8>::default();
        let replacement = ssa.definition(Vec::new());
        ssa.weak_bind(0, replacement);

        let retained = ssa.read(0);
        assert!(ssa.root_sources(retained).is_empty());

        let observed = ssa.definition(vec![retained]);
        let expected: HashSet<_> = [0].into_iter().collect();
        assert_eq!(ssa.root_sources(observed), expected);
    }

    #[test]
    fn rollback_discards_current_bindings_without_discarding_versions() {
        let mut ssa = SsaStore::default();
        let checkpoint = ssa.checkpoint();
        let source = ssa.read("source");
        let definition = ssa.definition(vec![source]);
        ssa.bind("destination", definition);

        let _ = ssa.capture_and_rollback(checkpoint);
        let restored = ssa.read("destination");

        let expected = ["source"].into_iter().collect::<HashSet<_>>();
        assert_eq!(ssa.root_sources(definition), expected);
        assert!(ssa.root_sources(restored).is_empty());
    }

    #[test]
    fn branch_state_contains_only_keys_changed_since_checkpoint() {
        let mut ssa = SsaStore::default();
        for key in 0..1_000 {
            let version = ssa.definition(Vec::new());
            ssa.bind(key, version);
        }

        let checkpoint = ssa.checkpoint();
        let version = ssa.definition(Vec::new());
        ssa.bind(500, version);
        let branch = ssa.capture_and_rollback(checkpoint);

        assert_eq!(branch.bindings.len(), 1);
        assert_eq!(branch.bindings[&500], version);
    }

    #[test]
    fn state_revision_aggregates_cumulative_unique_writes_linearly() {
        const COUNT: usize = 10_000;

        reset_flow_scaling_counters();
        let mut ssa = SsaStore::default();
        let checkpoint = ssa.checkpoint();
        let revision = ssa.begin_state_revision(checkpoint);
        for key in 0..COUNT {
            let version = ssa.definition(Vec::new());
            ssa.bind(key, version);
            ssa.record_state_revision_exit(revision);
        }

        let exits = ssa.finish_state_revision(revision);
        assert_eq!(exits.bindings.len(), COUNT);
        assert_eq!(REVISION_EVENT_VISITS.get(), 2 * COUNT);
        assert_eq!(REVISION_CANDIDATE_INPUTS.get(), 2 * COUNT - 1);

        let _ = ssa.capture_and_rollback(checkpoint);
        ssa.merge([&exits]);
        assert_eq!(ssa.current.len(), COUNT);
    }

    #[test]
    fn state_revision_observes_rollback_between_sibling_exits() {
        let mut ssa = SsaStore::default();
        let function = ssa.checkpoint();
        let revision = ssa.begin_state_revision(function);

        let branch = ssa.checkpoint();
        let source = ssa.read("source");
        let changed = ssa.definition(vec![source]);
        ssa.bind("destination", changed);
        ssa.record_state_revision_exit(revision);
        let _ = ssa.capture_and_rollback(branch);
        ssa.record_state_revision_exit(revision);

        let exits = ssa.finish_state_revision(revision);
        let _ = ssa.capture_and_rollback(function);
        ssa.merge([&exits]);

        let destination = ssa.read("destination");
        assert_eq!(
            ssa.root_sources(destination),
            ["source"].into_iter().collect()
        );
    }

    #[test]
    fn enclosing_revision_ignores_nested_exit_markers() {
        let mut ssa = SsaStore::default();
        let outer_checkpoint = ssa.checkpoint();
        let outer = ssa.begin_state_revision(outer_checkpoint);

        let inner_checkpoint = ssa.checkpoint();
        let inner = ssa.begin_state_revision(inner_checkpoint);
        let changed = ssa.definition(Vec::new());
        ssa.bind("inner", changed);
        ssa.record_state_revision_exit(inner);
        let _ = ssa.finish_state_revision(inner);
        let _ = ssa.capture_and_rollback(inner_checkpoint);

        ssa.record_state_revision_exit(outer);
        let exits = ssa.finish_state_revision(outer);
        assert!(exits.bindings.is_empty());
        let _ = ssa.capture_and_rollback(outer_checkpoint);
    }

    #[test]
    fn nested_rollback_preserves_the_outer_transaction() {
        let mut ssa = SsaStore::default();
        let base = ssa.definition(Vec::new());
        ssa.bind("outer", base);

        let outer_checkpoint = ssa.checkpoint();
        let outer_definition = ssa.definition(Vec::new());
        ssa.bind("outer", outer_definition);

        let inner_checkpoint = ssa.checkpoint();
        let inner_definition = ssa.definition(Vec::new());
        ssa.bind("inner", inner_definition);
        let inner_state = ssa.capture_and_rollback(inner_checkpoint);

        assert_eq!(ssa.read("outer"), outer_definition);
        assert_ne!(ssa.read("inner"), inner_definition);

        ssa.merge(&[BranchState::unchanged(), inner_state]);
        let merged_inner = ssa.read("inner");
        let outer_state = ssa.capture_and_rollback(outer_checkpoint);

        assert_eq!(ssa.read("outer"), base);
        assert_ne!(ssa.read("inner"), merged_inner);
        assert_eq!(outer_state.bindings["outer"], outer_definition);
        assert_eq!(outer_state.bindings["inner"], merged_inner);
    }

    #[test]
    fn merge_cost_tracks_sparse_bindings_not_branch_key_product() {
        let mut ssa = SsaStore::default();
        let mut states = Vec::new();
        for key in 0..10_000 {
            let version = ssa.definition(Vec::new());
            let mut bindings = HashMap::default();
            bindings.insert(key, version);
            states.push(BranchState { bindings });
        }

        ssa.merge(&states);

        assert_eq!(ssa.current.len(), states.len());
    }

    #[test]
    fn repeated_transfer_closes_dependencies_across_runtime_iterations() {
        let mut ssa = SsaStore::default();
        let checkpoint = ssa.checkpoint();

        let previous_middle = ssa.read("middle");
        let last = ssa.definition(vec![previous_middle]);
        ssa.weak_bind("last", last);

        let first = ssa.read("first");
        let middle = ssa.definition(vec![first]);
        ssa.weak_bind("middle", middle);

        let iteration = ssa.capture_and_rollback(checkpoint);
        let transfer = ssa.prepare_repeated_transfer(&iteration, checkpoint);
        ssa.apply_repeated_transfer(&transfer, false);

        let last = ssa.read("last");
        let sources = ssa.root_sources(last);
        assert!(sources.contains("first"));
    }

    #[test]
    fn repeated_break_preserves_a_direct_break_transfer() {
        let mut ssa = SsaStore::default();
        let checkpoint = ssa.checkpoint();
        let source = ssa.read("source");
        let output = ssa.definition(vec![source]);
        ssa.bind("output", output);
        let mut breaks = [(
            ssa.capture_and_rollback(checkpoint),
            PathCondition::default(),
        )];

        let transfer = ssa.prepare_repeated_transfer(&BranchState::empty(), checkpoint);
        ssa.lift_repeated_exit_states(
            &transfer,
            breaks
                .iter_mut()
                .map(|(state, condition)| (state, &*condition)),
        );
        ssa.merge([&breaks[0].0]);

        let output = ssa.read("output");
        assert_eq!(ssa.root_sources(output), ["source"].into_iter().collect());
    }

    #[test]
    fn repeated_break_retains_continuing_state_for_an_unwritten_key() {
        let mut ssa = SsaStore::default();
        let checkpoint = ssa.checkpoint();
        let source = ssa.read("source");
        let first = ssa.definition(vec![source]);
        ssa.bind("value", first);
        let continuing = ssa.capture_and_rollback(checkpoint);

        let mut breaks = [(BranchState::empty(), PathCondition::default())];
        let transfer = ssa.prepare_repeated_transfer(&continuing, checkpoint);
        ssa.lift_repeated_exit_states(
            &transfer,
            breaks
                .iter_mut()
                .map(|(state, condition)| (state, &*condition)),
        );
        ssa.merge([&breaks[0].0]);

        let value = ssa.read("value");
        assert!(ssa.root_sources(value).contains("source"));
    }

    #[test]
    fn root_source_walk_does_not_use_the_native_stack() {
        const COUNT: usize = 100_000;

        let mut ssa = SsaStore::default();
        let mut version = ssa.read("source");
        for _ in 0..COUNT {
            version = ssa.definition(vec![version]);
        }

        let expected = ["source"].into_iter().collect();
        assert_eq!(ssa.root_sources(version), expected);
    }

    #[test]
    fn opposite_arms_of_one_branch_are_incompatible() {
        let branch = BranchId::new(1, 0, 2);
        let true_path = PathCondition::default().with_choice(branch, 0);
        let false_path = PathCondition::default().with_choice(branch, 1);

        assert!(true_path.conjoin_if_compatible(&false_path).is_none());
    }

    #[test]
    fn expression_branch_namespaces_do_not_alias_procedures_or_calls() {
        let procedure = BranchId::new(7, 3, 2);
        let expression = BranchId::expression(7, 3, 2);
        let call = BranchId::expression_call(7, 3, 0, 2);

        assert_ne!(procedure, expression);
        assert_ne!(procedure, call);
        assert_ne!(expression, call);
    }

    #[test]
    fn arms_of_distinct_branches_are_compatible() {
        let first = PathCondition::default().with_choice(BranchId::new(1, 0, 2), 0);
        let second = PathCondition::default().with_choice(BranchId::new(1, 1, 2), 1);

        let combined = first
            .conjoin_if_compatible(&second)
            .expect("distinct branches can execute on the same path");
        assert!(first.covers(&combined));
        assert!(second.covers(&combined));
    }

    #[test]
    fn large_contiguous_arm_sets_remain_compact() {
        let branch = BranchId::new(1, 0, 1_000_001);
        let lower = PathCondition::default().with_choice_range(branch, 0, 500_000);
        let upper = PathCondition::default().with_choice_range(branch, 500_000, 1_000_001);

        assert_eq!(lower.disjoin(&upper), PathCondition::default());
        assert!(lower.conjoin_if_compatible(&upper).is_none());
    }

    #[test]
    fn sequential_branch_joins_do_not_enumerate_path_combinations() {
        let mut ssa = SsaStore::default();
        let source = ssa.read("source");
        let mut value = source;
        for local in 0..128 {
            let branch = BranchId::new(1, local, 2);
            let left = ssa.definition_guarded(
                vec![value],
                &PathCondition::default().with_choice(branch, 0),
            );
            let right = ssa.definition_guarded(
                vec![value],
                &PathCondition::default().with_choice(branch, 1),
            );
            value = ssa.phi(vec![left, right]);
        }

        assert_eq!(
            ssa.root_source_relations_guarded(value),
            vec![(
                "source",
                PositionRelation::whole(),
                PathCondition::default()
            )]
        );
    }
}
