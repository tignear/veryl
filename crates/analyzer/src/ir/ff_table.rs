use crate::conv::Context;
use crate::ir::VarId;
use crate::ir::declaration::Declaration;
use crate::ir::variable::FlatIndexSet;
use crate::ir::write_count::{UnsafeSelfReads, unsafe_self_reads};
use crate::{HashMap, HashSet};

#[cfg(test)]
thread_local! {
    static CANDIDATE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(super) fn reset_candidate_visits() {
    CANDIDATE_VISITS.set(0);
}

#[cfg(test)]
pub(super) fn candidate_visits() -> usize {
    CANDIDATE_VISITS.get()
}

#[cfg(test)]
fn count_candidate_visit() {
    CANDIDATE_VISITS.set(CANDIDATE_VISITS.get() + 1);
}

#[cfg(not(test))]
fn count_candidate_visit() {}

/// A compact packed-bit access. `Unknown` conservatively covers every bit.
///
/// Keeping this as an interval avoids allocating a dense `BigUint` whose
/// size grows with the selected bit number while walking constant loops.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PackedMask {
    Range { high: usize, low: usize },
    Unknown,
}

impl PackedMask {
    pub fn from_range(range: Option<(usize, usize)>) -> Self {
        match range {
            Some((high, low)) => Self::Range { high, low },
            None => Self::Unknown,
        }
    }
}

/// LHS of an assignment: `(VarId, array element index, packed access)`.
/// `None` array index = dynamic.
pub type AssignTarget = (VarId, Option<usize>, PackedMask);

type ReferenceKey = (VarId, usize, usize, Option<AssignTarget>, PackedMask, bool);
type ReferenceGroupKey = (
    VarId,
    usize,
    Option<AssignTarget>,
    PackedMask,
    bool,
    FlatIndexSet,
);
type AssignmentGroupKey = (VarId, usize, bool, FlatIndexSet);

#[derive(Clone, Debug)]
pub struct FfTableEntry {
    pub assigned: Option<usize>,
    /// `(decl_index, assign_target, src_read_mask, from_ff)` per reference.
    /// `assign_target` is `None` for condition expressions and similar
    /// non-assign contexts. `PackedMask::Unknown` is unavailable (consumers
    /// conservatively cover every bit). `from_ff` distinguishes always_ff (NBA-
    /// sensitive) from always_comb / continuous assign.
    pub refered: Vec<(usize, Option<AssignTarget>, PackedMask, bool)>,
    pub is_ff: bool,
    pub assigned_comb: Option<usize>,
}

impl FfTableEntry {
    fn update_is_ff(&mut self, self_key: (VarId, usize), unsafe_reads: &UnsafeSelfReads) {
        if let Some(assigned_decl) = self.assigned {
            let readable = !unsafe_reads.contains(&(assigned_decl, self_key.0, self_key.1));
            // FF classification rules (strict NBA semantics):
            // - A variable may be treated as comb (ff_opt) only if no always_ff
            //   block reads it (cross-block NBA races would be violated).
            // - always_comb / continuous assigns re-evaluate after NBA in SV,
            //   so they correctly see new FF values; ff_opt is safe for them.
            // - Within the same always_ff (assigned_decl), a self-reference
            //   is safe while it still reads what the block started with
            //   (see `write_count`); every other read must see old values.
            self.is_ff = self
                .refered
                .iter()
                .any(|(decl, assign_target, _src_mask, from_ff)| {
                    if !from_ff {
                        return false;
                    }
                    if *decl != assigned_decl {
                        return true;
                    }
                    match assign_target {
                        Some((target_id, target_idx, _)) => {
                            if *target_id != self_key.0 {
                                return true;
                            }
                            // A dynamic index is conservatively classified as FF.
                            match target_idx {
                                Some(idx) if *idx == self_key.1 => !readable,
                                Some(_) => true,
                                None => true,
                            }
                        }
                        None => true,
                    }
                });
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct FfTable {
    pub table: HashMap<(VarId, usize), FfTableEntry>,
    reference_set: HashSet<ReferenceKey>,
    reference_groups: HashSet<ReferenceGroupKey>,
    assignment_groups: HashSet<AssignmentGroupKey>,
    unknown_ff_reads: HashSet<VarId>,
    unknown_ff_assignments: HashSet<VarId>,
}

impl FfTable {
    /// `decls` must be the declarations this table was gathered from: what
    /// they write before a self-reference reads decides whether it needs the
    /// register.
    pub fn update_is_ff(&mut self, decls: &[Declaration], context: &mut Context) {
        let unsafe_reads = unsafe_self_reads(decls, context);
        let keys: Vec<_> = self.table.keys().cloned().collect();
        for key in keys {
            let entry = self.table.get_mut(&key).unwrap();
            if self.unknown_ff_assignments.contains(&key.0)
                || (self.unknown_ff_reads.contains(&key.0) && entry.assigned.is_some())
            {
                entry.is_ff = true;
            } else {
                entry.update_is_ff(key, &unsafe_reads);
            }
        }
    }

    /// Force all always_ff-assigned variables to FF, disabling the
    /// assign_target refinement. Used by --disable-ff-opt for debugging.
    pub fn force_all_ff(&mut self) {
        for entry in self.table.values_mut() {
            if entry.assigned.is_some() {
                entry.is_ff = true;
            }
        }
    }

    pub fn is_ff(&self, id: VarId, index: usize) -> bool {
        if self.unknown_ff_assignments.contains(&id) {
            return true;
        }
        if let Some(x) = self.table.get(&(id, index)) {
            x.is_ff || (x.assigned.is_some() && self.unknown_ff_reads.contains(&id))
        } else {
            false
        }
    }

    pub fn insert_refered(
        &mut self,
        id: VarId,
        index: usize,
        decl: usize,
        assign_target: Option<AssignTarget>,
        src_read_mask: PackedMask,
        from_ff: bool,
    ) {
        if !self
            .reference_set
            .insert((id, index, decl, assign_target, src_read_mask, from_ff))
        {
            return;
        }
        self.table
            .entry((id, index))
            .and_modify(|x| {
                x.refered
                    .push((decl, assign_target, src_read_mask, from_ff))
            })
            .or_insert_with(|| FfTableEntry {
                assigned: None,
                refered: vec![(decl, assign_target, src_read_mask, from_ff)],
                is_ff: false,
                assigned_comb: None,
            });
    }

    pub(crate) fn insert_refered_candidates(
        &mut self,
        id: VarId,
        candidates: FlatIndexSet,
        decl: usize,
        assign_target: Option<AssignTarget>,
        src_read_mask: PackedMask,
        from_ff: bool,
    ) {
        if !self.reference_groups.insert((
            id,
            decl,
            assign_target,
            src_read_mask,
            from_ff,
            candidates.clone(),
        )) {
            return;
        }
        for index in candidates {
            count_candidate_visit();
            self.insert_refered(id, index, decl, assign_target, src_read_mask, from_ff);
        }
    }

    pub(crate) fn insert_unknown_reference(&mut self, id: VarId, from_ff: bool) {
        if from_ff {
            self.unknown_ff_reads.insert(id);
        }
    }

    pub fn insert_assigned(&mut self, id: VarId, index: usize, decl: usize) {
        self.table
            .entry((id, index))
            .and_modify(|x| {
                x.assigned = Some(decl);
            })
            .or_insert(FfTableEntry {
                assigned: Some(decl),
                refered: vec![],
                is_ff: false,
                assigned_comb: None,
            });
    }

    pub fn insert_assigned_comb(&mut self, id: VarId, index: usize, decl: usize) {
        self.table
            .entry((id, index))
            .and_modify(|x| x.assigned_comb = Some(decl))
            .or_insert(FfTableEntry {
                assigned: None,
                refered: vec![],
                is_ff: false,
                assigned_comb: Some(decl),
            });
    }

    pub(crate) fn insert_assigned_candidates(
        &mut self,
        id: VarId,
        candidates: FlatIndexSet,
        decl: usize,
        from_comb: bool,
    ) {
        if !self
            .assignment_groups
            .insert((id, decl, from_comb, candidates.clone()))
        {
            return;
        }
        for index in candidates {
            count_candidate_visit();
            if from_comb {
                self.insert_assigned_comb(id, index, decl);
            } else {
                self.insert_assigned(id, index, decl);
            }
        }
    }

    pub(crate) fn insert_unknown_assignment(&mut self, id: VarId, from_comb: bool) {
        if !from_comb {
            self.unknown_ff_assignments.insert(id);
        }
    }

    #[cfg(debug_assertions)]
    pub fn validate(&self) {
        for ((id, index), entry) in &self.table {
            if let (Some(ff_decl), Some(comb_decl)) = (entry.assigned, entry.assigned_comb) {
                log::warn!(
                    "FfTable: variable {:?}[{}] assigned in both always_ff (decl {}) and always_comb (decl {})",
                    id,
                    index,
                    ff_decl,
                    comb_decl
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unknown_array_candidates_conservatively_retain_ff() {
        let read_id = VarId::from_raw(1);
        let assigned_id = VarId::from_raw(2);
        let comb_id = VarId::from_raw(3);
        let mut table = FfTable::default();

        table.insert_assigned(read_id, 7, 0);
        table.insert_unknown_reference(read_id, true);
        assert!(table.is_ff(read_id, 7));

        table.insert_unknown_assignment(assigned_id, false);
        assert!(table.is_ff(assigned_id, 0));
        assert!(table.is_ff(assigned_id, usize::MAX));

        table.insert_unknown_assignment(comb_id, true);
        assert!(!table.is_ff(comb_id, 0));
    }
}
