import ErdosProblems.Erdos591.CutCoarsening

/-!
# The actual chronological cut-word interleaving

Tag each global construction block by root ownership. Branch records
are subsequences of this log. Their canonical cut-label coarsenings
therefore merge to a single selected subsequence with exact projections.
-/

namespace Erdos591.Positive.Game.Macro.Forest

open Erdos591.Negative.Exact

variable {N H : Set ℕ} (hH : H.Infinite) (b : Concrete.Hist N → ℕ)

noncomputable def taggedLog (rootName r : ℕ) : List Atomic.Atom :=
  (stages hH b r).log.flatMap fun seg =>
    Atomic.tag (decide (root (seg.1 + 1) ≠ rootName)) seg.2

theorem retag_taggedLog (rootName r : ℕ) :
    Atomic.retag (fun _ => false) (taggedLog hH b rootName r) =
      Atomic.tag false (stages hH b r).atoms := by
  simp [taggedLog, Atomic.retag, Atomic.tag, Stage.atoms,
    List.map_flatMap, List.map_map, Function.comp_def]

theorem taggedLog_inputs (rootName r : ℕ) :
    Atomic.inputs (taggedLog hH b rootName r) = (stages hH b r).inputs := by
  rw [← Atomic.inputs_retag (fun _ => false) (taggedLog hH b rootName r), retag_taggedLog]
  rfl

theorem taggedLog_spaced (rootName r : ℕ) :
    Atomic.Spaced b ∅ (taggedLog hH b rootName r) := by
  apply Atomic.Spaced.of_retag (fun _ => false)
  rw [retag_taggedLog]
  exact (stages_valid hH b r).spaced

theorem taggedLog_increasing (rootName r : ℕ) :
    (Atomic.inputs (taggedLog hH b rootName r)).Pairwise (· < ·) := by
  rw [taggedLog_inputs]
  exact (stages_valid hH b r).increasing

theorem taggedLog_pool (rootName r : ℕ) :
    ∀ x ∈ Atomic.inputs (taggedLog hH b rootName r), x ∈ H := by
  rw [taggedLog_inputs]
  exact (stages_valid hH b r).pool

theorem taggedLog_positive (rootName r : ℕ) :
    ∀ x ∈ Atomic.inputs (taggedLog hH b rootName r), 0 < x := by
  rw [taggedLog_inputs]
  exact (stages_valid hH b r).positive

theorem branch_taggedLog_sublist (rootName p r : ℕ) (hp : p ≤ r) :
    List.Sublist (Atomic.tag (decide (root p ≠ rootName)) (node hH b p).atoms)
      (taggedLog hH b rootName r) := by
  have hh := (node_segments_sublist hH b p r hp).flatMap (fun seg =>
    Atomic.tag (decide (root (seg.1 + 1) ≠ rootName)) seg.2)
  have heq : ((node hH b p).segments.flatMap fun seg =>
      Atomic.tag (decide (root (seg.1 + 1) ≠ rootName)) seg.2) =
        Atomic.tag (decide (root p ≠ rootName)) (node hH b p).atoms := by
    calc
      _ = (node hH b p).segments.flatMap (fun seg =>
          Atomic.tag (decide (root p ≠ rootName)) seg.2) := by
        apply List.flatMap_congr
        intro seg hseg
        rw [segment_root hH b p seg hseg]
      _ = _ := by simp [Atomic.tag, Node.atoms, List.map_flatMap]
  simpa only [heq, taggedLog] using hh

/-- Both actual cut words occur as projections of one coarsened
subsequence of the existing global construction log. -/
theorem cut_interleaving (n m : ℕ) (hnm : root n ≠ root m) (s t : G)
    (hs : Erdos591.Negative.Exact.word s.val = (node hH b n).cursor.coordinates)
    (ht : Erdos591.Negative.Exact.word t.val = (node hH b m).cursor.coordinates) :
    ∃ xs, Atomic.Selects xs (taggedLog hH b (root n) (max n m)) ∧
      ∀ side, Atomic.project xs side = Atomic.cutProgram s.val t.val side := by
  apply Atomic.selects_merge_programs
  intro side
  cases side with
  | false =>
      have hsub : List.Sublist (Atomic.tag false (node hH b n).atoms)
          (taggedLog hH b (root n) (max n m)) := by
        simpa using branch_taggedLog_sublist hH b (root n) n (max n m) (le_max_left n m)
      have hsel := (cut_program_coarsens hH b n m hnm s t hs ht false).selects_sublist
        (Atomic.tag_sublist_filterSide false hsub)
      simpa only [Atomic.tag_project, Atomic.cutProgram] using hsel
  | true =>
      have hsub : List.Sublist (Atomic.tag true (node hH b m).atoms)
          (taggedLog hH b (root n) (max n m)) := by
        simpa [hnm.symm] using
          branch_taggedLog_sublist hH b (root n) m (max n m) (le_max_right n m)
      have hsel := (cut_program_coarsens hH b m n hnm.symm t s ht hs true).selects_sublist
        (Atomic.tag_sublist_filterSide true hsub)
      simpa only [Atomic.tag_project, Atomic.cutProgram] using hsel

#print axioms taggedLog_spaced
#print axioms branch_taggedLog_sublist
#print axioms cut_interleaving

end Erdos591.Positive.Game.Macro.Forest
