import ErdosProblems.Erdos118.Reused591.LabeledPrefix
import ErdosProblems.Erdos118.Reused591.CutLabels

namespace Erdos118.Reused591

/-!
# Actual cuts are relaxed prefixes under the computed labels

The coordinate index in `LeafCut` is identified with the exact prefix
of the canonical atom list. Executing that prefix gives the same body
and leaf indices selected by the computed root and body labels.
-/

namespace Erdos591.Positive.Game.CutLabels

open Erdos591.Negative.Exact Payoff LabeledCode

theorem cut_is_relaxed {s t : List (List ℕ)} {i j : ℕ} (hc : LeafCut s t i j) :
    ∃ w : LabeledWord,
      LabeledWord.initial.runAtoms
        ((atoms (root s t) (bodies s t)).take (leafPosition s i j + 1)) = some w ∧
      w.relaxed = true ∧ w.coordinates.length = leafPosition s i j + 1 ∧
      w.bodyLabels.length = i + 1 ∧ w.leafIndex = j + 1 := by
  let as := bodies s t
  let pre := as.take i
  let rest := as.drop (i + 1)
  let a := s.getD i []
  let us := a.take (j + 1)
  let vs := a.drop (j + 1)
  have hi : i < as.length := by simpa [as] using hc.1
  have hj : j < a.length := hc.2.1
  have hpre : pre.length = i := by simp [pre, min_eq_left hi.le]
  have hus : us.length = j + 1 := by
    simp [us, min_eq_left (Nat.succ_le_of_lt hj)]
  have huv : us ++ vs = a := List.take_append_drop (j + 1) a
  have hai : as[i] = (body s t i, a) := by
    change (bodies s t)[i] = (body s t i, s.getD i [])
    rw [List.getD_eq_getElem _ _ hc.1]
    simp [bodies]
  have has : as = pre ++ (body s t i, us ++ vs) :: rest := by
    have hh := List.take_append_drop i as
    rw [List.drop_eq_getElem_cons hi, hai] at hh
    simpa only [pre, rest, huv] using hh.symm
  let pref := leafPrefixAtoms (root s t) pre (body s t i) us vs rest
  let tail := (vs.map fun n => (∅, n)) ++ bodiesAtoms rest
  let w := leafPrefixCursor (root s t) pre (body s t i) us vs rest
  have hrun : LabeledWord.initial.runAtoms pref = some w := run_leafPrefix ..
  have hsplit : atoms (root s t) as = pref ++ tail := by
    rw [has]
    exact atoms_split_leafPrefix ..
  have herase : erase (pre ++ (body s t i, us ++ vs) :: rest) = s := by
    rw [← has]
    exact erase_bodies s t
  have hlen : w.coordinates.length = leafPosition s i j + 1 := by
    have hh := leafPrefix_length (root s t) pre (body s t i) us vs rest
      (by simp [hus])
    simpa [herase, hpre, hus] using hh
  have hpref : pref.length = leafPosition s i j + 1 := by
    have hh := congrArg List.length (LabeledWord.runAtoms_coordinates hrun)
    simpa [LabeledWord.initial, hlen] using hh.symm
  refine ⟨w, ?_, ?_, hlen, ?_, ?_⟩
  · change LabeledWord.initial.runAtoms
      ((atoms (root s t) as).take (leafPosition s i j + 1)) = some w
    rw [hsplit, ← hpref, List.take_left]
    exact hrun
  · apply (leafPrefix_relaxed (root s t) pre (body s t i) us vs rest).2
    refine ⟨by simp [hus], ?_, ?_⟩
    · rw [hpre, succ_mem_root]
      exact ⟨j, hc⟩
    · rw [hus, succ_mem_body]
      exact hc
  · simp [w, leafPrefixCursor, hpre]
  · exact hus

#print axioms cut_is_relaxed

end Erdos591.Positive.Game.CutLabels

end Erdos118.Reused591
