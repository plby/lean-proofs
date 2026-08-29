/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteInputCoordinateInterval

/-!
# Locating raw finite-compressor coordinates in maximal runs

Every raw edge coordinate has a canonical containing maximal colour run.
The explicit offset and boundary laws below are used to compare a
coordinate-restricted compressor with its parent without reconstructing
the original projection compiler.
-/

noncomputable section

namespace Erdos599.Alternating.RunCompressor

universe u

variable {V : Type u} {D : Digraph V}

/-- Every position in a flattened nonempty run list has a run and offset. -/
theorem exists_run_offset_of_lt_flatten
    (runs : List (List Direction)) {n : Nat}
    (hn : n < runs.flatten.length) :
    ∃ (i : Fin runs.length) (k : Nat),
      k < (runs.get i).length ∧ n = runLower runs i + k := by
  induction runs generalizing n with
  | nil => simp at hn
  | cons r runs ih =>
      by_cases hnr : n < r.length
      · exact ⟨⟨0, by simp⟩, n, by simpa using hnr,
          by simp [runLower]⟩
      · have hnTail : n - r.length < runs.flatten.length := by
          have hlen : n < r.length + runs.flatten.length := by
            simpa only [List.flatten_cons, List.length_append] using hn
          omega
        obtain ⟨i, k, hk, hnk⟩ := ih hnTail
        refine ⟨⟨i.1 + 1, by simp⟩, k, by simpa using hk, ?_⟩
        simp only [runLower, List.take_succ_cons, List.map_cons,
          List.sum_cons, List.get_cons_succ]
        change n = r.length + runLower runs i + k
        have hnGe : r.length ≤ n := Nat.le_of_not_gt hnr
        omega

namespace FiniteInput

/-- Canonical maximal run containing a raw edge coordinate. -/
noncomputable def rawRun (S : FiniteInput D) (n : Fin S.lastEdge) :
    Fin S.runs.length :=
  Classical.choose (exists_run_offset_of_lt_flatten S.runs (by
    rw [S.runs_flatten, S.colours_length]
    exact n.2))

/-- Offset of a raw edge coordinate inside its canonical maximal run. -/
noncomputable def rawRunOffset (S : FiniteInput D) (n : Fin S.lastEdge) : Nat :=
  Classical.choose (Classical.choose_spec
    (exists_run_offset_of_lt_flatten S.runs (by
      rw [S.runs_flatten, S.colours_length]
      exact n.2)))

theorem rawRunOffset_lt (S : FiniteInput D) (n : Fin S.lastEdge) :
    S.rawRunOffset n < (S.runs.get (S.rawRun n)).length :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_run_offset_of_lt_flatten S.runs (by
      rw [S.runs_flatten, S.colours_length]
      exact n.2)))).1

theorem rawRun_decomposition (S : FiniteInput D) (n : Fin S.lastEdge) :
    n.1 = runLower S.runs (S.rawRun n) + S.rawRunOffset n :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_run_offset_of_lt_flatten S.runs (by
      rw [S.runs_flatten, S.colours_length]
      exact n.2)))).2

theorem rawRun_lower_le (S : FiniteInput D) (n : Fin S.lastEdge) :
    runLower S.runs (S.rawRun n) ≤ n.1 := by
  rw [S.rawRun_decomposition n]
  exact Nat.le_add_right _ _

theorem rawRun_lt_upper (S : FiniteInput D) (n : Fin S.lastEdge) :
    n.1 < runLower S.runs ((S.rawRun n).1 + 1) := by
  rw [runLower_succ S.runs (S.rawRun n).2, S.rawRun_decomposition n]
  exact Nat.add_lt_add_left (S.rawRunOffset_lt n) _

theorem rawRun_colour (S : FiniteInput D) (n : Fin S.lastEdge) :
    S.colour n = S.runDirection (S.rawRun n) := by
  have h := S.colour_run_offset (S.rawRun n) (S.rawRunOffset_lt n)
  have hfin :
      (⟨runLower S.runs (S.rawRun n) + S.rawRunOffset n, by
        exact lt_of_lt_of_le
          (Nat.add_lt_add_left (S.rawRunOffset_lt n) _)
          (S.runUpper_le_lastEdge (S.rawRun n))⟩ : Fin S.lastEdge) = n := by
    apply Fin.ext
    exact (S.rawRun_decomposition n).symm
  simpa only [hfin] using h

theorem rawRun_eq_of_mem_interval (S : FiniteInput D)
    (n : Fin S.lastEdge) (i : Fin S.runs.length)
    (hlo : runLower S.runs i ≤ n.1)
    (hhi : n.1 < runLower S.runs (i.1 + 1)) :
    S.rawRun n = i := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstep : (S.rawRun n).1 + 1 ≤ i.1 := by omega
    have hbound := runLower_mono S.runs hstep
    have hnlt := S.rawRun_lt_upper n
    omega
  · have hstep : i.1 + 1 ≤ (S.rawRun n).1 := by omega
    have hbound := runLower_mono S.runs hstep
    have hnlo := S.rawRun_lower_le n
    omega

end FiniteInput
end Erdos599.Alternating.RunCompressor

#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.rawRun_eq_of_mem_interval
