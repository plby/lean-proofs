/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RunCompressor

/-!
# Separation of finite compressed runs by monotone occurrence tags

This small generic lemma is used by the finite fractured-projection
frontend.  If raw occurrence tags are monotone, two backward maximal runs
cannot have the same tag at their first edge: the intervening run has the
opposite direction, while monotonicity would trap its first tag between two
equal endpoint tags.
-/

namespace Erdos599
namespace Alternating
namespace RunCompressor

universe u w

variable {V : Type u} {D : Digraph V}

namespace FiniteInput

/-- The raw edge index at which a finite maximal run starts. -/
def runStart (S : FiniteInput D) (i : Fin S.runs.length) : Fin S.lastEdge :=
  ⟨runLower S.runs i, by
    exact lt_of_lt_of_le
      (Nat.lt_add_of_pos_right
        (List.length_pos_iff_ne_nil.2
          (S.run_ne_nil (List.get_mem _ i))))
      (S.runUpper_le_lastEdge i)⟩

theorem colour_runStart (S : FiniteInput D) (i : Fin S.runs.length) :
    S.colour (S.runStart i) = S.runDirection i := by
  exact S.colour_run_offset i
    (k := 0)
    (List.length_pos_iff_ne_nil.2
      (S.run_ne_nil (List.get_mem _ i)))

theorem runStart_mono (S : FiniteInput D) : Monotone S.runStart := by
  intro i j hij
  exact runLower_mono S.runs hij

/-- Equal first occurrence tags identify backward compressed runs. -/
theorem run_eq_of_backward_of_firstTag_eq
    (S : FiniteInput D) {N : ℕ}
    (tag : Fin S.lastEdge → Fin N) (htag : Monotone tag)
    (tagDirection : Fin N → Direction)
    (htagDirection : ∀ k, tagDirection (tag k) = S.colour k)
    (i j : Fin S.runs.length)
    (heq : tag (S.runStart i) = tag (S.runStart j)) :
    i = j := by
  apply le_antisymm
  · by_contra hnot
    have hji : j < i := lt_of_not_ge hnot
    let m : Fin S.runs.length := ⟨j + 1, by omega⟩
    have hjm : j ≤ m := by
      change j.1 ≤ j.1 + 1
      omega
    have hmi : m ≤ i := by
      change j.1 + 1 ≤ i.1
      omega
    have htagJM : tag (S.runStart j) ≤ tag (S.runStart m) :=
      htag (S.runStart_mono hjm)
    have htagMI : tag (S.runStart m) ≤ tag (S.runStart i) :=
      htag (S.runStart_mono hmi)
    have htagMJ : tag (S.runStart m) = tag (S.runStart j) :=
      le_antisymm (by simpa [heq] using htagMI) htagJM
    have hdirMJ : S.runDirection m = S.runDirection j := by
      rw [← S.colour_runStart m, ← S.colour_runStart j,
        ← htagDirection (S.runStart m), ← htagDirection (S.runStart j),
        htagMJ]
    have hne := finiteColourRuns_head_ne_head S.colours
      ⟨j.1, by
        apply Nat.lt_sub_of_add_lt
        change j.1 + 1 < S.runs.length
        omega⟩
    apply hne
    change S.runDirection ⟨j.1, by omega⟩ =
      S.runDirection ⟨j.1 + 1, by omega⟩
    exact hdirMJ.symm
  · by_contra hnot
    have hij : i < j := lt_of_not_ge hnot
    let m : Fin S.runs.length := ⟨i + 1, by omega⟩
    have him : i ≤ m := by
      change i.1 ≤ i.1 + 1
      omega
    have hmj : m ≤ j := by
      change i.1 + 1 ≤ j.1
      omega
    have htagIM : tag (S.runStart i) ≤ tag (S.runStart m) :=
      htag (S.runStart_mono him)
    have htagMJ : tag (S.runStart m) ≤ tag (S.runStart j) :=
      htag (S.runStart_mono hmj)
    have htagMI : tag (S.runStart m) = tag (S.runStart i) :=
      le_antisymm (by simpa [heq] using htagMJ) htagIM
    have hdirMI : S.runDirection m = S.runDirection i := by
      rw [← S.colour_runStart m, ← S.colour_runStart i,
        ← htagDirection (S.runStart m), ← htagDirection (S.runStart i),
        htagMI]
    have hne := finiteColourRuns_head_ne_head S.colours
      ⟨i.1, by
        apply Nat.lt_sub_of_add_lt
        change i.1 + 1 < S.runs.length
        omega⟩
    apply hne
    change S.runDirection ⟨i.1, by omega⟩ =
      S.runDirection ⟨i.1 + 1, by omega⟩
    exact hdirMI.symm

end FiniteInput
end RunCompressor
end Alternating
end Erdos599
