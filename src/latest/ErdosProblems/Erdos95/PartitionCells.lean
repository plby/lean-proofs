/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.SurfacePruning
import ErdosProblems.Erdos95.StoneTukey

/-!
# Covering a finite point set by strict sign cells and its wall

The iterated bisection construction uses strict sign cells.  This file
records the complementary fact needed by the incidence induction: every
input point is either on the product wall or belongs to the sign cell given
by the signs of the factors at that point.
-/

namespace Erdos95.PartitionCells

open Erdos95.Partitioning

abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Space3 := Fin 3 → ℝ

/-- Points of `S` on the product partition wall. -/
noncomputable def wallPoints (S : Finset Space3) {J : ℕ}
    (p : Fin J → Poly3) : Finset Space3 := by
  classical
  exact S.filter fun x ↦ MvPolynomial.eval x (partitionPolynomial p) = 0

theorem mem_wallPoints_iff {S : Finset Space3} {J : ℕ}
    {p : Fin J → Poly3} {x : Space3} :
    x ∈ wallPoints S p ↔
      x ∈ S ∧ MvPolynomial.eval x (partitionPolynomial p) = 0 := by
  classical
  simp [wallPoints]

/-- The strict sign pattern selected by a point. -/
noncomputable def pointSign {J : ℕ} (p : Fin J → Poly3)
    (x : Space3) : Fin J → Bool := fun j ↦ decide (0 < MvPolynomial.eval x (p j))

theorem mem_signCell_pointSign {S : Finset Space3} {J : ℕ}
    {p : Fin J → Poly3} {x : Space3} (hxS : x ∈ S)
    (hxwall : MvPolynomial.eval x (partitionPolynomial p) ≠ 0) :
    x ∈ signCell S p (pointSign p x) := by
  classical
  apply mem_signCell_iff.mpr
  refine ⟨hxS, ?_⟩
  intro j
  have hj : MvPolynomial.eval x (p j) ≠ 0 := by
    intro hzero
    apply hxwall
    rw [eval_partitionPolynomial]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact hzero
  unfold pointSign
  simp only [decide_eq_true_eq]
  split
  · assumption
  · have := lt_or_gt_of_ne hj
    tauto

/-- Every input point is covered by the product wall or by one strict sign
cell. -/
theorem mem_wallPoints_or_exists_mem_signCell
    {S : Finset Space3} {J : ℕ} {p : Fin J → Poly3} {x : Space3}
    (hx : x ∈ S) :
    x ∈ wallPoints S p ∨
      ∃ sign : Fin J → Bool, x ∈ signCell S p sign := by
  classical
  by_cases hwall : MvPolynomial.eval x (partitionPolynomial p) = 0
  · exact Or.inl (mem_wallPoints_iff.mpr ⟨hx, hwall⟩)
  · exact Or.inr ⟨pointSign p x, mem_signCell_pointSign hx hwall⟩

/-- Finite union of all strict sign cells. -/
noncomputable def allSignCells (S : Finset Space3) {J : ℕ}
    (p : Fin J → Poly3) : Finset Space3 := by
  classical
  exact (Finset.univ : Finset (Fin J → Bool)).biUnion (signCell S p)

theorem mem_allSignCells_iff {S : Finset Space3} {J : ℕ}
    {p : Fin J → Poly3} {x : Space3} :
    x ∈ allSignCells S p ↔
      ∃ sign : Fin J → Bool, x ∈ signCell S p sign := by
  classical
  simp [allSignCells]

theorem subset_wallPoints_union_allSignCells
    (S : Finset Space3) {J : ℕ} (p : Fin J → Poly3) :
    S ⊆ wallPoints S p ∪ allSignCells S p := by
  intro x hx
  rcases mem_wallPoints_or_exists_mem_signCell hx with hxwall | ⟨sign, hxsign⟩
  · exact Finset.mem_union_left _ hxwall
  · exact Finset.mem_union_right _ (mem_allSignCells_iff.mpr ⟨sign, hxsign⟩)

theorem card_biUnion_signCells_le_sum (S : Finset Space3) {J : ℕ}
    (p : Fin J → Poly3) (T : Finset (Fin J → Bool)) :
    (T.biUnion (signCell S p)).card ≤
      ∑ sign ∈ T, (signCell S p sign).card := by
  classical
  exact Finset.card_biUnion_le

end Erdos95.PartitionCells
