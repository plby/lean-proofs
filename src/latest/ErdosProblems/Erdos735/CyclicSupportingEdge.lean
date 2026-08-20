/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos735.PolarBoundaryOrder
import ErdosProblems.Erdos957.HullGeometryBridge

/-! Strict supporting edges are consecutive in a genuine cyclic hull order. -/

open Classical

namespace Erdos735.CyclicSupportingEdge

noncomputable section

open Erdos957

theorem CyclicHullOrder.isCCWNext {A : Finset Point}
    (P : CyclicHullOrder A) (i : Fin (hullVertexCount A)) :
    IsCCWNext A (P.vertex i) (P.vertex (cyclicSucc i)) := by
  refine ⟨P.vertex_mem_hullVertices _, P.edge_support i, ?_⟩
  intro z hz hzp hzq
  have hnonneg :
      0 ≤ crossVec (P.vertex (cyclicSucc i) - P.vertex i)
        (z - P.vertex i) :=
    Erdos957HullGeometryBridge.cyclic_edge_cross_nonneg P i
      (hullVertices_subset A hz)
  have hne :
      crossVec (P.vertex (cyclicSucc i) - P.vertex i)
        (z - P.vertex i) ≠ 0 := by
    intro hzero
    exact (hullVertices_not_collinear_three A
      (P.vertex_mem_hullVertices i)
      (P.vertex_mem_hullVertices (cyclicSucc i)) hz
      (P.consecutive_ne i) hzq.symm hzp.symm)
      (collinear_of_crossVec_sub_eq_zero (P.consecutive_ne i) hzero)
  rw [orientedTurn_eq_crossVec]
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem isStrictSupportingEdge_swap {A : Finset Point} {p q : Point}
    (h : IsStrictSupportingEdge A p q) : IsStrictSupportingEdge A q p := by
  obtain ⟨hpq, l, hl, hpqlevel, hmax, hstrict⟩ := h
  refine ⟨hpq.symm, l, hl, hpqlevel.symm, ?_, ?_⟩
  · intro z hz
    rw [← hpqlevel]
    exact hmax z hz
  · intro z hz hzq hzp
    rw [← hpqlevel]
    exact hstrict z hz hzp hzq

theorem isCCWNext_or_reverse_of_strictSupportingEdge
    {A : Finset Point} (hthree : 3 ≤ (hullVertices A).card)
    {p q : Point} (hp : p ∈ hullVertices A) (hq : q ∈ hullVertices A)
    (hedge : IsStrictSupportingEdge A p q) :
    IsCCWNext A p q ∨ IsCCWNext A q p := by
  obtain ⟨hpq, l, hl, hpqlevel, hmax, hstrict⟩ := hedge
  have herase : 0 < (((hullVertices A).erase p).erase q).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hpq.symm, hq⟩),
      Finset.card_erase_of_mem hp]
    omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp herase
  have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
  have hrp : r ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
  have hrhull : r ∈ hullVertices A :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).2
  have hturnne : orientedTurn p q r ≠ 0 := by
    rw [orientedTurn_eq_crossVec]
    intro hzero
    exact (hullVertices_not_collinear_three A hp hq hrhull hpq
      hrq.symm hrp.symm) (collinear_of_crossVec_sub_eq_zero hpq hzero)
  have hlu : l (q - p) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hpqlevel.symm
  have hlr : l (r - p) < 0 := by
    rw [map_sub]
    exact sub_neg.mpr (hstrict r hrhull hrp hrq)
  have hdet := support_turn_coordinate_det l (q - p) (r - p)
  rw [hlu, zero_mul, zero_sub, ← orientedTurn_eq_crossVec] at hdet
  by_cases hpos : 0 < orientedTurn p q r
  · left
    refine ⟨hq, ⟨hpq, l, hl, hpqlevel, hmax, hstrict⟩, ?_⟩
    intro z hz hzp hzq
    have hlz : l (z - p) < 0 := by
      rw [map_sub]
      exact sub_neg.mpr (hstrict z hz hzp hzq)
    have hdetz := support_turn_coordinate_det l (q - p) (z - p)
    rw [hlu, zero_mul, zero_sub, ← orientedTurn_eq_crossVec] at hdetz
    have hquarter : 0 < quarterTurnFunctional l (q - p) := by
      have hcoef := support_coefficient_sq_pos hl
      nlinarith
    have hcoef := support_coefficient_sq_pos hl
    nlinarith
  · right
    have hneg : orientedTurn p q r < 0 := lt_of_le_of_ne
      (le_of_not_gt hpos) hturnne
    refine ⟨hp, isStrictSupportingEdge_swap
      ⟨hpq, l, hl, hpqlevel, hmax, hstrict⟩, ?_⟩
    intro z hz hzq hzp
    have hlz : l (z - p) < 0 := by
      rw [map_sub]
      exact sub_neg.mpr (hstrict z hz hzp hzq)
    have hdetz := support_turn_coordinate_det l (q - p) (z - p)
    rw [hlu, zero_mul, zero_sub, ← orientedTurn_eq_crossVec] at hdetz
    have hquarter : quarterTurnFunctional l (q - p) < 0 := by
      have hcoef := support_coefficient_sq_pos hl
      nlinarith
    have hforward : orientedTurn p q z < 0 := by
      have hcoef := support_coefficient_sq_pos hl
      nlinarith
    have hreverse : orientedTurn q p z = -orientedTurn p q z := by
      simp only [orientedTurn]
      ring
    rw [hreverse]
    linarith

theorem strictSupportingEdge_eq_consecutive_or_reverse
    {A : Finset Point} (P : CyclicHullOrder A)
    (hthree : 3 ≤ (hullVertices A).card)
    {p q : Point} (hp : p ∈ hullVertices A) (hq : q ∈ hullVertices A)
    (hedge : IsStrictSupportingEdge A p q) :
    (∃ i, P.vertex i = p ∧ P.vertex (cyclicSucc i) = q) ∨
      (∃ i, P.vertex i = q ∧ P.vertex (cyclicSucc i) = p) := by
  rcases isCCWNext_or_reverse_of_strictSupportingEdge hthree hp hq hedge with
    hpq | hqp
  · obtain ⟨i, hi, -⟩ := P.existsUnique_vertex_eq hp
    left
    refine ⟨i, hi, ?_⟩
    have hcyclic := CyclicHullOrder.isCCWNext P i
    have hunique :=
      (Classical.choose_spec (hullVertex_existsUnique_isCCWNext A hthree hp)).2
    exact (hunique _ (hi ▸ hcyclic)).trans (hunique _ hpq).symm
  · obtain ⟨i, hi, -⟩ := P.existsUnique_vertex_eq hq
    right
    refine ⟨i, hi, ?_⟩
    have hcyclic := CyclicHullOrder.isCCWNext P i
    have hunique :=
      (Classical.choose_spec (hullVertex_existsUnique_isCCWNext A hthree hq)).2
    exact (hunique _ (hi ▸ hcyclic)).trans (hunique _ hqp).symm

end

end Erdos735.CyclicSupportingEdge
