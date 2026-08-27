/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceNibbleWitness
import ErdosProblems.Erdos207.TerminalOmissionRootTransfer

/-! # Mixed coordinates and the exact unrooted density factor -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

abbrev SourceNibbleCoordinate (V : Type*) [DecidableEq V] := TripleOn V ⊕ Sym2 V

def sourceNibbleCoordinates
    {V : Type*} [DecidableEq V] (T : TripleOn V) (x : TripleSystemOn V × TripleSystemOn V) :
    Finset (SourceNibbleCoordinate V) :=
  x.2.disjSum ((sourceNibbleRemaining T x).biUnion tripleEdgeFinset)

def sourceNibbleMixedWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (w p : ℝ≥0) : SourceNibbleCoordinate V → ℝ≥0 :=
  Sum.elim (vortexTripleWeight W w) (fun _ ↦ p)

theorem sourceNibbleMixedWeight_factor
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (w p : ℝ≥0) (A : Finset (SourceNibbleCoordinate V)) :
    setWeight (sourceNibbleMixedWeight W w p) A =
      setWeight (vortexTripleWeight W w) A.toLeft * p ^ A.toRight.card := by
  unfold setWeight
  rw [prod_sum_eq_prod_toLeft_mul_prod_toRight]
  simp only [sourceNibbleMixedWeight, Sum.elim_inl, Sum.elim_inr, prod_const]

theorem sourceNibbleCoordinates_remainder_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (w p : ℝ≥0) (hp : p ≤ 1) (T : TripleOn V)
    (x : TripleSystemOn V × TripleSystemOn V) (H : Finset (SourceNibbleCoordinate V)) :
    setWeight (sourceNibbleMixedWeight W w p) (sourceNibbleCoordinates T x \ H) ≤
      setWeight (vortexTripleWeight W w) (x.2 \ H.toLeft) := by
  rw [sourceNibbleMixedWeight_factor]
  simp only [toLeft_sdiff, sourceNibbleCoordinates, toLeft_disjSum]
  exact mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hp)

theorem sourceNibble_extension_le_root_omission
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (j j' : ℕ)
    (w p : ℝ≥0) (hp : p ≤ 1) (H : Finset (SourceNibbleCoordinate V)) :
    extensionWeight (fun x : sourceNibbleCodes W F T j j' ↦ sourceNibbleCoordinates T x.1)
      (sourceNibbleMixedWeight W w p) H ≤
      sourceRootOmissionWeight W F ({T} ∪ H.toLeft) (j' - j - H.toLeft.card) w := by
  classical
  unfold extensionWeight
  rw [← Finset.sum_subtype (sourceNibbleCodes W F T j j')
    (p := fun x ↦ x ∈ sourceNibbleCodes W F T j j') (fun _ ↦ Iff.rfl)
    (fun x ↦ if H ⊆ sourceNibbleCoordinates T x then
      setWeight (sourceNibbleMixedWeight W w p) (sourceNibbleCoordinates T x \ H) else 0)]
  apply le_trans _ (sourceRootOmission_remainder_weight_le W F {T} H.toLeft (j' - j) w)
  rw [sum_filter]
  apply sum_le_sum
  intro x _hx
  by_cases hroot : H ⊆ sourceNibbleCoordinates T x
  · have hleft : H.toLeft ⊆ x.2 := (subset_disjSum.mp hroot).1
    rw [if_pos hroot, if_pos hleft]
    exact sourceNibbleCoordinates_remainder_weight_le W w p hp T x H
  · rw [if_neg hroot]
    exact zero_le

theorem sourceNibble_extension_empty_eq
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V)
    (huniform : ∀ E ∈ F, E.card = j' - 2) (hpacking : ∀ E ∈ F, IsPackingOn E)
    (hj : 4 ≤ j) (hjj : j ≤ j') (w p : ℝ≥0) :
    extensionWeight (fun x : sourceNibbleCodes W F T j j' ↦ sourceNibbleCoordinates T x.1)
      (sourceNibbleMixedWeight W w p) ∅ =
      sourceRootOmissionWeight W F {T} (j' - j) w * p ^ (3 * (j - 3)) := by
  classical
  unfold extensionWeight
  simp only [empty_subset, ↓reduceIte, sdiff_empty]
  rw [← Finset.sum_subtype (sourceNibbleCodes W F T j j')
    (p := fun x ↦ x ∈ sourceNibbleCodes W F T j j') (fun _ ↦ Iff.rfl)
    (fun x ↦ setWeight (sourceNibbleMixedWeight W w p) (sourceNibbleCoordinates T x))]
  unfold sourceRootOmissionWeight
  rw [sum_mul]
  apply sum_congr rfl
  intro x hx
  rw [sourceNibbleMixedWeight_factor]
  simp only [sourceNibbleCoordinates, toLeft_disjSum, toRight_disjSum]
  rw [sourceNibbleRemaining_edge_card huniform hpacking hj hjj hx]

end

end Erdos207
