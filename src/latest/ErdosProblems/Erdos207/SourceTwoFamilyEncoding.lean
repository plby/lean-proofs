/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceTwoFamilyWitness
import ErdosProblems.Erdos207.RootedThreatAbsorberBound

/-! # Injective weighted encoding of the source's two-family partitions -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

abbrev SourceTwoFamilyExposureIndex
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F F' : ForbiddenFamilyOn V)
    (Q Q' : TripleSystemOn V) (j' v' f : ℕ) :=
  Σ a : range (f + 1),
    Σ x : terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) a.1,
      Σ B : sourceSecondRoots x.1.1 Q' j' v',
        terminalOmissionCodes W (familyExtensions F' B.1) (fun E' ↦ E' \ B.1) (f - a.1)

def sourceTwoFamilyExposureCode
    {V : Type*} [Fintype V] [DecidableEq V] {ell j' v' f : ℕ}
    {W : Vortex V ell} {F F' : ForbiddenFamilyOn V} {Q Q' : TripleSystemOn V}
    (hcard : ∀ E' ∈ F', E'.card = j' - 2)
    (x : SourceTwoFamilyWitness W F F' Q Q' j' v' f) :
    SourceTwoFamilyExposureIndex W F F' Q Q' j' v' f := by
  refine ⟨⟨x.left.card, mem_range.mpr (by have := x.selected_split_card; omega)⟩,
    ⟨(x.first, x.left), mem_terminalOmissionCodes_iff.mpr
      ⟨mem_familyExtensions_iff.mpr ⟨x.first_mem, x.first_root⟩,
        mem_terminalRemainderChoices_iff.mpr ⟨x.left_subset, rfl, x.first_terminal⟩⟩⟩,
    ⟨x.second ∩ (x.first ∪ Q'), ?_⟩,
    ⟨(x.second, x.right \ x.first), ?_⟩⟩
  · apply mem_filter.mpr
    refine ⟨mem_powerset.mpr inter_subset_right, x.exposed_nonempty, ?_, x.exposed_exponent⟩
    exact (card_le_card inter_subset_left).trans_eq (hcard x.second x.second_mem)
  · apply mem_terminalOmissionCodes_iff.mpr
    refine ⟨mem_familyExtensions_iff.mpr ⟨x.second_mem, inter_subset_left⟩,
      mem_terminalRemainderChoices_iff.mpr ⟨x.right_new_subset, ?_, x.right_new_terminal⟩⟩
    change (x.right \ x.first).card = f - x.left.card
    have := x.selected_split_card
    omega

theorem sourceTwoFamilyExposureCode_injective
    {V : Type*} [Fintype V] [DecidableEq V] {ell j' v' f : ℕ}
    {W : Vortex V ell} {F F' : ForbiddenFamilyOn V} {Q Q' : TripleSystemOn V}
    (hcard : ∀ E' ∈ F', E'.card = j' - 2) :
    Function.Injective (sourceTwoFamilyExposureCode (W := W) (F := F)
      (Q := Q) (Q' := Q') (v' := v') (f := f) hcard) := by
  intro x y hxy
  have hfirst := congrArg (fun i ↦ i.2.1.1.1) hxy
  have hsecond := congrArg (fun i ↦ i.2.2.2.1.1) hxy
  have hleft := congrArg (fun i ↦ i.2.1.1.2) hxy
  have hnew := congrArg (fun i ↦ i.2.2.2.1.2) hxy
  change x.first = y.first at hfirst
  change x.second = y.second at hsecond
  change x.left = y.left at hleft
  change x.right \ x.first = y.right \ y.first at hnew
  have hright : x.right = y.right := by
    rw [← x.right_reconstruct, ← y.right_reconstruct, hleft, hsecond, hnew]
  clear hxy hnew
  cases x
  cases y
  simp_all

def sourceTwoFamilyExposureWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell j' v' f : ℕ}
    {W : Vortex V ell} {F F' : ForbiddenFamilyOn V} {Q Q' : TripleSystemOn V}
    (w : ℝ≥0) (i : SourceTwoFamilyExposureIndex W F F' Q Q' j' v' f) : ℝ≥0 :=
  setWeight (vortexTripleWeight W w) i.2.1.1.2 *
    setWeight (vortexTripleWeight W w) i.2.2.2.1.2

theorem sourceTwoFamilyExposureCode_weight
    {V : Type*} [Fintype V] [DecidableEq V] {ell j' v' f : ℕ}
    {W : Vortex V ell} {F F' : ForbiddenFamilyOn V} {Q Q' : TripleSystemOn V}
    (hcard : ∀ E' ∈ F', E'.card = j' - 2)
    (x : SourceTwoFamilyWitness W F F' Q Q' j' v' f) (w : ℝ≥0) :
    setWeight (vortexTripleWeight W w) (x.left ∪ x.right) =
      sourceTwoFamilyExposureWeight w (sourceTwoFamilyExposureCode hcard x) := by
  change setWeight (vortexTripleWeight W w) (x.left ∪ x.right) =
    setWeight (vortexTripleWeight W w) x.left *
      setWeight (vortexTripleWeight W w) (x.right \ x.first)
  rw [← x.selected_split]
  exact prod_union x.selected_split_disjoint

theorem sourceTwoFamilyExposureWeight_sum
    {V : Type*} [Fintype V] [DecidableEq V] {ell j' v' f : ℕ}
    (W : Vortex V ell) (F F' : ForbiddenFamilyOn V) (Q Q' : TripleSystemOn V) (w : ℝ≥0) :
    ∑ i : SourceTwoFamilyExposureIndex W F F' Q Q' j' v' f,
      sourceTwoFamilyExposureWeight w i =
        sourceTwoFamilyEnvelopeWeight W F F' Q Q' j' v' f w := by
  classical
  unfold sourceTwoFamilyExposureWeight sourceTwoFamilyEnvelopeWeight
  rw [Fintype.sum_sigma, Finset.sum_subtype (range (f + 1))
    (p := fun a ↦ a ∈ range (f + 1)) (fun _ ↦ Iff.rfl)]
  apply sum_congr rfl
  intro a _ha
  rw [Fintype.sum_sigma]
  unfold sourceTwoFamilySplitWeight
  rw [Finset.sum_subtype
    (terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) a.1)
    (p := fun x ↦ x ∈ terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) a.1)
    (fun _ ↦ Iff.rfl)]
  apply sum_congr rfl
  intro x _hx
  rw [Fintype.sum_sigma]
  unfold sourceSecondRootWeight
  rw [mul_sum, Finset.sum_subtype (sourceSecondRoots x.1.1 Q' j' v')
    (p := fun B ↦ B ∈ sourceSecondRoots x.1.1 Q' j' v') (fun _ ↦ Iff.rfl)]
  apply sum_congr rfl
  intro B _hB
  unfold sourceRootOmissionWeight
  rw [mul_sum, Finset.sum_subtype
    (terminalOmissionCodes W (familyExtensions F' B.1) (fun E' ↦ E' \ B.1) (f - a.1))
    (p := fun x ↦ x ∈ terminalOmissionCodes W (familyExtensions F' B.1)
      (fun E' ↦ E' \ B.1) (f - a.1)) (fun _ ↦ Iff.rfl)]

theorem sourceTwoFamilyWitness_weight_le_envelope
    {V : Type*} [Fintype V] [DecidableEq V] {ell j' v' f : ℕ}
    (W : Vortex V ell) (F F' : ForbiddenFamilyOn V) (Q Q' : TripleSystemOn V)
    (hcard : ∀ E' ∈ F', E'.card = j' - 2) (w : ℝ≥0) :
    ∑ x : SourceTwoFamilyWitness W F F' Q Q' j' v' f,
      setWeight (vortexTripleWeight W w) (x.left ∪ x.right) ≤
        sourceTwoFamilyEnvelopeWeight W F F' Q Q' j' v' f w := by
  rw [← sourceTwoFamilyExposureWeight_sum]
  apply sum_le_sum_of_injective_code (sourceTwoFamilyExposureCode hcard)
    (sourceTwoFamilyExposureCode_injective hcard)
  intro x
  exact le_of_eq (sourceTwoFamilyExposureCode_weight hcard x w)

theorem sourceTwoFamilyWitness_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' v' f : ℕ}
    {W : Vortex V ell} {F F' : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z)
    (h' : SourceVortexWellSpread W j' F' y' z')
    (Q Q' : TripleSystemOn V) (hQ : Q.Nonempty) (hQcard : Q.card ≤ j - 2)
    (w : ℝ≥0) :
    ∑ x : SourceTwoFamilyWitness W F F' Q Q' j' v' f,
      setWeight (vortexTripleWeight W w) (x.left ∪ x.right) ≤
      ((f + 1) ^ (2 * ell + 1) : ℕ) *
        (2 : ℝ≥0) ^ (2 * (j - 2) + (j' - 2) + Q'.card) * z * z' * w ^ f *
        (W.terminalSize : ℝ≥0) ^ ((j - vortexRootExponent j Q.card) + (j' - v')) /
        (W.terminalSize : ℝ≥0) ^ f :=
  (sourceTwoFamilyWitness_weight_le_envelope W F F' Q Q'
    (fun E hE ↦ (h'.uniform E hE).1) w).trans
      (sourceTwoFamilyEnvelopeWeight_le h h' Q Q' hQ hQcard w)

end

end Erdos207
