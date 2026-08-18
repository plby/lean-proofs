/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterParameters
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Integer characters on finite unit tori

Hunter's exceptional-rotation estimate repeatedly pushes Haar measure
through a tuple of independent integer characters.  This file provides the
character homomorphism and proves surjectivity from surjectivity of the
corresponding real matrix.
-/

open Set Function MeasureTheory
open scoped BigOperators

namespace Erdos984

noncomputable section

/-- The additive circle character with integer coefficient vector `ξ`. -/
def integerCharacter {D : Type*} [Fintype D] (ξ : D → ℤ) :
    UnitAddTorus D →+ UnitAddCircle where
  toFun x := ∑ j, ξ j • x j
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

@[simp] lemma integerCharacter_apply {D : Type*} [Fintype D]
    (ξ : D → ℤ) (x : UnitAddTorus D) :
    integerCharacter ξ x = ∑ j, ξ j • x j := rfl

lemma continuous_integerCharacter {D : Type*} [Fintype D] (ξ : D → ℤ) :
    Continuous (integerCharacter ξ : UnitAddTorus D → UnitAddCircle) := by
  change Continuous (fun x : UnitAddTorus D ↦ ∑ j, ξ j • x j)
  fun_prop

/-- A finite tuple of integer characters. -/
def integerCharacterTuple {D R : Type*} [Fintype D]
    (ξ : R → D → ℤ) : UnitAddTorus D →+ UnitAddTorus R where
  toFun x r := integerCharacter (ξ r) x
  map_zero' := by ext; simp
  map_add' x y := by
    ext r
    simp only [integerCharacter_apply, Pi.add_apply, smul_add]
    exact Finset.sum_add_distrib

@[simp] lemma integerCharacterTuple_apply {D R : Type*} [Fintype D]
    (ξ : R → D → ℤ) (x : UnitAddTorus D) (r : R) :
    integerCharacterTuple ξ x r = ∑ j, ξ r j • x j := rfl

lemma continuous_integerCharacterTuple
    {D R : Type*} [Fintype D] (ξ : R → D → ℤ) :
    Continuous (integerCharacterTuple ξ : UnitAddTorus D → UnitAddTorus R) := by
  change Continuous (fun x : UnitAddTorus D ↦
    fun r ↦ ∑ j, ξ r j • x j)
  fun_prop

/-- The real matrix underlying a tuple of integer characters. -/
def integerCharacterRealMatrix {D R : Type*} (ξ : R → D → ℤ) :
    Matrix R D ℝ := fun r j ↦ (ξ r j : ℝ)

/-- Surjectivity of the real matrix implies surjectivity of the associated
torus character tuple.  A real preimage of the centered lift can simply be
projected coordinatewise to the torus. -/
lemma integerCharacterTuple_surjective_of_real
    {D R : Type*} [Fintype D] (ξ : R → D → ℤ)
    (hsurj : Surjective (integerCharacterRealMatrix ξ).mulVec) :
    Surjective (integerCharacterTuple ξ : UnitAddTorus D → UnitAddTorus R) := by
  intro y
  let z : R → ℝ := fun r ↦ centeredCircleLift (y r)
  obtain ⟨u, hu⟩ := hsurj z
  let x : UnitAddTorus D := fun j ↦ ((u j : ℝ) : UnitAddCircle)
  refine ⟨x, ?_⟩
  ext r
  change (∑ j, ξ r j • ((u j : ℝ) : UnitAddCircle)) = y r
  have hreal : (∑ j, (ξ r j : ℝ) * u j) = centeredCircleLift (y r) := by
    have hr := congrFun hu r
    simpa only [Matrix.mulVec, dotProduct, integerCharacterRealMatrix] using hr
  calc
    (∑ j, ξ r j • ((u j : ℝ) : UnitAddCircle)) =
        ∑ j, (((ξ r j : ℝ) * u j : ℝ) : UnitAddCircle) := by
      apply Finset.sum_congr rfl
      intro j _hj
      symm
      simp
    _ = (((∑ j, (ξ r j : ℝ) * u j : ℝ)) : UnitAddCircle) := by
      symm
      exact map_sum
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
        (fun j ↦ (ξ r j : ℝ) * u j) Finset.univ
    _ = ((centeredCircleLift (y r) : ℝ) : UnitAddCircle) := congrArg _ hreal
    _ = y r := coe_centeredCircleLift (y r)

/-- A surjective tuple of integer characters preserves normalized Haar
volume. -/
lemma measurePreserving_integerCharacterTuple
    {D R : Type*} [Fintype D] [Fintype R] (ξ : R → D → ℤ)
    (hsurj : Surjective (integerCharacterRealMatrix ξ).mulVec) :
    MeasurePreserving (integerCharacterTuple ξ :
      UnitAddTorus D →+ UnitAddTorus R) volume volume := by
  apply AddMonoidHom.measurePreserving
  · exact continuous_integerCharacterTuple ξ
  · exact integerCharacterTuple_surjective_of_real ξ hsurj
  · rw [volume_unitAddTorus_univ, volume_unitAddTorus_univ]

/-- First apply an integer character tuple and then multiply every output
coordinate by `n`. -/
def nsmulIntegerCharacterTuple {D R : Type*} [Fintype D]
    (n : ℕ) (ξ : R → D → ℤ) : UnitAddTorus D →+ UnitAddTorus R :=
  (nsmulAddMonoidHom n).comp (integerCharacterTuple ξ)

@[simp] lemma nsmulIntegerCharacterTuple_apply
    {D R : Type*} [Fintype D] (n : ℕ) (ξ : R → D → ℤ)
    (x : UnitAddTorus D) (r : R) :
    nsmulIntegerCharacterTuple n ξ x r = n • integerCharacter (ξ r) x := by
  rfl

lemma measurePreserving_nsmulIntegerCharacterTuple
    {D R : Type*} [Fintype D] [Fintype R]
    (n : ℕ) (hn : 0 < n) (ξ : R → D → ℤ)
    (hsurj : Surjective (integerCharacterRealMatrix ξ).mulVec) :
    MeasurePreserving (nsmulIntegerCharacterTuple n ξ :
      UnitAddTorus D →+ UnitAddTorus R) volume volume := by
  apply AddMonoidHom.measurePreserving
  · exact (continuous_nsmul n).comp (continuous_integerCharacterTuple ξ)
  · exact (nsmul_surjective_unitAddTorus n hn).comp
      (integerCharacterTuple_surjective_of_real ξ hsurj)
  · rw [volume_unitAddTorus_univ, volume_unitAddTorus_univ]

/-- Exact Haar measure of a simultaneous small-phase event. -/
lemma volume_small_nsmul_character_event
    {D R : Type*} [Fintype D] [Fintype R]
    (n : ℕ) (hn : 0 < n) (ξ : R → D → ℤ)
    (hsurj : Surjective (integerCharacterRealMatrix ξ).mulVec)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ (1 : ℝ) / 2) :
    volume (nsmulIntegerCharacterTuple n ξ ⁻¹'
      Metric.closedBall (0 : UnitAddTorus R) δ) =
      (ENNReal.ofReal (2 * δ)) ^ Fintype.card R := by
  rw [(measurePreserving_nsmulIntegerCharacterTuple n hn ξ hsurj).measure_preimage
    measurableSet_closedBall.nullMeasurableSet]
  exact volume_unitAddTorus_closedBall hδ0 hδhalf

end

end Erdos984
