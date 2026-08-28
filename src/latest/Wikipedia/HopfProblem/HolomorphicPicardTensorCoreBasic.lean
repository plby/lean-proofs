import Wikipedia.HopfProblem.HolomorphicPicardNativeGluing
import Wikipedia.HopfProblem.HolomorphicPicardCechAlgebra

/-!
# Multiplication and inversion of actual unit cocycle transitions

Addition in the original holomorphic unit sheaf is multiplication of its
actual nowhere-zero functions.  These identities hold for the transitions
of the native glued bundles, including the chosen value one off each
overlap.  The base sets and chosen fibre coordinates are independent of
the cocycle.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.HolomorphicPicard.TensorCore

open HolomorphicExponentialSheaf HolomorphicPicardNative
open HolomorphicFunctionSheaf.SphereH1

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type} (U : ι → Opens M) (hcover : ∀ x : M, ∃ i : ι, x ∈ U i)

/-- The genuine bundle transition of the sum cocycle is the product of
the two original transitions. -/
@[simp] theorem data_add_transition
    (c d : CechOneCocycle (unitsSheaf I M) U) (i j : ι) (x : M) :
    (cocycleTransitionData I M U hcover (c + d)).transition i j x =
      (cocycleTransitionData I M U hcover c).transition i j x *
        (cocycleTransitionData I M U hcover d).transition i j x := by
  classical
  change cocycleTransition I M U (c + d) i j x =
    cocycleTransition I M U c i j x * cocycleTransition I M U d i j x
  by_cases hx : x ∈ U i ⊓ U j
  · apply Units.ext
    simp only [Units.val_mul, cocycleTransition_apply I M U _ i j x hx,
      Cech.add_value]
    exact unitSectionEval_add (c.value i j) (d.value i j) ⟨x, hx⟩
  · simp only [cocycleTransition_of_not_mem I M U _ i j x hx, mul_one]

/-- The zero cocycle gives literal identity transition functions. -/
@[simp] theorem data_zero_transition (i j : ι) (x : M) :
    (cocycleTransitionData I M U hcover
      (0 : CechOneCocycle (unitsSheaf I M) U)).transition i j x = 1 := by
  classical
  change cocycleTransition I M U 0 i j x = 1
  by_cases hx : x ∈ U i ⊓ U j
  · apply Units.ext
    simp only [Units.val_one, cocycleTransition_apply I M U _ i j x hx,
      Cech.zero_value]
    exact unitSectionEval_zero ⟨x, hx⟩
  · exact cocycleTransition_of_not_mem I M U _ i j x hx

/-- Negation of the actual unit cocycle inverts the native transition. -/
@[simp] theorem data_neg_transition
    (c : CechOneCocycle (unitsSheaf I M) U) (i j : ι) (x : M) :
    (cocycleTransitionData I M U hcover (-c)).transition i j x =
      ((cocycleTransitionData I M U hcover c).transition i j x)⁻¹ := by
  classical
  change cocycleTransition I M U (-c) i j x = (cocycleTransition I M U c i j x)⁻¹
  by_cases hx : x ∈ U i ⊓ U j
  · apply Units.ext
    simp only [Units.val_inv_eq_inv_val, cocycleTransition_apply I M U _ i j x hx,
      Cech.neg_value]
    exact unitSectionEval_neg (c.value i j) ⟨x, hx⟩
  · simp only [cocycleTransition_of_not_mem I M U _ i j x hx, inv_one]

/-- On an actual overlap, reversing the two charts inverts their actual
transition function. -/
theorem data_reverse_transition
    (c : CechOneCocycle (unitsSheaf I M) U) (i j : ι) (x : M)
    (hx : x ∈ U i ⊓ U j) :
    (cocycleTransitionData I M U hcover c).transition j i x =
      ((cocycleTransitionData I M U hcover c).transition i j x)⁻¹ := by
  have h := (cocycleTransitionData I M U hcover c).transition_comp i j i x ⟨hx, hx.1⟩
  rw [(cocycleTransitionData I M U hcover c).transition_self i x hx.1] at h
  exact eq_inv_of_mul_eq_one_left h

end Wikipedia.HopfProblem.HolomorphicPicard.TensorCore
