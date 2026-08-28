import Wikipedia.NoExoticSixSphere.SkewSpectralPlane
import Wikipedia.NoExoticSixSphere.OrthogonalCommutator

/-!
# Actual skew wedge operators and their Hilbert--Schmidt form

The wedge of two real vectors is the difference of their two rank-one
operators. Its commutator with `K` differentiates each vector, and its
Hilbert--Schmidt pairing is the usual two-by-two Gram determinant.
-/

namespace NoExoticSixSphere.SkewWedge

open GLOrthonormalization CayleyTransform HilbertSchmidt OrthogonalCommutator InnerProductSpace

variable {n : ℕ}

noncomputable def operator (x y : Vector n) : Vector n →L[ℝ] Vector n :=
  rankOne ℝ y x - rankOne ℝ x y

theorem operator_apply (x y z : Vector n) :
    operator x y z = inner ℝ x z • y - inner ℝ y z • x := rfl

theorem operator_mem_skew (x y : Vector n) :
    operator x y ∈ skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n) := by
  change (operator x y).adjoint = -operator x y
  simp only [operator, map_sub, adjoint_rankOne, neg_sub]

noncomputable def skew (x y : Vector n) : SkewOperators n :=
  ⟨operator x y, operator_mem_skew x y⟩

theorem innerForm_rankOne (x y u v : Vector n) :
    innerForm (rankOne ℝ x y) (rankOne ℝ u v) = inner ℝ x u * inner ℝ y v := by
  rw [innerForm_eq_trace, adjoint_rankOne, rankOne_comp_rankOne]
  change LinearMap.trace ℝ (Vector n)
    (inner ℝ x u • (rankOne ℝ y v).toLinearMap) = _
  rw [map_smul, trace_rankOne, smul_eq_mul, real_inner_comm v y]

theorem innerForm_sub_left (A B C : Vector n →L[ℝ] Vector n) :
    innerForm (A - B) C = innerForm A C - innerForm B C := by
  simp only [innerForm, sub_apply, inner_sub_left, Finset.sum_sub_distrib]

theorem innerForm_sub_right (A B C : Vector n →L[ℝ] Vector n) :
    innerForm A (B - C) = innerForm A B - innerForm A C := by
  simp only [innerForm, sub_apply, inner_sub_right, Finset.sum_sub_distrib]

theorem innerForm_operator (x y u v : Vector n) :
    innerForm (operator x y) (operator u v) =
      2 * (inner ℝ x u * inner ℝ y v - inner ℝ x v * inner ℝ y u) := by
  simp only [operator, innerForm_sub_left, innerForm_sub_right, innerForm_rankOne]
  ring

theorem operator_smul_left (r : ℝ) (x y : Vector n) : operator (r • x) y = r • operator x y := by
  apply ContinuousLinearMap.ext
  intro z
  change inner ℝ (r • x) z • y - inner ℝ y z • (r • x) =
    r • (inner ℝ x z • y - inner ℝ y z • x)
  simp only [inner_smul_left, RCLike.conj_to_real, smul_sub, smul_smul]
  module

theorem operator_smul_right (r : ℝ) (x y : Vector n) : operator x (r • y) = r • operator x y := by
  apply ContinuousLinearMap.ext
  intro z
  change inner ℝ x z • (r • y) - inner ℝ (r • y) z • x =
    r • (inner ℝ x z • y - inner ℝ y z • x)
  simp only [inner_smul_left, RCLike.conj_to_real, smul_sub, smul_smul]
  module

theorem commutator_operator (K : SkewOperators n) (x y : Vector n) :
    commutator (K : Vector n →L[ℝ] Vector n) (operator x y) =
      operator ((K : Vector n →L[ℝ] Vector n) x) y +
        operator x ((K : Vector n →L[ℝ] Vector n) y) := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [OrthogonalCommutator.commutator, sub_apply,
    ContinuousLinearMap.comp_apply, add_apply, operator_apply,
    map_sub, map_smul, SkewSpectralPlane.inner_skew, neg_smul]
  abel

end NoExoticSixSphere.SkewWedge
