import Wikipedia.NoExoticSixSphere.OrthogonalInverseDerivative
import Wikipedia.NoExoticSixSphere.OrthogonalCommutator
import Wikipedia.NoExoticSixSphere.TwoParameterCalculus

/-!
# The Maurer--Cartan identity for actual orthogonal variations

For a smooth two-parameter family `a(s,t)`, define `V = a⁻¹ ∂t a` and
`W = a⁻¹ ∂s a` using actual Fréchet derivatives. Differentiating the inverse
and using equality of mixed partials proves `∂s V = ∂t W + [V,W]`.
Pairing with `V` eliminates the commutator in the variation of squared speed.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalMaurerCartan

open GLOrthonormalization OrthogonalPaths CayleyTransform OrthogonalVelocity
  OrthogonalCommutator HilbertSchmidt TwoParameterCalculus

variable {n : ℕ}

abbrev operator (a : ℝ × ℝ → OrthogonalOperators n) (p : ℝ × ℝ) := (a p).1.1

noncomputable def velocity (a : ℝ × ℝ → OrthogonalOperators n) (p : ℝ × ℝ) :
    Vector n →L[ℝ] Vector n :=
  (inverse (a p)).1.1.comp (second (operator a) p)

noncomputable def variation (a : ℝ × ℝ → OrthogonalOperators n) (p : ℝ × ℝ) :
    Vector n →L[ℝ] Vector n :=
  (inverse (a p)).1.1.comp (first (operator a) p)

variable {a : ℝ × ℝ → OrthogonalOperators n} (ha : ContDiff ℝ ∞ (operator a))

include ha

theorem contDiff_inverse_operator :
    ContDiff ℝ ∞ (fun p ↦ (inverse (a p)).1.1) := by
  let L : (Vector n →L[ℝ] Vector n) →L[ℝ] (Vector n →L[ℝ] Vector n) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  simpa only [L, inverse_eq_adjoint] using! L.contDiff.comp ha

theorem contDiff_velocity : ContDiff ℝ ∞ (velocity a) :=
  (contDiff_inverse_operator ha).clm_comp (contDiff_second ha)

theorem contDiff_variation : ContDiff ℝ ∞ (variation a) :=
  (contDiff_inverse_operator ha).clm_comp (contDiff_first ha)

theorem first_velocity (p : ℝ × ℝ) :
    first (velocity a) p = -(variation a p).comp (velocity a p) +
      (inverse (a p)).1.1.comp (first (second (operator a)) p) := by
  have hA := hasDerivAt_first ((ha.differentiable (by simp)) p)
  have hB := hasDerivAt_first (((contDiff_second ha).differentiable (by simp)) p)
  exact (hasDerivAt_first (((contDiff_velocity ha).differentiable (by simp)) p)).unique
    (hasDerivAt_leftTrivialized hA hB)

theorem second_variation (p : ℝ × ℝ) :
    second (variation a) p = -(velocity a p).comp (variation a p) +
      (inverse (a p)).1.1.comp (second (first (operator a)) p) := by
  have hA := hasDerivAt_second ((ha.differentiable (by simp)) p)
  have hB := hasDerivAt_second (((contDiff_first ha).differentiable (by simp)) p)
  exact (hasDerivAt_second (((contDiff_variation ha).differentiable (by simp)) p)).unique
    (hasDerivAt_leftTrivialized hA hB)

/-- The identity for genuine mixed derivatives of the operator family. -/
theorem maurer_cartan (p : ℝ × ℝ) :
    first (velocity a) p = second (variation a) p +
      commutator (velocity a p) (variation a p) := by
  rw [first_velocity ha, second_variation ha, first_second ha]
  unfold OrthogonalCommutator.commutator
  abel

theorem velocity_mem_skew (p : ℝ × ℝ) :
    velocity a p ∈ skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n) :=
  adjoint_velocity (fun t ↦ a (p.1, t)) (second (operator a) p) p.2
    (hasDerivAt_second ((ha.differentiable (by simp)) p))

/-- The local energy-density variation, before integrating in the path variable. -/
theorem hasDerivAt_squareSpeed (s t : ℝ) :
    HasDerivAt (fun r ↦ squareNorm (velocity a (r, t)))
      (2 * innerForm (velocity a (s, t)) (second (variation a) (s, t))) s := by
  have hd := hasDerivAt_squareNorm
    (hasDerivAt_first (((contDiff_velocity ha).differentiable (by simp)) (s, t)))
  have hc : innerForm (velocity a (s, t))
      (commutator (velocity a (s, t)) (variation a (s, t))) = 0 :=
    innerForm_self_commutator ⟨velocity a (s, t), velocity_mem_skew ha (s, t)⟩ _
  rw [maurer_cartan ha, innerForm_add_right, hc, add_zero] at hd
  exact hd

end NoExoticSixSphere.OrthogonalMaurerCartan
