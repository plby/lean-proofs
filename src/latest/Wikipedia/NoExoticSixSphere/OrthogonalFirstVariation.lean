import Wikipedia.NoExoticSixSphere.OrthogonalMaurerCartan
import Wikipedia.NoExoticSixSphere.OrthogonalPathEnergy
import Wikipedia.NoExoticSixSphere.SmoothIntervalIntegral
import Wikipedia.NoExoticSixSphere.HilbertSchmidtIntegration

/-!
# First variation of the actual orthogonal path energy

The energy is the integral of the Hilbert--Schmidt squared norm of the ambient
operator derivative. Orthogonal invariance identifies it with squared body
velocity. The Maurer--Cartan identity, differentiation under the integral, and
integration by parts give the first-variation formula including boundary terms.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalFirstVariation

open GLOrthonormalization OrthogonalPaths HilbertSchmidt OrthogonalPathEnergy
  OrthogonalMaurerCartan TwoParameterCalculus

variable {n : ℕ} {a : ℝ × ℝ → OrthogonalOperators n}
  (ha : ContDiff ℝ ∞ (operator a))

include ha

theorem energy_eq_bodyVelocity (s l u : ℝ) :
    energy (fun t ↦ operator a (s, t)) l u =
      ∫ t in l..u, squareNorm (velocity a (s, t)) := by
  unfold energy
  apply intervalIntegral.integral_congr
  intro t _
  have hd : HasDerivAt (fun r ↦ operator a (s, r)) (second (operator a) (s, t)) t :=
    hasDerivAt_second ((ha.differentiable (by simp)) (s, t))
  exact (congrArg (squareNorm (n := n)) hd.deriv).trans
    (squareNorm_left (inverse (a (s, t))) (second (operator a) (s, t))).symm

theorem hasDerivAt_energy (s l u : ℝ) :
    HasDerivAt (fun r ↦ energy (fun t ↦ operator a (r, t)) l u)
      (2 * ∫ t in l..u, innerForm (velocity a (s, t))
        (second (variation a) (s, t))) s := by
  have hF : Continuous (fun p ↦ squareNorm (velocity a p)) :=
    Continuous.comp (g := squareNorm (n := n)) (f := velocity a)
      (contDiff_squareNorm (n := n)).continuous (contDiff_velocity ha).continuous
  have hG₀ : Continuous (fun p ↦ innerForm (velocity a p) (second (variation a) p)) :=
    Continuous.comp
      (g := fun q : (Vector n →L[ℝ] Vector n) × (Vector n →L[ℝ] Vector n) ↦
        innerForm q.1 q.2) (f := fun p ↦ (velocity a p, second (variation a) p))
      (contDiff_innerForm (n := n)).continuous
      ((contDiff_velocity ha).continuous.prodMk
        (contDiff_second (contDiff_variation ha)).continuous)
  have hd := SmoothIntervalIntegral.hasDerivAt_integral_of_continuous hF
    (continuous_const.mul hG₀) (hasDerivAt_squareSpeed ha) s l u
  have heq : (fun r ↦ energy (fun t ↦ operator a (r, t)) l u) =
      (fun r ↦ ∫ t in l..u, squareNorm (velocity a (r, t))) := by
    funext r
    exact energy_eq_bodyVelocity ha r l u
  rw [heq, ← intervalIntegral.integral_const_mul]
  exact hd

/-- First variation, with both endpoint contributions retained. -/
theorem hasDerivAt_energy_boundary (s l u : ℝ) :
    HasDerivAt (fun r ↦ energy (fun t ↦ operator a (r, t)) l u)
      (2 * (innerForm (velocity a (s, u)) (variation a (s, u)) -
        innerForm (velocity a (s, l)) (variation a (s, l)) -
        ∫ t in l..u, innerForm (second (velocity a) (s, t)) (variation a (s, t)))) s := by
  have hV := (contDiff_velocity ha).continuous.comp
    (continuous_const.prodMk continuous_id : Continuous (fun t : ℝ ↦ (s, t)))
  have hW := (contDiff_variation ha).continuous.comp
    (continuous_const.prodMk continuous_id : Continuous (fun t : ℝ ↦ (s, t)))
  have hV' := (contDiff_second (contDiff_velocity ha)).continuous.comp
    (continuous_const.prodMk continuous_id : Continuous (fun t : ℝ ↦ (s, t)))
  have hW' := (contDiff_second (contDiff_variation ha)).continuous.comp
    (continuous_const.prodMk continuous_id : Continuous (fun t : ℝ ↦ (s, t)))
  have hparts := integral_innerForm_derivative hV hW hV' hW'
    (fun t ↦ hasDerivAt_second (((contDiff_velocity ha).differentiable (by simp)) (s, t)))
    (fun t ↦ hasDerivAt_second (((contDiff_variation ha).differentiable (by simp)) (s, t)))
    l u
  simp only [Function.comp_apply] at hparts
  rw [← hparts]
  exact hasDerivAt_energy ha s l u

theorem variation_eq_zero_of_constant_slice (t s : ℝ)
    (h : ∀ r, a (r, t) = a (s, t)) : variation a (s, t) = 0 := by
  have hd := hasDerivAt_first ((ha.differentiable (by simp)) (s, t))
  have heq : (fun r ↦ operator a (r, t)) = (fun _ : ℝ ↦ operator a (s, t)) := by
    funext r
    exact congrArg (fun b : OrthogonalOperators n ↦ b.1.1) (h r)
  rw [heq] at hd
  have hz := hd.unique (hasDerivAt_const s (operator a (s, t)))
  simp only [variation, hz, ContinuousLinearMap.comp_zero]

/-- Fixed endpoint slices remove the boundary terms from the actual derivative of energy. -/
theorem hasDerivAt_energy_fixedEndpoints (s l u : ℝ)
    (hl : ∀ r, a (r, l) = a (s, l)) (hu : ∀ r, a (r, u) = a (s, u)) :
    HasDerivAt (fun r ↦ energy (fun t ↦ operator a (r, t)) l u)
      (-2 * ∫ t in l..u, innerForm (second (velocity a) (s, t)) (variation a (s, t))) s := by
  have hd := hasDerivAt_energy_boundary ha s l u
  rw [variation_eq_zero_of_constant_slice ha l s hl,
    variation_eq_zero_of_constant_slice ha u s hu] at hd
  have hz (A : Vector n →L[ℝ] Vector n) : innerForm A 0 = 0 := by simp [innerForm]
  simpa only [hz, sub_self, zero_sub, mul_neg, neg_mul] using hd

end NoExoticSixSphere.OrthogonalFirstVariation
