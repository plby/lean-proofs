import Wikipedia.NoExoticSixSphere.HilbertSchmidt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Ambient energy of orthogonal exponential segments

Energy is defined using the actual operator curve and the Hilbert--Schmidt
quadratic form on its derivative. Exponential segments have constant squared
speed, proved from their actual derivatives and orthogonal invariance.
-/

namespace NoExoticSixSphere.OrthogonalPathEnergy

open GLOrthonormalization CayleyTransform OrthogonalExponential HilbertSchmidt

variable {n : ℕ}

noncomputable def energy (γ : ℝ → Vector n →L[ℝ] Vector n) (s u : ℝ) : ℝ :=
  ∫ t in s..u, squareNorm (deriv γ t)

theorem energy_nonneg (γ : ℝ → Vector n →L[ℝ] Vector n) {s u : ℝ} (hsu : s ≤ u) :
    0 ≤ energy γ s u :=
  intervalIntegral.integral_nonneg_of_forall hsu (fun t ↦ squareNorm_nonneg (deriv γ t))

theorem hasDerivAt_left_exp (a : OrthogonalOperators n) (K : SkewOperators n) (t : ℝ) :
    HasDerivAt (fun r : ℝ ↦ (a * exp (r • K)).1.1)
      (a.1.1.comp ((exp (t • K)).1.1.comp (K : Vector n →L[ℝ] Vector n))) t := by
  let L : (Vector n →L[ℝ] Vector n) →L[ℝ] (Vector n →L[ℝ] Vector n) :=
    ContinuousLinearMap.compL ℝ (Vector n) (Vector n) (Vector n) a.1.1
  exact L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_operator K t)

theorem deriv_left_exp (a : OrthogonalOperators n) (K : SkewOperators n) (t : ℝ) :
    deriv (fun r : ℝ ↦ (a * exp (r • K)).1.1) t =
      a.1.1.comp ((exp (t • K)).1.1.comp (K : Vector n →L[ℝ] Vector n)) :=
  (hasDerivAt_left_exp a K t).deriv

theorem squareNorm_deriv_left_exp (a : OrthogonalOperators n) (K : SkewOperators n) (t : ℝ) :
    squareNorm (deriv (fun r : ℝ ↦ (a * exp (r • K)).1.1) t) =
      squareNorm (K : Vector n →L[ℝ] Vector n) := by
  rw [deriv_left_exp, squareNorm_left, squareNorm_left]

/-- The signed interval-energy formula; for ordered endpoints this energy is nonnegative. -/
theorem energy_left_exp (a : OrthogonalOperators n) (K : SkewOperators n) (s u : ℝ) :
    energy (fun r : ℝ ↦ (a * exp (r • K)).1.1) s u =
      (u - s) * squareNorm (K : Vector n →L[ℝ] Vector n) := by
  unfold energy
  simp only [squareNorm_deriv_left_exp, intervalIntegral.integral_const, smul_eq_mul]

end NoExoticSixSphere.OrthogonalPathEnergy
