import Wikipedia.NoExoticSixSphere.SkewConjugation
import Wikipedia.NoExoticSixSphere.OrthogonalConstantVelocity

/-!
# Differentiating conjugation by an actual exponential

Conjugation along `exp(t K)` differentiates to the commutator with `K`.
This supplies the rotating fields used to evaluate the energy index form.
-/

open scoped ContDiff

namespace NoExoticSixSphere.SkewConjugation

open GLOrthonormalization OrthogonalPaths CayleyTransform OrthogonalExponential
  OrthogonalConstantVelocity OrthogonalCommutator

variable {n : ℕ}

theorem exp_smul_commute (K : SkewOperators n) (t : ℝ) :
    (exp (t • K)).1.1.comp (K : Vector n →L[ℝ] Vector n) =
      (K : Vector n →L[ℝ] Vector n).comp (exp (t • K)).1.1 := by
  exact ((Commute.refl (K : Vector n →L[ℝ] Vector n)).smul_left t).exp_left.eq

theorem contDiff_exp_smul_operator (K : SkewOperators n) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ (exp (t • K)).1.1) :=
  ContDiff.comp (g := fun L : SkewOperators n ↦ (exp L).1.1)
    (f := fun t : ℝ ↦ t • K) contDiff_exp_operator (contDiff_id.smul contDiff_const)

theorem contDiff_conjugate_exp (K A : SkewOperators n) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ conjugate (exp (t • K)) A) :=
  contDiff_conjugate (contDiff_exp_smul_operator K) contDiff_const

theorem hasDerivAt_conjugate_exp (K A : SkewOperators n) (t : ℝ) :
    HasDerivAt (fun r : ℝ ↦ (conjugate (exp (r • K)) A : Vector n →L[ℝ] Vector n))
      (commutator (K : Vector n →L[ℝ] Vector n)
        (conjugate (exp (t • K)) A : Vector n →L[ℝ] Vector n)) t := by
  have hd := (hasDerivAt_exp_smul_operator K t).clm_comp
    ((hasDerivAt_const t (A : Vector n →L[ℝ] Vector n)).clm_comp (hasDerivAt_inverse_exp K t))
  apply hd.congr_deriv
  rw [commutator_conjugate _ _ _ (exp_smul_commute K t)]
  simp only [OrthogonalCommutator.commutator, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.zero_comp, zero_add,
    ContinuousLinearMap.comp_neg, ContinuousLinearMap.neg_comp,
    ContinuousLinearMap.comp_assoc, sub_eq_add_neg]

end NoExoticSixSphere.SkewConjugation
