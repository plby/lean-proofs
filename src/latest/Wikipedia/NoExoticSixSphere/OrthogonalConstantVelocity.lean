import Wikipedia.NoExoticSixSphere.OrthogonalInverseDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Solving the constant-body-velocity equation

An actual orthogonal curve satisfying `γ' = γ K` is `γ(0) * exp(t K)`.
The proof differentiates its product with the inverse exponential and uses
the mean-value theorem. No separate differential-equation uniqueness result
or classification input is assumed.
-/

namespace NoExoticSixSphere.OrthogonalConstantVelocity

open GLOrthonormalization OrthogonalPaths CayleyTransform OrthogonalExponential
  OrthogonalVelocity

variable {n : ℕ}

theorem hasDerivAt_inverse_exp (K : SkewOperators n) (t : ℝ) :
    HasDerivAt (fun r : ℝ ↦ (inverse (exp (r • K))).1.1)
      (-((K : Vector n →L[ℝ] Vector n).comp (inverse (exp (t • K))).1.1)) t := by
  have hd := hasDerivAt_inverse (hasDerivAt_exp_smul_operator K t)
  have heq : (inverse (exp (t • K))).1.1.comp
      (((exp (t • K)).1.1.comp (K : Vector n →L[ℝ] Vector n)).comp
        (inverse (exp (t • K))).1.1) =
      (K : Vector n →L[ℝ] Vector n).comp (inverse (exp (t • K))).1.1 := by
    apply ContinuousLinearMap.ext
    intro x
    exact inverse_apply_self (exp (t • K)) _
  rw [heq] at hd
  exact hd

theorem eq_mul_exp_of_hasDerivAt (γ : ℝ → OrthogonalOperators n) (K : SkewOperators n)
    (hγ : ∀ t, HasDerivAt (fun r ↦ (γ r).1.1)
      ((γ t).1.1.comp (K : Vector n →L[ℝ] Vector n)) t) (t : ℝ) :
    γ t = γ 0 * exp (t • K) := by
  let F : ℝ → Vector n →L[ℝ] Vector n :=
    fun r ↦ (γ r).1.1.comp (inverse (exp (r • K))).1.1
  have hd (r : ℝ) : HasDerivAt F 0 r := by
    simpa only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_assoc,
      add_neg_cancel] using! (hγ r).clm_comp (hasDerivAt_inverse_exp K r)
  have hc : F t = F 0 := is_const_of_deriv_eq_zero
    (fun r ↦ (hd r).differentiableAt) (fun r ↦ (hd r).deriv) t 0
  have hgroup : γ t * (exp (t • K))⁻¹ = γ 0 := by
    calc
      _ = γ 0 * (exp ((0 : ℝ) • K))⁻¹ := by
        apply Subtype.ext
        apply Subtype.ext
        exact hc
      _ = γ 0 := by rw [zero_smul, exp_zero, inv_one, mul_one]
  calc
    γ t = (γ t * (exp (t • K))⁻¹) * exp (t • K) :=
      (inv_mul_cancel_right _ _).symm
    _ = γ 0 * exp (t • K) := by rw [hgroup]

/-- A differentiable curve with constant actual body velocity is exponential. -/
theorem eq_mul_exp_of_bodyVelocity (γ : ℝ → OrthogonalOperators n) (K : SkewOperators n)
    (hγ : Differentiable ℝ (fun r ↦ (γ r).1.1))
    (hK : ∀ t, (inverse (γ t)).1.1.comp (deriv (fun r ↦ (γ r).1.1) t) =
      (K : Vector n →L[ℝ] Vector n)) (t : ℝ) :
    γ t = γ 0 * exp (t • K) := by
  apply eq_mul_exp_of_hasDerivAt γ K _ t
  intro r
  apply (hγ r).hasDerivAt.congr_deriv
  rw [← hK r]
  apply ContinuousLinearMap.ext
  intro x
  exact (self_apply_inverse (γ r) _).symm

theorem eq_of_hasDerivAt_zero_Ioo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {l u : ℝ} (hlu : l < u) (hf : Continuous f)
    (hd : ∀ t ∈ Set.Ioo l u, HasDerivAt f 0 t)
    {s t : ℝ} (hs : s ∈ Set.Icc l u) (ht : t ∈ Set.Icc l u) : f s = f t := by
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun r hr ↦ (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr ↦ (hd r hr).deriv)
  have he : Set.EqOn f (fun _ ↦ c) (Set.Ioo l u) := hc
  have hec := he.closure hf continuous_const
  rw [closure_Ioo hlu.ne] at hec
  exact (hec hs).trans (hec ht).symm

/-- The same ODE solution on a closed interval, with derivatives needed only in its interior. -/
theorem eq_mul_exp_on_Icc (γ : ℝ → OrthogonalOperators n) (K : SkewOperators n)
    {l u : ℝ} (hlu : l < u) (hc : Continuous (fun r ↦ (γ r).1.1))
    (hγ : ∀ r ∈ Set.Ioo l u, HasDerivAt (fun t ↦ (γ t).1.1)
      ((γ r).1.1.comp (K : Vector n →L[ℝ] Vector n)) r)
    {t : ℝ} (ht : t ∈ Set.Icc l u) : γ t = γ l * exp ((t - l) • K) := by
  let F : ℝ → Vector n →L[ℝ] Vector n :=
    fun r ↦ (γ r).1.1.comp (inverse (exp (r • K))).1.1
  have hF : Continuous F := hc.clm_comp
    (continuous_iff_continuousAt.mpr (fun r ↦ (hasDerivAt_inverse_exp K r).continuousAt))
  have hd (r : ℝ) (hr : r ∈ Set.Ioo l u) : HasDerivAt F 0 r := by
    simpa only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_assoc,
      add_neg_cancel] using! (hγ r hr).clm_comp (hasDerivAt_inverse_exp K r)
  have heq : F t = F l := eq_of_hasDerivAt_zero_Ioo hlu hF hd ht ⟨le_rfl, hlu.le⟩
  have hgroup : γ t * (exp (t • K))⁻¹ = γ l * (exp (l • K))⁻¹ := by
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  have hexp : (exp (l • K))⁻¹ * exp (t • K) = exp ((t - l) • K) := by
    rw [← exp_neg, ← neg_smul, ← exp_add_smul]
    congr 2
    ring
  calc
    γ t = (γ t * (exp (t • K))⁻¹) * exp (t • K) :=
      (inv_mul_cancel_right _ _).symm
    _ = (γ l * (exp (l • K))⁻¹) * exp (t • K) := by rw [hgroup]
    _ = γ l * exp ((t - l) • K) := by rw [_root_.mul_assoc, hexp]

end NoExoticSixSphere.OrthogonalConstantVelocity
