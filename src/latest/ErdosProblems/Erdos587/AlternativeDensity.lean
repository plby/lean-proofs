import ErdosProblems.Erdos587.AlternativeRoots

/-!
# Positive integrals in the alternative main term

This module transfers the complete-root lower bound from the physical
periodization to real weighted integrals.
-/

open MeasureTheory
open scoped BigOperators SchwartzMap

namespace Erdos587

lemma integrable_schwartz_weighted_comp (f g : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ)
    (θ : ℝ → ℝ) (hθ : Continuous θ) :
    Integrable (fun x : ℝ => f (δ * x) * g (θ x)) := by
  have hf : Integrable (fun x : ℝ => f (δ * x)) := by
    change Integrable (dilateSchwartz f δ hδ.ne' : ℝ → ℂ)
    exact (dilateSchwartz f δ hδ.ne').integrable
  have hcont : Continuous (fun x : ℝ => f (δ * x) * g (θ x)) :=
    (f.continuous.comp (continuous_const.mul continuous_id)).mul (g.continuous.comp hθ)
  apply (hf.norm.const_mul (SchwartzMap.seminorm ℝ 0 0 g)).mono' hcont.aestronglyMeasurable
  filter_upwards [] with x
  rw [norm_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (SchwartzMap.norm_le_seminorm ℝ g (θ x)) (norm_nonneg (f (δ * x)))

lemma integrable_real_schwartz_weighted_comp (f g : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ)
    (θ : ℝ → ℝ) (hθ : Continuous θ) (hf : ∀ x : ℝ, (f x).im = 0) :
    Integrable (fun x : ℝ => (f (δ * x)).re * (g (θ x)).re) := by
  have hh := (integrable_schwartz_weighted_comp f g hδ θ hθ).re
  change Integrable (fun x : ℝ => (f (δ * x) * g (θ x)).re) at hh
  simpa only [Complex.mul_re, hf, zero_mul, sub_zero] using hh

lemma integrable_real_weighted_periodization (f g : 𝓢(ℝ, ℂ)) {δ σ : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (θ : ℝ → ℝ) (hθ : Continuous θ)
    (hf : ∀ x : ℝ, (f x).im = 0) :
    Integrable (fun x : ℝ => (f (δ * x)).re * (periodizedSchwartz g σ (θ x)).re) := by
  have hh := (integrable_weighted_periodization f g hδ hσ θ hθ).re
  change Integrable (fun x : ℝ => (f (δ * x) * periodizedSchwartz g σ (θ x)).re) at hh
  simpa only [Complex.mul_re, hf, zero_mul, sub_zero] using hh

lemma alternativeSquareMain_re (f g : 𝓢(ℝ, ℂ)) (a u b v t : ℕ)
    {L σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) (hf : ∀ x : ℝ, (f x).im = 0) :
    (alternativeSquareMain f g a u b v t L σ).re =
      (u : ℝ)⁻¹ * ∑ r : Fin u, ∫ x : ℝ, (f (L⁻¹ * x)).re *
        (periodizedSchwartz g σ (alternativeRootArgument a u b v t (r : ℕ) x)).re := by
  have hcoeff : (u : ℂ)⁻¹ = (((u : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  unfold alternativeSquareMain
  rw [hcoeff, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  have hsum (F : Fin u → ℂ) : (∑ r : Fin u, F r).re = ∑ r : Fin u, (F r).re := by
    exact map_sum Complex.reCLM F Finset.univ
  rw [hsum]
  apply Finset.sum_congr rfl
  intro r hr
  exact re_integral_weighted_periodization f g (inv_pos.mpr hL) hσ _
    (continuous_alternativeRootArgument a u b v t (r : ℕ)) hf

lemma alternativeSquareMain_re_nonneg (f g : 𝓢(ℝ, ℂ)) (a u b v t : ℕ)
    {L σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) (hf : ∀ x : ℝ, (f x).im = 0)
    (hfpos : ∀ x : ℝ, 0 ≤ (f x).re) (hgpos : ∀ x : ℝ, 0 ≤ (g x).re) :
    0 ≤ (alternativeSquareMain f g a u b v t L σ).re := by
  rw [alternativeSquareMain_re f g a u b v t hL hσ hf]
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg u))
  apply Finset.sum_nonneg
  intro r hr
  apply integral_nonneg
  intro x
  exact mul_nonneg (hfpos _) (re_periodizedSchwartz_nonneg g hσ hgpos _)

/-- Retain any finite collection of complete roots inside the alternative main term. -/
theorem complete_root_integrals_le_alternativeMain (f g : 𝓢(ℝ, ℂ))
    {a u b v H : ℕ} (hu : 0 < u) (hv : 0 < v) (hH : 0 < H)
    (hab : a * u = b * v + 1) (t : ℕ) (Y : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (hf : ∀ x : ℝ, (f x).im = 0)
    (hfpos : ∀ x : ℝ, 0 ≤ (f x).re) (hgpos : ∀ x : ℝ, 0 ≤ (g x).re) :
    (u : ℝ)⁻¹ * (∑ y ∈ Y, (squareRootCount u (t + v * y) : ℝ) *
      ∫ z : ℝ, (f (L⁻¹ * z)).re * (g ((z ^ 2 - t - (v : ℝ) * y) / (u * H))).re) ≤
      (alternativeSquareMain f g a u b v t L (((v : ℝ) / H)⁻¹)).re := by
  let σ : ℝ := ((v : ℝ) / H)⁻¹
  have hσ : 0 < σ := inv_pos.mpr
    (div_pos (by exact_mod_cast hv) (by exact_mod_cast hH))
  let F (y : ℕ) (z : ℝ) := (f (L⁻¹ * z)).re *
    (g ((z ^ 2 - t - (v : ℝ) * y) / (u * H))).re
  let P (r : Fin u) (z : ℝ) := (f (L⁻¹ * z)).re *
    (periodizedSchwartz g σ (alternativeRootArgument a u b v t (r : ℕ) z)).re
  have hF (y : ℕ) : Integrable (F y) := by
    apply integrable_real_schwartz_weighted_comp f g (inv_pos.mpr hL) _ _ hf
    fun_prop
  have hP (r : Fin u) : Integrable (P r) :=
    integrable_real_weighted_periodization f g (inv_pos.mpr hL) hσ _
      (continuous_alternativeRootArgument a u b v t (r : ℕ)) hf
  have hpoint (z : ℝ) :
      (∑ y ∈ Y, (squareRootCount u (t + v * y) : ℝ) * F y z) ≤
        ∑ r : Fin u, P r z := by
    have hh := mul_le_mul_of_nonneg_left
      (complete_roots_le_alternative_periods g hu hv hH hab hgpos t Y z) (hfpos (L⁻¹ * z))
    simpa only [Finset.mul_sum, F, P, σ, mul_left_comm] using hh
  have hleft (y : ℕ) : Integrable (fun z : ℝ =>
      (squareRootCount u (t + v * y) : ℝ) * F y z) := (hF y).const_mul _
  have hint := integral_mono (integrable_finsetSum Y (fun y _ => hleft y))
    (integrable_finsetSum Finset.univ (fun r _ => hP r)) hpoint
  rw [integral_finsetSum Y (fun y _ => hleft y),
    integral_finsetSum Finset.univ (fun r _ => hP r)] at hint
  simp_rw [integral_const_mul] at hint
  rw [alternativeSquareMain_re f g a u b v t hL hσ hf]
  exact mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (Nat.cast_nonneg u))

end Erdos587
