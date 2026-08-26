/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# The residue-one factor in the Selberg zeta quotient

The singularity of `z * ζ(1+z)` at zero is filled with its proved limit.
The resulting continuous function packages the uniform comparison of the
zeta quotient with `s*t/(s+t)`; it is not an analytic assumption.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped Topology

def selbergZetaResidueFactor (z : ℂ) : ℂ :=
  Function.update (fun s : ℂ ↦ (s - 1) * riemannZeta s) 1 1 (1 + z)

@[simp] theorem selbergZetaResidueFactor_zero :
    selbergZetaResidueFactor 0 = 1 := by
  simp [selbergZetaResidueFactor]

theorem selbergZetaResidueFactor_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    selbergZetaResidueFactor z = z * riemannZeta (1 + z) := by
  have hne : 1 + z ≠ (1 : ℂ) := by simpa using hz
  simp [selbergZetaResidueFactor, Function.update_of_ne hne]

theorem continuousAt_selbergZetaResidueFactor_zero :
    ContinuousAt selbergZetaResidueFactor 0 := by
  have h : ContinuousAt
      (Function.update (fun s : ℂ ↦ (s - 1) * riemannZeta s) 1 1) 1 := by
    simpa only [continuousAt_update_same] using riemannZeta_residue_one
  simpa only [selbergZetaResidueFactor, Function.comp_def, Pi.add_apply] using!
    h.comp_of_eq (continuousAt_const.add continuousAt_id :
      ContinuousAt (fun z : ℂ ↦ 1 + z) 0) (by simp)

def selbergZetaQuotientCorrection (s t : ℂ) : ℂ :=
  selbergZetaResidueFactor (s + t) /
    (selbergZetaResidueFactor s * selbergZetaResidueFactor t)

@[simp] theorem selbergZetaQuotientCorrection_zero :
    selbergZetaQuotientCorrection 0 0 = 1 := by
  simp [selbergZetaQuotientCorrection]

theorem continuousAt_selbergZetaQuotientCorrection_zero :
    ContinuousAt (fun z : ℂ × ℂ ↦ selbergZetaQuotientCorrection z.1 z.2)
      (0, 0) := by
  have hs : ContinuousAt
      (fun z : ℂ × ℂ ↦ selbergZetaResidueFactor z.1) (0, 0) :=
    continuousAt_selbergZetaResidueFactor_zero.comp_of_eq
      (continuousAt_fst : ContinuousAt (Prod.fst : ℂ × ℂ → ℂ) (0, 0)) rfl
  have ht : ContinuousAt
      (fun z : ℂ × ℂ ↦ selbergZetaResidueFactor z.2) (0, 0) :=
    continuousAt_selbergZetaResidueFactor_zero.comp_of_eq
      (continuousAt_snd : ContinuousAt (Prod.snd : ℂ × ℂ → ℂ) (0, 0)) rfl
  have hst : ContinuousAt
      (fun z : ℂ × ℂ ↦ selbergZetaResidueFactor (z.1 + z.2)) (0, 0) :=
    continuousAt_selbergZetaResidueFactor_zero.comp_of_eq
      (continuousAt_fst.add continuousAt_snd :
        ContinuousAt (fun z : ℂ × ℂ ↦ z.1 + z.2) (0, 0)) (by simp)
  exact hst.div (hs.mul ht) (by simp)

theorem selbergZetaQuotient_eq_main_mul_correction
    {s t : ℂ} (hs : s ≠ 0) (ht : t ≠ 0) (hst : s + t ≠ 0) :
    riemannZeta (1 + s + t) /
        (riemannZeta (1 + s) * riemannZeta (1 + t)) =
      (s * t / (s + t)) * selbergZetaQuotientCorrection s t := by
  unfold selbergZetaQuotientCorrection
  rw [selbergZetaResidueFactor_of_ne_zero hs,
    selbergZetaResidueFactor_of_ne_zero ht,
    selbergZetaResidueFactor_of_ne_zero hst]
  by_cases hzs : riemannZeta (1 + s) = 0
  · simp [hzs]
  by_cases hzt : riemannZeta (1 + t) = 0
  · simp [hzt]
  field_simp [hs, ht, hst, hzs, hzt]
  simp only [add_assoc]

/-- The normalized zeta quotient tends to one along any pair of
parameters tending to zero. -/
theorem tendsto_selbergZetaQuotientCorrection
    {α : Type*} {l : Filter α} {s t : α → ℂ}
    (hs : Tendsto s l (𝓝 0)) (ht : Tendsto t l (𝓝 0)) :
    Tendsto (fun a ↦ selbergZetaQuotientCorrection (s a) (t a)) l (𝓝 1) := by
  simpa only [Function.comp_def, selbergZetaQuotientCorrection_zero] using
    continuousAt_selbergZetaQuotientCorrection_zero.tendsto.comp
    (hs.prodMk_nhds ht)

/-- A uniform two-variable estimate, suitable for Fourier boxes whose
exponents approach zero while the Fourier variables themselves grow. -/
theorem exists_uniform_selbergZetaQuotientCorrection_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s t : ℂ, ‖s‖ < δ → ‖t‖ < δ →
      ‖selbergZetaQuotientCorrection s t - 1‖ < ε := by
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousAt_iff.mp
    continuousAt_selbergZetaQuotientCorrection_zero ε hε
  refine ⟨δ, hδ, fun s t hs ht ↦ ?_⟩
  have hdist : dist (s, t) ((0 : ℂ), (0 : ℂ)) < δ := by
    simpa only [Prod.dist_eq, dist_zero_right] using max_lt hs ht
  simpa only [selbergZetaQuotientCorrection_zero, dist_eq_norm] using hbound hdist

def fourierLaplaceParameter (ξ : ℝ) : ℂ := 1 + Complex.I * ξ

@[simp] theorem fourierLaplaceParameter_re (ξ : ℝ) :
    (fourierLaplaceParameter ξ).re = 1 := by
  simp [fourierLaplaceParameter]

theorem fourierLaplaceParameter_ne_zero (ξ : ℝ) :
    fourierLaplaceParameter ξ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem fourierLaplaceParameter_add_ne_zero (ξ τ : ℝ) :
    fourierLaplaceParameter ξ + fourierLaplaceParameter τ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

theorem norm_fourierLaplaceParameter_le (ξ : ℝ) :
    ‖fourierLaplaceParameter ξ‖ ≤ 1 + |ξ| := by
  simpa only [fourierLaplaceParameter, norm_mul, Complex.norm_I, norm_one,
    one_mul, Complex.norm_real, Real.norm_eq_abs] using
    norm_add_le (1 : ℂ) (Complex.I * ξ)

def fourierLaplacePairKernel (ξ τ : ℝ) : ℂ :=
  fourierLaplaceParameter ξ * fourierLaplaceParameter τ /
    (fourierLaplaceParameter ξ + fourierLaplaceParameter τ)

theorem norm_fourierLaplacePairKernel_le (ξ τ : ℝ) :
    ‖fourierLaplacePairKernel ξ τ‖ ≤
      ‖fourierLaplaceParameter ξ‖ * ‖fourierLaplaceParameter τ‖ / 2 := by
  have hden : (2 : ℝ) ≤
      ‖fourierLaplaceParameter ξ + fourierLaplaceParameter τ‖ := by
    simpa only [Complex.add_re, fourierLaplaceParameter_re, one_add_one_eq_two] using
      Complex.re_le_norm (fourierLaplaceParameter ξ + fourierLaplaceParameter τ)
  rw [fourierLaplacePairKernel, norm_div, norm_mul]
  exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hden

theorem norm_fourierLaplacePairKernel_le_polynomial (ξ τ : ℝ) :
    ‖fourierLaplacePairKernel ξ τ‖ ≤ (1 + |ξ|) * (1 + |τ|) / 2 := by
  apply (norm_fourierLaplacePairKernel_le ξ τ).trans
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul (norm_fourierLaplaceParameter_le ξ)
    (norm_fourierLaplaceParameter_le τ) (norm_nonneg _) (by positivity)

theorem selbergFourierZetaQuotient_identity (ξ τ : ℝ) {L : ℝ} (hL : L ≠ 0) :
    riemannZeta (1 + fourierLaplaceParameter ξ / L + fourierLaplaceParameter τ / L) /
        (riemannZeta (1 + fourierLaplaceParameter ξ / L) *
          riemannZeta (1 + fourierLaplaceParameter τ / L)) =
      (fourierLaplacePairKernel ξ τ / L) *
        selbergZetaQuotientCorrection
          (fourierLaplaceParameter ξ / L) (fourierLaplaceParameter τ / L) := by
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hsum : fourierLaplaceParameter ξ / (L : ℂ) +
      fourierLaplaceParameter τ / L ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (fourierLaplaceParameter_add_ne_zero ξ τ) hLC
  rw [selbergZetaQuotient_eq_main_mul_correction
    (div_ne_zero (fourierLaplaceParameter_ne_zero ξ) hLC)
    (div_ne_zero (fourierLaplaceParameter_ne_zero τ) hLC) hsum]
  congr 1
  unfold fourierLaplacePairKernel
  rw [← add_div]
  field_simp

/-- On a Fourier box, the explicit ratio `(1+T)/L` controls all
parameters simultaneously.  The choice of `δ` is independent of the
box, of its frequencies, and of the logarithmic scale. -/
theorem exists_uniform_selbergFourierZetaQuotientCorrection_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ L T ξ τ : ℝ, 0 < L → |ξ| ≤ T → |τ| ≤ T →
      (1 + T) / L < δ →
      ‖selbergZetaQuotientCorrection
        (fourierLaplaceParameter ξ / L) (fourierLaplaceParameter τ / L) - 1‖ < ε := by
  obtain ⟨δ, hδ, hbound⟩ := exists_uniform_selbergZetaQuotientCorrection_bound hε
  refine ⟨δ, hδ, fun L T ξ τ hL hξ hτ hbox ↦ ?_⟩
  have hnorm (u : ℝ) (hu : |u| ≤ T) :
      ‖fourierLaplaceParameter u / (L : ℂ)‖ < δ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    apply lt_of_le_of_lt _ hbox
    apply div_le_div_of_nonneg_right _ hL.le
    exact (norm_fourierLaplaceParameter_le u).trans (add_le_add le_rfl hu)
  exact hbound _ _ (hnorm ξ hξ) (hnorm τ hτ)

end

end Erdos4b
