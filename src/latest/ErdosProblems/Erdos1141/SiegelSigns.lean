import ErdosProblems.Erdos1141.PositiveCutoff
import BoundedGaps.BombieriVinogradov.Analytic.SiegelZeroFreeRegion

/-!
# Real signs in the Siegel zero-free interval
-/

open Complex
open scoped ComplexOrder Topology

namespace Erdos1141

lemma quadratic_LFunction_real {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsquare : χ ^ 2 = 1) (σ : ℝ) :
    (χ.LFunction (σ : ℂ)).im = 0 := by
  have h := BoundedGaps.Maynard.LFunction_conj_of_sq_eq_one χ hχ hsquare (σ : ℂ)
  apply Complex.conj_eq_iff_im.mp
  simpa only [Complex.conj_ofReal] using h.symm

lemma quadratic_LFunction_one_pos {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsquare : χ ^ 2 = 1) :
    0 < (χ.LFunction 1).re := by
  have h := Complex.re_le_re
    (BoundedGaps.Maynard.effectiveQuadraticLValueLowerBound hq χ hχ hsquare)
  simp only [Complex.ofReal_re] at h
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  exact lt_of_lt_of_le (by positivity) h

/-- Positivity at one persists along a real interval containing no zeros. -/
lemma quadratic_LFunction_pos_of_zeroFree {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsquare : χ ^ 2 = 1)
    {β : ℝ} (hβ : β ≤ 1)
    (hzeroFree : ∀ σ ∈ Set.Icc β 1, χ.LFunction (σ : ℂ) ≠ 0) :
    0 < (χ.LFunction (β : ℂ)).re := by
  have hcont : Continuous (fun σ : ℝ ↦ (χ.LFunction (σ : ℂ)).re) :=
    Complex.continuous_re.comp
      ((χ.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal)
  have hone := quadratic_LFunction_one_pos hq χ hχ hsquare
  by_contra hnonpos
  have hsign : (χ.LFunction (β : ℂ)).re ≤ 0 := le_of_not_gt hnonpos
  obtain ⟨σ, hσ, hval⟩ := intermediate_value_Icc hβ hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc ((χ.LFunction (β : ℂ)).re) ((χ.LFunction (1 : ℂ)).re) from
      ⟨hsign, hone.le⟩)
  apply hzeroFree σ hσ
  apply Complex.ext
  · simpa only [Complex.zero_re] using hval
  · simpa only [Complex.zero_im] using quadratic_LFunction_real χ hχ hsquare σ

/-- The regularized zeta function has real part between zero and two near one. -/
lemma exists_zeta_left_sign_bound :
    ∃ η : ℝ, 0 < η ∧ ∀ β : ℝ, 1 - η < β → β < 1 →
      (riemannZeta (β : ℂ)).re ≤ 0 ∧
        -(riemannZeta (β : ℂ)).re ≤ 2 / (1 - β) := by
  have hcont : ContinuousAt (fun β : ℝ ↦ (riemannZeta₁ (β : ℂ)).re) 1 :=
    (Complex.continuous_re.comp
      (differentiable_riemannZeta₁.continuous.comp Complex.continuous_ofReal)).continuousAt
  have hevent : ∀ᶠ β : ℝ in 𝓝 1, (riemannZeta₁ (β : ℂ)).re ∈ Set.Ioo (0 : ℝ) 2 := by
    apply hcont
    change Set.Ioo (0 : ℝ) 2 ∈ 𝓝 ((riemannZeta₁ ((1 : ℝ) : ℂ)).re)
    rw [show (riemannZeta₁ ((1 : ℝ) : ℂ)).re = 1 by norm_num]
    exact isOpen_Ioo.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 2)
  obtain ⟨η, hη, hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨η, hη, ?_⟩
  intro β hlo hhi
  have hdist : dist β 1 < η := by
    rw [Real.dist_eq, abs_of_neg (by linarith : β - 1 < 0)]
    linarith
  obtain ⟨hpos, htwo⟩ := hnear hdist
  have hβne : (β : ℂ) ≠ 1 := by exact_mod_cast hhi.ne
  have hvalue : (riemannZeta (β : ℂ)).re =
      (β - 1)⁻¹ * (riemannZeta₁ (β : ℂ)).re := by
    rw [riemannZeta_eq_inv_sub_mul hβne]
    rw [show (β : ℂ) - 1 = ((β - 1 : ℝ) : ℂ) by push_cast; rfl]
    rw [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  have hnegative : (β - 1)⁻¹ ≤ 0 := inv_nonpos.mpr (by linarith)
  refine ⟨hvalue.trans_le (mul_nonpos_of_nonpos_of_nonneg hnegative hpos.le), ?_⟩
  have hid : -(riemannZeta (β : ℂ)).re = (riemannZeta₁ (β : ℂ)).re / (1 - β) := by
    rw [hvalue, div_eq_mul_inv, show β - 1 = -(1 - β) by ring, inv_neg]
    ring
  rw [hid]
  exact div_le_div_of_nonneg_right htwo.le (by linarith)

end Erdos1141
