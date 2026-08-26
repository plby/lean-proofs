import ErdosProblems.Erdos747.NormalizedSurvivalBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

/-! ## A heavy cutoff with vanishing normalized influence and hit probability -/

def adjustedHeavyScale (L gamma : ℝ) : ℝ := Real.sqrt (gamma + 1 / L)

def adjustedHeavyCutoff (L gamma : ℝ) : ℝ := L * adjustedHeavyScale L gamma

lemma adjustedHeavyScale_pos (L gamma : ℝ) (hL : 0 < L) (hg : 0 ≤ gamma) :
    0 < adjustedHeavyScale L gamma := by unfold adjustedHeavyScale; positivity

lemma adjustedHeavyScale_tendsto_zero (L gamma : ℕ → ℝ)
    (hL : Tendsto L atTop atTop) (hg : Tendsto gamma atTop (𝓝 0)) :
    Tendsto (fun n ↦ adjustedHeavyScale (L n) (gamma n)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n ↦ (1 : ℝ) / L n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  simpa only [adjustedHeavyScale, add_zero, Real.sqrt_zero] using (hg.add hinv).sqrt

lemma gamma_div_adjustedHeavyScale_le (L gamma : ℝ) (hL : 0 < L) (hg : 0 ≤ gamma) :
    gamma / adjustedHeavyScale L gamma ≤ adjustedHeavyScale L gamma := by
  apply (div_le_iff₀ (adjustedHeavyScale_pos L gamma hL hg)).mpr
  have hs : (adjustedHeavyScale L gamma)^2 = gamma + 1 / L :=
    Real.sq_sqrt (by positivity)
  have hinv : 0 ≤ (1 : ℝ) / L := by positivity
  nlinarith only [hs, hinv]

lemma gamma_div_adjustedHeavyScale_tendsto_zero (L gamma : ℕ → ℝ)
    (hL : Tendsto L atTop atTop) (hg : Tendsto gamma atTop (𝓝 0))
    (hg0 : ∀ᶠ n in atTop, 0 ≤ gamma n) :
    Tendsto (fun n ↦ gamma n / adjustedHeavyScale (L n) (gamma n)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (adjustedHeavyScale_tendsto_zero L gamma hL hg)
  · filter_upwards [hg0] with n hn
    exact div_nonneg hn (Real.sqrt_nonneg _)
  · filter_upwards [hg0, hL.eventually_gt_atTop 0] with n hgn hLn
    exact gamma_div_adjustedHeavyScale_le (L n) (gamma n) hLn hgn

lemma sqrt_le_adjustedHeavyCutoff (L gamma : ℝ) (hL : 0 < L) (hg : 0 ≤ gamma) :
    Real.sqrt L ≤ adjustedHeavyCutoff L gamma := by
  have hs : (adjustedHeavyScale L gamma)^2 = gamma + 1 / L :=
    Real.sq_sqrt (by positivity)
  have hc : (adjustedHeavyCutoff L gamma)^2 = L^2 * gamma + L := by
    unfold adjustedHeavyCutoff
    rw [mul_pow, hs]
    field_simp
  have hc0 : 0 ≤ adjustedHeavyCutoff L gamma :=
    mul_nonneg hL.le (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ (Real.sqrt_nonneg L) hc0).mp
  rw [Real.sq_sqrt hL.le, hc]
  have hp := mul_nonneg (sq_nonneg L) hg
  linarith only [hp]

lemma adjustedHeavyCutoff_tendsto_atTop (L gamma : ℕ → ℝ)
    (hL : Tendsto L atTop atTop) (hg0 : ∀ᶠ n in atTop, 0 ≤ gamma n) :
    Tendsto (fun n ↦ adjustedHeavyCutoff (L n) (gamma n)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  have hs := (Real.tendsto_sqrt_atTop.comp hL).eventually_ge_atTop R
  filter_upwards [hs, hg0, hL.eventually_gt_atTop 0] with n hn hgn hLn
  exact hn.trans (sqrt_le_adjustedHeavyCutoff (L n) (gamma n) hLn hgn)

lemma adjustedHeavyCutoff_div (L gamma : ℝ) (hL : L ≠ 0) :
    adjustedHeavyCutoff L gamma / L = adjustedHeavyScale L gamma := by
  unfold adjustedHeavyCutoff
  exact mul_div_cancel_left₀ _ hL

lemma exp_neg_min_div_tendsto_zero (v : ℕ → ℝ) (A B : ℝ)
    (hv : Tendsto v atTop (𝓝 0)) (hvpos : ∀ᶠ n in atTop, 0 < v n)
    (hA : 0 < A) (hB : 0 < B) :
    Tendsto (fun n ↦ Real.exp (-min (A / v n) (B / v n))) atTop (𝓝 0) := by
  have hwithin : Tendsto v atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hv, hvpos⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hwithin
  have hAtop : Tendsto (fun n ↦ A / v n) atTop atTop := by
    simpa only [div_eq_mul_inv, Function.comp_def] using hinv.const_mul_atTop hA
  have hBtop : Tendsto (fun n ↦ B / v n) atTop atTop := by
    simpa only [div_eq_mul_inv, Function.comp_def] using hinv.const_mul_atTop hB
  have hmin : Tendsto (fun n ↦ min (A / v n) (B / v n)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro R
    filter_upwards [hAtop.eventually_ge_atTop R, hBtop.eventually_ge_atTop R] with n hAn hBn
    exact le_min hAn hBn
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hmin)

end

end Erdos747
