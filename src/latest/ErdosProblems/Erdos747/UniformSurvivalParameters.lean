import ErdosProblems.Erdos747.HeavyCutoffParameters
import ErdosProblems.Erdos747.UniformSurvivalBound

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

def uniformSurvivalError (T L gamma : ℝ) : ℝ :=
  T * gamma / adjustedHeavyScale L gamma + 2 * Real.exp (-min
    ((coarseSurvivalFraction T)^2 / (64 * T * adjustedHeavyScale L gamma))
    (coarseSurvivalFraction T / (16 * adjustedHeavyScale L gamma)))

lemma uniformSurvivalError_nonneg (T L gamma : ℝ) (hT : 0 ≤ T) (hg : 0 ≤ gamma) :
    0 ≤ uniformSurvivalError T L gamma := by
  unfold uniformSurvivalError adjustedHeavyScale
  positivity

lemma uniformSurvivalError_tendsto_zero (T : ℝ) (L gamma : ℕ → ℝ)
    (hT : 0 < T) (hL : Tendsto L atTop atTop) (hg : Tendsto gamma atTop (𝓝 0))
    (hg0 : ∀ᶠ n in atTop, 0 ≤ gamma n) :
    Tendsto (fun n ↦ uniformSurvivalError T (L n) (gamma n)) atTop (𝓝 0) := by
  have hv := adjustedHeavyScale_tendsto_zero L gamma hL hg
  have hvpos : ∀ᶠ n in atTop, 0 < adjustedHeavyScale (L n) (gamma n) := by
    filter_upwards [hg0, hL.eventually_gt_atTop 0] with n hgn hLn
    exact adjustedHeavyScale_pos (L n) (gamma n) hLn hgn
  have hhit := (gamma_div_adjustedHeavyScale_tendsto_zero L gamma hL hg hg0).const_mul T
  have hr := coarseSurvivalFraction_pos T
  have htail := exp_neg_min_div_tendsto_zero
    (fun n ↦ adjustedHeavyScale (L n) (gamma n))
    ((coarseSurvivalFraction T)^2 / (64 * T)) (coarseSurvivalFraction T / 16)
    hv hvpos (by positivity) (by positivity)
  simpa only [uniformSurvivalError, mul_div_assoc, div_div, zero_mul, mul_zero, add_zero]
    using hhit.add (htail.const_mul 2)

lemma completionThinning_relative_lower_failure_le_adjusted
    {n t : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hn : 2 ≤ n) (hZ : Z ∈ allEdges n) (delta eta gamma T L : ℝ)
    (hdelta : 0 ≤ delta) (heta : 0 ≤ eta) (hgamma : delta + eta ≤ gamma)
    (hh : 1 + delta ≤ adjustedHeavyCutoff L gamma)
    (hhmass : 2 * gamma ≤ adjustedHeavyCutoff L gamma)
    (hL : 8 ≤ L) (hT : 0 < T) (ht0 : 0 < t) (ht : (t : ℝ) ≤ T * L)
    (hcollision : 4 * t * t ≤ H.card) (hw : 0 < completionWeight H Z)
    (hmean : L / 2 ≤ ((reindexGraphAway H Z hZ).card : ℝ) / ((n - 1 : ℕ) : ℝ))
    (hspread : PresentWeightSpread (reindexGraphAway H Z hZ) delta eta) :
    finsetProbability (H.powersetCard t)
        (fun U ↦ (completionWeight (H \ U) Z : ℝ) <
          coarseSurvivalFraction T * (completionWeight H Z : ℝ)) ≤
      uniformSurvivalError T L gamma := by
  have hL0 : 0 < L := by linarith only [hL]
  have hg0 : 0 ≤ gamma := (add_nonneg hdelta heta).trans hgamma
  have hspos := adjustedHeavyScale_pos L gamma hL0 hg0
  have hcutpos : 0 < adjustedHeavyCutoff L gamma := mul_pos hL0 hspos
  have hraw := completionThinning_relative_lower_failure_le_normalized H hn hZ delta eta
    (adjustedHeavyCutoff L gamma) T L hdelta heta hh
    ((mul_le_mul_of_nonneg_left hgamma (by norm_num : (0 : ℝ) ≤ 2)).trans hhmass)
    hL hT ht0 ht hcollision hw hmean hspread
  apply hraw.trans
  unfold uniformSurvivalError
  rw [adjustedHeavyCutoff_div L gamma hL0.ne']
  apply add_le_add _ le_rfl
  calc
    _ ≤ T * L * gamma / adjustedHeavyCutoff L gamma :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgamma (by positivity)) hcutpos.le
    _ = _ := by unfold adjustedHeavyCutoff; field_simp

/-- This one eventual statement is uniform in the graph dimension, graph,
triple, thinning size, and individual spreading errors. -/
lemma eventually_completionThinning_relative_lower_failure_le_uniform
    (T : ℝ) (L gamma : ℕ → ℝ) (hT : 0 < T)
    (hL : Tendsto L atTop atTop) (hg : Tendsto gamma atTop (𝓝 0))
    (hg0 : ∀ᶠ i in atTop, 0 ≤ gamma i) :
    ∀ᶠ i in atTop, ∀ n t : ℕ, ∀ H : Finset (Edge n), ∀ Z : Edge n,
      ∀ (hZ : Z ∈ allEdges n) (delta eta : ℝ),
      2 ≤ n → 0 ≤ delta → 0 ≤ eta → delta + eta ≤ gamma i →
      0 < t → (t : ℝ) ≤ T * L i → 4 * t * t ≤ H.card →
      0 < completionWeight H Z →
      L i / 2 ≤ ((reindexGraphAway H Z hZ).card : ℝ) / ((n - 1 : ℕ) : ℝ) →
      PresentWeightSpread (reindexGraphAway H Z hZ) delta eta →
      finsetProbability (H.powersetCard t)
          (fun U ↦ (completionWeight (H \ U) Z : ℝ) <
            coarseSurvivalFraction T * (completionWeight H Z : ℝ)) ≤
        uniformSurvivalError T (L i) (gamma i) := by
  have hcut := (adjustedHeavyCutoff_tendsto_atTop L gamma hL hg0).eventually_ge_atTop 2
  have hgsmall := (tendsto_order.mp hg).2 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hL.eventually_ge_atTop 8, hcut, hgsmall] with i hLi hcuti hgi
  intro n t H Z hZ delta eta hn hdelta heta hgamma ht0 ht hcollision hw hmean hspread
  exact completionThinning_relative_lower_failure_le_adjusted H hn hZ delta eta (gamma i) T (L i)
    hdelta heta hgamma (by linarith only [hcuti, hgi, heta, hgamma])
    (by linarith only [hcuti, hgi]) hLi hT ht0 ht hcollision hw hmean hspread

end

end Erdos747
