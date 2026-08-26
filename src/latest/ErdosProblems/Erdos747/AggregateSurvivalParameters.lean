import ErdosProblems.Erdos747.ResidualEntropyParameters
import ErdosProblems.Erdos747.UniformSurvivalParameters
import ErdosProblems.Erdos747.SelectedThinningTop

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

def aggregateSurvivalError (k : ℕ) (C g q eta B T L : ℝ) : ℝ :=
  uniformSurvivalError T L (2 * residualPresentTolerance k C (1 / 2) g q eta B)

lemma aggregateSurvivalError_nonneg (k : ℕ) (C g q eta B T L : ℝ) (hT : 0 ≤ T) :
    0 ≤ aggregateSurvivalError k C g q eta B T L :=
  uniformSurvivalError_nonneg T L _ hT
    (mul_nonneg (by norm_num) (residualPresentTolerance_nonneg k C (1 / 2) g q eta B))

lemma aggregateSurvivalError_tendsto_zero
    (k : ℕ → ℕ) (C g q eta L : ℕ → ℝ) (B T : ℝ)
    (hk : Tendsto k atTop atTop) (hL : Tendsto L atTop atTop) (hT : 0 < T)
    (hC : Tendsto C atTop (𝓝 0)) (hg : Tendsto g atTop (𝓝 0))
    (hgpos : ∀ᶠ i in atTop, 0 < g i)
    (hq : Tendsto q atTop (𝓝 0)) (heta : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun i ↦ aggregateSurvivalError (k i) (C i) (g i) (q i) (eta i) B T (L i))
      atTop (𝓝 0) := by
  have herr := residualPresentTolerance_tendsto_zero_along k C g q eta (1 / 2) B
    hk hC hg hgpos hq heta
  apply uniformSurvivalError_tendsto_zero T L _ hT hL
  · simpa only [mul_zero] using herr.const_mul 2
  · exact Eventually.of_forall fun i ↦
      mul_nonneg (by norm_num) (residualPresentTolerance_nonneg (k i) (C i) (1 / 2) (g i) (q i) (eta i) B)

/-- The pool may be the parent graph or the parent with the tested edge
erased.  Both have exactly the same completion family and residual graph. -/
lemma eventually_aggregate_completion_survival
    (k : ℕ → ℕ) (C g q eta L : ℕ → ℝ) (B T : ℝ)
    (hk : Tendsto k atTop atTop) (hL : Tendsto L atTop atTop)
    (hB : 0 ≤ B) (hT : 0 < T)
    (hC : Tendsto C atTop (𝓝 0)) (hC0 : ∀ᶠ i in atTop, 0 ≤ C i)
    (hg : Tendsto g atTop (𝓝 0)) (hgpos : ∀ᶠ i in atTop, 0 < g i)
    (hq : Tendsto q atTop (𝓝 0)) (hq0 : ∀ᶠ i in atTop, 0 ≤ q i)
    (heta : Tendsto eta atTop (𝓝 0)) (heta0 : ∀ᶠ i in atTop, 0 ≤ eta i) :
    ∀ᶠ i in atTop, ∀ M cap : ℕ, ∀ H : Finset (Edge (k i)),
      0 < cap → L i ≤ (M : ℝ) / k i →
      (cap : ℝ) / ((M : ℝ) / k i) ≤ g i →
      KahnAggregateInsertionGood (k i) M cap (C i) (q i) (eta i) B H →
      ∀ Z : Edge (k i), ∀ hZ : Z ∈ allEdges (k i),
      (1 / 2 : ℝ)^2 * matchingWeightTarget (k i) H ≤ completionWeight H Z →
      ∀ X : Finset (Edge (k i)), reindexGraphAway X Z hZ = reindexGraphAway H Z hZ →
      completionWeight X Z = completionWeight H Z →
      ∀ t : ℕ, 0 < t → (t : ℝ) ≤ T * L i → 4 * t * t ≤ X.card →
      finsetProbability (X.powersetCard t)
          (fun U ↦ (completionWeight (X \ U) Z : ℝ) <
            coarseSurvivalFraction T * (completionWeight X Z : ℝ)) ≤
        aggregateSurvivalError (k i) (C i) (g i) (q i) (eta i) B T (L i) := by
  let a := fun i ↦ residualPresentTolerance (k i) (C i) (1 / 2) (g i) (q i) (eta i) B
  let gamma := fun i ↦ 2 * a i
  have ha : Tendsto a atTop (𝓝 0) :=
    residualPresentTolerance_tendsto_zero_along k C g q eta (1 / 2) B hk hC hg hgpos hq heta
  have hgamma : Tendsto gamma atTop (𝓝 0) := by simpa only [mul_zero] using ha.const_mul 2
  have ha0 : ∀ i, 0 ≤ a i := fun i ↦ residualPresentTolerance_nonneg _ _ _ _ _ _ _
  have hgamma0 : ∀ᶠ i in atTop, 0 ≤ gamma i :=
    Eventually.of_forall fun i ↦ mul_nonneg (by norm_num) (ha0 i)
  have hsurv := eventually_completionThinning_relative_lower_failure_le_uniform T L gamma
    hT hL hgamma hgamma0
  have hres := eventually_kahnAggregateInsertionGood_residualPresentWeightSpread
    k C g q eta (1 / 2) B hk hC0 (by norm_num) (by norm_num) hB hg hgpos hq hq0 heta0
  filter_upwards [hsurv, hres, hk.eventually_ge_atTop 4, hL.eventually_ge_atTop 1]
    with i hsurvi hresi hki hLi
  intro M cap H hcap hmean hrelative hgood Z hZ hweight X hXres hXweight t ht0 ht hcollision
  have hparentmean : 1 ≤ (M : ℝ) / k i := hLi.trans hmean
  have hresdata := hresi M cap H Z hZ hcap hparentmean hrelative hgood hweight
  have hHpos : 0 < H.card := by
    obtain ⟨F, hFsub, hFcard, -⟩ := hgood.2.1
    have hFle := Finset.card_le_card hFsub
    omega
  have hPhi : (perfectMatchings (k i) H).card ≠ 0 :=
    Finset.card_ne_zero.mpr (hasPerfectMatching_iff_perfectMatchings_nonempty.mp hgood.2.1)
  have hw : 0 < completionWeight X Z := by
    rw [hXweight]
    exact completionWeight_pos_of_matchingWeightTarget_lower (by omega) hHpos hPhi (by norm_num) hweight
  apply hsurvi (k i) t X Z hZ (a i) (a i) (by omega) (ha0 i) (ha0 i)
    (by dsimp only [gamma]; linarith) ht0 ht hcollision hw
  · rw [hXres]
    exact (div_le_div_of_nonneg_right hmean (by norm_num : (0 : ℝ) ≤ 2)).trans hresdata.2
  · rw [hXres]
    exact hresdata.1

end

end Erdos747
