import ErdosProblems.Erdos747.LogarithmicThinningParameters

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

def spreadThinningMultiplier (zeta kappa : ℝ) : ℝ :=
  logarithmicThinningMultiplier (1024 * kappa / zeta)

lemma spreadThinningMultiplier_pos (zeta kappa : ℝ) (hzeta : 0 < zeta) (hkappa : 0 < kappa) :
    0 < spreadThinningMultiplier zeta kappa :=
  logarithmicThinningMultiplier_pos _ (by positivity)

/-- Any fixed polynomial failure exponent is available uniformly over all
densities above half the logarithmic mean degree.  No regularity or
thinning parameter is postulated in the conclusion. -/
lemma eventually_aggregate_global_failure_probability_le_exp
    (k : ℕ → ℕ) (C g q eta : ℕ → ℝ) (B zeta kappa : ℝ)
    (hk : Tendsto k atTop atTop) (hB : 0 ≤ B) (hzeta : 0 < zeta) (hkappa : 0 < kappa)
    (hC : Tendsto C atTop (𝓝 0)) (hC0 : ∀ᶠ i in atTop, 0 ≤ C i)
    (hg : Tendsto g atTop (𝓝 0)) (hgpos : ∀ᶠ i in atTop, 0 < g i)
    (hq : Tendsto q atTop (𝓝 0)) (hq0 : ∀ᶠ i in atTop, 0 ≤ q i)
    (heta : Tendsto eta atTop (𝓝 0)) (heta0 : ∀ᶠ i in atTop, 0 ≤ eta i) :
    ∀ᶠ i in atTop, ∀ M cap : ℕ,
      0 < cap → halfLogMean (k i) ≤ (M : ℝ) / k i →
      (cap : ℝ) / ((M : ℝ) / k i) ≤ g i →
      finsetProbability (sample (k i) M)
          (fun H ↦ KahnAggregateInsertionGood (k i) M cap (C i) (q i) (eta i) B H ∧
            ¬ GlobalUpperWeightSpread (k i) H
              (coarseUpperFactor (spreadThinningMultiplier zeta kappa)) zeta) ≤
          4 * Real.exp (-kappa * Real.log ((3 * k i : ℕ) : ℝ)) ∧
      finsetProbability (sample (k i) M)
          (fun H ↦ KahnAggregateInsertionGood (k i) M cap (C i) (q i) (eta i) B H ∧
            ¬ GlobalLowerWeightSpread (k i) H
              (coarseLowerFactor (spreadThinningMultiplier zeta kappa)) zeta) ≤
          4 * Real.exp (-kappa * Real.log ((3 * k i : ℕ) : ℝ)) := by
  let nu := 1024 * kappa / zeta
  let T := spreadThinningMultiplier zeta kappa
  have hnu : 0 < nu := by dsimp only [nu]; positivity
  have hT : 0 < T := spreadThinningMultiplier_pos zeta kappa hzeta hkappa
  have hL : Tendsto (fun i ↦ halfLogMean (k i)) atTop atTop := halfLogMean_tendsto_atTop.comp hk
  have hglobal := eventually_aggregate_global_failure_probability_le k C g q eta
    (fun i ↦ halfLogMean (k i)) B T zeta hk hL hB hT hzeta hC hC0 hg hgpos hq hq0 heta heta0
  have hbudgets := hk.eventually (eventually_logarithmicThinning_finite_budgets nu zeta hnu hzeta)
  filter_upwards [hglobal, hbudgets] with i hglobali hbudgeti
  intro M cap hcap hmean hrelative
  let t := logarithmicThinningSize nu (k i)
  have ht2 : 2 ≤ t := hbudgeti.1
  have hs : 0 < t - 1 := by omega
  have hsucc : t - 1 + 1 = t := by omega
  have ht : (t : ℝ) ≤ T * halfLogMean (k i) := hbudgeti.2.1
  have hcollision : 4 * t * t ≤ M := hbudgeti.2.2.2 M hmean
  have htsq : t * t ≤ thinningBlockSize (allEdges (k i)).card zeta := hbudgeti.2.2.1
  have hraw := hglobali M cap (t - 1) hcap hmean hrelative hs
    (by simpa only [hsucc] using ht) (by simpa only [hsucc] using hcollision)
    (by simpa only [hsucc] using htsq)
  rw [hsucc] at hraw
  have htail : 4 * Real.exp (-((t : ℝ) * zeta) / 1024) ≤
      4 * Real.exp (-kappa * Real.log ((3 * k i : ℕ) : ℝ)) := by
    have hcoeff : nu * zeta / 1024 = kappa := by dsimp only [nu]; field_simp
    simpa only [hcoeff] using logarithmicThinning_tail_le (k i) nu zeta hzeta.le
  exact ⟨hraw.1.trans htail, hraw.2.trans htail⟩

end

end Erdos747
