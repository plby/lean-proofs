import ErdosProblems.Erdos980.ElliottTail.Burgess
import ErdosProblems.Erdos980.ElliottTail.Definitions

/-!
# From rarity to the vanishing normalized large tail

The remaining input to this module is only a cardinal power-saving for the
moving exceptional-prime set.  Pólya--Vinogradov supplies the pointwise
`3/4` exponent, so any rarity exponent below `1/4` makes the normalized
weighted large tail tend to zero.
-/

namespace Erdos980.ElliottTail

open Filter
open scoped Topology

/-- Flexible Pólya--Vinogradov form: a rarity exponent `a` and any
pointwise exponent `β > 1/2` suffice provided `a + β < 1`. -/
theorem normalizedWeightedTail_tendsto_zero_of_eventually_card_rpow_and_beta
    (k : ℕ) (hk : 2 ≤ k) (cutoff : ℕ → ℕ) (C a β : ℝ)
    (hβ : 1 / 2 < β) (haβ : a + β < 1)
    (hcutoff : Tendsto cutoff atTop atTop)
    (hcard : ∀ᶠ x : ℕ in atTop,
      ((exceptionalPrimes k (cutoff x) x).card : ℝ) ≤
        C * (x : ℝ) ^ a) :
    Tendsto (fun x ↦ normalizedWeightedTail k (cutoff x) x)
      atTop (nhds 0) := by
  obtain ⟨P, hP⟩ := eventually_atTop.mp
    (eventually_leastKthPowerNonresidue_le_rpow k hk hβ)
  have hcutoffP : ∀ᶠ x in atTop, P ≤ cutoff x :=
    hcutoff.eventually (eventually_ge_atTop P)
  have hnonneg : ∀ᶠ x in atTop,
      0 ≤ normalizedWeightedTail k (cutoff x) x := by
    filter_upwards [eventually_ge_atTop 2] with x hx
    exact normalizedWeightedTail_nonneg k (cutoff x) x hx
  have hmajor : ∀ᶠ x in atTop,
      normalizedWeightedTail k (cutoff x) x ≤
        C * ((x : ℝ) ^ (a + β) * Real.log (x : ℝ) / (x : ℝ)) := by
    filter_upwards [hcard, hcutoffP, eventually_ge_atTop 2]
      with x hxcard hxcut hx2
    have hpoint : ∀ p ∈ exceptionalPrimes k (cutoff x) x,
        (leastKthPowerNonresidue k p : ℝ) ≤ (x : ℝ) ^ β := by
      intro p hp
      have helig := eligible_of_mem_exceptionalPrimes hk hp
      have hpData := mem_exceptionalPrimes.mp hp
      have hnp : leastKthPowerNonresidue k p < p :=
        leastKthPowerNonresidue_lt_modulus hk helig
      have hPp : P ≤ p :=
        hxcut.trans (hpData.2.2.le.trans hnp.le)
      have hpBound := hP p hPp helig
      have hpx : (p : ℝ) ≤ x := by exact_mod_cast hpData.1.le
      exact hpBound.trans
        (Real.rpow_le_rpow (by positivity) hpx (by linarith))
    calc
      normalizedWeightedTail k (cutoff x) x ≤
          C * 1 * (x : ℝ) ^ (a + β) * Real.log (x : ℝ) / (x : ℝ) :=
        normalizedWeightedTail_le_rpow k (cutoff x) x C 1 a β hx2
          hxcard (by simpa using hpoint) (by norm_num)
      _ = C * ((x : ℝ) ^ (a + β) * Real.log (x : ℝ) / (x : ℝ)) := by
        ring
  exact tendsto_zero_of_eventually_le_largeTail_majorant
    (fun x ↦ normalizedWeightedTail k (cutoff x) x) haβ hnonneg hmajor

/-- A moving cutoff tending to infinity, together with a power-saving rarity
estimate of exponent `a < 1/4`, makes the normalized large tail vanish. -/
theorem normalizedWeightedTail_tendsto_zero_of_eventually_card_rpow
    (k : ℕ) (hk : 2 ≤ k) (cutoff : ℕ → ℕ) (C a : ℝ)
    (ha : a + 3 / 4 < 1)
    (hcutoff : Tendsto cutoff atTop atTop)
    (hcard : ∀ᶠ x : ℕ in atTop,
      ((exceptionalPrimes k (cutoff x) x).card : ℝ) ≤
        C * (x : ℝ) ^ a) :
    Tendsto (fun x ↦ normalizedWeightedTail k (cutoff x) x)
      atTop (nhds 0) := by
  obtain ⟨P, hP⟩ := (eventually_atTop.mp
    (eventually_leastKthPowerNonresidue_le_threeQuarter_rpow k hk))
  have hcutoffP : ∀ᶠ x in atTop, P ≤ cutoff x :=
    hcutoff.eventually (eventually_ge_atTop P)
  have hnonneg : ∀ᶠ x in atTop,
      0 ≤ normalizedWeightedTail k (cutoff x) x := by
    filter_upwards [eventually_ge_atTop 2] with x hx
    exact normalizedWeightedTail_nonneg k (cutoff x) x hx
  have hmajor : ∀ᶠ x in atTop,
      normalizedWeightedTail k (cutoff x) x ≤
        C * ((x : ℝ) ^ (a + 3 / 4) * Real.log (x : ℝ) / (x : ℝ)) := by
    filter_upwards [hcard, hcutoffP, eventually_ge_atTop 2]
      with x hxcard hxcut hx2
    have hpoint : ∀ p ∈ exceptionalPrimes k (cutoff x) x,
        (leastKthPowerNonresidue k p : ℝ) ≤
          (x : ℝ) ^ (3 / 4 : ℝ) := by
      intro p hp
      have helig := eligible_of_mem_exceptionalPrimes hk hp
      have hpData := mem_exceptionalPrimes.mp hp
      have hnp : leastKthPowerNonresidue k p < p :=
        leastKthPowerNonresidue_lt_modulus hk helig
      have hPp : P ≤ p := by
        exact hxcut.trans (hpData.2.2.le.trans hnp.le)
      have hpBound := hP p hPp helig
      have hpx : (p : ℝ) ≤ x := by exact_mod_cast hpData.1.le
      exact hpBound.trans (Real.rpow_le_rpow (by positivity) hpx (by norm_num))
    calc
      normalizedWeightedTail k (cutoff x) x ≤
          C * 1 * (x : ℝ) ^ (a + 3 / 4) * Real.log (x : ℝ) / (x : ℝ) :=
        normalizedWeightedTail_le_rpow k (cutoff x) x C 1 a (3 / 4) hx2
          hxcard (by simpa using hpoint) (by norm_num)
      _ = C * ((x : ℝ) ^ (a + 3 / 4) * Real.log (x : ℝ) / (x : ℝ)) := by
        ring
  exact tendsto_zero_of_eventually_le_largeTail_majorant
    (fun x ↦ normalizedWeightedTail k (cutoff x) x) ha hnonneg hmajor

end Erdos980.ElliottTail
