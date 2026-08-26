import ErdosProblems.Erdos157b.Parameters

namespace Erdos157.Binary

open Erdos157.Elementary Elementary.PolynomialCharacters Filter
open scoped Topology

theorem tendsto_prefix_relativeError (q : ℝ) (hq : 1 < q) :
    Tendsto (fun k : ℕ => progressionRelativeError q ((prefixLength k : ℝ) ^ 2)
      (levelDegree k)) atTop (𝓝 0) := by
  apply tendsto_progressionRelativeError_of_sublinear q hq
    (fun k => (prefixLength k : ℝ) ^ 2) (fun k => (levelDegree k : ℝ))
    (fun k => (k : ℝ)) (7 / 20) (by norm_num) tendsto_levelDegree
    tendsto_natCast_atTop_atTop tendsto_prefixDegree_div_level
  · exact Eventually.of_forall (fun k => pow_pos (by exact_mod_cast prefixLength_pos k) _)
  · exact Eventually.of_forall levelDegree_lower

theorem eventually_prefixDegree_lt_levelDegree :
    ∀ᶠ k in atTop, prefixLength k ^ 2 < levelDegree k := by
  filter_upwards [tendsto_prefixDegree_div_level.eventually (gt_mem_nhds zero_lt_one),
    eventually_ge_atTop 3] with k hsmall hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 3) hk
  have hH : (prefixLength k : ℝ) ^ 2 < k := by
    simpa only [one_mul] using (div_lt_iff₀ hkpos).mp hsmall
  have hklower : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hdegree := levelDegree_lower k
  have hlt : (prefixLength k : ℝ) ^ 2 < levelDegree k := by nlinarith
  exact_mod_cast hlt

theorem eventually_twice_prefixDegree_le_levelDegree :
    ∀ᶠ k in atTop, 2 * prefixLength k ^ 2 ≤ levelDegree k := by
  filter_upwards [tendsto_prefixDegree_div_level.eventually (gt_mem_nhds zero_lt_one),
    eventually_ge_atTop 6] with k hsmall hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 6) hk
  have hH : (prefixLength k : ℝ) ^ 2 < k := by
    simpa only [one_mul] using (div_lt_iff₀ hkpos).mp hsmall
  have hklower : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have hdegree := levelDegree_lower k
  have hle : 2 * (prefixLength k : ℝ) ^ 2 ≤ levelDegree k := by nlinarith
  exact_mod_cast hle

theorem eventually_prefixLength_le : ∀ᶠ k in atTop, prefixLength k ≤ k := by
  filter_upwards [tendsto_prefixDegree_div_level.eventually (gt_mem_nhds zero_lt_one),
    eventually_ge_atTop 1] with k hsmall hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hH : (prefixLength k : ℝ) ^ 2 < k := by
    simpa only [one_mul] using (div_lt_iff₀ hkpos).mp hsmall
  have hpos : (1 : ℝ) ≤ prefixLength k := by exact_mod_cast Nat.succ_le_of_lt (prefixLength_pos k)
  have hle : (prefixLength k : ℝ) ≤ k := by nlinarith
  exact_mod_cast hle


end Erdos157.Binary
