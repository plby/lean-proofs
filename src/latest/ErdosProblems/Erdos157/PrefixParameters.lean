import ErdosProblems.Erdos157.ProgressionErrorBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The logarithmic prefix and the even quadratic degree sequence. -/

namespace Erdos157.Elementary

open Filter
open scoped Topology
open PolynomialCharacters

/-- One extra coordinate avoids a zero-degree prefix at the initial levels. -/
def prefixLength (k : ℕ) : ℕ := 12 * Nat.clog 7 k + 1

def levelDegree (k : ℕ) : ℕ := 2 * ((7 * k ^ 2 + 39) / 40)

theorem prefixLength_pos (k : ℕ) : 0 < prefixLength k := by
  unfold prefixLength
  omega

theorem trialCount_le_pow_prefixLength (k : ℕ) : k ^ 12 ≤ 7 ^ prefixLength k := by
  have h := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 7) k) 12
  calc
    _ ≤ (7 ^ Nat.clog 7 k) ^ 12 := h
    _ = 7 ^ (12 * Nat.clog 7 k) := by rw [← pow_mul, mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold prefixLength; omega)

theorem prefixLength_le_log (k : ℕ) (hk : 1 ≤ k) :
    (prefixLength k : ℝ) ≤ 12 * Real.logb 7 k + 13 := by
  have hlog : 0 ≤ Real.logb 7 k := Real.logb_nonneg (by norm_num) (by exact_mod_cast hk)
  have hceil : (Nat.clog 7 k : ℝ) ≤ Real.logb 7 k + 1 := by
    rw [← Real.natCeil_logb_natCast]
    exact (Nat.ceil_lt_add_one hlog).le
  dsimp only [prefixLength]
  push_cast
  linarith

theorem tendsto_prefixDegree_div_level :
    Tendsto (fun k : ℕ => (prefixLength k : ℝ) ^ 2 / k) atTop (𝓝 0) := by
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h2 := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 7) 1 0 2 one_ne_zero).comp hcast
  have h1 := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 7) 1 0 1 one_ne_zero).comp hcast
  have h0 := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 7) 1 0 0 one_ne_zero).comp hcast
  have hlim : Tendsto (fun k : ℕ => (12 * Real.logb 7 k + 13) ^ 2 / k) atTop (𝓝 0) := by
    have h := ((h2.const_mul 144).add (h1.const_mul 312)).add (h0.const_mul 169)
    convert h using 1
    · ext k
      simp only [Function.comp_def, one_mul, add_zero, pow_zero, pow_one]
      ring
    · norm_num
  apply squeeze_zero' (Eventually.of_forall (fun k => by positivity)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with k hk
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (prefixLength_le_log k hk) 2

theorem levelDegree_even (k : ℕ) : Even (levelDegree k) := by
  exact ⟨(7 * k ^ 2 + 39) / 40, by unfold levelDegree; omega⟩

theorem levelDegree_lower (k : ℕ) : (7 / 20 : ℝ) * (k : ℝ) ^ 2 ≤ levelDegree k := by
  have hmod := Nat.mod_lt (7 * k ^ 2 + 39) (by decide : 0 < 40)
  have hdiv := Nat.mod_add_div (7 * k ^ 2 + 39) 40
  have hnat : 7 * k ^ 2 ≤ 20 * levelDegree k := by unfold levelDegree; omega
  have hc : (7 : ℝ) * (k : ℝ) ^ 2 ≤ 20 * (levelDegree k : ℝ) := by exact_mod_cast hnat
  linarith

theorem levelDegree_upper (k : ℕ) : (levelDegree k : ℝ) < (7 / 20 : ℝ) * (k : ℝ) ^ 2 + 2 := by
  have hdiv := Nat.mod_add_div (7 * k ^ 2 + 39) 40
  have hnat : 20 * levelDegree k < 7 * k ^ 2 + 40 := by unfold levelDegree; omega
  have hc : 20 * (levelDegree k : ℝ) < 7 * (k : ℝ) ^ 2 + 40 := by exact_mod_cast hnat
  linarith

theorem double_levelDegree_lt_square (k : ℕ) (hk : 4 ≤ k) : 2 * levelDegree k < k ^ 2 := by
  have h := levelDegree_upper k
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hreal : 2 * (levelDegree k : ℝ) < (k : ℝ) ^ 2 := by nlinarith
  exact_mod_cast hreal

theorem square_le_triple_levelDegree (k : ℕ) : k ^ 2 ≤ 3 * levelDegree k := by
  have h := levelDegree_lower k
  have hreal : (k : ℝ) ^ 2 ≤ 3 * (levelDegree k : ℝ) := by nlinarith [sq_nonneg (k : ℝ)]
  exact_mod_cast hreal

theorem levelDegree_lt_next_window (k : ℕ) (hk : 3 ≤ k) :
    (levelDegree k : ℝ) < (7 / 20 : ℝ) * (k + 1 : ℝ) ^ 2 := by
  have h := levelDegree_upper k
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

theorem tendsto_levelDegree : Tendsto (fun k : ℕ => (levelDegree k : ℝ)) atTop atTop := by
  have hquad : Tendsto (fun k : ℕ => (7 / 20 : ℝ) * (k : ℝ) ^ 2) atTop atTop :=
    ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (by norm_num)
  exact tendsto_atTop_mono levelDegree_lower hquad

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

end Erdos157.Elementary
