import ErdosProblems.Erdos380.HighOrderSmoothRuns
import ErdosProblems.Erdos380.ParameterGrowth

/-! # The high-order sieve at one global smoothness cutoff -/

open Filter
open scoped Topology

namespace Erdos380

noncomputable def runWidth (N : ℕ) : ℕ := shortWidth N / 2

theorem scaleBase_loglog_relation :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) * Real.log (Real.log N) /
      Real.log (scaleBase N : ℝ) ^ 2) atTop (𝓝 2000000) := by
  have hinv := log_scaleBase_div_saddleLog_tendsto_one.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simp only [inv_div, inv_one] at hinv
  have h := (hinv.pow 2).const_mul 2000000
  simp only [one_pow, mul_one] at h
  apply h.congr'
  filter_upwards [log_nat_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with N hL hS
  rw [div_pow, saddleLog_sq (by linarith) (Real.log_pos hL).le]
  field_simp

lemma highOrder_base_lower {B H k : ℕ} {t : ℝ} (hB : 60 ≤ B) (hk : 0 < k) (ht : 0 < t)
    (hH : (B : ℝ) ^ 20 ≤ 3 * H) (hden : 40 * (k : ℝ) * t ≤ 20 * B) :
    (B : ℝ) ^ 18 ≤ (H : ℝ) / (40 * k * t) := by
  have hBR : (60 : ℝ) ≤ B := by exact_mod_cast hB
  have hpow : 60 * (B : ℝ) ^ 19 ≤ (B : ℝ) ^ 20 := by
    calc
      _ ≤ (B : ℝ) * (B : ℝ) ^ 19 := mul_le_mul_of_nonneg_right hBR (by positivity)
      _ = _ := (pow_succ' _ _).symm
  have hH' : 20 * (B : ℝ) ^ 19 ≤ H := by linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  apply (le_div_iff₀ (show 0 < 40 * (k : ℝ) * t by positivity)).mpr
  calc
    _ ≤ (B : ℝ) ^ 18 * (20 * B) := mul_le_mul_of_nonneg_left hden (by positivity)
    _ = 20 * (B : ℝ) ^ 19 := by ring
    _ ≤ H := hH'

lemma global_sieve_log_exponent {L s : ℝ} {B k : ℕ} (hL : 1 ≤ L) (hs : 0 < s)
    (hLB : L ≤ B) (hcost : 1900000 * s ^ 2 ≤ L * Real.log L)
    (hk : L ≤ 15000 * k * s) : 2200 * s ≤ 18 * k * Real.log (B : ℝ) := by
  have hLpos : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogB : Real.log L ≤ Real.log (B : ℝ) := Real.log_le_log hLpos hLB
  have hm : s * (1900000 * s) ≤ s * (15000 * k * Real.log (B : ℝ)) := by
    calc
      _ = 1900000 * s ^ 2 := by ring
      _ ≤ L * Real.log L := hcost
      _ ≤ (15000 * k * s) * Real.log L := mul_le_mul_of_nonneg_right hk hlogL
      _ ≤ (15000 * k * s) * Real.log (B : ℝ) := mul_le_mul_of_nonneg_left hlogB (by positivity)
      _ = _ := by ring
  have hcancel := (mul_le_mul_iff_right₀ hs).mp hm
  nlinarith

lemma highOrder_denominator_lower {N k : ℕ} (hB : 60 ≤ logarithmicCeiling N) (hk : 0 < k)
    (hL : 2 ≤ Real.log (N : ℝ)) (hN : 1 ≤ N) (hS : 0 < Real.log (scaleBase N : ℝ))
    (hcost : 1900000 * Real.log (scaleBase N : ℝ) ^ 2 ≤
      Real.log (N : ℝ) * Real.log (Real.log N))
    (hklo : (2 / 5 : ℝ) * Real.log N / Real.log (largePrimeScale N : ℝ) ≤ k)
    (hkhi : (k : ℝ) ≤ Real.log N / (2 * Real.log (2 * largePrimeScale N : ℕ))) :
    (scaleBase N : ℝ) ^ 2200 ≤
      ((runWidth N : ℝ) / (40 * k * Real.log (largePrimeScale N : ℝ))) ^ k := by
  have hSpos : (0 : ℝ) < scaleBase N := by exact_mod_cast
    (lt_of_lt_of_le Nat.zero_lt_one (one_le_scaleBase N))
  have ht : 0 < Real.log (largePrimeScale N : ℝ) := by
    rw [largePrimeScale, Nat.cast_pow, Real.log_pow]
    positivity
  have htpos : (0 : ℝ) < largePrimeScale N := by
    rw [largePrimeScale, Nat.cast_pow]
    exact pow_pos hSpos 6000
  have htlog : Real.log (largePrimeScale N : ℝ) ≤ Real.log (2 * largePrimeScale N : ℕ) :=
    Real.log_le_log htpos (by push_cast; linarith)
  have htlogpos : 0 < Real.log (2 * largePrimeScale N : ℕ) := ht.trans_le htlog
  have hBpos : 0 < logarithmicCeiling N := by omega
  have hW2 : 2 ≤ shortWidth N := by
    exact (by omega : 2 ≤ logarithmicCeiling N).trans
      (le_self_pow (by omega) (by decide : 20 ≠ 0))
  have hH : 0 < runWidth N := Nat.div_pos hW2 (by norm_num)
  have hW3 : shortWidth N ≤ 3 * runWidth N := by
    have hmod := Nat.mod_lt (shortWidth N) (by norm_num : 0 < 2)
    have hdiv := Nat.div_add_mod (shortWidth N) 2
    change 2 * runWidth N + shortWidth N % 2 = shortWidth N at hdiv
    omega
  have hHcast : (logarithmicCeiling N : ℝ) ^ 20 ≤ 3 * runWidth N := by exact_mod_cast hW3
  have hkb := (le_div_iff₀ (show 0 < 2 * Real.log (2 * largePrimeScale N : ℕ) by positivity)).mp hkhi
  have hden : 40 * (k : ℝ) * Real.log (largePrimeScale N : ℝ) ≤ 20 * logarithmicCeiling N := by
    have hm := mul_le_mul_of_nonneg_left htlog (show (0 : ℝ) ≤ k by positivity)
    have hLB := (logarithmicCeiling_bounds hN hL).1
    nlinarith
  have hbase := highOrder_base_lower hB hk ht hHcast hden
  have hkL : Real.log (N : ℝ) ≤ 15000 * k * Real.log (scaleBase N : ℝ) := by
    have hm := (div_le_iff₀ ht).mp hklo
    rw [largePrimeScale, Nat.cast_pow, Real.log_pow] at hm
    norm_num only [Nat.cast_ofNat] at hm
    nlinarith
  have hexp := global_sieve_log_exponent (by linarith : 1 ≤ Real.log (N : ℝ)) hS
    (logarithmicCeiling_bounds hN hL).1 hcost hkL
  have hpow : (scaleBase N : ℝ) ^ 2200 ≤ ((logarithmicCeiling N : ℝ) ^ 18) ^ k := by
    apply (Real.log_le_log_iff (pow_pos hSpos 2200)
      (pow_pos (pow_pos (by exact_mod_cast hBpos) 18) k)).mp
    rw [Real.log_pow, Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  exact hpow.trans (pow_le_pow_left₀ (by positivity) hbase k)

theorem eventually_smoothRunStarts_scale_bound : ∀ᶠ N : ℕ in atTop,
    ((smoothRunStarts N (runWidth N) (largePrimeScale N)).card : ℝ) ≤
      2 * N / (scaleBase N : ℝ) ^ 2200 := by
  obtain ⟨T₀, hbound⟩ := exists_uniform_smoothRunStarts_highOrder_bound
  filter_upwards [scaleBase_tendsto_atTop.eventually (eventually_ge_atTop (max T₀ 256)),
    eventually_scaleBase_pow_le 120020, eventually_log_pow_le_scaleBase 2,
    eventually_logarithmicCeiling_pow_le_scaleBase 20,
    log_nat_tendsto_atTop.eventually (eventually_ge_atTop (60 : ℝ)), eventually_ge_atTop 1,
    log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    scaleBase_loglog_relation.eventually (lt_mem_nhds (by norm_num : (1900000 : ℝ) < 2000000))]
      with N hSbig hNpow hLpow hW hL hN hS hcost
  have hS1 := one_le_scaleBase N
  have hS2 : 2 ≤ scaleBase N := by have := (le_max_right T₀ 256).trans hSbig; omega
  have hST : scaleBase N ≤ largePrimeScale N := le_self_pow hS1 (by decide : 6000 ≠ 0)
  have hT256 : 256 ≤ largePrimeScale N := ((le_max_right _ _).trans hSbig).trans hST
  have hTT₀ : T₀ ≤ largePrimeScale N := ((le_max_left _ _).trans hSbig).trans hST
  have hTpower : (2 * largePrimeScale N) ^ 20 ≤ N := by
    calc
      _ ≤ (scaleBase N * scaleBase N ^ 6000) ^ 20 := by
        apply Nat.pow_le_pow_left
        exact Nat.mul_le_mul_right _ hS2
      _ = scaleBase N ^ 120020 := by rw [← pow_succ', ← pow_mul]
      _ ≤ N := hNpow
  have hTsize : 10 * Real.log (N : ℝ) ≤ largePrimeScale N := by
    have hSTr : (scaleBase N : ℝ) ≤ largePrimeScale N := by exact_mod_cast hST
    nlinarith
  obtain ⟨k, hk, hkpow, hkT, hklo, hkhi⟩ := exists_sieve_order hT256 hTpower hTsize
  have hL2 : 2 ≤ Real.log (N : ℝ) := by linarith
  have hB : 60 ≤ logarithmicCeiling N := by
    have hLB := (logarithmicCeiling_bounds hN hL2).1
    exact_mod_cast (show (60 : ℝ) ≤ logarithmicCeiling N by linarith)
  have hW2 : 2 ≤ shortWidth N := (by omega : 2 ≤ logarithmicCeiling N).trans
    (le_self_pow (by omega) (by decide : 20 ≠ 0))
  have hH : 0 < runWidth N := Nat.div_pos hW2 (by norm_num)
  have hHT : runWidth N ≤ largePrimeScale N := (Nat.div_le_self _ _).trans (hW.trans hST)
  have hcost' := (le_div_iff₀ (pow_pos hS 2)).mp hcost.le
  have hden := highOrder_denominator_lower hB hk hL2 hN hS hcost' hklo hkhi
  have hsieve := hbound (largePrimeScale N) hTT₀ k (runWidth N) hk hH hHT hkT N hkpow
  apply hsieve.trans
  have hSpos : (0 : ℝ) < scaleBase N := by exact_mod_cast (by omega : 0 < scaleBase N)
  have hh := div_le_div_of_nonneg_left (show 0 ≤ (N : ℝ) + N by positivity) (pow_pos hSpos 2200) hden
  simpa only [two_mul] using hh

end Erdos380
