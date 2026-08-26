import ErdosProblems.Erdos380.ShortIntervalPrime
import ErdosProblems.Erdos380.PrimeCounts
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# An eventual Sylvester bound sufficient for bad intervals

The binomial coefficient has each prime-power factor at most its upper
index. The prime number theorem and elementary binomial lower bounds
therefore force a prime greater than the interval length, once the length
is large. The previously proved cubic bound handles the bounded lengths.
-/

open scoped BigOperators
open Filter

namespace Erdos380

lemma log_choose_le_primeCounting_mul_log {v k : ℕ} (hv : 0 < v) (hkv : k ≤ v)
    (hsmall : ∀ p, p.Prime → p ∣ v.choose k → p ≤ k) :
    Real.log (v.choose k : ℝ) ≤ Nat.primeCounting k * Real.log (v : ℝ) := by
  have hc := Nat.choose_pos hkv
  have hsub : (v.choose k).primeFactors ⊆ (k + 1).primesBelow := by
    intro p hp
    exact Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_iff.mpr
      (hsmall p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)),
      Nat.prime_of_mem_primeFactors hp⟩
  have hcard : (v.choose k).primeFactors.card ≤ Nat.primeCounting k := by
    have h := Finset.card_le_card hsub
    simpa only [Nat.primesBelow_card_eq_primeCounting', Nat.primeCounting] using h
  have hprod : v.choose k ≤ v ^ Nat.primeCounting k := by
    calc
      v.choose k = ∏ p ∈ (v.choose k).primeFactors, p ^ (v.choose k).factorization p :=
        Nat.prod_primeFactors_pow_factorization hc.ne'
      _ ≤ ∏ _p ∈ (v.choose k).primeFactors, v :=
        Finset.prod_le_prod' fun _ _ => Nat.pow_factorization_choose_le hv
      _ = v ^ (v.choose k).primeFactors.card := Finset.prod_const v
      _ ≤ v ^ Nat.primeCounting k := Nat.pow_le_pow_right hv hcard
  calc
    Real.log (v.choose k : ℝ) ≤ Real.log ((v : ℝ) ^ Nat.primeCounting k) := by
      apply Real.log_le_log (by exact_mod_cast hc)
      exact_mod_cast hprod
    _ = _ := by rw [Real.log_pow]

lemma log_choose_ge_central {v k : ℕ} (hk : 4 ≤ k) (hkv : 2 * k ≤ v) :
    (k : ℝ) * Real.log 4 - Real.log k < Real.log (v.choose k : ℝ) := by
  have hp := Nat.four_pow_lt_mul_centralBinom k hk
  have hm : Nat.centralBinom k ≤ v.choose k :=
    Nat.choose_mono k hkv
  have hlt : (4 : ℝ) ^ k < (k : ℝ) * v.choose k := by
    exact_mod_cast hp.trans_le (Nat.mul_le_mul_left k hm)
  have hc : 0 < v.choose k := Nat.choose_pos (by omega)
  have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < 4 ^ k) hlt
  rw [Real.log_pow, Real.log_mul (by exact_mod_cast (by omega : k ≠ 0))
    (by exact_mod_cast hc.ne')] at hlog
  linarith

lemma log_choose_ge_interval {u v k : ℕ} (hu : 1 ≤ u) (hk : 1 ≤ k)
    (hku : u + k = v + 1) :
    (k : ℝ) * (Real.log (u : ℝ) - Real.log k) ≤ Real.log (v.choose k : ℝ) := by
  have hc : 0 < v.choose k := Nat.choose_pos (by omega)
  have hl : u ^ k ≤ k ^ k * v.choose k := by
    calc
      u ^ k ≤ intervalProduct u v := intervalProduct_ge_pow hku
      _ = k.factorial * v.choose k := intervalProduct_eq_factorial_mul_choose hu hku
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.factorial_le_pow k)
  have hlog := Real.log_le_log (by exact_mod_cast (pow_pos (by omega : 0 < u) k))
    (show ((u ^ k : ℕ) : ℝ) ≤ ((k ^ k * v.choose k : ℕ) : ℝ) by exact_mod_cast hl)
  simp only [Nat.cast_pow, Nat.cast_mul] at hlog
  rw [Real.log_mul (pow_ne_zero k (by exact_mod_cast (by omega : k ≠ 0)))
    (by exact_mod_cast hc.ne'), Real.log_pow, Real.log_pow] at hlog
  linarith

lemma intervalPrime_gt_of_log_bounds {u v k : ℕ} (hu : 1 ≤ u) (hk : 4 ≤ k)
    (hku : u + k = v + 1) (hkv : 2 * k ≤ v)
    (hcount : (Nat.primeCounting k : ℝ) ≤ (11 / 10 : ℝ) * ((k : ℝ) / Real.log k))
    (hlog : 100 ≤ Real.log (k : ℝ)) (hsmall : Real.log (k : ℝ) ≤ (k : ℝ) / 100) :
    k < intervalPrime u v := by
  by_contra hnot
  have hQ : intervalPrime u v ≤ k := by omega
  have hv : 0 < v := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have ht : 0 < Real.log (k : ℝ) := by linarith
  have hL : 0 < Real.log (v : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < v))
  have hchoose : v.choose k ∣ intervalProduct u v := by
    rw [intervalProduct_eq_factorial_mul_choose hu hku]
    exact dvd_mul_left _ _
  have hupper := log_choose_le_primeCounting_mul_log hv (by omega : k ≤ v)
    (fun p hp hpc => (prime_le_largestPrimeFactor (intervalProduct_pos hu).ne' hp
      (hpc.trans hchoose)).trans hQ)
  have hcountMul : (Nat.primeCounting k : ℝ) * Real.log k ≤ (11 / 10 : ℝ) * k := by
    apply (le_div_iff₀ ht).mp
    simpa only [mul_div_assoc] using hcount
  have hlog2lo : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  by_cases hvsmall : v ≤ 16 * k
  · have hLupper : Real.log (v : ℝ) ≤ Real.log k + 4 := by
      have h := Real.log_le_log (by exact_mod_cast hv : (0 : ℝ) < v)
        (show (v : ℝ) ≤ 16 * k by exact_mod_cast hvsmall)
      rw [Real.log_mul (by norm_num) hkR.ne', hlog16] at h
      linarith
    have hcount100 : 100 * (Nat.primeCounting k : ℝ) ≤ (11 / 10 : ℝ) * k := by
      have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (Nat.primeCounting k) : (0 : ℝ) ≤ _)
      nlinarith
    have hLcount := mul_le_mul_of_nonneg_left hLupper
      (Nat.cast_nonneg (Nat.primeCounting k) : (0 : ℝ) ≤ _)
    have hupper' : Real.log (v.choose k : ℝ) ≤ (6 / 5 : ℝ) * k := by
      nlinarith
    have hlower := log_choose_ge_central hk hkv
    have hlog4 : (4 / 3 : ℝ) < Real.log 4 := by rw [Real.log_four_eq]; linarith
    have h := mul_lt_mul_of_pos_left hlog4 hkR
    nlinarith
  · have hLlower : Real.log k + 4 * Real.log 2 ≤ Real.log (v : ℝ) := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < 16 * k)
        (show (16 : ℝ) * k ≤ v by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hvsmall)))
      rw [Real.log_mul (by norm_num) hkR.ne', hlog16] at h
      linarith
    have huR : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
    have hLu : Real.log (v : ℝ) - Real.log 2 ≤ Real.log (u : ℝ) := by
      have h := Real.log_le_log (by exact_mod_cast hv : (0 : ℝ) < v)
        (show (v : ℝ) ≤ 2 * u by exact_mod_cast (by omega : v ≤ 2 * u))
      rw [Real.log_mul (by norm_num) huR.ne'] at h
      linarith
    have hlower := log_choose_ge_interval hu (by omega) hku
    have hlu := mul_le_mul_of_nonneg_left hLu hkR.le
    have hboth : (k : ℝ) * (Real.log v - Real.log 2 - Real.log k) ≤
        Nat.primeCounting k * Real.log v := by nlinarith
    have hbad : Real.log k * (Real.log v - Real.log 2 - Real.log k) ≤
        (11 / 10 : ℝ) * Real.log v := by
      apply le_of_mul_le_mul_left _ hkR
      have h₁ := mul_le_mul_of_nonneg_right hboth ht.le
      have h₂ := mul_le_mul_of_nonneg_right hcountMul hL.le
      nlinarith
    have hprod := mul_nonneg (show 0 ≤ Real.log (k : ℝ) - (11 / 10 : ℝ) by linarith)
      (sub_nonneg.mpr hLlower)
    have htwo := mul_le_mul_of_nonneg_left hlog2lo.le ht.le
    nlinarith

theorem exists_intervalPrime_gt_length_threshold : ∃ u₀ : ℕ, ∀ u v k : ℕ,
    u₀ ≤ u → 1 ≤ u → 2 ≤ k → u + k = v + 1 → 2 * k ≤ v →
      k < intervalPrime u v := by
  have hlogsmall := tendsto_natCast_atTop_atTop.eventually
    (Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 100))
  have hloglarge := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (100 : ℝ))
  have hall : ∀ᶠ k : ℕ in atTop, 4 ≤ k ∧
      (Nat.primeCounting k : ℝ) ≤ (11 / 10 : ℝ) * ((k : ℝ) / Real.log k) ∧
      100 ≤ Real.log (k : ℝ) ∧ Real.log (k : ℝ) ≤ (k : ℝ) / 100 := by
    filter_upwards [eventually_ge_atTop 4, eventually_primeCounting_bounds,
      hloglarge, hlogsmall] with k hk hc hl hs
    change 100 ≤ Real.log (k : ℝ) at hl
    refine ⟨hk, hc.2, hl, ?_⟩
    simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ Real.log (k : ℝ)),
      abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k), one_div_mul_eq_div] using hs
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp hall
  refine ⟨4 * k₀ ^ 3 + 1, ?_⟩
  intro u v k hu₀ hu hk hku hkv
  by_cases hkk : k₀ ≤ k
  · obtain ⟨hk4, hc, hl, hs⟩ := hk₀ k hkk
    exact intervalPrime_gt_of_log_bounds hu hk4 hku hkv hc hl hs
  · apply intervalPrime_gt_of_cubic hu hk hku (by omega)
    have hpow := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_of_not_ge hkk)) 3
    omega

theorem exists_badInterval_square_anchor_threshold : ∃ u₀ : ℕ, ∀ u v : ℕ,
    u₀ ≤ u → BadInterval u v → ∃ a ∈ Finset.Icc u v,
      intervalPrime u v ^ 2 ∣ a ∧ largestPrimeFactor a = intervalPrime u v := by
  obtain ⟨u₀, hu₀⟩ := exists_intervalPrime_gt_length_threshold
  refine ⟨u₀, ?_⟩
  intro u v hu hbad
  apply hbad.exists_square_anchor_of_short
  by_cases heq : u = v
  · have hQ := one_le_largestPrimeFactor (intervalProduct u v)
    change v - u < largestPrimeFactor (intervalProduct u v)
    omega
  · have huv := hbad.2.1
    have hratio := hbad.right_lt_two_mul_left
    have hlt := hu₀ u v (v - u + 1) hu hbad.1 (by omega) (by omega) (by omega)
    omega

end Erdos380
