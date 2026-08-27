import ErdosProblems.Erdos587.HooleySieveTailRange

/-!
# The terminal bounded-prime range

At a fixed smoothness cutoff, a half-power Rankin twist saves `R^(1/2)`.
An arbitrarily small divisor-power bound absorbs the unrestricted
cofactor and the remaining logarithm. This also includes prime powers.
-/

open scoped BigOperators

namespace Erdos587

lemma delta_linear_exp_decay (x : ℝ) : x * Real.exp (-x / 4) ≤ 4 := by
  have h : x / 4 ≤ Real.exp (x / 4) := by linarith [Real.add_one_le_exp (x / 4)]
  calc
    _ = 4 * ((x / 4) * Real.exp (-x / 4)) := by ring
    _ ≤ 4 * (Real.exp (x / 4) * Real.exp (-x / 4)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)) (by norm_num)
    _ = _ := by rw [← Real.exp_add, show x / 4 + -x / 4 = 0 by ring, Real.exp_zero, mul_one]

lemma delta_small_prime_cost_bound {x H k : ℝ} (hk : 0 < k) (hH0 : 0 ≤ H)
    (hH : H ≤ 2 * k * x) :
    Real.exp (H / (8 * k) - x / 2) * H ≤ 8 * k := by
  have heps : H / (8 * k) ≤ x / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * k)).mpr
    nlinarith
  have hexp : Real.exp (H / (8 * k) - x / 2) ≤ Real.exp (-x / 4) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ Real.exp (-x / 4) * (2 * k * x) :=
      mul_le_mul hexp hH hH0 (Real.exp_nonneg _)
    _ = (2 * k) * (x * Real.exp (-x / 4)) := by ring
    _ ≤ (2 * k) * 4 := mul_le_mul_of_nonneg_left (delta_linear_exp_decay x) (by positivity)
    _ = _ := by ring

theorem exists_delta_small_prime_sieve_bound (k W : ℕ) (hk : 0 < k) (hW : 2 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℤ), B ≠ 0 → IsCoprime A B →
      ∀ R N Y : ℕ, 2 ≤ R → 2 ≤ N → R ^ 4 ≤ Y → N ≤ (R + 1) ^ k →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Y →
      (∀ n ∈ S, (A + B * n).natAbs ≤ N) →
      (∀ n ∈ S, ∃ a b : ℕ, (A + B * n).natAbs = a * b ∧
        0 < a ∧ 0 < b ∧ a ≤ R ^ 2 ∧ R ≤ a ∧ a.primeFactors ⊆ Nat.primesLE W) →
      (∑ n ∈ S, (hooleyDelta (A + B * n).natAbs : ℝ)) ≤
        C * ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
          (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let ε : ℝ := 1 / (8 * k)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨C₁, hC₁, hdivisor⟩ := Erdos1148.DukeArithmetic.exists_card_divisors_le_rpow hε
  obtain ⟨C₀, hC₀, hmean⟩ := exists_hooleyDelta_harmonic_loglog_bound
  let M : ℝ := Real.log (W : ℝ) / 2
  let E : ℝ := 20 * deltaRankinMertensConstant * M * Real.exp M
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨(3 * C₁ * C₀ * Real.exp E / Real.log 2) * (8 * k), by positivity, ?_⟩
  intro A B hB hAB R N Y hR hN hRY hRN S hS hvalues hcover
  let K : ℝ := C₁ * Real.exp (Real.log (N : ℝ) / (8 * k))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hcut : R ^ 2 * 1 ^ 2 ≤ Y := by
    simpa only [one_pow, mul_one] using
      (Nat.pow_le_pow_right (by omega : 1 ≤ R) (by norm_num : 2 ≤ 4)).trans hRY
  have hβM : (1 / 2 : ℝ) * Real.log (W : ℝ) ≤ M := by dsimp only [M]; linarith
  have hcover' : ∀ n ∈ S, ∃ a b : ℕ, (A + B * n).natAbs = a * b ∧
      0 < a ∧ 0 < b ∧ a ≤ R ^ 2 ∧ (R : ℝ) ≤ a ∧ a.primeFactors ⊆ Nat.primesLE W ∧
      (∀ p ∈ b.primeFactors, 1 < p) ∧ (b.divisors.card : ℝ) ≤ K := by
    intro n hn
    obtain ⟨a, b, hfactor, ha, hb, haR, hRa, hsmooth⟩ := hcover n hn
    have hbN : b ≤ N := by nlinarith [hvalues n hn]
    refine ⟨a, b, hfactor, ha, hb, haR, by exact_mod_cast hRa, hsmooth,
      fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt, ?_⟩
    calc
      _ ≤ C₁ * (b : ℝ) ^ ε := hdivisor b hb.ne'
      _ ≤ C₁ * (N : ℝ) ^ ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hbN) hε.le) hC₁.le
      _ = K := by
        rw [Real.rpow_def_of_pos hNpos]
        dsimp only [K, ε]
        congr 2
        ring
  have hsieve := delta_sieve_tail_range_weighted_le hB hAB (by norm_num : 0 < 1) hW hcut
    hRpos (by norm_num : (0 : ℝ) ≤ 1 / 2) le_rfl hβM S hS hvalues hK hcover'
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlogN : Real.log (N : ℝ) ≤ 2 * (k : ℝ) * Real.log (R : ℝ) := by
    have h := Real.log_le_log hNpos
      (show (N : ℝ) ≤ ((R + 1 : ℕ) : ℝ) ^ k by exact_mod_cast hRN)
    rw [Real.log_pow] at h
    nlinarith [mul_le_mul_of_nonneg_left (delta_log_succ_le hR) hkR.le]
  have hcost := delta_small_prime_cost_bound hkR hlogN0 hlogN
  calc
    _ ≤ 3 * ((B.natAbs : ℝ) / B.natAbs.totient) * Y / Real.log 2 * K *
        Real.exp (E - (1 / 2 : ℝ) * Real.log (R : ℝ)) *
          ∑ d ∈ Finset.Icc 1 N, (hooleyDelta d : ℝ) / d := by
      simpa only [Nat.reduceAdd, Nat.cast_ofNat] using hsieve
    _ ≤ 3 * ((B.natAbs : ℝ) / B.natAbs.totient) * Y / Real.log 2 * K *
        Real.exp (E - (1 / 2 : ℝ) * Real.log (R : ℝ)) *
          (C₀ * Real.log (N : ℝ) * (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5) :=
      mul_le_mul_of_nonneg_left (hmean N hN) (by positivity)
    _ = ((3 * C₁ * C₀ * Real.exp E / Real.log 2) *
        ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
          (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5) *
            (Real.exp (Real.log (N : ℝ) / (8 * k) - Real.log (R : ℝ) / 2) * Real.log (N : ℝ)) := by
      dsimp only [K]
      rw [show E - (1 / 2 : ℝ) * Real.log (R : ℝ) = E + (-Real.log (R : ℝ) / 2) by ring,
        show Real.log (N : ℝ) / (8 * k) - Real.log (R : ℝ) / 2 =
          Real.log (N : ℝ) / (8 * k) + (-Real.log (R : ℝ) / 2) by ring]
      rw [Real.exp_add, Real.exp_add]
      ring
    _ ≤ ((3 * C₁ * C₀ * Real.exp E / Real.log 2) *
        ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
          (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5) * (8 * k) :=
      mul_le_mul_of_nonneg_left hcost (by positivity)
    _ = _ := by ring

end Erdos587
