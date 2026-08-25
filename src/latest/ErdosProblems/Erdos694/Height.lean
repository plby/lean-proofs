import ErdosProblems.Erdos694.PrimeProducts
import ErdosProblems.Erdos694.SmallModuli

/-!
# Unconditional collisions with controlled height

For each fixed positive integer `D`, put `Y = k^D`. Choose at most `2Y`
distinct primes in `(2^k, 2^(k+1)]` whose predecessor product is divisible
by `A Y`. Their product `N` is coprime to its totient. The composite
construction then has height at most `exp (8*k^(D+1))` and ratio
asymptotic to `exp(γ)*D*log k`.
-/

namespace Erdos694

open Filter Topology
open scoped BigOperators

noncomputable def dyadicRatio (D k : ℕ) : ℝ :=
  primeEulerProdNat (k ^ D) * (1 - 2 * (k : ℝ) ^ D / (2 : ℝ) ^ k)

lemma primeEulerProdNat_nonneg (Y : ℕ) : 0 ≤ primeEulerProdNat Y := by
  apply Finset.prod_nonneg
  intro p hp
  exact (one_le_prime_factor p (Finset.mem_filter.mp hp).2).trans' zero_le_one

lemma dyadic_collision_height (D : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      ∃ a b n : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ n ∧
        Nat.totient a = n ∧ Nat.totient b = n ∧
        dyadicRatio D k ≤ (b : ℝ) / a ∧
        (n : ℝ) ≤ Real.exp (8 * (k : ℝ) ^ (D + 1)) := by
  filter_upwards [eventually_dyadic_primes D, eventually_ge_atTop 1] with k hk hk1
  let Y := k ^ D
  let T := 2 ^ k
  have hT : 2 ≤ T := by
    change 2 ^ 1 ≤ 2 ^ k
    exact Nat.pow_le_pow_right (by decide) hk1
  obtain ⟨S, hcard, hS, hA, hcop⟩ :=
    LowerConstruction.exists_dyadic_totient_multiple Y T hT hk
  let N := ∏ p ∈ S, p
  let U := Nat.totient N / LowerConstruction.A Y
  let Q := LowerConstruction.Q Y U
  have hN : 0 < N := Finset.prod_pos fun p hp => (hS p hp).1.pos
  have hU : 0 < U := Nat.div_pos (Nat.le_of_dvd (Nat.totient_pos.mpr hN) hA)
    (LowerConstruction.A_pos Y)
  have hQ : 0 < Q := LowerConstruction.Q_pos Y U
  have ha : 0 < N * Q := Nat.mul_pos hN hQ
  have hb : 0 < LowerConstruction.P Y * U * Q :=
    Nat.mul_pos (Nat.mul_pos (LowerConstruction.P_pos Y) hU) hQ
  refine ⟨N * Q, LowerConstruction.P Y * U * Q, Nat.totient (N * Q),
    ha, hb, Nat.totient_pos.mpr ha, rfl,
    (LowerConstruction.composite_collision Y N hN hcop hA).symm, ?_, ?_⟩
  · have hratio := LowerConstruction.dyadic_totient_ratio_lower T S (by omega)
      (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩)
    have hcardR : (S.card : ℝ) ≤ 2 * (k : ℝ) ^ D := by exact_mod_cast hcard
    have hratio' : 1 - 2 * (k : ℝ) ^ D / (2 : ℝ) ^ k ≤ (Nat.totient N : ℝ) / N := by
      have h := div_le_div_of_nonneg_right hcardR
        (show (0 : ℝ) ≤ (2 : ℝ) ^ k by positivity)
      dsimp only [T] at hratio
      push_cast at hratio
      exact (sub_le_sub_left h 1).trans (by simpa only [N, Nat.cast_prod] using hratio)
    rw [LowerConstruction.composite_collision_ratio Y N hN hA]
    exact mul_le_mul_of_nonneg_left hratio' (primeEulerProdNat_nonneg Y)
  · have hNle : N ≤ (2 * T) ^ (2 * Y) := by
      apply (Finset.prod_le_pow_card S (fun p => p) (2 * T)
        (fun p hp => (hS p hp).2.2)).trans
      exact Nat.pow_le_pow_right (by omega) hcard
    have hnle := LowerConstruction.composite_collision_size Y N hN hA
    have hnR : (Nat.totient (N * Q) : ℝ) ≤ ((2 * T : ℕ) : ℝ) ^ (4 * Y) := by
      exact_mod_cast hnle.trans ((Nat.pow_le_pow_left hNle 2).trans_eq (by
        rw [← pow_mul]
        congr 1
        ring))
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at this
      exact this
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hlogT : Real.log ((2 * T : ℕ) : ℝ) = (k + 1 : ℝ) * Real.log 2 := by
      dsimp [T]
      push_cast
      rw [← pow_succ', Real.log_pow]
      norm_num
    have hpowpos : (0 : ℝ) < ((2 * T : ℕ) : ℝ) ^ (4 * Y) := by positivity
    apply hnR.trans
    rw [← Real.exp_log hpowpos, Real.exp_le_exp, Real.log_pow, hlogT]
    have hkD : 0 ≤ (k : ℝ) ^ D := by positivity
    have h1 : ((k : ℝ) + 1) * Real.log 2 ≤ 2 * k := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hkD)
    dsimp [Y]
    push_cast
    rw [pow_succ]
    nlinarith

lemma dyadicRatio_tendsto (D : ℕ) (hD : 0 < D) :
    Tendsto (fun k : ℕ => dyadicRatio D k / Real.log k) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant * D)) := by
  have hpow : Tendsto (fun k : ℕ => k ^ D) atTop atTop :=
    tendsto_pow_atTop hD.ne'
  have hmertens : Tendsto
      (fun k : ℕ => primeEulerProdNat (k ^ D) /
        (Real.exp Real.eulerMascheroniConstant * Real.log (k ^ D : ℕ))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Nat.floor_natCast, primeEulerProdNat] using
      _root_.mertens_product.comp (tendsto_natCast_atTop_atTop.comp hpow)
  have hsmall : Tendsto (fun k : ℕ => 2 * (k : ℝ) ^ D / (2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (tendsto_pow_const_div_const_pow_of_one_lt D (by norm_num : (1 : ℝ) < 2)).const_mul 2
  have h := (hmertens.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hsmall)).mul_const
    (Real.exp Real.eulerMascheroniConstant * D)
  simp only [sub_zero, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hlog : Real.log (k : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < k by omega))).ne'
  have hγ : Real.exp Real.eulerMascheroniConstant ≠ 0 := (Real.exp_pos _).ne'
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  simp only [dyadicRatio, Nat.cast_pow, Real.log_pow]
  field_simp

end Erdos694
