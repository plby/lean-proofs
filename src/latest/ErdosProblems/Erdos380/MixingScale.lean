import ErdosProblems.Erdos380.PrimeReciprocals

/-!
# Decay of the finite mixing bound

The prime number theorem supplies lower bounds for the pool cardinalities.
The exponent gap between fifth products and the square of the modulus range
then makes the primitive-character moment logarithmic in the pool scale.
-/

open scoped BigOperators Topology
open Filter

namespace Erdos380

lemma dyadicPrimes_prime {N p : ℕ} (hp : p ∈ dyadicPrimes N) : p.Prime :=
  (Finset.mem_filter.mp hp).2

lemma dyadicPrimes_le {N p : ℕ} (hp : p ∈ dyadicPrimes N) : p ≤ 2 * N :=
  (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2

lemma dyadic_pool_card_positive {N : ℕ} (hN : 4 ≤ N)
    (hc : ((N : ℝ) / Real.log N) / 10 ≤ ((dyadicPrimes N).card : ℝ)) :
    0 < ((dyadicPrimes N).card : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  exact lt_of_lt_of_le (by positivity) hc

lemma dyadic_pool_card_lower_mul {N : ℕ} (hN : 4 ≤ N)
    (hc : ((N : ℝ) / Real.log N) / 10 ≤ ((dyadicPrimes N).card : ℝ)) :
    (N : ℝ) ≤ 10 * Real.log N * ((dyadicPrimes N).card : ℝ) := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have h1 : (N : ℝ) / Real.log N ≤ 10 * ((dyadicPrimes N).card : ℝ) := by linarith
  have h2 := (div_le_iff₀ hlog).mp h1
  nlinarith

lemma dyadic_pool_reciprocal_card_le {N : ℕ} (hN : 4 ≤ N)
    (hc : ((N : ℝ) / Real.log N) / 10 ≤ ((dyadicPrimes N).card : ℝ)) :
    2 / ((dyadicPrimes N).card : ℝ) ≤ 20 * Real.log N / (N : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  apply (div_le_div_iff₀ (dyadic_pool_card_positive hN hc) hn).mpr
  nlinarith [dyadic_pool_card_lower_mul hN hc]

lemma dyadic_pool_moment_coefficient_le {N Y : ℕ} (hN : 4 ≤ N)
    (hc : ((N : ℝ) / Real.log N) / 10 ≤ ((dyadicPrimes N).card : ℝ))
    (hY : Y ^ 4 ≤ N ^ 5) :
    (((((2 * N : ℕ) : ℝ) ^ 5 + (Y : ℝ) ^ 4) * 120) /
      ((dyadicPrimes N).card : ℝ) ^ 5) ≤ 396000000 * (Real.log N) ^ 5 := by
  have hM := dyadic_pool_card_positive hN hc
  apply (div_le_iff₀ (pow_pos hM 5)).mpr
  have hYreal : (Y : ℝ) ^ 4 ≤ (N : ℝ) ^ 5 := by exact_mod_cast hY
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg N) (dyadic_pool_card_lower_mul hN hc) 5
  calc
    _ ≤ 3960 * (N : ℝ) ^ 5 := by push_cast; nlinarith
    _ ≤ 3960 * (10 * Real.log N * ((dyadicPrimes N).card : ℝ)) ^ 5 :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = _ := by ring

theorem eventually_dyadic_pool_estimates : ∀ᶠ N : ℕ in atTop,
    (dyadicPrimes N).Nonempty ∧
      2 / ((dyadicPrimes N).card : ℝ) ≤ 20 * Real.log N / (N : ℝ) ∧
      ∀ Y : ℕ, Y ^ 4 ≤ N ^ 5 →
        (((((2 * N : ℕ) : ℝ) ^ 5 + (Y : ℝ) ^ 4) * 120) /
          ((dyadicPrimes N).card : ℝ) ^ 5) ≤ 396000000 * (Real.log N) ^ 5 := by
  filter_upwards [eventually_dyadicPrimes_card_bounds, eventually_ge_atTop 4] with N hc hN
  have hM : 0 < (dyadicPrimes N).card := by exact_mod_cast dyadic_pool_card_positive hN hc.1
  exact ⟨Finset.card_pos.mp hM, dyadic_pool_reciprocal_card_le hN hc.1,
    fun Y hY => dyadic_pool_moment_coefficient_le hN hc.1 hY⟩

/-- Integer-power parameters avoid rounding issues in the modulus scale. -/
def mixingModulusPrimes (T : ℕ) : Finset ℕ :=
  (Finset.Ioc T (T ^ 110)).filter Nat.Prime

lemma mixingModulusPrimes_prime {T p : ℕ} (hp : p ∈ mixingModulusPrimes T) : p.Prime :=
  (Finset.mem_filter.mp hp).2

lemma mixingModulusPrimes_lower {T p : ℕ} (hp : p ∈ mixingModulusPrimes T) : T < p :=
  (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1

lemma mixingModulusPrimes_upper {T p : ℕ} (hp : p ∈ mixingModulusPrimes T) : p ≤ T ^ 110 :=
  (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2

lemma mixingModulusPrimes_card_le (T : ℕ) : (mixingModulusPrimes T).card ≤ T ^ 110 := by
  have h := Finset.card_filter_le (Finset.Ioc T (T ^ 110)) Nat.Prime
  simp only [Nat.card_Ioc] at h
  exact h.trans (Nat.sub_le _ _)

theorem exists_mixingModulusPrimes_totient_bound : ∃ S : ℝ, 0 ≤ S ∧
    ∀ T : ℕ, 2 ≤ T → (∑ p ∈ mixingModulusPrimes T, 1 / (p.totient : ℝ)) ≤ S := by
  obtain ⟨C, hC0, hC⟩ := exists_prime_band_totient_bound
  refine ⟨2 * Real.log 110 + C, by positivity, fun T hT => ?_⟩
  have hpow : T ≤ T ^ 110 := by
    calc
      T = T ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  apply hC T (T ^ 110) 110 (mixingModulusPrimes T) hT hpow (by norm_num)
  · rw [Nat.cast_pow, Real.log_pow]
    norm_num
  · exact fun _ hp => mixingModulusPrimes_prime hp
  · exact fun _ hp => mixingModulusPrimes_lower hp
  · exact fun _ hp => mixingModulusPrimes_upper hp

lemma mixing_modulus_coefficient_le {T : ℕ} (hT : 1 ≤ T) {S s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ S) :
    (1 / (T : ℝ)) * (1 + 2 * s) + 2 * (1 / (T : ℝ)) ^ 2 ≤
      (3 + 2 * S) / (T : ℝ) := by
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hw0 : (0 : ℝ) ≤ 1 / (T : ℝ) := by positivity
  have hw1 : (1 : ℝ) / (T : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hTreal
  have hw2 : (1 / (T : ℝ)) ^ 2 ≤ 1 / (T : ℝ) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hs hw0
  simp only [div_eq_mul_inv, one_mul] at *
  nlinarith

lemma mixing_scale_fifth_product_dominates {T N : ℕ} (hT : 1 ≤ T) (hN : T ^ 90 ≤ N) :
    (T ^ 110) ^ 4 ≤ N ^ 5 := by
  calc
    (T ^ 110) ^ 4 = T ^ 440 := by rw [← pow_mul]
    _ ≤ T ^ 450 := Nat.pow_le_pow_right hT (by decide)
    _ = (T ^ 90) ^ 5 := by rw [← pow_mul]
    _ ≤ N ^ 5 := Nat.pow_le_pow_left hN 5

lemma mixing_scale_log_le {T N : ℕ} (hT : 1 ≤ T) (hN0 : 0 < N) (hN : N ≤ T ^ 110) :
    Real.log (N : ℝ) ≤ 110 * Real.log T := by
  have h := Real.log_le_log (by exact_mod_cast hN0 : (0 : ℝ) < N)
    (by exact_mod_cast hN : (N : ℝ) ≤ (T : ℝ) ^ 110)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

lemma mixing_scale_reciprocal_pool_le {T N : ℕ} (hT : 1 ≤ T)
    (hNlo : T ^ 90 ≤ N) (hNhi : N ≤ T ^ 110)
    (hc : 2 / ((dyadicPrimes N).card : ℝ) ≤ 20 * Real.log N / (N : ℝ)) :
    2 / ((dyadicPrimes N).card : ℝ) ≤ 2200 / (T : ℝ) ^ 24 := by
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hN25 : T ^ 25 ≤ N := (Nat.pow_le_pow_right hT (by decide : 25 ≤ 90)).trans hNlo
  have hNpos : 0 < N := (pow_pos (by omega : 0 < T) 25).trans_le hN25
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hlogT : Real.log (T : ℝ) ≤ T := (Real.log_le_sub_one_of_pos hTpos).trans (by linarith)
  have hlogN : Real.log (N : ℝ) ≤ 110 * (T : ℝ) :=
    (mixing_scale_log_le hT hNpos hNhi).trans (mul_le_mul_of_nonneg_left hlogT (by norm_num))
  refine hc.trans ((div_le_div_iff₀ hNR (pow_pos hTpos 24)).mpr ?_)
  calc
    20 * Real.log N * (T : ℝ) ^ 24 ≤ (2200 * (T : ℝ)) * (T : ℝ) ^ 24 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 2200 * (T : ℝ) ^ 25 := by rw [pow_succ]; ring
    _ ≤ 2200 * (N : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hN25) (by norm_num)

lemma mixing_scale_moment_coefficient_le {T N : ℕ} (hT : 1 ≤ T) (hN4 : 4 ≤ N)
    (hNlo : T ^ 90 ≤ N) (hNhi : N ≤ T ^ 110)
    (hc : ((N : ℝ) / Real.log N) / 10 ≤ ((dyadicPrimes N).card : ℝ)) :
    (((((2 * N : ℕ) : ℝ) ^ 5 + ((T ^ 110 : ℕ) : ℝ) ^ 4) * 120) /
      ((dyadicPrimes N).card : ℝ) ^ 5) ≤
        (396000000 * (110 : ℝ) ^ 5) * (Real.log T) ^ 5 := by
  have h := dyadic_pool_moment_coefficient_le hN4 hc
    (mixing_scale_fifth_product_dominates hT hNlo)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  calc
    _ ≤ 396000000 * (Real.log N) ^ 5 := by exact_mod_cast h
    _ ≤ 396000000 * (110 * Real.log T) ^ 5 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlogN (mixing_scale_log_le hT (by omega) hNhi) 5) (by norm_num)
    _ = _ := by ring

lemma mixing_scale_pair_error_le {T : ℕ} (hT : 1 ≤ T) :
    ((T : ℝ) ^ 110 + (T : ℝ) ^ 220) * (2200 / (T : ℝ) ^ 24) ^ 10 ≤
      (2 * (2200 : ℝ) ^ 10) / (T : ℝ) := by
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : 0 < (T : ℝ) := by linarith
  have hT0 : (T : ℝ) ≠ 0 := hTpos.ne'
  have hpow : (T : ℝ) ^ 110 ≤ (T : ℝ) ^ 220 := pow_le_pow_right₀ hTr (by decide)
  have hpow20 : (T : ℝ) ≤ (T : ℝ) ^ 20 := by
    calc
      (T : ℝ) = (T : ℝ) ^ 1 := by simp
      _ ≤ _ := pow_le_pow_right₀ hTr (by decide)
  calc
    _ ≤ (2 * (T : ℝ) ^ 220) * (2200 / (T : ℝ) ^ 24) ^ 10 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (2 * (2200 : ℝ) ^ 10) / (T : ℝ) ^ 20 := by
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hTpos hpow20

lemma mixing_scale_one_pool_bound {T N : ℕ} {S : ℝ}
    (hT : 1 ≤ T) (hlogT : 1 ≤ Real.log (T : ℝ)) (hN4 : 4 ≤ N)
    (hNlo : T ^ 90 ≤ N) (hNhi : N ≤ T ^ 110)
    (hc : ((N : ℝ) / Real.log N) / 10 ≤ ((dyadicPrimes N).card : ℝ))
    (hS : 0 ≤ S)
    (hsum : (∑ p ∈ mixingModulusPrimes T, 1 / (p.totient : ℝ)) ≤ S) :
    (2 / ((dyadicPrimes N).card : ℝ)) *
        ((∑ p ∈ mixingModulusPrimes T, 1 / (p.totient : ℝ)) +
          (∑ p ∈ mixingModulusPrimes T, 1 / (p.totient : ℝ)) ^ 2) +
      512 * (((1 / (T : ℝ)) *
        (1 + 2 * ∑ p ∈ mixingModulusPrimes T, 1 / (p.totient : ℝ)) +
          2 * (1 / (T : ℝ)) ^ 2) *
        (((((2 * N : ℕ) : ℝ) ^ 5 + ((T ^ 110 : ℕ) : ℝ) ^ 4) * 120) /
          ((dyadicPrimes N).card : ℝ) ^ 5) +
        (((mixingModulusPrimes T).card : ℝ) + ((mixingModulusPrimes T).card : ℝ) ^ 2) *
          (2 / ((dyadicPrimes N).card : ℝ)) ^ 10) ≤
      (2200 * (S + S ^ 2) +
        512 * ((3 + 2 * S) * (396000000 * (110 : ℝ) ^ 5) + 2 * (2200 : ℝ) ^ 10)) *
          ((Real.log T) ^ 5 / (T : ℝ)) := by
  let r : ℝ := ∑ p ∈ mixingModulusPrimes T, 1 / (p.totient : ℝ)
  let M : ℝ := (dyadicPrimes N).card
  let c : ℝ := (mixingModulusPrimes T).card
  let K : ℝ := 396000000 * (110 : ℝ) ^ 5
  let F : ℝ := (Real.log T) ^ 5 / (T : ℝ)
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : 0 < (T : ℝ) := by linarith
  have hr0 : 0 ≤ r := Finset.sum_nonneg fun _ _ => by positivity
  have hL5 : 1 ≤ (Real.log (T : ℝ)) ^ 5 := one_le_pow₀ hlogT
  have hR := mixing_scale_reciprocal_pool_le hT hNlo hNhi (dyadic_pool_reciprocal_card_le hN4 hc)
  have hRweak : 2 / M ≤ 2200 / (T : ℝ) := by
    refine hR.trans (div_le_div_of_nonneg_left (by norm_num) hTpos ?_)
    calc
      (T : ℝ) = (T : ℝ) ^ 1 := by simp
      _ ≤ _ := pow_le_pow_right₀ hTr (by decide : 1 ≤ 24)
  have hrS : r + r ^ 2 ≤ S + S ^ 2 := by nlinarith
  have hprincipal : (2 / M) * (r + r ^ 2) ≤ (2200 * (S + S ^ 2)) * F := by
    calc
      _ ≤ (2200 / (T : ℝ)) * (S + S ^ 2) := mul_le_mul hRweak hrS (by positivity) (by positivity)
      _ ≤ ((2200 / (T : ℝ)) * (S + S ^ 2)) * (Real.log T) ^ 5 :=
        le_mul_of_one_le_right (by positivity) hL5
      _ = _ := by dsimp [F]; ring
  have hcoefficient := mixing_modulus_coefficient_le hT hr0 hsum
  have hmoment := mixing_scale_moment_coefficient_le hT hN4 hNlo hNhi hc
  have hmain : ((1 / (T : ℝ)) * (1 + 2 * r) + 2 * (1 / (T : ℝ)) ^ 2) *
      (((((2 * N : ℕ) : ℝ) ^ 5 + ((T ^ 110 : ℕ) : ℝ) ^ 4) * 120) / M ^ 5) ≤
        ((3 + 2 * S) * K) * F := by
    calc
      _ ≤ ((3 + 2 * S) / (T : ℝ)) * (K * (Real.log T) ^ 5) :=
        mul_le_mul hcoefficient hmoment (by positivity) (by positivity)
      _ = _ := by dsimp [F]; ring
  have hcard : c ≤ (T : ℝ) ^ 110 := by
    dsimp [c]
    exact_mod_cast mixingModulusPrimes_card_le T
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hcards : c + c ^ 2 ≤ (T : ℝ) ^ 110 + (T : ℝ) ^ 220 := by
    have hh := add_le_add hcard (pow_le_pow_left₀ hc0 hcard 2)
    simpa only [← pow_mul] using hh
  have herr : (c + c ^ 2) * (2 / M) ^ 10 ≤ (2 * (2200 : ℝ) ^ 10) * F := by
    calc
      _ ≤ ((T : ℝ) ^ 110 + (T : ℝ) ^ 220) * (2200 / (T : ℝ) ^ 24) ^ 10 :=
        mul_le_mul hcards (pow_le_pow_left₀ (by positivity) hR 10) (by positivity) (by positivity)
      _ ≤ (2 * (2200 : ℝ) ^ 10) / (T : ℝ) := mixing_scale_pair_error_le hT
      _ ≤ ((2 * (2200 : ℝ) ^ 10) / (T : ℝ)) * (Real.log T) ^ 5 :=
        le_mul_of_one_le_right (by positivity) hL5
      _ = _ := by dsimp [F]; ring
  calc
    _ ≤ (2200 * (S + S ^ 2)) * F +
        512 * (((3 + 2 * S) * K) * F + (2 * (2200 : ℝ) ^ 10) * F) :=
      add_le_add hprincipal (mul_le_mul_of_nonneg_left (add_le_add hmain herr) (by norm_num))
    _ = _ := by dsimp [K, F]; ring

/-- Unconditional uniform mixing at integer-power scales. The ten pool
endpoints may vary independently throughout the stated range. -/
theorem exists_uniform_ten_prime_mixing_bound : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ,
    ∀ T : ℕ, T₀ ≤ T → ∀ N : Fin 10 → ℕ,
      (∀ i, T ^ 90 ≤ N i) → (∀ i, N i ≤ T ^ 110) →
      modulusPairSum (mixingModulusPrimes T)
        (tenPrimeResidueError (fun i => dyadicPrimes (N i))) ≤
          C * ((Real.log T) ^ 5 / (T : ℝ)) := by
  obtain ⟨S, hS0, hS⟩ := exists_mixingModulusPrimes_totient_bound
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp eventually_dyadicPrimes_card_bounds
  have hlog : ∀ᶠ T : ℕ in atTop, 1 ≤ Real.log (T : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hlog
  let C₀ : ℝ := 2200 * (S + S ^ 2) +
    512 * ((3 + 2 * S) * (396000000 * (110 : ℝ) ^ 5) + 2 * (2200 : ℝ) ^ 10)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨10 * C₀, by positivity, max N₀ (max T₁ 4), fun T hT N hNlo hNhi => ?_⟩
  have hTN : N₀ ≤ T := (le_max_left _ _).trans hT
  have hTT : T₁ ≤ T := (le_max_left T₁ 4).trans ((le_max_right N₀ _).trans hT)
  have hT4 : 4 ≤ T := (le_max_right T₁ 4).trans ((le_max_right N₀ _).trans hT)
  have hT1 : 1 ≤ T := by omega
  have hTpow : T ≤ T ^ 90 := by
    calc
      T = T ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right hT1 (by decide)
  have hNi (i : Fin 10) : N₀ ≤ N i := hTN.trans (hTpow.trans (hNlo i))
  have hNi4 (i : Fin 10) : 4 ≤ N i := hT4.trans (hTpow.trans (hNlo i))
  have hc (i : Fin 10) : ((N i : ℝ) / Real.log (N i)) / 10 ≤
      ((dyadicPrimes (N i)).card : ℝ) := (hN₀ (N i) (hNi i)).1
  have hne (i : Fin 10) : (dyadicPrimes (N i)).Nonempty := by
    have hcard : 0 < (dyadicPrimes (N i)).card := by
      exact_mod_cast dyadic_pool_card_positive (hNi4 i) (hc i)
    exact Finset.card_pos.mp hcard
  have hfinite := ten_prime_product_mixing_bound
    (fun i => dyadicPrimes (N i)) (mixingModulusPrimes T) (fun i => 2 * N i) (T ^ 110)
    (fun _ _ hp => dyadicPrimes_prime hp) (fun _ _ hp => dyadicPrimes_le hp) hne
    (fun _ hp => mixingModulusPrimes_prime hp) (fun _ hp => mixingModulusPrimes_upper hp)
    (by positivity : (0 : ℝ) ≤ 1 / (T : ℝ))
    (fun _ hp => prime_band_reciprocal_totient_le (by omega)
      (mixingModulusPrimes_prime hp) (mixingModulusPrimes_lower hp))
  refine hfinite.trans ?_
  calc
    _ ≤ ∑ _i : Fin 10, C₀ * ((Real.log T) ^ 5 / (T : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mixing_scale_one_pool_bound hT1 (hT₁ T hTT) (hNi4 i)
        (hNlo i) (hNhi i) (hc i) hS0 (hS T (by omega))
    _ = _ := by simp; ring

end Erdos380
