import ErdosProblems.Erdos380.SingletonCount
import ErdosProblems.Erdos380.PrimeReciprocals
import ErdosProblems.Erdos469

/-!
# A prime-reciprocal Rankin bound for smooth numbers

The elementary Euler-product argument is sharpened by keeping the harmonic
sum over primes, rather than replacing it by the harmonic sum over all
integers.  This suffices for the required logarithmic upper estimate in
the growing-parameter range.
-/

open scoped BigOperators

namespace Erdos380

lemma prime_rankin_sum_le_reciprocal {y : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ p ∈ (y + 1).primesBelow, (p : ℝ) ^ (δ - 1)) ≤
      (y : ℝ) ^ δ * primeReciprocalSum y := by
  unfold primeReciprocalSum
  change _ ≤ (y : ℝ) ^ δ * ∑ p ∈ (y + 1).primesBelow, (1 : ℝ) / p
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpp := Nat.prime_of_mem_primesBelow hp
  have hpy : p ≤ y := Nat.lt_succ_iff.mp (Nat.mem_primesBelow.mp hp).1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  rw [Real.rpow_sub_one hpR.ne']
  simpa only [mul_one_div] using
    (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg p) (by exact_mod_cast hpy) hδ) hpR.le)

lemma smoothRankinEulerProduct_le_primeReciprocal {y : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    Erdos469.smoothRankinEulerProduct δ y ≤
      Real.exp (Erdos469.rankinEulerConstant * (y : ℝ) ^ δ * primeReciprocalSum y) := by
  calc
    Erdos469.smoothRankinEulerProduct δ y ≤
        ∏ p ∈ (y + 1).primesBelow,
          Real.exp (Erdos469.rankinEulerConstant * (p : ℝ) ^ (δ - 1)) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact inv_nonneg.mpr (sub_nonneg.mpr
          ((Erdos469.prime_rankinWeight_le_half_reference hδhalf
            (Nat.prime_of_mem_primesBelow hp)).trans
              (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)).le))
      · intro p hp
        exact Erdos469.inv_one_sub_le_exp_rankinEulerConstant_mul
          (Real.rpow_nonneg (Nat.cast_nonneg p) _)
          (Erdos469.prime_rankinWeight_le_half_reference hδhalf (Nat.prime_of_mem_primesBelow hp))
    _ = Real.exp (Erdos469.rankinEulerConstant *
        ∑ p ∈ (y + 1).primesBelow, (p : ℝ) ^ (δ - 1)) := by
      rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (prime_rankin_sum_le_reciprocal hδ0) Erdos469.rankinEulerConstant_pos.le)

theorem smoothCount_rankin_primeReciprocal {x y : ℕ} {δ : ℝ}
    (hx : 0 < x) (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    (smoothCount x y : ℝ) ≤ (x : ℝ) *
      Real.exp (-δ * Real.log x + Erdos469.rankinEulerConstant * (y : ℝ) ^ δ * primeReciprocalSum y) := by
  have hbase := Erdos469.card_smoothNumbersUpTo_rankin_le (x := x) (y := y)
    hx hδ0 (hδhalf.trans_lt (by norm_num))
  have hbound := hbase.trans (mul_le_mul_of_nonneg_left
    (smoothRankinEulerProduct_le_primeReciprocal hδ0.le hδhalf)
    (Real.rpow_nonneg (Nat.cast_nonneg x) _))
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hpow : (x : ℝ) ^ (1 - δ) = (x : ℝ) * Real.exp (-δ * Real.log x) := by
    rw [Real.rpow_def_of_pos hxR, show Real.log (x : ℝ) * (1 - δ) =
      Real.log (x : ℝ) + -δ * Real.log x by ring, Real.exp_add, Real.exp_log hxR]
  simpa only [smoothCount, hpow, Real.exp_add, mul_assoc] using hbound

theorem exists_smoothCount_rankin_loglog_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℕ, 0 < x → 2 ≤ y → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      (smoothCount x y : ℝ) ≤ (x : ℝ) *
        Real.exp (-δ * Real.log x + Erdos469.rankinEulerConstant * (y : ℝ) ^ δ *
          (Real.log (Real.log y) + C)) := by
  obtain ⟨C, hC, hM⟩ := exists_primeReciprocalSum_error_bound
  refine ⟨C, hC, fun x y hx hy δ hδ hδhalf => ?_⟩
  apply (smoothCount_rankin_primeReciprocal hx hδ hδhalf).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg x)
  apply Real.exp_le_exp.mpr
  have hsum : primeReciprocalSum y ≤ Real.log (Real.log y) + C := by
    have h := (abs_le.mp (hM y hy)).2
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ Erdos469.rankinEulerConstant * (y : ℝ) ^ δ by
      exact mul_nonneg Erdos469.rankinEulerConstant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg y) δ))
  linarith

lemma smoothCount_rankin_parameter_bound {x y : ℕ} {u ε A : ℝ}
    (hx : 0 < x) (hy : 2 ≤ y) (hu : 1 < u) (hε : 0 < ε) (hε1 : ε < 1)
    (hparam : Real.log (x : ℝ) = u * Real.log y)
    (hlogu : Real.log u ≤ Real.log (y : ℝ) / 2)
    (hprime : primeReciprocalSum y ≤ A * Real.log u)
    (hdecay : Erdos469.rankinEulerConstant * A ≤ ε * u ^ ε) :
    (smoothCount x y : ℝ) ≤ (x : ℝ) * Real.exp (-(1 - 2 * ε) * u * Real.log u) := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hlu : 0 < Real.log u := Real.log_pos hu
  let δ := (1 - ε) * Real.log u / Real.log y
  have hδ : 0 < δ := div_pos (mul_pos (sub_pos.mpr hε1) hlu) hlogy
  have hδhalf : δ ≤ 1 / 2 := by
    apply (div_le_iff₀ hlogy).mpr
    nlinarith [mul_nonneg hε.le hlu.le]
  have hypow : (y : ℝ) ^ δ = u ^ (1 - ε) := by
    rw [Real.rpow_def_of_pos hyR, Real.rpow_def_of_pos hu0]
    congr 1
    dsimp [δ]
    field_simp
  have hmain : -δ * Real.log (x : ℝ) = -(1 - ε) * u * Real.log u := by
    rw [hparam]
    dsimp [δ]
    field_simp
  have hpow : u ^ ε * u ^ (1 - ε) = u := by
    rw [← Real.rpow_add hu0]
    norm_num
  have hsmall : Erdos469.rankinEulerConstant * A * u ^ (1 - ε) ≤ ε * u := by
    have hmul := mul_le_mul_of_nonneg_right hdecay (Real.rpow_nonneg hu0.le (1 - ε))
    simpa only [mul_assoc, hpow] using hmul
  have herror : Erdos469.rankinEulerConstant * u ^ (1 - ε) * primeReciprocalSum y ≤
      ε * u * Real.log u := by
    calc
      _ ≤ Erdos469.rankinEulerConstant * u ^ (1 - ε) * (A * Real.log u) :=
        mul_le_mul_of_nonneg_left hprime (mul_nonneg Erdos469.rankinEulerConstant_pos.le
          (Real.rpow_nonneg hu0.le _))
      _ = (Erdos469.rankinEulerConstant * A * u ^ (1 - ε)) * Real.log u := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hlu.le
  apply (smoothCount_rankin_primeReciprocal hx hδ hδhalf).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg x)
  apply Real.exp_le_exp.mpr
  rw [hypow, hmain]
  nlinarith

/-- A uniform logarithmic upper estimate in a growing-parameter regime.
The condition relating `log log y` to `log u` is explicit; it includes the
saddle range needed for this problem. -/
theorem smoothCount_growing_parameter_upper
    {ε A : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hA : 0 ≤ A) :
    ∃ u₀ : ℝ, 1 < u₀ ∧ ∀ x y : ℕ, 0 < x → 2 ≤ y →
      ∀ u : ℝ, u₀ ≤ u → Real.log (x : ℝ) = u * Real.log y →
      Real.log (Real.log y) ≤ A * Real.log u → Real.log u ≤ Real.log (y : ℝ) / 2 →
      (smoothCount x y : ℝ) ≤ (x : ℝ) * Real.exp (-(1 - 2 * ε) * u * Real.log u) := by
  obtain ⟨C, hC, hM⟩ := exists_primeReciprocalSum_error_bound
  have hpower := (Filter.tendsto_atTop.mp (tendsto_rpow_atTop hε))
    (Erdos469.rankinEulerConstant * (A + C) / ε)
  obtain ⟨u₁, hu₁⟩ := Filter.eventually_atTop.mp hpower
  refine ⟨max u₁ (Real.exp 1), ?_, ?_⟩
  · exact (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le (le_max_right _ _)
  · intro x y hx hy u hu hparam hloglog hlogu
    have huexp : Real.exp 1 ≤ u := (le_max_right _ _).trans hu
    have hu0 : 0 < u := (Real.exp_pos 1).trans_le huexp
    have hu1 : 1 < u := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le huexp
    have hlu : 1 ≤ Real.log u := by
      have h := Real.log_le_log (Real.exp_pos 1) huexp
      simpa only [Real.log_exp] using h
    apply smoothCount_rankin_parameter_bound hx hy hu1 hε hε1 hparam hlogu
      (A := A + C)
    · have hsum := (abs_le.mp (hM y hy)).2
      have hCm := mul_le_mul_of_nonneg_left hlu hC
      nlinarith
    · have hpow := hu₁ u ((le_max_left _ _).trans hu)
      have hmul := (div_le_iff₀ hε).mp hpow
      simpa only [mul_comm] using hmul

end Erdos380
