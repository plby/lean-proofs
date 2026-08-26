import Mathlib

/-!
# Subpower bounds for divisor counts

Elementary subpower bounds for divisor counts and products of prime-exponent factors.
Adapted from the checked repository proof in Erdos1148/DivisorBounds.lean.
-/

namespace Erdos941.Analytic

lemma nat_add_one_le_mul_pow {b : ℝ} (hb : 1 < b) (k : ℕ) :
    (k : ℝ) + 1 ≤ (1 + (b - 1)⁻¹) * b ^ k := by
  have hpow : 1 ≤ b ^ k := one_le_pow₀ hb.le
  have hbern : 1 + (k : ℝ) * (b - 1) ≤ b ^ k :=
    one_add_mul_sub_le_pow (by linarith) k
  have hk : (k : ℝ) ≤ b ^ k / (b - 1) := by
    apply (le_div_iff₀ (by linarith)).2
    linarith
  calc
    (k : ℝ) + 1 ≤ b ^ k / (b - 1) + b ^ k := add_le_add hk hpow
    _ = (1 + (b - 1)⁻¹) * b ^ k := by ring

lemma nat_add_one_le_two_pow (k : ℕ) : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, mul_one, add_comm] using
    one_add_mul_sub_le_pow (a := (2 : ℝ)) (by norm_num) k

/-- The divisor-counting function is bounded by every positive power. -/
theorem exists_card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let b : ℝ := (2 : ℝ) ^ ε
  let A : ℝ := 1 + (b - 1)⁻¹
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hε
  have hA : 1 ≤ A := by
    have : 0 ≤ (b - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    dsimp [A]
    linarith
  have hApos : 0 < A := zero_lt_one.trans_le hA
  obtain ⟨B, hB⟩ := exists_nat_gt ((2 : ℝ) ^ ε⁻¹)
  have hsmall (p k : ℕ) (hp : 2 ≤ p) :
      (k : ℝ) + 1 ≤ A * ((p : ℝ) ^ k) ^ ε := by
    calc
      (k : ℝ) + 1 ≤ A * b ^ k := nat_add_one_le_mul_pow hb k
      _ ≤ A * ((p : ℝ) ^ ε) ^ k := by
        apply mul_le_mul_of_nonneg_left _ hApos.le
        apply pow_le_pow_left₀ (by positivity)
        exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp) hε.le
      _ = A * ((p : ℝ) ^ k) ^ ε := by rw [Real.rpow_pow_comm (by positivity)]
  have hlarge (p k : ℕ) (hp : B ≤ p) :
      (k : ℝ) + 1 ≤ ((p : ℝ) ^ k) ^ ε := by
    have hpR : (2 : ℝ) ^ ε⁻¹ ≤ p := hB.le.trans (by exact_mod_cast hp)
    have ht : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
      calc
        (2 : ℝ) = ((2 : ℝ) ^ ε⁻¹) ^ ε :=
          (Real.rpow_inv_rpow (by norm_num) hε.ne').symm
        _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hpR hε.le
    calc
      (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := nat_add_one_le_two_pow k
      _ ≤ ((p : ℝ) ^ ε) ^ k := pow_le_pow_left₀ (by norm_num) ht k
      _ = ((p : ℝ) ^ k) ^ ε := Real.rpow_pow_comm (by positivity) ε k
  refine ⟨A ^ B, pow_pos hApos _, ?_⟩
  intro n hn
  have hprod : (∏ p ∈ n.primeFactors, if p < B then A else 1) ≤ A ^ B := by
    have hcard : (n.primeFactors.filter (fun p => p < B)).card ≤ B := by
      calc
        _ ≤ (Finset.range B).card := Finset.card_le_card (by
          intro p hp
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        _ = B := Finset.card_range B
    simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
    exact pow_le_pow_right₀ hA hcard
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn, Nat.cast_prod]
      simp only [Nat.cast_add, Nat.cast_one]
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < B then A else 1) * ((p : ℝ) ^ n.factorization p) ^ ε := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro p hp
      split_ifs with hpB
      · exact hsmall p (n.factorization p) (Nat.prime_of_mem_primeFactors hp).two_le
      · simpa only [one_mul] using hlarge p (n.factorization p) (by omega)
    _ = (∏ p ∈ n.primeFactors, if p < B then A else 1) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
      congr 1
      congr 1
      exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
    _ ≤ A ^ B * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hprod (by positivity)

/-- Uniform constants and quadratic prime-exponent factors still have subpower growth. -/
theorem exists_prod_factorization_le_rpow {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 →
      (∏ p ∈ n.primeFactors, c * ((n.factorization p : ℝ) + 1) ^ 2) ≤
        C * (n : ℝ) ^ ε := by
  obtain ⟨m, hm⟩ := exists_nat_gt c
  have hc2 : c ≤ (2 : ℝ) ^ m := by
    linarith [nat_add_one_le_two_pow m]
  have hmpos : 0 < ((m + 2 : ℕ) : ℝ) := by positivity
  obtain ⟨D, hD, hdiv⟩ := exists_card_divisors_le_rpow (div_pos hε hmpos)
  refine ⟨D ^ (m + 2), pow_pos hD _, ?_⟩
  intro n hn
  have hprod : (∏ p ∈ n.primeFactors, c * ((n.factorization p : ℝ) + 1) ^ 2) ≤
      (n.divisors.card : ℝ) ^ (m + 2) := by
    calc
      _ ≤ ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ^ (m + 2) := by
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro p hp
        have hfp : 0 < n.factorization p :=
          (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn
            (Nat.dvd_of_mem_primeFactors hp)
        have hfpR : (2 : ℝ) ≤ (n.factorization p : ℝ) + 1 := by
          exact_mod_cast (show 2 ≤ n.factorization p + 1 by omega)
        have hcp : c ≤ ((n.factorization p : ℝ) + 1) ^ m :=
          hc2.trans (pow_le_pow_left₀ (by norm_num) hfpR m)
        rw [pow_add]
        exact mul_le_mul_of_nonneg_right hcp (sq_nonneg _)
      _ = (n.divisors.card : ℝ) ^ (m + 2) := by
        rw [Finset.prod_pow, Nat.card_divisors hn, Nat.cast_prod]
        simp only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ (n.divisors.card : ℝ) ^ (m + 2) := hprod
    _ ≤ (D * (n : ℝ) ^ (ε / ((m + 2 : ℕ) : ℝ))) ^ (m + 2) :=
      pow_le_pow_left₀ (by positivity) (hdiv n hn) _
    _ = D ^ (m + 2) * (n : ℝ) ^ ε := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), div_mul_cancel₀ _ hmpos.ne']

lemma prod_primeFactors_factorization_of_dvd {n f : ℕ} (hn : n ≠ 0) (hf : f ∣ n) :
    (∏ p ∈ n.primeFactors, (p : ℝ) ^ f.factorization p) = f := by
  have hf0 : f ≠ 0 := by
    intro hf0
    apply hn
    simpa [hf0] using hf
  have hsub := Nat.primeFactors_mono hf hn
  have hprod : (∏ p ∈ f.primeFactors, (p : ℝ) ^ f.factorization p) =
      ∏ p ∈ n.primeFactors, (p : ℝ) ^ f.factorization p := by
    apply Finset.prod_subset hsub
    intro p _ hpf
    have hz : f.factorization p = 0 := by
      simpa only [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] using hpf
    simp only [hz, pow_zero]
  rw [← hprod]
  exact_mod_cast (Nat.prod_primeFactors_pow_factorization hf0).symm

/-- The factor coming from the common square divisor is exactly linear in `f`. -/
theorem exists_local_factor_product_le {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n f : ℕ, n ≠ 0 → f ∣ n →
      (∏ p ∈ n.primeFactors,
        (c * ((n.factorization p : ℝ) + 1) ^ 2) * (p : ℝ) ^ f.factorization p) ≤
        C * f * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hprod⟩ := exists_prod_factorization_le_rpow hc hε
  refine ⟨C, hC, ?_⟩
  intro n f hn hf
  rw [Finset.prod_mul_distrib, prod_primeFactors_factorization_of_dvd hn hf]
  calc
    _ ≤ (C * (n : ℝ) ^ ε) * f :=
      mul_le_mul_of_nonneg_right (hprod n hn) (by positivity)
    _ = C * f * (n : ℝ) ^ ε := by ring

end Erdos941.Analytic
