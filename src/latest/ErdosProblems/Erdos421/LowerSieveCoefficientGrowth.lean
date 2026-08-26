import ErdosProblems.Erdos421.LowerSieveCoefficients

/-! # Subpower bounds for the lower-sieve coefficients -/

namespace Erdos421

theorem lowerSieveCoefficient_abs_le {D : ℕ} (hD : 1 ≤ D) (z : ℕ) {k : ℕ} (hk : 0 < k) :
    |lowerSieveCoefficient D z k| ≤ 2 * (32 : ℝ) ^ k.primeFactors.card := by
  classical
  let T := (lowerSievePairs D z).filter (fun v ↦ v.1 * v.2 = k)
  have hprime (v : ℕ × ℕ) (hv : v ∈ T) : v.1.Prime :=
    (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hv).1).1).2
  have hdiv (v : ℕ × ℕ) (hv : v ∈ T) : v.1 ∣ k ∧ v.2 ∣ k := by
    rw [← (Finset.mem_filter.mp hv).2]
    exact ⟨dvd_mul_right _ _, dvd_mul_left _ _⟩
  have hinj : Set.InjOn Prod.fst (↑T : Set (ℕ × ℕ)) := by
    intro v hv w hw heq
    apply Prod.ext heq
    apply Nat.eq_of_mul_eq_mul_left (hprime v hv).pos
    have hveq := (Finset.mem_filter.mp hv).2
    have hweq := (Finset.mem_filter.mp hw).2
    change v.1 = w.1 at heq
    calc
      _ = k := hveq
      _ = w.1 * w.2 := hweq.symm
      _ = _ := by rw [heq]
  have hcard : T.card ≤ k.primeFactors.card := by
    calc
      _ = (T.image Prod.fst).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ _ := Finset.card_le_card (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        exact Nat.mem_primeFactors.mpr ⟨hprime v hv, (hdiv v hv).1, hk.ne'⟩)
  have hw (v : ℕ × ℕ) (hv : v ∈ T) :
      |canonicalUpperSieve D v.1 v.2| ≤ (16 : ℝ) ^ k.primeFactors.card := by
    apply (uniform_selberg_lambda_abs_le (primeProductBelow v.1)
      (primeProductBelow_squarefree v.1) hD v.2).trans
    apply pow_le_pow_right₀ (by norm_num)
    exact Finset.card_le_card (Nat.primeFactors_mono (hdiv v hv).2 hk.ne')
  have hsum : |∑ v ∈ T, canonicalUpperSieve D v.1 v.2| ≤
      (k.primeFactors.card : ℝ) * (16 : ℝ) ^ k.primeFactors.card := by
    calc
      _ ≤ ∑ v ∈ T, |canonicalUpperSieve D v.1 v.2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ T, (16 : ℝ) ^ k.primeFactors.card := Finset.sum_le_sum hw
      _ = T.card * (16 : ℝ) ^ k.primeFactors.card := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have hcount : (k.primeFactors.card : ℝ) ≤ (2 : ℝ) ^ k.primeFactors.card := by
    exact_mod_cast k.primeFactors.card.lt_two_pow_self.le
  have hpow : (2 : ℝ) ^ k.primeFactors.card * (16 : ℝ) ^ k.primeFactors.card =
      (32 : ℝ) ^ k.primeFactors.card := by rw [← mul_pow]; norm_num
  have hone : (1 : ℝ) ≤ 32 ^ k.primeFactors.card := one_le_pow₀ (by norm_num)
  unfold lowerSieveCoefficient
  calc
    _ ≤ |if k = 1 then (1 : ℝ) else 0| + |∑ v ∈ T, canonicalUpperSieve D v.1 v.2| := by
      simpa using abs_sub_le (if k = 1 then (1 : ℝ) else 0) 0
        (∑ v ∈ T, canonicalUpperSieve D v.1 v.2)
    _ ≤ 1 + (k.primeFactors.card : ℝ) * (16 : ℝ) ^ k.primeFactors.card := by
      apply add_le_add _ hsum
      split_ifs <;> norm_num
    _ ≤ 1 + (2 : ℝ) ^ k.primeFactors.card * (16 : ℝ) ^ k.primeFactors.card :=
      add_le_add_right (mul_le_mul_of_nonneg_right hcount (by positivity)) _
    _ ≤ _ := by rw [hpow]; linarith

theorem lowerSieveCoefficient_subpower {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D → ∀ z k : ℕ, 0 < k →
      |lowerSieveCoefficient D z k| ≤ C * (k : ℝ) ^ η := by
  obtain ⟨C, hC, hb⟩ := primeFactorCard_power_bound (by norm_num : (1 : ℝ) ≤ 32) hη
  refine ⟨2 * C, by positivity, ?_⟩
  intro D hD z k hk
  apply (lowerSieveCoefficient_abs_le hD z hk).trans
  have h := mul_le_mul_of_nonneg_left (hb k hk) (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_assoc] using h

end Erdos421
