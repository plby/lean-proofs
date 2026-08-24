import ErdosProblems.Erdos587.RootDensity

/-!
# A polylogarithmic reciprocal Euler density

A divisor-moment estimate suffices here; no sharp Mertens theorem is needed.
The local reciprocal factor is at most `1 + 2/p`, and expansion over prime
subsets embeds into the harmonic divisor-count sum.
-/

open scoped BigOperators

namespace Erdos587

lemma inv_one_sub_inv_le_one_add_two_div {x : ℝ} (hx : 2 ≤ x) :
    (1 - x⁻¹)⁻¹ ≤ 1 + 2 / x := by
  have hx0 : 0 < x := by linarith
  have hinv : x⁻¹ < 1 := (inv_lt_one₀ hx0).mpr (by linarith)
  rw [← one_div (1 - x⁻¹)]
  apply (div_le_iff₀ (sub_pos.mpr hinv)).mpr
  have hmul : (1 + 2 / x) * (1 - x⁻¹) - 1 = (x - 2) / x ^ 2 := by
    field_simp
    ring
  have hnonneg : 0 ≤ (x - 2) / x ^ 2 := div_nonneg (by linarith) (sq_nonneg x)
  linarith

lemma primeSetUnitDensity_inv_le_prime_subset_sum
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (primeSetUnitDensity s)⁻¹ ≤
      ∑ t ∈ s.powerset, (2 : ℝ) ^ t.card / (primeSetModulus t : ℝ) := by
  calc
    (primeSetUnitDensity s)⁻¹ = ∏ p ∈ s, (1 - (p : ℝ)⁻¹)⁻¹ := by
      rw [primeSetUnitDensity, Finset.prod_inv_distrib]
    _ ≤ ∏ p ∈ s, (1 + 2 / (p : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hs p hp).two_le
        have hp0 : (0 : ℝ) < p := by linarith
        have hinv : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr (by linarith)
        exact inv_nonneg.mpr (by linarith)
      · intro p hp
        exact inv_one_sub_inv_le_one_add_two_div (by exact_mod_cast (hs p hp).two_le)
    _ = ∑ t ∈ s.powerset, (2 : ℝ) ^ t.card / (primeSetModulus t : ℝ) := by
      rw [Finset.prod_one_add]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.prod_div_distrib, Finset.prod_const]
      congr 1
      simp only [primeSetModulus, Nat.cast_prod]

lemma prime_subset_sum_le_harmonic_divisor_sum
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (∑ t ∈ s.powerset, (2 : ℝ) ^ t.card / (primeSetModulus t : ℝ)) ≤
      ∑ d ∈ Finset.Icc 1 (primeSetModulus s), (d.divisors.card : ℝ) / d := by
  classical
  have hinj : Set.InjOn primeSetModulus (s.powerset : Set (Finset ℕ)) := by
    intro t ht u hu heq
    have htprime : ∀ p ∈ t, p.Prime := fun p hp => hs p (Finset.mem_powerset.mp ht hp)
    have huprime : ∀ p ∈ u, p.Prime := fun p hp => hs p (Finset.mem_powerset.mp hu hp)
    calc
      t = (primeSetModulus t).primeFactors := (primeFactors_primeSetModulus t htprime).symm
      _ = (primeSetModulus u).primeFactors := congrArg Nat.primeFactors heq
      _ = u := primeFactors_primeSetModulus u huprime
  have hsubset : s.powerset.image primeSetModulus ⊆ Finset.Icc 1 (primeSetModulus s) := by
    intro d hd
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
    have hts := Finset.mem_powerset.mp ht
    have htpos : 0 < primeSetModulus t :=
      Finset.prod_pos (fun p hp => (hs p (hts hp)).pos)
    have hspos : 0 < primeSetModulus s := Finset.prod_pos (fun p hp => (hs p hp).pos)
    have hdvd : primeSetModulus t ∣ primeSetModulus s :=
      Finset.prod_dvd_prod_of_subset t s id hts
    exact Finset.mem_Icc.mpr ⟨htpos, Nat.le_of_dvd hspos hdvd⟩
  calc
    _ = ∑ t ∈ s.powerset, ((primeSetModulus t).divisors.card : ℝ) / primeSetModulus t := by
      apply Finset.sum_congr rfl
      intro t ht
      have hcard : ((primeSetModulus t).divisors.card : ℝ) = (2 : ℝ) ^ t.card := by
        exact_mod_cast card_divisors_prod_primes t
          (fun p hp => hs p (Finset.mem_powerset.mp ht hp))
      rw [hcard]
    _ = ∑ d ∈ s.powerset.image primeSetModulus, (d.divisors.card : ℝ) / d :=
      (Finset.sum_image (f := fun d : ℕ => (d.divisors.card : ℝ) / d) hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d hd hnot => by positivity)

theorem exists_primeSetUnitDensity_inv_polylog_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ (s : Finset ℕ),
      (∀ p ∈ s, p.Prime) → 3 ≤ primeSetModulus s →
        (primeSetUnitDensity s)⁻¹ ≤ C * Real.log (primeSetModulus s) ^ O := by
  obtain ⟨C, hC, O, hO, hbound⟩ := exists_weighted_divisorPower_log_bound 1
  refine ⟨C, hC, O, hO, ?_⟩
  intro s hs hQ
  have hh := hbound (primeSetModulus s) hQ
  simp only [pow_one] at hh
  exact (primeSetUnitDensity_inv_le_prime_subset_sum s hs).trans
    ((prime_subset_sum_le_harmonic_divisor_sum s hs).trans hh)

end Erdos587
