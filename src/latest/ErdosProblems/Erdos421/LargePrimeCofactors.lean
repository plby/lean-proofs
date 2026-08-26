import ErdosProblems.Erdos421.SievePrimeProducts

/-! # Bounded multiplicity of large prime factors in cofactor weights -/

namespace Erdos421

theorem large_prime_divisor_card_lt (S : Finset ℕ) {w n k : ℕ} (hw : 0 < w) (hn : 0 < n)
    (hnk : n < w ^ k) (hS : ∀ p ∈ S, p.Prime ∧ w ≤ p ∧ p ∣ n) : S.card < k := by
  have hsub : S ⊆ n.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨(hS p hp).1, (hS p hp).2.2, hn.ne'⟩
  have hdiv : (∏ p ∈ S, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset _ _ (fun p ↦ p) hsub).trans n.prod_primeFactors_dvd
  have hprod : w ^ S.card ≤ n := by
    calc
      _ = ∏ _p ∈ S, w := (Finset.prod_const w).symm
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' (fun p hp ↦ (hS p hp).2.1)
      _ ≤ n := Nat.le_of_dvd hn hdiv
  by_contra hk
  have hpow := Nat.pow_le_pow_right hw (by omega : k ≤ S.card)
  omega

noncomputable def primeCofactorWeight (P : Finset ℕ) (z n : ℕ) : ℝ :=
  ∑ p ∈ P, if p ∣ n then roughIndicator (n / p) z else 0

theorem primeCofactorWeight_nonneg (P : Finset ℕ) (z n : ℕ) :
    0 ≤ primeCofactorWeight P z n := by
  apply Finset.sum_nonneg
  intro p hp
  split_ifs
  · exact roughIndicator_nonneg _ _
  · exact le_rfl

theorem roughIndicator_le_one (n z : ℕ) : roughIndicator n z ≤ 1 := by
  unfold roughIndicator
  split_ifs <;> norm_num

theorem primeCofactorWeight_le (P : Finset ℕ) {w n k : ℕ} (hw : 0 < w) (hn : 0 < n)
    (hnk : n < w ^ k) (hP : ∀ p ∈ P, p.Prime ∧ w ≤ p) (z : ℕ) :
    primeCofactorWeight P z n ≤ (k : ℝ) := by
  have hcard := large_prime_divisor_card_lt (P.filter (fun p ↦ p ∣ n)) hw hn hnk (by
    intro p hp
    obtain ⟨hpP, hpn⟩ := Finset.mem_filter.mp hp
    exact ⟨(hP p hpP).1, (hP p hpP).2, hpn⟩)
  calc
    _ = ∑ p ∈ P.filter (fun p ↦ p ∣ n), roughIndicator (n / p) z := by
      rw [Finset.sum_filter]
      rfl
    _ ≤ ∑ _p ∈ P.filter (fun p ↦ p ∣ n), (1 : ℝ) :=
      Finset.sum_le_sum (fun p _ ↦ roughIndicator_le_one _ _)
    _ = ((P.filter (fun p ↦ p ∣ n)).card : ℝ) := by simp
    _ ≤ k := by exact_mod_cast hcard.le

end Erdos421
