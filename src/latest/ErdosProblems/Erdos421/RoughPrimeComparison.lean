import ErdosProblems.Erdos421.RoughRealIntervals

/-! # The prime-counting base case for rough-number intervals -/

namespace Erdos421

theorem primes_real_interval_subset_rough {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {z : ℕ} (hza : (z : ℝ) ≤ a) :
    primesInRealInterval a b ⊆ roughInRealInterval a b z := by
  intro p hp
  obtain ⟨hpp, hpa, hpb⟩ := (mem_primesInRealInterval ha hab p).mp hp
  apply (mem_roughInRealInterval ha hab p z).mpr
  refine ⟨hpa, hpb, roughAt_iff_minFac.mpr (Or.inr ?_)⟩
  rw [hpp.minFac_eq]
  exact_mod_cast hza.trans hpa.le

theorem rough_real_interval_subset_prime_square {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    {z : ℕ} (hbz : b ≤ (z : ℝ) ^ 2) :
    roughInRealInterval a b z ⊆ primesInRealInterval a b ∪ {z ^ 2} := by
  intro n hn
  obtain ⟨hna, hnb, hnr⟩ := (mem_roughInRealInterval (by linarith) hab n z).mp hn
  by_cases hnp : n.Prime
  · apply Finset.mem_union_left
    exact (mem_primesInRealInterval (by linarith) hab n).mpr ⟨hnp, hna, hnb⟩
  · have hn1 : 1 < n := by exact_mod_cast ha.trans_lt hna
    have hmin : z ≤ n.minFac := (roughAt_iff_minFac.mp hnr).resolve_left (by omega)
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
    have hnz : n ≤ z ^ 2 := by exact_mod_cast hnb.trans hbz
    have heq : n = z ^ 2 := by nlinarith
    exact Finset.mem_union_right _ (Finset.mem_singleton.mpr heq)

theorem rough_real_interval_prime_card_bounds {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    {z : ℕ} (hza : (z : ℝ) ≤ a) (hbz : b ≤ (z : ℝ) ^ 2) :
    (primesInRealInterval a b).card ≤ (roughInRealInterval a b z).card ∧
      (roughInRealInterval a b z).card ≤ (primesInRealInterval a b).card + 1 := by
  constructor
  · exact Finset.card_le_card (primes_real_interval_subset_rough (by linarith) hab hza)
  · calc
      _ ≤ (primesInRealInterval a b ∪ {z ^ 2}).card :=
        Finset.card_le_card (rough_real_interval_subset_prime_square ha hab hbz)
      _ ≤ (primesInRealInterval a b).card + ({z ^ 2} : Finset ℕ).card := Finset.card_union_le _ _
      _ = _ := by simp

theorem rough_real_interval_prime_error {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    {z : ℕ} (hza : (z : ℝ) ≤ a) (hbz : b ≤ (z : ℝ) ^ 2) :
    |((roughInRealInterval a b z).card : ℝ) - (primesInRealInterval a b).card| ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := rough_real_interval_prime_card_bounds ha hab hza hbz
  have hlor : ((primesInRealInterval a b).card : ℝ) ≤ (roughInRealInterval a b z).card :=
    by exact_mod_cast hlo
  have hhir : ((roughInRealInterval a b z).card : ℝ) ≤ (primesInRealInterval a b).card + 1 :=
    by exact_mod_cast hhi
  rw [abs_of_nonneg (sub_nonneg.mpr hlor)]
  linarith

end Erdos421
