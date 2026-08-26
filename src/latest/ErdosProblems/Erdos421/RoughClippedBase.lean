import ErdosProblems.Erdos421.RoughPrimeComparison

/-! # The prime-counting base case when the roughness cutoff crosses the left endpoint

The cofactor intervals in Buchstab's identity can have this configuration near
the square-root boundary. Both possible endpoint integers are retained explicitly.
-/

namespace Erdos421

theorem rough_real_interval_subset_clipped_primes {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    {z : ℕ} (hz : (z : ℝ) ≤ b) (hbz : b ≤ (z : ℝ) ^ 2) :
    roughInRealInterval a b z ⊆ primesInRealInterval (max a z) b ∪ {z, z ^ 2} := by
  intro n hn
  obtain ⟨hna, hnb, hnr⟩ := (mem_roughInRealInterval (by linarith) hab n z).mp hn
  have hn1 : 1 < n := by exact_mod_cast ha.trans_lt hna
  have hzn : z ≤ n := by
    have hmin := (roughAt_iff_minFac.mp hnr).resolve_left (by omega : n ≠ 1)
    exact hmin.trans (Nat.minFac_le (by omega : 0 < n))
  by_cases hnp : n.Prime
  · by_cases hnz : n = z
    · exact Finset.mem_union_right _ (by simp [hnz])
    · have hzn' : (z : ℝ) < n := by exact_mod_cast (show z < n by omega)
      apply Finset.mem_union_left
      exact (mem_primesInRealInterval (by positivity) (max_le hab hz) n).mpr
        ⟨hnp, max_lt hna hzn', hnb⟩
  · have hsub := rough_real_interval_subset_prime_square ha hab hbz hn
    rcases Finset.mem_union.mp hsub with hp | hs
    · exact (hnp (Finset.mem_filter.mp hp).2).elim
    · have heq := Finset.mem_singleton.mp hs
      exact Finset.mem_union_right _ (by simp [heq])

theorem clipped_primes_subset_rough_real_interval {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {z : ℕ} (hz : (z : ℝ) ≤ b) :
    primesInRealInterval (max a z) b ⊆ roughInRealInterval a b z := by
  intro p hp
  obtain ⟨hpp, hplo, hphi⟩ :=
    (mem_primesInRealInterval (by positivity) (max_le hab hz) p).mp hp
  apply (mem_roughInRealInterval ha hab p z).mpr
  refine ⟨(le_max_left _ _).trans_lt hplo, hphi, roughAt_iff_minFac.mpr (Or.inr ?_)⟩
  rw [hpp.minFac_eq]
  exact_mod_cast ((le_max_right a (z : ℝ)).trans_lt hplo).le

theorem rough_real_interval_clipped_prime_error {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    {z : ℕ} (hz : (z : ℝ) ≤ b) (hbz : b ≤ (z : ℝ) ^ 2) :
    |((roughInRealInterval a b z).card : ℝ) - (primesInRealInterval (max a z) b).card| ≤ 2 := by
  have hlo := Finset.card_le_card (clipped_primes_subset_rough_real_interval (by linarith) hab hz)
  have hhi : (roughInRealInterval a b z).card ≤ (primesInRealInterval (max a z) b).card + 2 := by
    calc
      _ ≤ (primesInRealInterval (max a z) b ∪ {z, z ^ 2}).card :=
        Finset.card_le_card (rough_real_interval_subset_clipped_primes ha hab hz hbz)
      _ ≤ (primesInRealInterval (max a z) b).card + ({z, z ^ 2} : Finset ℕ).card :=
        Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left Finset.card_le_two _
  have hlor : ((primesInRealInterval (max a z) b).card : ℝ) ≤
      (roughInRealInterval a b z).card := by exact_mod_cast hlo
  have hhir : ((roughInRealInterval a b z).card : ℝ) ≤
      (primesInRealInterval (max a z) b).card + 2 := by exact_mod_cast hhi
  rw [abs_of_nonneg (sub_nonneg.mpr hlor)]
  linarith

end Erdos421
