import ErdosProblems.Erdos964.ScalarMomentBounds

/-!
# The mass of divisors containing a distinguished prime

This controls the omitted `p|r` terms without making the bad modulus vary.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem sum_Ioc_multiples_reindex (Q p : ℕ) (hp : 0 < p) (F : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc 0 Q, if p ∣ n then F n else 0) =
      ∑ m ∈ Finset.Ioc 0 (Q / p), F (p * m) := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun n _ => n / p) (fun m _ => p * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hn, hpn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn0, hnQ⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn0 hpn) hp,
      Nat.div_le_div_right hnQ⟩
  · intro m hm
    obtain ⟨hm0, hmQ⟩ := Finset.mem_Ioc.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨Nat.mul_pos hp hm0, ?_⟩, dvd_mul_right p m⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hmQ
  · intro n hn
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2
  · intro m hm
    exact Nat.mul_div_cancel_left m hp
  · intro n hn
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]

theorem abelCumulative_mono_of_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    Monotone (abelCumulative a) := by
  intro x y hxy
  unfold abelCumulative
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans (Nat.floor_le_floor hxy)⟩
  · intro n hn hnot
    exact ha n

theorem scalarMoment_prime_divisor_sum_le (M k Q : ℕ) (h2M : 2 ∣ M) (h3M : 3 ∣ M)
    {p : ℕ} (hp : p.Prime) :
    (∑ n ∈ Finset.Ioc 0 Q, if p ∣ n then scalarMomentAF M k n else 0) ≤
      scalarMomentAF M k p * abelCumulative (scalarMomentAF M k) (Q / p : ℕ) := by
  rw [sum_Ioc_multiples_reindex Q p hp.pos]
  calc
    _ ≤ ∑ m ∈ Finset.Ioc 0 (Q / p), scalarMomentAF M k p * scalarMomentAF M k m :=
      Finset.sum_le_sum (fun m _ => scalarMomentAF_prime_mul_le M k m h2M h3M hp)
    _ = _ := by
      rw [abelCumulative_arithmeticFunction, Nat.floor_natCast, Finset.mul_sum]

theorem exists_scalarMoment_two_prime_divisor_mass_bound (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R Q p : ℕ, 1 ≤ R → Q ≤ R → p.Prime →
      (∑ n ∈ Finset.Ioc 0 Q, if p ∣ n then scalarMomentAF M 2 n else 0) ≤
        (8 / (p : ℝ)) * D * (1 + Real.log R) ^ 2 := by
  obtain ⟨D, hD, hbound⟩ := exists_scalarMoment_two_cumulative_growth M hM h2M h3M
  refine ⟨D, hD, ?_⟩
  intro R Q p hR hQR hp
  have hcum : abelCumulative (scalarMomentAF M 2) (Q / p : ℕ) ≤
      D * (1 + Real.log R) ^ 2 := by
    refine ((abelCumulative_mono_of_nonneg (scalarMomentAF M 2)
      (fun n => scalarMomentAF_nonneg M 2 n h2M h3M))
      (show ((Q / p : ℕ) : ℝ) ≤ R by exact_mod_cast (Nat.div_le_self Q p).trans hQR)).trans ?_
    exact hbound R (by exact_mod_cast hR)
  have hcum0 : 0 ≤ abelCumulative (scalarMomentAF M 2) (Q / p : ℕ) :=
    Finset.sum_nonneg (fun n _ => scalarMomentAF_nonneg M 2 n h2M h3M)
  calc
    _ ≤ scalarMomentAF M 2 p * abelCumulative (scalarMomentAF M 2) (Q / p : ℕ) :=
      scalarMoment_prime_divisor_sum_le M 2 Q h2M h3M hp
    _ ≤ (8 / (p : ℝ)) * (D * (1 + Real.log R) ^ 2) :=
      mul_le_mul (scalarMomentAF_two_prime_le M h2M h3M hp) hcum hcum0 (by positivity)
    _ = _ := by ring

end Erdos964
