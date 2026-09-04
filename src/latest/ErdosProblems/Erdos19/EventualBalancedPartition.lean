import ErdosProblems.Erdos19.BalancedPartition
import ErdosProblems.Erdos76.PippengerSpencerParameters

/-! # Balanced partitions for polynomially many constraints -/

namespace Erdos19

theorem eventually_exists_balanced_partition (k C d : ℕ) (hk : 0 < k)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (I : Type*) [Fintype I],
      Fintype.card I ≤ C * n ^ d → ∀ S : I → Finset (Fin n),
      ∃ z : Fin n → Fin k, ∀ i a,
        |(((S i).filter fun v ↦ z v = a).card : ℝ) - (S i).card / k| < eta * n := by
  classical
  let c := eta ^ 2 / 2
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨N₀, hN₀⟩ :=
    Erdos76.PippengerSpencerParameters.exists_exp_tail_mul_polynomial_le_one
      c ((C : ℝ) * k) d hc
  refine ⟨max N₀ 1, ?_⟩
  intro n hn I _ hI S
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hIReal : (Fintype.card I : ℝ) ≤ C * (n : ℝ) ^ d := by exact_mod_cast hI
  have hexp : -(eta * (n : ℝ)) ^ 2 / (2 * n) = -c * n := by
    dsimp only [c]
    field_simp
  have hprob : 2 * Fintype.card I * Fintype.card (Fin k) *
      Real.exp (-(eta * (n : ℝ)) ^ 2 / (2 * n)) < 1 := by
    rw [Fintype.card_fin, hexp]
    calc
      (2 : ℝ) * Fintype.card I * k * Real.exp (-c * n) ≤
          2 * Real.exp (-c * n) * ((C : ℝ) * k * (n : ℝ) ^ d) := by
        have hm := mul_le_mul_of_nonneg_right hIReal
          (show 0 ≤ (2 : ℝ) * k * Real.exp (-c * n) by positivity)
        nlinarith only [hm]
      _ < 2 * Real.exp (-c * n) * ((C : ℝ) * k * (n : ℝ) ^ d + 1) := by
        apply mul_lt_mul_of_pos_left (lt_add_one _)
        positivity
      _ ≤ 1 := hN₀ n ((le_max_left _ _).trans hn)
  obtain ⟨z, hz⟩ := exists_balanced_partition n hnpos S (eta * n) (by positivity) hprob
  exact ⟨z, by simpa only [Fintype.card_fin] using hz⟩

#print axioms eventually_exists_balanced_partition

end Erdos19
