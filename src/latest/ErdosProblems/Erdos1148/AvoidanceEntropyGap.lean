import ErdosProblems.Erdos1148.PartitionAvoidanceEntropy

/-! # An open hole forces a uniform gap below entropy one -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

theorem exists_entropy_rate_gap_of_linear_bound {u : ℕ → ℝ} {n : ℕ} (hn : 0 < n)
    {d D : ℝ} (hd : 0 < d)
    (hbound : ∀ k : ℕ, 0 < k → u (k * n) ≤ D + (1 - 3 * d / 8) * ((k : ℝ) * n)) :
    ∃ L : ℕ, 0 < L ∧ u L / L ≤ 1 - d / 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < d / 8 * (n : ℝ) := by positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (D / (d / 8 * (n : ℝ)))
  have hD : D < (k : ℝ) * (d / 8 * (n : ℝ)) := (div_lt_iff₀ ha).mp hk
  have hL : 0 < (k + 1) * n := Nat.mul_pos (Nat.succ_pos k) hn
  have hLR : (0 : ℝ) < ((k + 1) * n : ℕ) := by exact_mod_cast hL
  refine ⟨(k + 1) * n, hL, (div_le_iff₀ hLR).mpr ?_⟩
  have h := hbound (k + 1) (Nat.succ_pos k)
  push_cast at h ⊢
  nlinarith only [h, hD, ha]

theorem exists_uniform_continuity_partition_entropy_gap
    (μ : Measure ModularOrbitSpace) [IsProbabilityMeasure μ]
    (hf : MeasurePreserving modularTimeOne μ μ)
    {U : Set ModularOrbitSpace} (hU : IsOpen U) (hne : U.Nonempty) (hnull : μ U = 0) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∀ (ι : Type*) [Fintype ι] [Nonempty ι]
        (P : FiniteMeasurablePartition ModularOrbitSpace ι),
        (∀ i, μ (frontier (P.atom i)) = 0) →
        ∃ L : ℕ, 0 < L ∧ P.orbitEntropy μ modularTimeOne L / L ≤ 1 - γ := by
  obtain ⟨n, hn, d, hd, hd1, hcover⟩ := exists_positive_mass_avoidance_rate μ hf hU hne hnull
  refine ⟨d / 4, by positivity, by linarith only [hd1], ?_⟩
  intro ι _ _ P hboundary
  obtain ⟨D, hD⟩ := orbitEntropy_linear_gap_of_avoidance_rate μ hf hn hd hd1 hcover P hboundary
  exact exists_entropy_rate_gap_of_linear_bound hn hd hD

end Erdos1148.DukeArithmetic
