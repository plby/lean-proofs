import ErdosProblems.Erdos1148.PositiveMassAvoidanceCover
import ErdosProblems.Erdos1148.FiniteShrinkingBowenCover

/-! # A uniform strict exponential rate for positive-mass avoidance covers -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

theorem exists_positive_mass_avoidance_rate (μ : Measure ModularOrbitSpace)
    [IsProbabilityMeasure μ] (hf : MeasurePreserving modularTimeOne μ μ)
    {U : Set ModularOrbitSpace} (hU : IsOpen U) (hne : U.Nonempty) (hnull : μ U = 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → ∃ M : ℝ, 1 ≤ M ∧
        ∀ k : ℕ, 0 < k → ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
          (N : ℝ) ≤ M * Real.exp ((1 - d) * ((k : ℝ) * n)) ∧
          (3 / 4 : ℝ) ≤ μ.real (⋃ i, modularMk '' B i) ∧
          (∀ i, IsCompact (B i)) ∧ ∀ i, LiftForwardClose δ ((k : ℝ) * n) (B i) := by
  obtain ⟨η, hη, hηsmall, n, hn, M₀, hM₀, hcover⟩ :=
    exists_positive_mass_avoidance_cover μ hf hU hne hnull
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let d := Real.log 2 / n
  have hd : 0 < d := div_pos (Real.log_pos (by norm_num)) hnR
  have hd1 : d ≤ 1 := by
    apply (div_le_iff₀ hnR).mpr
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [hlog, hone]
  have hpow (k : ℕ) : (Real.exp n / 2) ^ k =
      Real.exp ((1 - d) * ((k : ℝ) * n)) := by
    have hbase : Real.exp n / 2 = Real.exp ((n : ℝ) - Real.log 2) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [hbase, ← Real.exp_nat_mul]
    congr 1
    dsimp only [d]
    field_simp
    <;> ring
  refine ⟨n, hn, d, hd, hd1, ?_⟩
  intro δ hδ
  let R := (32 * η / δ + 1) ^ 3
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  refine ⟨max 1 (M₀ * R), le_max_left _ _, ?_⟩
  intro k hk
  obtain ⟨N, B, hN, hmass, _, hB⟩ := hcover k hk
  obtain ⟨N', B', hN', hB', hcov, hclose⟩ := exists_shrunk_finite_lift_cover hη
    (hηsmall.trans (by norm_num)) hδ (by positivity : 0 ≤ (k : ℝ) * n) B hB
  refine ⟨N', B', ?_, ?_, hB', hclose⟩
  · calc
      (N' : ℝ) ≤ (N : ℝ) * R := hN'
      _ ≤ (M₀ * (Real.exp n / 2) ^ k) * R := mul_le_mul_of_nonneg_right hN hR
      _ = (M₀ * R) * Real.exp ((1 - d) * ((k : ℝ) * n)) := by rw [hpow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · apply hmass.trans (measureReal_mono ?_)
    intro x hx
    obtain ⟨i, g, hg, rfl⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov (Set.mem_iUnion.mpr ⟨i, hg⟩))
    exact Set.mem_iUnion.mpr ⟨j, g, hj, rfl⟩

end Erdos1148.DukeArithmetic
