/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SlowCutoffSquarefreeMass
import ErdosProblems.Erdos822.B5SquarefreeMass

/-!
# The positive-mass B4--B5 family at the common slow cutoff
-/

namespace Erdos822

open scoped BigOperators

/-- Squarefree slow-B4 cofactors whose shifted-prime reciprocal mass is
bounded by the fixed B5 Markov threshold. -/
noncomputable def slowSquarefreeB5GoodCofactors
    (N y : ℕ) (C₀ : ℝ) : Finset ℕ := by
  classical
  exact (squarefreeLargeGcdFreeOddCofactors N y).filter fun m =>
    shiftedTotientReciprocalMass m 2 y ≤ C₀

@[simp]
theorem mem_slowSquarefreeB5GoodCofactors_iff
    {N y m : ℕ} {C₀ : ℝ} :
    m ∈ slowSquarefreeB5GoodCofactors N y C₀ ↔
      m ∈ squarefreeLargeGcdFreeOddCofactors N y ∧
        shiftedTotientReciprocalMass m 2 y ≤ C₀ := by
  simp [slowSquarefreeB5GoodCofactors]

theorem slowSquarefreeB5GoodCofactors_subset_squarefree
    (N y : ℕ) (C₀ : ℝ) :
    slowSquarefreeB5GoodCofactors N y C₀ ⊆
      squarefreeLargeGcdFreeOddCofactors N y := by
  intro m hm
  exact (mem_slowSquarefreeB5GoodCofactors_iff.mp hm).1

theorem slowSquarefreeB5GoodCofactors_subset_oddRaw
    (N y : ℕ) (C₀ : ℝ) :
    slowSquarefreeB5GoodCofactors N y C₀ ⊆ oddRawCofactors N :=
  (slowSquarefreeB5GoodCofactors_subset_squarefree N y C₀).trans
    (squarefreeLargeGcdFreeOddCofactors_subset_oddRaw N y)

theorem slowSquarefreeB5GoodCofactors_subset_massGood
    (N y : ℕ) (C₀ : ℝ) :
    slowSquarefreeB5GoodCofactors N y C₀ ⊆
      massGoodOddCofactors N 2 y C₀ := by
  intro m hm
  rw [mem_massGoodOddCofactors_iff]
  have hmData := mem_slowSquarefreeB5GoodCofactors_iff.mp hm
  exact ⟨squarefreeLargeGcdFreeOddCofactors_subset_oddRaw N y hmData.1,
    hmData.2⟩

/-- Fixed constants can be chosen so that the simultaneous slow-B4,
squarefree, and B5 family retains logarithmic reciprocal mass. -/
theorem exists_eventually_slowSquarefreeB5Good_log_mass :
    ∃ S : ℕ, ∃ C₀ : ℝ, 101 ≤ S ∧ 0 < C₀ ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let y := Nat.nthRoot (4 * S) N
        (1 / 16000 : ℝ) * Real.log (N : ℝ) ≤
          ∑ m ∈ slowSquarefreeB5GoodCofactors N y C₀,
            (1 : ℝ) / m := by
  obtain ⟨S, D, hS, hD, hmoment⟩ :=
    exists_eventually_shiftedMassFirstMoment_slowCutoff_le
  let C₀ : ℝ := 32000 * (D + 1)
  have hSpos : 0 < S := by omega
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    nlinarith
  refine ⟨S, C₀, hS, hC₀, ?_⟩
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_slowSquarefreeLargeGcdFree_log_mass hSpos,
      hmoment, hlog] with N hraw hmomentN hlogN
  change (1 : ℝ) ≤ Real.log (N : ℝ) at hlogN
  dsimp only at hmomentN ⊢
  let y := Nat.nthRoot (4 * S) N
  have hmoment' :
      ∑ m ∈ oddRawCofactors N,
          shiftedTotientReciprocalMass m 2 y / m ≤
        D * (1 + Real.log (N : ℝ)) := by
    simpa [shiftedMassFirstMoment, y] using hmomentN.2
  have hraw' :
      (1 / 8000 : ℝ) * Real.log (N : ℝ) ≤
        ∑ m ∈ squarefreeLargeGcdFreeOddCofactors N y,
          (1 : ℝ) / m := by
    simpa [y] using hraw
  have hgood := sum_inv_filter_massGood_ge_of_firstMoment
    (N := N) (y := y) (B := squarefreeLargeGcdFreeOddCofactors N y)
    hC₀ (squarefreeLargeGcdFreeOddCofactors_subset_oddRaw N y)
    hraw' hmoment'
  have hDratio : D / (D + 1) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (by nlinarith : 0 < D + 1)).2
    nlinarith
  have hbad :
      (D * (1 + Real.log (N : ℝ))) / C₀ ≤
        (1 / 16000 : ℝ) * Real.log (N : ℝ) := by
    calc
      (D * (1 + Real.log (N : ℝ))) / C₀ =
          (D / (D + 1)) *
            ((1 + Real.log (N : ℝ)) / 32000) := by
        dsimp [C₀]
        field_simp
      _ ≤ (1 : ℝ) *
          ((1 + Real.log (N : ℝ)) / 32000) := by
        exact mul_le_mul_of_nonneg_right hDratio (by
          have : 0 ≤ Real.log (N : ℝ) := by linarith
          positivity)
      _ ≤ (1 / 16000 : ℝ) * Real.log (N : ℝ) := by
        nlinarith
  calc
    (1 / 16000 : ℝ) * Real.log (N : ℝ) ≤
        (1 / 8000 : ℝ) * Real.log (N : ℝ) -
          (D * (1 + Real.log (N : ℝ))) / C₀ := by
      linarith
    _ ≤ ∑ m ∈ slowSquarefreeB5GoodCofactors N y C₀,
          (1 : ℝ) / m := by
      simpa [slowSquarefreeB5GoodCofactors, y] using hgood

end Erdos822
