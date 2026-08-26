/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.LargeCutoffSquarefreeMass
import ErdosProblems.Erdos822.B5FirstMoment

/-!
# Intersecting B5 with the corrected B4 layer

The corrected squarefree B4 layer has logarithmic reciprocal mass.  The B5
first moment is logarithmic as well, so taking a sufficiently large fixed
Markov cutoff removes only half of that mass.
-/

namespace Erdos822

open scoped BigOperators

/-- Corrected B4 cofactors which also have bounded shifted-prime mass at
the sieve cutoff y. -/
noncomputable def squarefreeB5GoodCofactors
    (N y : ℕ) (C₀ : ℝ) : Finset ℕ := by
  classical
  exact (squarefreeLargeGcdFreeOddCofactors N (N ^ 4)).filter fun m =>
    shiftedTotientReciprocalMass m 2 y ≤ C₀

@[simp]
theorem mem_squarefreeB5GoodCofactors_iff
    {N y m : ℕ} {C₀ : ℝ} :
    m ∈ squarefreeB5GoodCofactors N y C₀ ↔
      m ∈ squarefreeLargeGcdFreeOddCofactors N (N ^ 4) ∧
        shiftedTotientReciprocalMass m 2 y ≤ C₀ := by
  simp [squarefreeB5GoodCofactors]

theorem squarefreeB5GoodCofactors_subset_squarefree
    (N y : ℕ) (C₀ : ℝ) :
    squarefreeB5GoodCofactors N y C₀ ⊆
      squarefreeLargeGcdFreeOddCofactors N (N ^ 4) := by
  intro m hm
  exact (mem_squarefreeB5GoodCofactors_iff.mp hm).1

theorem squarefreeB5GoodCofactors_subset_massGood
    (N y : ℕ) (C₀ : ℝ) :
    squarefreeB5GoodCofactors N y C₀ ⊆
      massGoodOddCofactors N 2 y C₀ := by
  intro m hm
  rw [mem_massGoodOddCofactors_iff]
  have hmData := mem_squarefreeB5GoodCofactors_iff.mp hm
  exact ⟨squarefreeLargeGcdFreeOddCofactors_subset_oddRaw N (N ^ 4)
      hmData.1, hmData.2⟩

/-- Markov subtraction inside an arbitrary subfamily of the odd raw
cofactors. -/
theorem sum_inv_filter_massGood_ge_of_firstMoment
    {N y : ℕ} {B : Finset ℕ} {C R D : ℝ}
    (hC : 0 < C)
    (hB : B ⊆ oddRawCofactors N)
    (hraw : R ≤ ∑ m ∈ B, (1 : ℝ) / m)
    (hmoment : ∑ m ∈ oddRawCofactors N,
        shiftedTotientReciprocalMass m 2 y / m ≤ D) :
    R - D / C ≤
      ∑ m ∈ B.filter
        (fun m => shiftedTotientReciprocalMass m 2 y ≤ C),
        (1 : ℝ) / m := by
  classical
  let good := B.filter fun m =>
    shiftedTotientReciprocalMass m 2 y ≤ C
  let bad := B.filter fun m =>
    C < shiftedTotientReciprocalMass m 2 y
  have hpartition : B = good ∪ bad := by
    ext m
    simp only [good, bad, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hm
      by_cases hmass : shiftedTotientReciprocalMass m 2 y ≤ C
      · exact Or.inl ⟨hm, hmass⟩
      · exact Or.inr ⟨hm, lt_of_not_ge hmass⟩
    · rintro (⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
  have hdisj : Disjoint good bad := by
    rw [Finset.disjoint_left]
    intro m hmg hmb
    have hg := (Finset.mem_filter.mp hmg).2
    have hb := (Finset.mem_filter.mp hmb).2
    linarith
  have hbadSubset :
      bad ⊆ (oddRawCofactors N).filter fun m =>
        C < shiftedTotientReciprocalMass m 2 y := by
    intro m hm
    have hmData := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨hB hmData.1, hmData.2⟩
  have hbad :
      ∑ m ∈ bad, (1 : ℝ) / m ≤ D / C := by
    calc
      ∑ m ∈ bad, (1 : ℝ) / m ≤
          ∑ m ∈ (oddRawCofactors N).filter fun m =>
            C < shiftedTotientReciprocalMass m 2 y,
            (1 : ℝ) / m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hbadSubset
        intro m hm hnot
        positivity
      _ ≤ (∑ m ∈ oddRawCofactors N,
          shiftedTotientReciprocalMass m 2 y / m) / C :=
        sum_inv_bad_massGoodOddCofactors_le_firstMoment_div
          N 2 y hC
      _ ≤ D / C := div_le_div_of_nonneg_right hmoment hC.le
  have htotal :
      ∑ m ∈ B, (1 : ℝ) / m =
        ∑ m ∈ good, (1 : ℝ) / m +
          ∑ m ∈ bad, (1 : ℝ) / m := by
    rw [hpartition, Finset.sum_union hdisj]
  dsimp [good] at htotal ⊢
  linarith

/-- There are fixed B5 constants for which the corrected squarefree B4
family retains logarithmic reciprocal mass. -/
theorem exists_eventually_squarefreeB5Good_log_mass :
    ∃ S : ℕ, ∃ C₀ : ℝ, 101 ≤ S ∧ 0 < C₀ ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let y := Nat.nthRoot (4 * S) N
        (1 / 16000 : ℝ) * Real.log (N : ℝ) ≤
          ∑ m ∈ squarefreeB5GoodCofactors N y C₀,
            (1 : ℝ) / m := by
  obtain ⟨S, D, hS, hD, hmoment⟩ :=
    exists_eventually_shiftedMassFirstMoment_slowCutoff_le
  let C₀ : ℝ := 32000 * (D + 1)
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    nlinarith
  refine ⟨S, C₀, hS, hC₀, ?_⟩
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_squarefreeLargeGcdFree_pow_four_log_mass,
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
        ∑ m ∈ squarefreeLargeGcdFreeOddCofactors N (N ^ 4),
          (1 : ℝ) / m := hraw
  have hgood := sum_inv_filter_massGood_ge_of_firstMoment
    (N := N) (y := y) (B := squarefreeLargeGcdFreeOddCofactors N (N ^ 4))
    hC₀ (squarefreeLargeGcdFreeOddCofactors_subset_oddRaw N (N ^ 4))
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
    _ ≤ ∑ m ∈ squarefreeB5GoodCofactors N y C₀,
          (1 : ℝ) / m := by
      simpa [squarefreeB5GoodCofactors, y] using hgood

end Erdos822
