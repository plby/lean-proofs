/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.EnergyFromAverage

/-!
# The bounded shifted-prime-mass cofactor layer

Condition (B5) is imposed by a finite filter.  The lemmas here are purely
finite: a reciprocal first-moment estimate removes only a controlled
fraction of reciprocal cofactor mass.
-/

namespace Erdos822

open scoped BigOperators

/-- Odd raw cofactors whose shifted coefficient has bounded reciprocal
prime mass in the sieve interval. -/
noncomputable def massGoodOddCofactors
    (N z y : ℕ) (C : ℝ) : Finset ℕ :=
  (oddRawCofactors N).filter fun m =>
    shiftedTotientReciprocalMass m z y ≤ C

@[simp]
theorem mem_massGoodOddCofactors_iff
    {N z y m : ℕ} {C : ℝ} :
    m ∈ massGoodOddCofactors N z y C ↔
      m ∈ oddRawCofactors N ∧
        shiftedTotientReciprocalMass m z y ≤ C := by
  simp [massGoodOddCofactors]

/-- The complementary bad cofactors have reciprocal mass at most their
weighted first moment divided by the cutoff. -/
theorem sum_inv_bad_massGoodOddCofactors_le_firstMoment_div
    (N z y : ℕ) {C : ℝ} (hC : 0 < C) :
    (∑ m ∈ (oddRawCofactors N).filter fun m =>
        C < shiftedTotientReciprocalMass m z y,
        (1 : ℝ) / m) ≤
      (∑ m ∈ oddRawCofactors N,
        shiftedTotientReciprocalMass m z y / m) / C := by
  have hterm : ∀ m ∈ (oddRawCofactors N).filter fun m =>
      C < shiftedTotientReciprocalMass m z y,
      (1 : ℝ) / m ≤
        (shiftedTotientReciprocalMass m z y / m) / C := by
    intro m hm
    have hmData := Finset.mem_filter.mp hm
    have hmpos : (0 : ℝ) < m := by
      exact_mod_cast oddRawCofactors_pos hmData.1
    have hmass := hmData.2.le
    apply (le_div_iff₀ hC).2
    apply (le_div_iff₀ hmpos).2
    calc
      (1 : ℝ) / m * C * m = C := by
        field_simp
      _ ≤ shiftedTotientReciprocalMass m z y := hmass
  calc
    (∑ m ∈ (oddRawCofactors N).filter fun m =>
        C < shiftedTotientReciprocalMass m z y,
        (1 : ℝ) / m) ≤
        ∑ m ∈ (oddRawCofactors N).filter fun m =>
          C < shiftedTotientReciprocalMass m z y,
          (shiftedTotientReciprocalMass m z y / m) / C :=
      Finset.sum_le_sum hterm
    _ ≤ ∑ m ∈ oddRawCofactors N,
          (shiftedTotientReciprocalMass m z y / m) / C := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro m hm hnot
      unfold shiftedTotientReciprocalMass
      positivity
    _ = (∑ m ∈ oddRawCofactors N,
          shiftedTotientReciprocalMass m z y / m) / C := by
      rw [Finset.sum_div]

/-- Subtracting the bad reciprocal mass gives a retained-mass lower bound
for the B5-filtered layer. -/
theorem sum_inv_massGoodOddCofactors_ge_of_firstMoment
    (N z y : ℕ) {C R D : ℝ} (hC : 0 < C)
    (hraw : R ≤ ∑ m ∈ oddRawCofactors N, (1 : ℝ) / m)
    (hmoment : ∑ m ∈ oddRawCofactors N,
        shiftedTotientReciprocalMass m z y / m ≤ D) :
    R - D / C ≤
      ∑ m ∈ massGoodOddCofactors N z y C, (1 : ℝ) / m := by
  let good := massGoodOddCofactors N z y C
  let bad := (oddRawCofactors N).filter fun m =>
    C < shiftedTotientReciprocalMass m z y
  have hpartition : oddRawCofactors N = good ∪ bad := by
    ext m
    simp only [good, bad, massGoodOddCofactors, Finset.mem_union,
      Finset.mem_filter]
    constructor
    · intro hm
      by_cases hmass : shiftedTotientReciprocalMass m z y ≤ C
      · exact Or.inl ⟨hm, hmass⟩
      · exact Or.inr ⟨hm, lt_of_not_ge hmass⟩
    · rintro (⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
  have hdisj : Disjoint good bad := by
    rw [Finset.disjoint_left]
    intro m hmg hmb
    have hg := (Finset.mem_filter.mp hmg).2
    have hb := (Finset.mem_filter.mp hmb).2
    linarith
  have hbad :
      ∑ m ∈ bad, (1 : ℝ) / m ≤ D / C := by
    calc
      ∑ m ∈ bad, (1 : ℝ) / m ≤
          (∑ m ∈ oddRawCofactors N,
            shiftedTotientReciprocalMass m z y / m) / C := by
        dsimp [bad]
        exact sum_inv_bad_massGoodOddCofactors_le_firstMoment_div
          N z y hC
      _ ≤ D / C := div_le_div_of_nonneg_right hmoment hC.le
  have htotal :
      ∑ m ∈ oddRawCofactors N, (1 : ℝ) / m =
        ∑ m ∈ good, (1 : ℝ) / m +
          ∑ m ∈ bad, (1 : ℝ) / m := by
    rw [hpartition, Finset.sum_union hdisj]
  dsimp [good] at htotal ⊢
  linarith

end Erdos822
