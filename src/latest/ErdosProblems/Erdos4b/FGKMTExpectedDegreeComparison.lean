/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeEdgeMarginal

/-! # Comparing actual expected edge degree with the normalized pinned mass -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem weighted_denominator_relative_error {A M X r : ℝ}
    (hA : 0 ≤ A) (hM : 0 < M) (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (herror : |X / M - 1| ≤ r) : |A / X - A / M| ≤ 2 * r * (A / M) := by
  have hlow : M / 2 ≤ X := by
    have hh : (1 / 2 : ℝ) ≤ X / M := by linarith [(abs_le.mp herror).1]
    have h := (le_div_iff₀ hM).mp hh
    linarith
  have hX : 0 < X := (half_pos hM).trans_le hlow
  have hratio : X / M - 1 = (X - M) / M := by field_simp
  rw [hratio, abs_div, abs_of_pos hM] at herror
  have hnum := (div_le_iff₀ hM).mp herror
  have heq : A / X - A / M = A * (M - X) / (X * M) := by
    field_simp [hX.ne', hM.ne']
  rw [heq, abs_div, abs_mul, abs_of_nonneg hA, abs_sub_comm,
    abs_of_pos (mul_pos hX hM)]
  calc
    _ ≤ A * (r * M) / (X * M) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hA) (mul_pos hX hM).le
    _ ≤ A * (r * M) / ((M / 2) * M) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hlow hM.le)
    _ = _ := by field_simp [hM.ne']

def SourceProbabilityData.primeTupleExpectedDegree {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S Q : Finset ℕ) (a : ResidueAssignment S) (q : ℕ) : ℝ :=
  ∑ p ∈ commonPinnedPrimeSet (x / 2) x, D.primeTupleEdgeProbability S Q a p q

theorem SourceProbabilityData.primeTupleExpectedDegree_error_good {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x)
    (hshift : 2 * (D.dimension : ℝ) ^ 2 * x ≤ sourceIntervalLength c x)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) (a : ResidueAssignment S) (hL : 2 ≤ Real.log (x : ℝ))
    {q : ℕ} (hq : q ∈ Q) (hqy : (q : ℝ) ≤ sourceIntervalLength c x)
    (hsurv : residueAssignmentAvoids S {(q : ℤ)} a) :
    |D.primeTupleExpectedDegree S Q a q - D.pinnedGoodMass S q a| ≤
      2 * (1 / Real.log (x : ℝ) ^ 3) * D.pinnedGoodMass S q a := by
  classical
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  have hM := pow_pos hσ D.dimension
  have hrhalf : 1 / Real.log (x : ℝ) ^ 3 ≤ (1 / 2 : ℝ) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL 3
    apply (div_le_iff₀ (pow_pos hLpos 3)).mpr
    norm_num at h
    linarith
  let A : ℕ → ℝ := fun p => ∑ i : Fin D.dimension,
    D.survivingTupleWeight S a p ((q : ℤ) - (D.shifts i : ℤ) * p)
  let F : ℕ → ℝ := fun p => if p ∈ D.badTuplePrimes S a then 0 else
    A p / residueSieveDensity S ^ D.dimension
  have hgoodsum : D.pinnedGoodMass S q a = ∑ p ∈ commonPinnedPrimeSet (x / 2) x, F p :=
    D.pinnedGoodMass_eq_prime_sum S q a
  calc
    _ = |∑ p ∈ commonPinnedPrimeSet (x / 2) x,
        (D.primeTupleEdgeProbability S Q a p q - F p)| := by
      rw [Finset.sum_sub_distrib, ← hgoodsum]
      rfl
    _ ≤ ∑ p ∈ commonPinnedPrimeSet (x / 2) x,
        |D.primeTupleEdgeProbability S Q a p q - F p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ commonPinnedPrimeSet (x / 2) x, 2 * (1 / Real.log (x : ℝ) ^ 3) * F p := by
      apply Finset.sum_le_sum
      intro p hp
      rw [D.primeTupleEdgeProbability_eq_good_pinned hshift S Q hQ a hp hq hqy hsurv]
      change |(if p ∈ D.badTuplePrimes S a then 0 else A p / D.tupleSurvivalMass S p a) -
          (if p ∈ D.badTuplePrimes S a then 0 else A p / residueSieveDensity S ^ D.dimension)| ≤ _
      by_cases hbad : p ∈ D.badTuplePrimes S a
      · simp only [F, if_pos hbad, sub_zero, abs_zero, mul_zero, le_refl]
      · simp only [F, if_neg hbad]
        have herror : |D.tupleSurvivalMass S p a / residueSieveDensity S ^ D.dimension - 1| ≤
            1 / Real.log (x : ℝ) ^ 3 := by
          apply le_of_not_gt
          intro h
          exact hbad (Finset.mem_filter.mpr ⟨hp, h⟩)
        exact weighted_denominator_relative_error
          (Finset.sum_nonneg fun i _hi => D.survivingTupleWeight_nonneg S a hp _)
          hM (by positivity) hrhalf herror
    _ = _ := by rw [← Finset.mul_sum, ← hgoodsum]

theorem SourceProbabilityData.primeTupleExpectedDegree_error_total {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x)
    (hshift : 2 * (D.dimension : ℝ) ^ 2 * x ≤ sourceIntervalLength c x)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) (a : ResidueAssignment S) (hL : 2 ≤ Real.log (x : ℝ))
    {q : ℕ} (hq : q ∈ Q) (hqy : (q : ℝ) ≤ sourceIntervalLength c x)
    (hsurv : residueAssignmentAvoids S {(q : ℤ)} a) :
    |D.primeTupleExpectedDegree S Q a q -
        D.pinnedSurvivalMass S q a / residueSieveDensity S ^ D.dimension| ≤
      D.pinnedBadMass S q a + 2 * (1 / Real.log (x : ℝ) ^ 3) *
        (D.pinnedSurvivalMass S q a / residueSieveDensity S ^ D.dimension) := by
  have hpart := D.pinnedGoodMass_add_bad S q a
  have hbad := D.pinnedBadMass_nonneg hS q a
  have hgoodle : D.pinnedGoodMass S q a ≤
      D.pinnedSurvivalMass S q a / residueSieveDensity S ^ D.dimension := by linarith
  have hfactor : 0 ≤ 2 * (1 / Real.log (x : ℝ) ^ 3) := by positivity
  calc
    _ = |(D.primeTupleExpectedDegree S Q a q - D.pinnedGoodMass S q a) -
        D.pinnedBadMass S q a| := by congr 1; linarith
    _ ≤ |D.primeTupleExpectedDegree S Q a q - D.pinnedGoodMass S q a| +
        |D.pinnedBadMass S q a| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (D.primeTupleExpectedDegree S Q a q - D.pinnedGoodMass S q a) 0
          (D.pinnedBadMass S q a))
    _ ≤ 2 * (1 / Real.log (x : ℝ) ^ 3) * D.pinnedGoodMass S q a + D.pinnedBadMass S q a :=
      add_le_add (D.primeTupleExpectedDegree_error_good hshift hS Q hQ a hL hq hqy hsurv)
        (le_of_eq (abs_of_nonneg hbad))
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hgoodle hfactor
      linarith

end

end Erdos4b.FGKMT
