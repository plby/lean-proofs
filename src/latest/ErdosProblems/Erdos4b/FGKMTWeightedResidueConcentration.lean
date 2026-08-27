/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSurvivorConcentration

/-! # Weighted tuple concentration with the overlap mass retained -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

theorem residueAvoidanceMass_nonneg (S : Finset ℕ) (N : Finset ℤ) :
    0 ≤ residueAvoidanceMass S N := by
  classical
  exact Finset.sum_nonneg fun a _ha => by
    split_ifs <;> first | exact residueAssignmentMass_nonneg S a | rfl

theorem residueAvoidanceMass_le_one {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p)
    (N : Finset ℤ) : residueAvoidanceMass S N ≤ 1 := by
  classical
  rw [← residueAssignmentMass_sum hS]
  apply Finset.sum_le_sum
  intro a _ha
  split_ifs
  · exact le_rfl
  · exact residueAssignmentMass_nonneg S a

open scoped Classical in
def residueTupleOverlapMass {α : Type*} (J : Finset α) (b : α → ℝ)
    (N : α → Finset ℤ) : ℝ :=
  ∑ i ∈ J, ∑ j ∈ J, if Disjoint (N i) (N j) then 0 else b i * b j

theorem residueWeighted_expectation_error {α : Type*} (S : Finset ℕ) (J : Finset α)
    (b : α → ℝ) (N : α → Finset ℤ) (hb : ∀ j ∈ J, 0 ≤ b j)
    (hsum : ∑ j ∈ J, b j = 1) {s e : ℝ}
    (hpoint : ∀ j ∈ J, |residueAvoidanceMass S (N j) - s| ≤ e * s) :
    |residueExpectation S (fun a => ∑ j ∈ J, b j * residueAvoidanceIndicator S (N j) a) - s| ≤
      e * s := by
  rw [residueExpectation_weighted_indicator_sum]
  have hsub : (∑ j ∈ J, b j * residueAvoidanceMass S (N j)) - s =
      ∑ j ∈ J, b j * (residueAvoidanceMass S (N j) - s) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [hsub]
  calc
    _ ≤ ∑ j ∈ J, |b j * (residueAvoidanceMass S (N j) - s)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ J, b j * (e * s) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (hb j hj)]
      exact mul_le_mul_of_nonneg_left (hpoint j hj) (hb j hj)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

theorem residueWeighted_second_moment_le {α : Type*} {S : Finset ℕ}
    (hS : ∀ p ∈ S, 0 < p) (J : Finset α) (b : α → ℝ) (N : α → Finset ℤ)
    (hb : ∀ j ∈ J, 0 ≤ b j) (hsum : ∑ j ∈ J, b j = 1)
    {s e : ℝ} (he : 0 ≤ e)
    (hpair : ∀ i ∈ J, ∀ j ∈ J, Disjoint (N i) (N j) →
      residueAvoidanceMass S (N i ∪ N j) ≤ (1 + e) * s ^ 2) :
    residueExpectation S (fun a => (∑ j ∈ J, b j * residueAvoidanceIndicator S (N j) a) ^ 2) ≤
      (1 + e) * s ^ 2 + residueTupleOverlapMass J b N := by
  classical
  rw [residueExpectation_weighted_indicator_square]
  calc
    _ ≤ ∑ i ∈ J, ∑ j ∈ J,
        ((b i * b j) * ((1 + e) * s ^ 2) +
          if Disjoint (N i) (N j) then 0 else b i * b j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hbij := mul_nonneg (hb i hi) (hb j hj)
      by_cases hd : Disjoint (N i) (N j)
      · rw [if_pos hd, add_zero]
        exact mul_le_mul_of_nonneg_left (hpair i hi j hj hd) hbij
      · rw [if_neg hd]
        have htriv := mul_le_mul_of_nonneg_left
          (residueAvoidanceMass_le_one hS (N i ∪ N j)) hbij
        have hmain : 0 ≤ (b i * b j) * ((1 + e) * s ^ 2) :=
          mul_nonneg hbij (mul_nonneg (by linarith) (sq_nonneg _))
        linarith
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      congr 1
      simp only [← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_one, one_mul]

theorem residueWeighted_tail_le {α : Type*} {S : Finset ℕ}
    (hS : ∀ p ∈ S, 0 < p) (J : Finset α) (b : α → ℝ) (N : α → Finset ℤ)
    (hb : ∀ j ∈ J, 0 ≤ b j) (hsum : ∑ j ∈ J, b j = 1)
    {s e r : ℝ} (hs : 0 < s) (he : 0 ≤ e) (hr : 0 < r)
    (hpoint : ∀ j ∈ J, |residueAvoidanceMass S (N j) - s| ≤ e * s)
    (hpair : ∀ i ∈ J, ∀ j ∈ J, Disjoint (N i) (N j) →
      residueAvoidanceMass S (N i ∪ N j) ≤ (1 + e) * s ^ 2) :
    (∑ a : ResidueAssignment S,
      if r * s ≤ |(∑ j ∈ J, b j * residueAvoidanceIndicator S (N j) a) - s|
        then residueAssignmentMass S a else 0) ≤
      (3 * e * s ^ 2 + residueTupleOverlapMass J b N) / (r * s) ^ 2 := by
  exact finite_concentration_of_moments (residueAssignmentMass S) _
    (residueAssignmentMass_nonneg S) (residueAssignmentMass_sum hS) hs hr
    (residueWeighted_expectation_error S J b N hb hsum hpoint)
    (residueWeighted_second_moment_le hS J b N hb hsum he hpair)

theorem residue_correlation_absolute_error {S : Finset ℕ} {N : Finset ℤ} {e : ℝ}
    (hσ : 0 < residueSieveDensity S)
    (hcor : |residueAvoidanceMass S N / residueSieveDensity S ^ N.card - 1| ≤ e) :
    |residueAvoidanceMass S N - residueSieveDensity S ^ N.card| ≤
      e * residueSieveDensity S ^ N.card := by
  have hp := pow_pos hσ N.card
  have heq : residueAvoidanceMass S N / residueSieveDensity S ^ N.card - 1 =
      (residueAvoidanceMass S N - residueSieveDensity S ^ N.card) /
        residueSieveDensity S ^ N.card := by field_simp
  rw [heq, abs_div, abs_of_pos hp] at hcor
  exact (div_le_iff₀ hp).mp hcor

theorem eventually_uniform_weighted_residue_concentration {α : Type*}
    {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ x : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      ∀ (J : Finset α) (b : α → ℝ) (N : α → Finset ℤ) (k : ℕ),
      (∀ j ∈ J, 0 ≤ b j) → (∑ j ∈ J, b j = 1) →
      (∀ j ∈ J, (N j).card = k) → 2 * (k : ℝ) ≤ Real.log (x : ℝ) →
      (∀ j ∈ J, ∀ n ∈ N j, |(n : ℝ)| ≤ (x : ℝ) ^ A) →
      ∀ r : ℝ, 0 < r →
      (∑ a : ResidueAssignment S,
        if r * residueSieveDensity S ^ k ≤
            |(∑ j ∈ J, b j * residueAvoidanceIndicator S (N j) a) - residueSieveDensity S ^ k|
          then residueAssignmentMass S a else 0) ≤
        (3 * (48 * (A + 1) / Real.log (x : ℝ) ^ 16) * (residueSieveDensity S ^ k) ^ 2 +
          residueTupleOverlapMass J b N) / (r * residueSieveDensity S ^ k) ^ 2 := by
  classical
  filter_upwards [eventually_uniform_residue_correlation hA] with x hcor
  intro S hS hrough J b N k hb hsum hcard hk hheight r hr
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  apply residueWeighted_tail_le (fun p hp => (hS p hp).pos) J b N hb hsum
    (pow_pos hσ k) (by positivity) hr
  · intro j hj
    have hjk : ((N j).card : ℝ) ≤ Real.log (x : ℝ) := by
      rw [hcard j hj]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    simpa only [hcard j hj] using
      residue_correlation_absolute_error hσ (hcor S hS hrough (N j) hjk (hheight j hj))
  · intro i hi j hj hd
    have hijcard : (N i ∪ N j).card = k * 2 := by
      rw [Finset.card_union_of_disjoint hd, hcard i hi, hcard j hj]
      omega
    have hijsize : ((N i ∪ N j).card : ℝ) ≤ Real.log (x : ℝ) := by
      rw [hijcard, Nat.cast_mul, Nat.cast_ofNat]
      linarith
    have hijheight : ∀ n ∈ N i ∪ N j, |(n : ℝ)| ≤ (x : ℝ) ^ A := by
      intro n hn
      rcases Finset.mem_union.mp hn with hn | hn
      · exact hheight i hi n hn
      · exact hheight j hj n hn
    have hc := hcor S hS hrough (N i ∪ N j) hijsize hijheight
    rw [hijcard, pow_mul] at hc
    apply (div_le_iff₀ (sq_pos_of_pos (pow_pos hσ k))).mp
    linarith [(abs_le.mp hc).2]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.residueWeighted_second_moment_le
#print axioms Erdos4b.FGKMT.residueWeighted_tail_le
#print axioms Erdos4b.FGKMT.eventually_uniform_weighted_residue_concentration
