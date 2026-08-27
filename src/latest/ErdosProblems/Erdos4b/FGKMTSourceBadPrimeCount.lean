/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceTupleBadProbability

/-! # The number of bad source prime labels is small with high probability -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

theorem finite_nonnegative_tail_le {Ω : Type*} [Fintype Ω] (μ X : Ω → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hX : ∀ a, 0 ≤ X a) {r : ℝ} (hr : 0 < r) :
    (∑ a, if r ≤ X a then μ a else 0) ≤ (∑ a, μ a * X a) / r := by
  classical
  apply (le_div_iff₀ hr).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _ha
  by_cases ht : r ≤ X a
  · rw [if_pos ht]
    exact mul_le_mul_of_nonneg_left ht (hμ a)
  · rw [if_neg ht, zero_mul]
    exact mul_nonneg (hμ a) (hX a)

open scoped Classical in
def SourceProbabilityData.badTuplePrimes {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (a : ResidueAssignment S) : Finset ℕ :=
  (commonPinnedPrimeSet (x / 2) x).filter fun p =>
    1 / Real.log (x : ℝ) ^ 3 <
      |D.tupleSurvivalMass S p a / residueSieveDensity S ^ D.dimension - 1|

theorem SourceProbabilityData.expectation_badTuplePrimes {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) :
    residueExpectation S (fun a => ((D.badTuplePrimes S a).card : ℝ)) =
      ∑ p ∈ commonPinnedPrimeSet (x / 2) x, ∑ a : ResidueAssignment S,
        if 1 / Real.log (x : ℝ) ^ 3 <
            |D.tupleSurvivalMass S p a / residueSieveDensity S ^ D.dimension - 1|
          then residueAssignmentMass S a else 0 := by
  classical
  unfold residueExpectation badTuplePrimes
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  exact Finset.sum_comm

theorem eventually_source_badPrimeCount_mean_le {c e : ℝ} (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      (∀ p ∈ S, p ≤ x) →
      residueExpectation S (fun a => ((D.badTuplePrimes S a).card : ℝ)) ≤
        4 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_source_tuple_bad_probability hc he,
    eventually_commonPinnedPrimeSet_card_bounds,
    hlog.eventually (eventually_ge_atTop (1 : ℝ))] with x hbad hP hL
  intro D S hS hrough hupper
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  rw [D.expectation_badTuplePrimes]
  calc
    _ ≤ ∑ _p ∈ commonPinnedPrimeSet (x / 2) x, 2 / Real.log (x : ℝ) ^ 6 :=
      Finset.sum_le_sum fun p hp => hbad D S hS hrough hupper p hp
    _ = ((commonPinnedPrimeSet (x / 2) x).card : ℝ) * (2 / Real.log (x : ℝ) ^ 6) := by simp
    _ ≤ (2 * x / Real.log (x : ℝ)) * (2 / Real.log (x : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_right hP.2 (by positivity)
    _ = _ := by field_simp [hLpos.ne']; ring

theorem eventually_source_badPrimeCount_tail_le {c e : ℝ} (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      (∀ p ∈ S, p ≤ x) →
      (∑ a : ResidueAssignment S,
        if 4 * (x : ℝ) / Real.log (x : ℝ) ^ 4 ≤ ((D.badTuplePrimes S a).card : ℝ)
          then residueAssignmentMass S a else 0) ≤ 1 / Real.log (x : ℝ) ^ 3 := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_source_badPrimeCount_mean_le hc he,
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with x hmean hL hx
  intro D S hS hrough hupper
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hr : 0 < 4 * (x : ℝ) / Real.log (x : ℝ) ^ 4 := by positivity
  have ht := finite_nonnegative_tail_le (residueAssignmentMass S)
    (fun a => ((D.badTuplePrimes S a).card : ℝ)) (residueAssignmentMass_nonneg S)
    (fun a => Nat.cast_nonneg _) hr
  refine ht.trans ((div_le_div_of_nonneg_right (hmean D S hS hrough hupper) hr.le).trans_eq ?_)
  field_simp [hLpos.ne', hxR.ne']

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_source_badPrimeCount_mean_le
#print axioms Erdos4b.FGKMT.eventually_source_badPrimeCount_tail_le
