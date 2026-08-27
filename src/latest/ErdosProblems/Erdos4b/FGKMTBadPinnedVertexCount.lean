/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedBadProbability

/-! # A small exceptional set of surviving vertices for the pinned mass -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

open scoped Classical in
def SourceProbabilityData.badPinnedVertices {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (a : ResidueAssignment S) : Finset ℕ :=
  (sourceSievingPrimes c x).filter fun q => residueAssignmentAvoids S {(q : ℤ)} a ∧
    1 / Real.log (x : ℝ) ^ 3 <
      |D.pinnedNormalizedSurvival S q a / residueSieveDensity S ^ (D.dimension - 1) - 1|

open scoped Classical in
theorem SourceProbabilityData.expectation_badPinnedVertices {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) :
    residueExpectation S (fun a => ((D.badPinnedVertices S a).card : ℝ)) =
      ∑ q ∈ sourceSievingPrimes c x, ∑ a : ResidueAssignment S,
        if residueAssignmentAvoids S {(q : ℤ)} a ∧
            1 / Real.log (x : ℝ) ^ 3 <
              |D.pinnedNormalizedSurvival S q a / residueSieveDensity S ^ (D.dimension - 1) - 1|
          then residueAssignmentMass S a else 0 := by
  classical
  unfold residueExpectation badPinnedVertices
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  exact Finset.sum_comm

theorem eventually_source_badPinnedVertexCount_mean_le {c e : ℝ}
    (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      (∀ p ∈ S, p ≤ x) →
      residueExpectation S (fun a => ((D.badPinnedVertices S a).card : ℝ)) ≤
        2 * residueSieveDensity S * (sourceSievingPrimes c x).card / Real.log (x : ℝ) ^ 6 := by
  filter_upwards [eventually_source_surviving_pinned_bad_probability hc he] with x hbad
  intro D S hS hrough hupper
  rw [D.expectation_badPinnedVertices]
  calc
    _ ≤ ∑ _q ∈ sourceSievingPrimes c x, 2 * residueSieveDensity S / Real.log (x : ℝ) ^ 6 :=
      Finset.sum_le_sum fun q hq => hbad D S hS hrough hupper q hq
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

theorem eventually_source_badPinnedVertexCount_tail_le {c e : ℝ}
    (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      (∀ p ∈ S, p ≤ x) → ∀ v : ℝ, 0 < v →
      (∑ a : ResidueAssignment S,
        if v ≤ ((D.badPinnedVertices S a).card : ℝ) then residueAssignmentMass S a else 0) ≤
        2 * residueSieveDensity S * (sourceSievingPrimes c x).card /
          (Real.log (x : ℝ) ^ 6 * v) := by
  filter_upwards [eventually_source_badPinnedVertexCount_mean_le hc he] with x hmean
  intro D S hS hrough hupper v hv
  have ht := finite_nonnegative_tail_le (residueAssignmentMass S)
    (fun a => ((D.badPinnedVertices S a).card : ℝ)) (residueAssignmentMass_nonneg S)
    (fun a => Nat.cast_nonneg _) hv
  refine ht.trans ((div_le_div_of_nonneg_right (hmean D S hS hrough hupper) hv.le).trans_eq ?_)
  ring

end

end Erdos4b.FGKMT
