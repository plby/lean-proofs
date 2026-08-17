import ErdosProblems.Erdos444.Bounded
import ErdosProblems.Erdos444.HighGrowthScales
import ErdosProblems.Erdos444.Sparse

/-!
# Completion of the natural-cutoff proof of Erdős Problem 444

The unbounded reciprocal-mass case is split according to whether the mass is
eventually bounded by a fixed polynomial in the twice-iterated base-four
logarithm.  `Sparse` handles the low branch and `HighGrowth` handles its
negation.  The bounded-mass branch is the elementary finite-product argument.
-/

open Filter

namespace Erdos444

noncomputable section

/-- An unbounded reciprocal mass forces the required quotient to be unbounded
on every natural tail. -/
theorem tailUnbounded_ratioNat_of_reciprocalMass_tailUnbounded
    (A : Set ℕ) (k : ℕ)
    (hdiv : tailUnbounded (reciprocalMassNat A)) :
    tailUnbounded (ratioNat A k) := by
  let M : ℕ := 8 * ((2 * k + 2) + 2) + 1
  by_cases hlow : ∃ D : ℝ, 0 ≤ D ∧ ∃ U : ℕ, ∀ X : ℕ, U ≤ X →
      reciprocalMassNat A X ≤
        D * ((Nat.log 4 (Nat.log 4 X) : ℝ) + 1) ^ M
  · exact tailUnbounded_ratioNat_of_exists_shifted_iteratedLog_growth
      A k M hdiv hlow
  · exact tailUnbounded_ratioNat_of_not_shifted_iteratedLog_bound
      A k hdiv (by simpa [M] using hlow)

/-- The exact natural-cutoff quotient is tail-unbounded for every infinite
set, whether or not its reciprocal series converges. -/
theorem tailUnbounded_ratioNat_of_infinite
    (A : Set ℕ) (hA : A.Infinite) (k : ℕ) :
    tailUnbounded (ratioNat A k) := by
  by_cases hbounded : ∃ B : ℝ, ∀ x : ℕ, reciprocalMassNat A x ≤ B
  · obtain ⟨B, hB⟩ := hbounded
    exact tailUnbounded_ratioNat_of_reciprocalMass_bounded A hA k B hB
  · have hunbounded : ∀ C : ℝ, ∃ x : ℕ, C < reciprocalMassNat A x := by
      intro C
      by_contra hnone
      apply hbounded
      refine ⟨C, ?_⟩
      intro x
      exact le_of_not_gt fun hx ↦ hnone ⟨x, hx⟩
    exact tailUnbounded_ratioNat_of_reciprocalMass_tailUnbounded A k
      (tailUnbounded_reciprocalMassNat_of_unbounded A hunbounded)

/-- Transfer tail-unboundedness from integral to real cutoffs. -/
theorem tailUnbounded_ratio_of_infinite
    (A : Set ℕ) (hA : A.Infinite) (k : ℕ) :
    tailUnbounded (ratio A k) := by
  have hnat := tailUnbounded_ratioNat_of_infinite A hA k
  intro C X
  obtain ⟨N, hXN⟩ := exists_nat_ge X
  obtain ⟨n, hNn, hn⟩ := hnat C N
  refine ⟨(n : ℝ), hXN.trans ?_, ?_⟩
  · exact_mod_cast hNn
  · simpa using hn

end


end Erdos444
