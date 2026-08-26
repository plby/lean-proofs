/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.BranchEvents
import ErdosProblems.Erdos730.DensityAssembly
import ErdosProblems.Erdos730.TransitionDensity
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Erdős 730: assembly of the four analytic ranges

This file contains only the finite four-range union bound and the topology
needed to add the four normalized estimates.  In particular, the hypotheses
of `limsup_badDensity_le_budget_of_range_estimates` are the concrete
higher-power, small-prime, and top-prime estimates, not a restatement of the
headline density claim.
-/

open Filter
open scoped Topology

namespace Erdos730
namespace RangeAssembly

open BranchEvents DensityAssembly DensityEvents FullDensityCore
  TransitionDensity

noncomputable section

local instance : DecidablePred GoodParameter :=
  fun _ ↦ Classical.propDecidable _

/-- Normalized count of local witnesses with exponent at least two. -/
def normalizedHigherPowerWitnessCount (X : ℕ) : ℝ :=
  ((localHigherPowerWitnessesUpTo X).card : ℝ) / (X : ℝ)

/-- Normalized count of first-power witnesses with `p ≤ sqrt X`. -/
def normalizedSmallPrimeWitnessCount (X : ℕ) : ℝ :=
  ((localSmallPrimeWitnessesUpTo X (Nat.sqrt X)).card : ℝ) / (X : ℝ)

/-- Normalized count of first-power witnesses above the transition cutoff. -/
def normalizedTopPrimeWitnessCount (X : ℕ) : ℝ :=
  ((localTopPrimeWitnessesUpTo X (transitionTopCut X)).card : ℝ) / (X : ℝ)

/-- The exact normalized sum of the four disjoint local ranges. -/
def normalizedFourRangeCount (X : ℕ) : ℝ :=
  normalizedHigherPowerWitnessCount X +
    (normalizedSmallPrimeWitnessCount X +
      (normalizedTransitionWitnessCount X +
        normalizedTopPrimeWitnessCount X))

theorem normalizedHigherPowerWitnessCount_nonneg (X : ℕ) :
    0 ≤ normalizedHigherPowerWitnessCount X := by
  unfold normalizedHigherPowerWitnessCount
  positivity

theorem normalizedSmallPrimeWitnessCount_nonneg (X : ℕ) :
    0 ≤ normalizedSmallPrimeWitnessCount X := by
  unfold normalizedSmallPrimeWitnessCount
  positivity

theorem normalizedTransitionWitnessCount_nonneg (X : ℕ) :
    0 ≤ normalizedTransitionWitnessCount X := by
  unfold normalizedTransitionWitnessCount
  positivity

theorem normalizedTopPrimeWitnessCount_nonneg (X : ℕ) :
    0 ≤ normalizedTopPrimeWitnessCount X := by
  unfold normalizedTopPrimeWitnessCount
  positivity

theorem normalizedFourRangeCount_nonneg (X : ℕ) :
    0 ≤ normalizedFourRangeCount X := by
  unfold normalizedFourRangeCount
  exact add_nonneg (normalizedHigherPowerWitnessCount_nonneg X)
    (add_nonneg (normalizedSmallPrimeWitnessCount_nonneg X)
      (add_nonneg (normalizedTransitionWitnessCount_nonneg X)
        (normalizedTopPrimeWitnessCount_nonneg X)))

/-- The exact finite ledger inequality once the two moving cutoffs are in
their natural order. -/
theorem badDensity_le_normalizedFourRangeCount
    (X : ℕ) (hcut : Nat.sqrt X ≤ transitionTopCut X) :
    badDensity X ≤ normalizedFourRangeCount X := by
  have hcard := bad_card_le_localBranchWitnesses_card X
  rw [localBranchWitnesses_card_fourRange X (Nat.sqrt X)
    (transitionTopCut X) hcut] at hcard
  unfold badDensity normalizedFourRangeCount
  unfold normalizedHigherPowerWitnessCount normalizedSmallPrimeWitnessCount
    normalizedTransitionWitnessCount normalizedTopPrimeWitnessCount
  have hcast :
      ((badParametersUpTo X).card : ℝ) ≤
        ((localHigherPowerWitnessesUpTo X).card : ℝ) +
          (((localSmallPrimeWitnessesUpTo X (Nat.sqrt X)).card : ℝ) +
            (((localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
              (transitionTopCut X)).card : ℝ) +
              ((localTopPrimeWitnessesUpTo X
                (transitionTopCut X)).card : ℝ))) := by
    exact_mod_cast hcard
  simpa only [add_div] using
    (div_le_div_of_nonneg_right hcast (Nat.cast_nonneg X))

theorem eventually_badDensity_le_normalizedFourRangeCount :
    badDensity ≤ᶠ[atTop] normalizedFourRangeCount := by
  filter_upwards [eventually_sqrt_le_transitionTopCut] with X hcut
  exact badDensity_le_normalizedFourRangeCount X hcut

/-- The vanishing higher-power and transition ranges plus the two bounded
limsup estimates imply the paper's complete bad-density budget. -/
theorem limsup_badDensity_le_budget_of_range_estimates
    (hhigher : Tendsto normalizedHigherPowerWitnessCount atTop (𝓝 0))
    (hsmallBdd :
      IsBoundedUnder (· ≤ ·) atTop normalizedSmallPrimeWitnessCount)
    (hsmall : limsup normalizedSmallPrimeWitnessCount atTop ≤
      4 * densityBudgetSeries)
    (htopBdd :
      IsBoundedUnder (· ≤ ·) atTop normalizedTopPrimeWitnessCount)
    (htop : limsup normalizedTopPrimeWitnessCount atTop ≤
      (2 / 3) * Real.log 2) :
    limsup badDensity atTop ≤
      4 * densityBudgetSeries + (2 / 3) * Real.log 2 := by
  let vanishing : ℕ → ℝ := fun X ↦
    normalizedHigherPowerWitnessCount X +
      normalizedTransitionWitnessCount X
  let principal : ℕ → ℝ := fun X ↦
    normalizedSmallPrimeWitnessCount X +
      normalizedTopPrimeWitnessCount X
  have hvanishing : Tendsto vanishing atTop (𝓝 0) := by
    simpa only [vanishing, zero_add] using
      hhigher.add tendsto_normalizedTransitionWitnessCount
  have hsmallCob :
      IsCoboundedUnder (· ≤ ·) atTop normalizedSmallPrimeWitnessCount :=
    isCoboundedUnder_le_of_le atTop normalizedSmallPrimeWitnessCount_nonneg
  have hsmallLower :
      IsBoundedUnder (· ≥ ·) atTop normalizedSmallPrimeWitnessCount := by
    exact isBoundedUnder_of
      ⟨0, normalizedSmallPrimeWitnessCount_nonneg⟩
  have htopCob :
      IsCoboundedUnder (· ≤ ·) atTop normalizedTopPrimeWitnessCount :=
    isCoboundedUnder_le_of_le atTop normalizedTopPrimeWitnessCount_nonneg
  have htopLower :
      IsBoundedUnder (· ≥ ·) atTop normalizedTopPrimeWitnessCount := by
    exact isBoundedUnder_of
      ⟨0, normalizedTopPrimeWitnessCount_nonneg⟩
  have hprincipalBdd : IsBoundedUnder (· ≤ ·) atTop principal := by
    simpa only [principal] using! isBoundedUnder_le_add hsmallBdd htopBdd
  have hprincipalCob : IsCoboundedUnder (· ≤ ·) atTop principal := by
    exact isCoboundedUnder_le_of_le atTop fun X ↦ by
      dsimp only [principal]
      exact add_nonneg (normalizedSmallPrimeWitnessCount_nonneg X)
        (normalizedTopPrimeWitnessCount_nonneg X)
  have hprincipal : limsup principal atTop ≤
      4 * densityBudgetSeries + (2 / 3) * Real.log 2 := by
    calc
      limsup principal atTop ≤
          limsup normalizedSmallPrimeWitnessCount atTop +
            limsup normalizedTopPrimeWitnessCount atTop := by
        simpa only [principal] using!
          (limsup_add_le (f := atTop)
            (u := normalizedSmallPrimeWitnessCount)
            (v := normalizedTopPrimeWitnessCount)
            (h₁ := hsmallLower) (h₂ := hsmallBdd)
            (h₃ := htopCob) (h₄ := htopBdd))
      _ ≤ 4 * densityBudgetSeries + (2 / 3) * Real.log 2 :=
        add_le_add hsmall htop
  have hrangeBdd :
      IsBoundedUnder (· ≤ ·) atTop normalizedFourRangeCount := by
    unfold normalizedFourRangeCount
    exact isBoundedUnder_le_add hhigher.isBoundedUnder_le
      (isBoundedUnder_le_add hsmallBdd
        (isBoundedUnder_le_add
          tendsto_normalizedTransitionWitnessCount.isBoundedUnder_le htopBdd))
  have hbadToRange := limsup_le_limsup
    eventually_badDensity_le_normalizedFourRangeCount
    badDensity_isCoboundedUnder_le hrangeBdd
  calc
    limsup badDensity atTop ≤ limsup normalizedFourRangeCount atTop :=
      hbadToRange
    _ = limsup (vanishing + principal) atTop := by
      apply limsup_congr
      exact Eventually.of_forall fun X ↦ by
        dsimp only [vanishing, principal]
        unfold normalizedFourRangeCount
        change normalizedHigherPowerWitnessCount X +
            (normalizedSmallPrimeWitnessCount X +
              (normalizedTransitionWitnessCount X +
                normalizedTopPrimeWitnessCount X)) =
          (normalizedHigherPowerWitnessCount X +
              normalizedTransitionWitnessCount X) +
            (normalizedSmallPrimeWitnessCount X +
              normalizedTopPrimeWitnessCount X)
        ring
    _ ≤ limsup vanishing atTop + limsup principal atTop := by
      exact limsup_add_le (f := atTop) (u := vanishing) (v := principal)
        (h₁ := hvanishing.isBoundedUnder_ge)
        (h₂ := hvanishing.isBoundedUnder_le)
        (h₃ := hprincipalCob) (h₄ := hprincipalBdd)
    _ ≤ 4 * densityBudgetSeries + (2 / 3) * Real.log 2 := by
      rw [hvanishing.limsup_eq, zero_add]
      exact hprincipal

/-- Once the three remaining concrete range estimates are supplied, the
existing exact numerical certificate yields positive lower density. -/
theorem hasCandidatePositiveDensity_of_range_estimates
    (hhigher : Tendsto normalizedHigherPowerWitnessCount atTop (𝓝 0))
    (hsmallBdd :
      IsBoundedUnder (· ≤ ·) atTop normalizedSmallPrimeWitnessCount)
    (hsmall : limsup normalizedSmallPrimeWitnessCount atTop ≤
      4 * densityBudgetSeries)
    (htopBdd :
      IsBoundedUnder (· ≤ ·) atTop normalizedTopPrimeWitnessCount)
    (htop : limsup normalizedTopPrimeWitnessCount atTop ≤
      (2 / 3) * Real.log 2) :
    FullDensity.HasCandidatePositiveDensity GoodParameter := by
  exact hasCandidatePositiveDensity_of_limsup_bad_le
    (limsup_badDensity_le_budget_of_range_estimates
      hhigher hsmallBdd hsmall htopBdd htop)

#print axioms badDensity_le_normalizedFourRangeCount
#print axioms limsup_badDensity_le_budget_of_range_estimates
#print axioms hasCandidatePositiveDensity_of_range_estimates

end

end RangeAssembly
end Erdos730
