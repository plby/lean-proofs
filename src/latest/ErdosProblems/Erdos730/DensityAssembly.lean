/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.DensityEvents
import ErdosProblems.Erdos730.FullDensityBudget
import ErdosProblems.Erdos730.PositiveDensityBridge
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Erdős 730: final limsup-to-positive-density assembly

This file is independent of the four analytic range estimates.  It proves
that the strict numerical budget for the normalized bad-event count implies
the exact `107/2500` lower-density claim used by the upstream infinitude
bridge.
-/

open Filter
open scoped Topology

namespace Erdos730
namespace DensityAssembly

open DensityEvents FullDensityCore

noncomputable section

local instance : DecidablePred GoodParameter :=
  fun _ ↦ Classical.propDecidable _

/-- Normalized finite bad-parameter count. -/
def badDensity (X : ℕ) : ℝ :=
  ((badParametersUpTo X).card : ℝ) / (X : ℝ)

/-- Normalized finite good-parameter count. -/
def goodDensity (X : ℕ) : ℝ :=
  ((goodParametersUpTo X).card : ℝ) / (X : ℝ)

theorem badParameters_card_le (X : ℕ) :
    (badParametersUpTo X).card ≤ X := by
  calc
    (badParametersUpTo X).card ≤ (parameterRange X).card :=
      Finset.card_le_card (by
        intro x hx
        exact (mem_badParametersUpTo.mp hx).1)
    _ = X := parameterRange_card X

theorem badDensity_nonneg (X : ℕ) : 0 ≤ badDensity X := by
  unfold badDensity
  positivity

theorem badDensity_le_one (X : ℕ) : badDensity X ≤ 1 := by
  by_cases hX : X = 0
  · subst X
    simp [badDensity]
  · rw [badDensity, div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hX)]
    exact_mod_cast badParameters_card_le X

theorem badDensity_isBoundedUnder_le :
    IsBoundedUnder (· ≤ ·) atTop badDensity := by
  exact isBoundedUnder_of ⟨1, badDensity_le_one⟩

theorem badDensity_isCoboundedUnder_le :
    IsCoboundedUnder (· ≤ ·) atTop badDensity := by
  exact isCoboundedUnder_le_of_le atTop badDensity_nonneg

/-- Exact finite complement identity away from the harmless endpoint `X=0`. -/
theorem goodDensity_eq_one_sub_badDensity {X : ℕ} (hX : 0 < X) :
    goodDensity X = 1 - badDensity X := by
  have hsum := good_card_add_bad_card X
  have hsumR : ((goodParametersUpTo X).card : ℝ) +
      ((badParametersUpTo X).card : ℝ) = (X : ℝ) := by
    exact_mod_cast hsum
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  unfold goodDensity badDensity
  field_simp [hXR]
  linarith [hsumR]

/-- The lower density of good parameters is exactly one minus the upper
density of bad parameters. -/
theorem liminf_goodDensity_eq_one_sub_limsup_badDensity :
    liminf goodDensity atTop = 1 - limsup badDensity atTop := by
  rw [liminf_congr ((eventually_gt_atTop (0 : ℕ)).mono fun X hX ↦
    goodDensity_eq_one_sub_badDensity hX),
    liminf_const_sub atTop badDensity 1 badDensity_isBoundedUnder_le
      badDensity_isCoboundedUnder_le]

theorem parameterCount_eq_good_card (X : ℕ) :
    FullDensity.parameterCount GoodParameter X = (goodParametersUpTo X).card := by
  rfl

/-- Any bad-density limsup within the paper's analytic budget proves the
exact candidate positive-density statement. -/
theorem hasCandidatePositiveDensity_of_limsup_bad_le
    (hbad : limsup badDensity atTop ≤
      4 * densityBudgetSeries + (2 / 3) * Real.log 2) :
    FullDensity.HasCandidatePositiveDensity GoodParameter := by
  unfold FullDensity.HasCandidatePositiveDensity
  simp_rw [parameterCount_eq_good_card]
  change (107 : ℝ) / 2500 < liminf goodDensity atTop
  rw [liminf_goodDensity_eq_one_sub_limsup_badDensity]
  have hbudget := densityBudget_final_lt
  linarith

#print axioms liminf_goodDensity_eq_one_sub_limsup_badDensity
#print axioms hasCandidatePositiveDensity_of_limsup_bad_le

end

end DensityAssembly
end Erdos730
