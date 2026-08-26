/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceLeafCoreMass

/-!
# The source leaf saving pays the two matching margins and rounding
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceLeafCoreNumerics

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceLeafCoreMass Erdos547b.ZhaoSourceLeafBranchRestriction
open Erdos547b.ZhaoClaim68ConcreteLeaves Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

theorem leaf_surplus_margin (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    2 * (3 * (gamma α : ℝ) * q) + 2 * (2 * (W.clusterSize : ℝ)) ≤
      (fourthRoot α : ℝ) ^ 2 * q := by
  subst hostN
  have hN := (degreeForm_source_bounds hα hα1 W horder).2.2
  have hd : (degreeError α : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 / 100 := by
    exact_mod_cast (reservoir_cleanup_bounds hα hα1).2.2.2.1
  have hg : (gamma α : ℝ) ≤ (degreeError α : ℝ) / 1000000 := by
    exact_mod_cast (parameter_upper_bounds hα hα1).2.2.2.2.2.1
  have hdq := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hgq := mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hnonneg : 0 ≤ (fourthRoot α : ℝ) ^ 2 * q := by positivity
  nlinarith only [hN, hdq, hgq, hnonneg]

variable (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ} (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)

include hT in
theorem core_row_surplus (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (hcard : Fintype.card U = q + 1)
    (hleaves : 11 * (fourthRoot α : ℝ) ^ 2 * q ≤ (originalLevelOneLeaves P).card) (s : Fin 2) :
    (OrderedBranchForest.edgeDemand (OrderedBranchForest.restrict (branchForest P) (keptBranches P)) : ℝ) +
      2 * (3 * (gamma α : ℝ) * q) + 2 * (2 * (W.clusterSize : ℝ)) ≤
        ∑ e ∈ awayEdges W Q, sideWeight W Q S s e := by
  have hmass := retained_mass_le P hT hcard
  have hmargin := leaf_surplus_margin W hα hα1 hhost horder
  have hrow := awayWeight_lower W Q S hα hα1 hhost horder s
  nlinarith only [hmass, hmargin, hrow, hleaves]

end Erdos547b.ZhaoSourceLeafCoreNumerics

#print axioms Erdos547b.ZhaoSourceLeafCoreNumerics.leaf_surplus_margin
#print axioms Erdos547b.ZhaoSourceLeafCoreNumerics.core_row_surplus
