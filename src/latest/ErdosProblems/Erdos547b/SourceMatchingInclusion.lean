/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.MatchingEdgeInclusion
import ErdosProblems.Erdos547b.SourceMatchingRowIdentity

/-! # Source weights are unchanged by physical-subgraph edge inclusions -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingInclusion

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceMatchingGeometry
open Erdos547b.ZhaoSourceMatchingCapacityMargins Erdos547b.ZhaoSourceMatchingRowIdentity
open Erdos547b.ZhaoSourceSwitchRows Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoMatchingEdgeInclusion

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {P R : (padGraph (reduced W)).Subgraph} (h : P ≤ R)

theorem pairWeight_edgeInclusion (C : Index W) (e : MatchingEdge P) :
    pairWeight W Q S R C (edgeInclusion h e) = pairWeight W Q S P C e := rfl

theorem sum_lifted_pairWeight (C : Index W) (E : Finset (MatchingEdge P)) :
    (∑ e ∈ liftedEdges h E, pairWeight W Q S R C e) =
      ∑ e ∈ E, pairWeight W Q S P C e := by
  rw [sum_liftedEdges]
  rfl

theorem sum_lifted_all_row (hP : P.IsMatching) (s : Fin 2) :
    (∑ e ∈ liftedEdges h (allMatchingEdges P), pairWeight W Q S R (rootCluster W Q s) e) =
      matchingRow W Q S s P := by
  rw [sum_lifted_pairWeight, sum_pairWeight_eq_matchingRow W Q S P hP]

end Erdos547b.ZhaoSourceMatchingInclusion

#print axioms Erdos547b.ZhaoSourceMatchingInclusion.pairWeight_edgeInclusion
#print axioms Erdos547b.ZhaoSourceMatchingInclusion.sum_lifted_all_row
