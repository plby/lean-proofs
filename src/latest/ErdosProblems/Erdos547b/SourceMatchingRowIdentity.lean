/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingCapacityMargins
import ErdosProblems.Erdos547b.SourceSwitchRows

/-! # The arbitrary matching's indexed rows are its literal support rows -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingRowIdentity

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoRichClaim61Lemma611 Erdos547b.ZhaoMatchingSupportSeparation
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceMatchingGeometry
open Erdos547b.ZhaoSourceMatchingCapacityMargins Erdos547b.ZhaoSourceSwitchRows
open Erdos547b.ZhaoSourceParentCleanup

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable (P : (padGraph (reduced W)).Subgraph)

theorem sum_pairWeight_eq_matchingRow (hP : P.IsMatching) (s : Fin 2) :
    (∑ e ∈ allMatchingEdges P, pairWeight W Q S P (rootCluster W Q s) e) =
      matchingRow W Q S s P := by
  rw [matchingRow, ← sum_matchingEndpoints_eq_sum_support P hP (padFinset (large W))]
  apply Finset.sum_congr rfl
  intro e _
  unfold pairWeight vertexWeight pairVertex
  ring

theorem sum_selected_pairWeight (hP : P.IsMatching) (s : Fin 2) (E : Finset (MatchingEdge P)) :
    (∑ e ∈ E, pairWeight W Q S P (rootCluster W Q s) e) =
      matchingRow W Q S s (edgeFinsetSubgraph P (padFinset (large W)) E) := by
  rw [matchingRow, sum_selectedSupport P hP]
  apply Finset.sum_congr rfl
  intro e _
  unfold pairWeight vertexWeight pairVertex
  ring

omit Q S in
theorem pairVertex_mem_support (e : MatchingEdge P) (c : Fin 2) :
    pairVertex W P e c ∈ matchingSupport P := by
  fin_cases c
  · exact (mem_matchingSupport P _).mpr (orientedEndpoint_adj P (padFinset (large W)) e).fst_mem
  · exact (mem_matchingSupport P _).mpr (orientedEndpoint_adj P (padFinset (large W)) e).snd_mem

omit S in
theorem all_edges_away
    (haway : Disjoint (matchingSupport P) {Sum.inl Q.A, Sum.inl Q.B}) :
    allMatchingEdges P ⊆ edgesAwayFromDistinguished P (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B) := by
  intro e he
  refine Finset.mem_sdiff.mpr ⟨he, ?_⟩
  intro hbad
  rcases (Finset.mem_filter.mp hbad).2 with hzero | hone
  · exact Finset.disjoint_left.mp haway (pairVertex_mem_support W P e 0) hzero
  · exact Finset.disjoint_left.mp haway (pairVertex_mem_support W P e 1) hone

end Erdos547b.ZhaoSourceMatchingRowIdentity

#print axioms Erdos547b.ZhaoSourceMatchingRowIdentity.sum_pairWeight_eq_matchingRow
#print axioms Erdos547b.ZhaoSourceMatchingRowIdentity.sum_selected_pairWeight
#print axioms Erdos547b.ZhaoSourceMatchingRowIdentity.all_edges_away
