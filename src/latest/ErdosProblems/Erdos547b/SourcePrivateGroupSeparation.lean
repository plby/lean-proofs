/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePrivateGroupSupports
import ErdosProblems.Erdos547b.SourceMarkedRootExclusions
import ErdosProblems.Erdos547b.SourceTerminalBranchEmbedding

/-!
# Group separation from root reservoirs and ordinary residual families

The ordinary edges are the literal Min minus Mzero, or the reserved Mb.
Their separation is a consequence of the matching allocation, not a new
host-disjointness premise for the global marked history.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePrivateGroupSeparation

open Finset SimpleGraph
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceMarkedAvailableSets
open Erdos547b.ZhaoSourceMarkedRootExclusions Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceCleanCrossingAccess Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceGlobalPrefixState Erdos547b.ZhaoSourceRootExclusions
open Erdos547b.ZhaoClaim616 Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSection6Dichotomy
open Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)

theorem reservoir_disjoint_group (hCV1 : C ⊆ O.D.V1) (s : Fin 2) (x : {c // c ∈ C}) :
    Disjoint (reservoir W Q s) (P.support W Q S O x) := by
  have hxV1 : Sum.inl (P.center x) ∈ O.D.V1 := by rw [← P.center_eq x]; exact hCV1 x.2
  have hn := ne_roots_of_mem_V1 W Q S O hxV1
  have hne : rootCluster W Q s ≠ P.center x := by
    intro h
    rcases rootCluster_cases W Q s with hs | hs
    · exact hn.1 (congrArg Sum.inl (h.symm.trans hs))
    · exact hn.2 (congrArg Sum.inl (h.symm.trans hs))
  have hc : Disjoint (reservoir W Q s) (whole W (P.center x)) :=
    (clusterVertices_disjoint (assignment W) hne).mono (reservoir_subset W Q s) (Finset.Subset.refl _)
  apply Finset.disjoint_union_right.mpr
  refine ⟨hc, ?_⟩
  apply Finset.disjoint_left.mpr
  intro v hvr hvp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hvp
  rw [P.pair_eq (x, i)] at hi
  have he := availableEdges_subset_away W Q S O (P.edge_available (x, i))
  rcases Finset.mem_union.mp hi with h0 | h1
  · exact Finset.disjoint_left.mp (reservoir_disjoint_edgeWhole W Q s _ he 0) hvr h0
  · exact Finset.disjoint_left.mp (reservoir_disjoint_edgeWhole W Q s _ he 1) hvr h1

theorem ordinary_endpoint_not_center (hCV1 : C ⊆ O.D.V1)
    (e : MatchingEdge Q.claim67.M)
    (he : e ∈ O.D.minEdges \ MatchingDecomposition.MzeroEdges O.D C ∨ e ∈ O.D.mbEdges)
    (x : {c // c ∈ C}) (d : Fin 2) :
    Sum.inl (P.center x) ≠ edgeVertex W Q e d := by
  intro h
  rcases he with hm | hb
  · have heMin := (Finset.mem_sdiff.mp hm).1
    have heNot := (Finset.mem_sdiff.mp hm).2
    have hc : edgeVertex W Q e d ∈ C := by rw [← h, ← P.center_eq x]; exact x.2
    apply heNot
    apply Finset.mem_filter.mpr
    refine ⟨heMin, ?_⟩
    rcases Erdos547b.RegularPair.OrderedRootedForest.fin_two_eq_zero_or_one d with hd | hd
    · exact Or.inl (hd ▸ hc)
    · exact Or.inr (hd ▸ hc)
  · have hn := (Finset.mem_sdiff.mp (O.D.mb_subset hb)).2
    have hxV1 : edgeVertex W Q e d ∈ O.D.V1 := by rw [← h, ← P.center_eq x]; exact hCV1 x.2
    exact hn ((O.D.endpoint_mem_V1_iff e d).mp hxV1)

theorem private_ne_ordinary (p : {c // c ∈ C} × Fin 4) (e : MatchingEdge Q.claim67.M)
    (he : e ∈ O.D.minEdges \ MatchingDecomposition.MzeroEdges O.D C ∨ e ∈ O.D.mbEdges) :
    P.edge p ≠ e := by
  intro h
  have ha := (Finset.mem_inter.mp (P.edge_available p)).1
  have hnMb := (Finset.mem_sdiff.mp ha).2
  have hnMin := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ha).1).2
  rcases he with hm | hb
  · exact hnMin (h ▸ (Finset.mem_sdiff.mp hm).1)
  · exact hnMb (h ▸ hb)

theorem group_disjoint_ordinary (hCV1 : C ⊆ O.D.V1)
    (e : MatchingEdge Q.claim67.M)
    (he : e ∈ O.D.minEdges \ MatchingDecomposition.MzeroEdges O.D C ∨ e ∈ O.D.mbEdges)
    (x : {c // c ∈ C}) :
    Disjoint (P.support W Q S O x) (pairWhole W Q e) := by
  have hcenter (d : Fin 2) : Disjoint (whole W (P.center x)) (edgeWhole W Q e d) := by
    have h := clusterVertices_disjoint (padAssignment (assignment W))
      (ordinary_endpoint_not_center W Q S O P hCV1 e he x d)
    simpa only [whole, edgeWhole, clusterVertices_padAssignment, padCluster] using h
  apply Finset.disjoint_union_left.mpr
  refine ⟨Finset.disjoint_union_right.mpr ⟨hcenter 0, hcenter 1⟩, ?_⟩
  apply Finset.disjoint_left.mpr
  intro v hvp hve
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hvp
  rw [P.pair_eq (x, i)] at hi
  exact Finset.disjoint_left.mp (pairWhole_disjoint W Q _ e (private_ne_ordinary W Q S O P (x, i) e he)) hi hve

end Erdos547b.ZhaoSourcePrivateGroupSeparation

#print axioms Erdos547b.ZhaoSourcePrivateGroupSeparation.reservoir_disjoint_group
#print axioms Erdos547b.ZhaoSourcePrivateGroupSeparation.group_disjoint_ordinary
