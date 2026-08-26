/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616
import ErdosProblems.Erdos547b.HierarchicalRootReservoir

/-!
# Claim 6.16 host data selects the hierarchical original root

This is the concrete specialization of the quantitative root selector to
`Claim616.IndexedHostSystem`: the source cluster is the distinguished large
cluster `A`, and every direct hierarchy target is one of the indexed `C`
clusters.  Uniformity and high degree are derived from the record, not
accepted as extra hypotheses.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616HierarchicalRoot

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest
open Erdos547b.ZhaoHierarchicalRootReservoir

universe u v

theorem IndexedHostSystem.exists_highDegree_oneRootImage
    {B : Type u} {I : Type v}
    [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I]
    (G Gdegree : SimpleGraph B)
    [DecidableRel G.Adj] [DecidableRel Gdegree.Adj]
    (cluster : I → Finset B) (epsilon density : ℚ)
    [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
    (A Broot : I) (C : Finset I)
    (M : (regularityReducedGraph G cluster epsilon density).Subgraph)
    (W : Finset I) (rhoK : ℕ)
    (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
    (H : IndexedHostSystem G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree)
    {s : ℕ} (F : HierarchicalSegmentForest 1 s)
    (rootGroup : Fin s → Fin C.card)
    (hepsilon : (epsilon : ℝ) ≤ 1)
    (hbadBudget :
      (#(Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0) : ℝ) *
          ((epsilon : ℝ) * #(cluster A)) < quota) :
    ∃ z ∈ H.rootReservoir G cluster epsilon density A Broot C M W rhoK
        Pcluster threshold quota Gdegree,
      threshold ≤ Gdegree.degree z ∧
      ∀ i, F.parent i = Sum.inl 0 →
        z ∈ Erdos547b.RegularPair.cleanedSide G (epsilon : ℝ)
          (cluster A) (indexedCluster cluster C (rootGroup i)) := by
  have hbadReal :
      (#(oneRootBad F G (epsilon : ℝ) (cluster A) rootGroup
          (fun i ↦ indexedCluster cluster C i)) : ℝ) < quota :=
    (card_oneRootBad_le F G (epsilon : ℝ) (cluster A) rootGroup
      (fun i ↦ indexedCluster cluster C i)
      (fun i hi ↦ (H.root_pair i).1) hepsilon).trans_lt hbadBudget
  have hbad :
      #(oneRootBad F G (epsilon : ℝ) (cluster A) rootGroup
          (fun i ↦ indexedCluster cluster C i)) <
        #(H.rootReservoir G cluster epsilon density A Broot C M W rhoK
          Pcluster threshold quota Gdegree) := by
    have hbadQuota :
        #(oneRootBad F G (epsilon : ℝ) (cluster A) rootGroup
            (fun i ↦ indexedCluster cluster C i)) < quota := by
      exact_mod_cast hbadReal
    change #(oneRootBad F G (epsilon : ℝ) (cluster A) rootGroup
      (fun i ↦ indexedCluster cluster C i)) < H.rootReserve.card
    rw [H.rootReserve_card]
    exact hbadQuota
  obtain ⟨z, hz, hclean⟩ :=
    exists_oneRootImage_in_reservoir_of_bad_card F G (epsilon : ℝ)
      (cluster A)
      (H.rootReservoir G cluster epsilon density A Broot C M W rhoK
        Pcluster threshold quota Gdegree)
      rootGroup (fun i ↦ indexedCluster cluster C i)
      (H.rootReservoir_subset_rootCluster G cluster epsilon density
        A Broot C M W rhoK Pcluster threshold quota Gdegree) hbad
  refine ⟨z, hz,
    H.rootReservoir_highDegree G cluster epsilon density A Broot C M W rhoK
      Pcluster threshold quota Gdegree hz, ?_⟩
  intro i hi
  exact hclean i hi

end Erdos547b.ZhaoClaim616HierarchicalRoot

#print axioms Erdos547b.ZhaoClaim616HierarchicalRoot.IndexedHostSystem.exists_highDegree_oneRootImage
