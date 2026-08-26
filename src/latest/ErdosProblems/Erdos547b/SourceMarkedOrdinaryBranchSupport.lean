/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedBranchImage

/-!
# Actual allocated matching support for each ordinary branch image
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedGlobalPrefix

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceCapacityFamilyState Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoLemma58ThresholdResidualCapacity
open Erdos547b.ZhaoSourceReservationFamilyState (castPlacement)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)

theorem ordinary_current_edge_mem (D : Index W) (kind : FamilyKind)
    {edges : Finset (MatchingEdge Q.claim67.M)} {items : List (Fin b)}
    {rootImage : Fin r → Fin hostN} {stage : ℕ}
    (A : FamilyState W Q S D F owner kind edges items rootImage stage)
    (i : {i // i ∈ items.toFinset.filter (fun i => (owner i).val < stage)}) :
    (A.currentPlacement W Q S D F owner kind).edge i ∈ edges := by
  have hi : i.1 ∈ A.completed.toFinset ∪ activeSelected W Q S D F owner kind A.active :=
    (A.domain_eq W Q S D F owner kind).symm ▸ i.2
  by_cases hc : i.1 ∈ A.completed.toFinset
  · simpa only [FamilyState.currentPlacement, castPlacement, FamilyState.unionPlacement,
      BranchPlacement.append, dif_pos hc] using A.closed_subset (A.closed_edge_mem ⟨i.1, hc⟩)
  · have ha := (Finset.mem_union.mp hi).resolve_left hc
    simpa only [FamilyState.currentPlacement, castPlacement, FamilyState.unionPlacement,
      BranchPlacement.append, dif_neg hc] using
      A.active_subset (activePlacement_edge_mem W Q S D F owner kind A.active ⟨i.1, ha⟩)

variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable (marks : ∀ i, Finset (Fin (F.size i))) (selected : Finset (Fin b))
variable (rootSide : Fin r → Fin 2) (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin b)) (locate : Fin b → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∉ selected → i ∈ family (locate i).1 (locate i).2)
variable {stage : ℕ} (A : PrefixState W Q S O P F owner marks selected rootSide kinds allocation family stage)

theorem PrefixState.ordinary_branch_support (i : Fin b) (hs : i ∉ selected)
    (hi : (owner i).val < stage) (a : Fin (F.size i)) :
    ∃ e ∈ allocation (locate i).1 (locate i).2, ∃ c : Fin 2,
      A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i hi a ∈ edgeWhole W Q e c := by
  let E := (A.ordinary.families (locate i).1 (locate i).2).currentPlacement W Q S
    (rootCluster W Q (locate i).1) F owner (kinds (locate i).1 (locate i).2)
  let himem : i ∈ (family (locate i).1 (locate i).2).toFinset.filter (fun i => (owner i).val < stage) :=
    Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hcover i hs), hi⟩
  refine ⟨E.edge ⟨i, himem⟩, ?_, E.orient ⟨i, himem⟩ ((F.isTree i).coloringTwoOfVert (F.root i) a), ?_⟩
  · exact ordinary_current_edge_mem W Q S F owner _ _ (A.ordinary.families (locate i).1 (locate i).2) ⟨i, himem⟩
  · rw [A.branchCopy_eq_ordinary W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i hi hs]
    exact (Finset.mem_sdiff.mp (E.map_side i himem a)).1

end Erdos547b.ZhaoSourceMarkedGlobalPrefix

#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.ordinary_current_edge_mem
#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.PrefixState.ordinary_branch_support
