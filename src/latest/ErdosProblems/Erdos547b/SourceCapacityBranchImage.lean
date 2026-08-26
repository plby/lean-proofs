/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityGlobalPrefix
import ErdosProblems.Erdos547b.SourceFamilyParentDegree

/-!
# Literal branch images and reconnection degrees in capacity-aware prefixes

A fixed source classification selects the stored original-index copy.
Its support, attachment, physical side and cleanup degree are inherited
from that same copy, and the global successor preserves it exactly.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityGlobalPrefix

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceFamilyParentDegree Erdos547b.ZhaoSourceCapacityFamilyState
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity
open Erdos547b.ZhaoSourceFamilyOwnerAdvance (processedFamily_mono)
open Erdos547b.ZhaoSourceReservationFamilyState (castPlacement)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)

private theorem current_edge_mem (C : Index W) (kind : FamilyKind)
    {edges : Finset (MatchingEdge Q.claim67.M)} {items : List (Fin b)}
    {rootImage : Fin r → Fin hostN} {stage : ℕ}
    (A : FamilyState W Q S C F owner kind edges items rootImage stage)
    (i : {i // i ∈ items.toFinset.filter (fun i => (owner i).val < stage)}) :
    (A.currentPlacement W Q S C F owner kind).edge i ∈ edges := by
  have hi : i.1 ∈ A.completed.toFinset ∪ activeSelected W Q S C F owner kind A.active :=
    (A.domain_eq W Q S C F owner kind).symm ▸ i.2
  by_cases hc : i.1 ∈ A.completed.toFinset
  · simpa only [FamilyState.currentPlacement, castPlacement, FamilyState.unionPlacement,
      BranchPlacement.append, dif_pos hc] using A.closed_subset (A.closed_edge_mem ⟨i.1, hc⟩)
  · have ha := (Finset.mem_union.mp hi).resolve_left hc
    simpa only [FamilyState.currentPlacement, castPlacement, FamilyState.unionPlacement,
      BranchPlacement.append, dif_neg hc] using
      A.active_subset (activePlacement_edge_mem W Q S C F owner kind A.active ⟨i.1, ha⟩)

variable (rootSide : Fin r → Fin 2) (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin b))
variable (locate : Fin b → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∈ family (locate i).1 (locate i).2)
variable {stage : ℕ} (A : PrefixState W Q S F owner rootSide kinds allocation family stage)

def PrefixState.branchCopy (i : Fin b) (hi : (owner i).val < stage) :
    (F.tree i).Copy (embeddingHost W) :=
  ((A.families (locate i).1 (locate i).2).currentPlacement W Q S
      (rootCluster W Q (locate i).1) F owner (kinds (locate i).1 (locate i).2)).forestCopy.componentCopy i
    (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hcover i), hi⟩)

def PrefixState.branchEdge (i : Fin b) (hi : (owner i).val < stage) : MatchingEdge Q.claim67.M :=
  ((A.families (locate i).1 (locate i).2).currentPlacement W Q S
      (rootCluster W Q (locate i).1) F owner (kinds (locate i).1 (locate i).2)).edge
    ⟨i, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hcover i), hi⟩⟩

def PrefixState.branchOrient (i : Fin b) (hi : (owner i).val < stage) : Fin 2 ≃ Fin 2 :=
  ((A.families (locate i).1 (locate i).2).currentPlacement W Q S
      (rootCluster W Q (locate i).1) F owner (kinds (locate i).1 (locate i).2)).orient
    ⟨i, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hcover i), hi⟩⟩

theorem PrefixState.branchEdge_mem (i : Fin b) (hi : (owner i).val < stage) :
    A.branchEdge W Q S F owner rootSide kinds allocation family locate hcover i hi ∈
      allocation (locate i).1 (locate i).2 :=
  current_edge_mem W Q S F owner _ _ (A.families (locate i).1 (locate i).2) _

theorem PrefixState.branchCopy_attach (i : Fin b) (hi : (owner i).val < stage) :
    (embeddingHost W).Adj (A.rootImage (owner i))
      (A.branchCopy W Q S F owner rootSide kinds allocation family locate hcover i hi (F.root i)) :=
  ((A.families (locate i).1 (locate i).2).currentPlacement W Q S
    (rootCluster W Q (locate i).1) F owner (kinds (locate i).1 (locate i).2)).attach i _

theorem PrefixState.branchCopy_side (i : Fin b) (hi : (owner i).val < stage) (a : Fin (F.size i)) :
    A.branchCopy W Q S F owner rootSide kinds allocation family locate hcover i hi a ∈
      residualSide (edgeWhole W Q (A.branchEdge W Q S F owner rootSide kinds allocation family locate hcover i hi))
        (deleted W Q (A.branchEdge W Q S F owner rootSide kinds allocation family locate hcover i hi))
        (A.branchOrient W Q S F owner rootSide kinds allocation family locate hcover i hi
          ((F.isTree i).coloringTwoOfVert (F.root i) a)) :=
  ((A.families (locate i).1 (locate i).2).currentPlacement W Q S
    (rootCluster W Q (locate i).1) F owner (kinds (locate i).1 (locate i).2)).map_side i _ a

theorem PrefixState.branch_rootColor_degree (i : Fin b) (hi : (owner i).val < stage)
    (a : Fin (F.size i)) (hcolor : (F.isTree i).coloringTwoOfVert (F.root i) a = 0) :
    ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q (locate i).1).filter ((embeddingHost W).Adj
        (A.branchCopy W Q S F owner rootSide kinds allocation family locate hcover i hi a))) : ℝ) :=
  placement_rootColor_degree W Q S (locate i).1 F _ _
    ((A.families (locate i).1 (locate i).2).currentPlacement W Q S (rootCluster W Q (locate i).1)
      F owner (kinds (locate i).1 (locate i).2))
    ((A.families (locate i).1 (locate i).2).current_root_positive W Q S (rootCluster W Q (locate i).1)
      F owner (kinds (locate i).1 (locate i).2))
    i (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hcover i), hi⟩) a hcolor

theorem PrefixState.branchCopy_preserved
    (D : PrefixState W Q S F owner rootSide kinds allocation family (stage + 1))
    (hcopies : ∀ s j i hi,
      ((D.families s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i
          (processedFamily_mono owner (Nat.le_succ stage) (family s j) hi) =
        ((A.families s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i hi)
    (i : Fin b) (hi : (owner i).val < stage) :
    D.branchCopy W Q S F owner rootSide kinds allocation family locate hcover i (Nat.lt_succ_of_lt hi) =
      A.branchCopy W Q S F owner rootSide kinds allocation family locate hcover i hi :=
  hcopies (locate i).1 (locate i).2 i (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hcover i), hi⟩)

end Erdos547b.ZhaoSourceCapacityGlobalPrefix

#print axioms Erdos547b.ZhaoSourceCapacityGlobalPrefix.PrefixState.branchEdge_mem
#print axioms Erdos547b.ZhaoSourceCapacityGlobalPrefix.PrefixState.branchCopy_attach
#print axioms Erdos547b.ZhaoSourceCapacityGlobalPrefix.PrefixState.branchCopy_side
#print axioms Erdos547b.ZhaoSourceCapacityGlobalPrefix.PrefixState.branch_rootColor_degree
#print axioms Erdos547b.ZhaoSourceCapacityGlobalPrefix.PrefixState.branchCopy_preserved
