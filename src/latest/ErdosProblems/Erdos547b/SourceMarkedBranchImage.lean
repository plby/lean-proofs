/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedGlobalPrefix
import ErdosProblems.Erdos547b.SourceCapacityBranchImage

/-!
# A literal original-branch image across the two kinds of placement

Ordinary coverage is required only outside the selected marked family.
Reconnection degrees on selected branches are used only at actual marks.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedGlobalPrefix

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceCapacityFamilyState Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourceFamilyParentDegree Erdos547b.ZhaoSourceOriginalBranchPlacement
open Erdos547b.ZhaoSourceMarkedBranchPlacement Erdos547b.ZhaoSourceMarkedOwnerAdvance
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceMarkedAvailableSets
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoSourceFamilyOwnerAdvance (processedFamily_mono)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable (marks : ∀ i, Finset (Fin (F.size i))) (selected : Finset (Fin b))
variable (rootSide : Fin r → Fin 2) (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin b)) (locate : Fin b → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∉ selected → i ∈ family (locate i).1 (locate i).2)
variable {stage : ℕ} (A : PrefixState W Q S O P F owner marks selected rootSide kinds allocation family stage)

def PrefixState.branchCopy (i : Fin b) (hi : (owner i).val < stage) : (F.tree i).Copy (embeddingHost W) :=
  if hs : i ∈ selected then A.marked.forestCopy.componentCopy i (Finset.mem_filter.mpr ⟨hs, hi⟩)
  else ((A.ordinary.families (locate i).1 (locate i).2).currentPlacement W Q S
    (rootCluster W Q (locate i).1) F owner (kinds (locate i).1 (locate i).2)).forestCopy.componentCopy i
      (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hcover i hs), hi⟩)

theorem PrefixState.branchCopy_eq_marked (i : Fin b) (hi : (owner i).val < stage) (hs : i ∈ selected) :
    A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i hi =
      A.marked.forestCopy.componentCopy i (Finset.mem_filter.mpr ⟨hs, hi⟩) := by
  simp only [PrefixState.branchCopy, dif_pos hs]

theorem PrefixState.branchCopy_eq_ordinary (i : Fin b) (hi : (owner i).val < stage) (hs : i ∉ selected) :
    A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i hi =
      ((A.ordinary.families (locate i).1 (locate i).2).currentPlacement W Q S
        (rootCluster W Q (locate i).1) F owner (kinds (locate i).1 (locate i).2)).forestCopy.componentCopy i
        (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hcover i hs), hi⟩) := by
  simp only [PrefixState.branchCopy, dif_neg hs]

theorem PrefixState.branchCopy_attach (i : Fin b) (hi : (owner i).val < stage) :
    (embeddingHost W).Adj (A.ordinary.rootImage (owner i))
      (A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i hi (F.root i)) := by
  by_cases hs : i ∈ selected
  · rw [A.branchCopy_eq_marked W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i hi hs]
    exact A.marked.attach i (Finset.mem_filter.mpr ⟨hs, hi⟩)
  · rw [A.branchCopy_eq_ordinary W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i hi hs]
    exact ((A.ordinary.families (locate i).1 (locate i).2).currentPlacement W Q S
      (rootCluster W Q (locate i).1) F owner (kinds (locate i).1 (locate i).2)).attach i _

theorem PrefixState.branchCopy_degree
    (hselectedLocate : ∀ i ∈ selected, (locate i).1 = 0)
    (i : Fin b) (hi : (owner i).val < stage) (a : Fin (F.size i))
    (hcolor : (F.isTree i).coloringTwoOfVert (F.root i) a = 0)
    (hmark : i ∈ selected → a ∈ marks i) :
    ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      ((reservoir W Q (locate i).1).filter ((embeddingHost W).Adj
        (A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i hi a))).card := by
  by_cases hs : i ∈ selected
  · rw [A.branchCopy_eq_marked W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i hi hs]
    have h := (A.marked.marked i (Finset.mem_filter.mpr ⟨hs, hi⟩) a
      (Finset.mem_insert_of_mem (hmark hs))).2
    rw [hselectedLocate i hs]
    simpa only [reservoir, ↓reduceIte] using h
  · rw [A.branchCopy_eq_ordinary W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i hi hs]
    exact placement_rootColor_degree W Q S (locate i).1 F _ _
      ((A.ordinary.families (locate i).1 (locate i).2).currentPlacement W Q S (rootCluster W Q (locate i).1)
        F owner (kinds (locate i).1 (locate i).2))
      ((A.ordinary.families (locate i).1 (locate i).2).current_root_positive W Q S (rootCluster W Q (locate i).1)
        F owner (kinds (locate i).1 (locate i).2))
      i (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hcover i hs), hi⟩) a hcolor

theorem PrefixState.marked_copy_mem_support (i : Fin b) (hi : i ∈ ownerPrefix selected owner stage)
    (a : Fin (F.size i)) :
    A.marked.forestCopy.componentCopy i hi a ∈ P.support W Q S O (A.marked.group ⟨i, hi⟩) := by
  by_cases hm : a ∈ insert (F.root i) (marks i)
  · exact Finset.mem_union_left _ (A.marked.marked i hi a hm).1
  · have hnot : a ≠ F.root i ∧ a ∉ marks i := by simpa only [Finset.mem_insert, not_or] using hm
    exact Finset.mem_union_right _ (A.marked.other i hi a hnot.1 hnot.2)

theorem PrefixState.branchCopy_preserved
    (D : PrefixState W Q S O P F owner marks selected rootSide kinds allocation family (stage + 1))
    (hcopies : ∀ s j i hi,
      ((D.ordinary.families s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i
          (processedFamily_mono owner (Nat.le_succ stage) (family s j) hi) =
        ((A.ordinary.families s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i hi)
    (hmarked : ∀ i (hi : i ∈ ownerPrefix selected owner stage), D.marked.forestCopy.componentCopy i
      (ownerPrefix_mono selected owner (Nat.le_succ stage) hi) = A.marked.forestCopy.componentCopy i hi)
    (i : Fin b) (hi : (owner i).val < stage) :
    D.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i (Nat.lt_succ_of_lt hi) =
      A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i hi := by
  by_cases hs : i ∈ selected
  · simp only [PrefixState.branchCopy, dif_pos hs]
    exact hmarked i (Finset.mem_filter.mpr ⟨hs, hi⟩)
  · simp only [PrefixState.branchCopy, dif_neg hs]
    exact hcopies (locate i).1 (locate i).2 i (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hcover i hs), hi⟩)

end Erdos547b.ZhaoSourceMarkedGlobalPrefix

#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.PrefixState.branchCopy_attach
#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.PrefixState.branchCopy_degree
#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.PrefixState.marked_copy_mem_support
#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.PrefixState.branchCopy_preserved
