/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58ChosenMatchingAssembly

/-!
# Reindexing side loads of selected branch families

Lemma 5.4 chooses an orientation on the canonical `Fin selected.card`
enumeration of one matching fiber.  Coordinate-pool accounting sums the
same oriented colour classes over the literal original branch indices.
These identities connect the two forms without any graph or embedding data.
-/

open scoped BigOperators
noncomputable section

namespace Erdos547b.ZhaoLemma58SelectedOrientationReindex

open Finset Fintype
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58ChosenMatchingAssembly

/-- One selected local colour class is definitionally the corresponding
original branch colour class under the extended orientation. -/
theorem orientedClassSize_selectedForest
    {b : ℕ} (F : OrderedRootedForest b) (selected : Finset (Fin b))
    (localOrient : Fin selected.card → Fin 2 ≃ Fin 2)
    (i : Fin selected.card) (c : Fin 2) :
    orientedClassSize (selectedForest F selected) localOrient i c =
      orientedClassSize F (extendSelectedOrient selected localOrient)
        (selectedEquiv selected i) c := by
  classical
  unfold orientedClassSize
  simp only [selectedForest, extendSelectedOrient_selectedEquiv]
  congr 1

/-- The order of a reindexed selected forest is the literal sum of the
original component sizes over the selected family. -/
theorem selectedForest_order
    {b : ℕ} (F : OrderedRootedForest b) (selected : Finset (Fin b)) :
    (selectedForest F selected).order = ∑ j ∈ selected, F.size j := by
  rw [OrderedRootedForest.order]
  simpa only [selectedForest_size] using
    sum_selectedEquiv selected (fun j ↦ F.size j)

/-- The local side load is the literal selected-family sum after extending
the orientation to the original branch type. -/
theorem sideLoad_selectedForest
    {b : ℕ} (F : OrderedRootedForest b) (selected : Finset (Fin b))
    (localOrient : Fin selected.card → Fin 2 ≃ Fin 2) (c : Fin 2) :
    sideLoad (selectedForest F selected) localOrient c =
      ∑ j ∈ selected,
        orientedClassSize F (extendSelectedOrient selected localOrient) j c := by
  classical
  rw [sideLoad]
  calc
    ∑ i : Fin selected.card,
        orientedClassSize (selectedForest F selected) localOrient i c =
      ∑ i : Fin selected.card,
        orientedClassSize F (extendSelectedOrient selected localOrient)
          (selectedEquiv selected i) c := by
        apply Finset.sum_congr rfl
        intro i _
        exact orientedClassSize_selectedForest F selected localOrient i c
    _ = ∑ j ∈ selected,
        orientedClassSize F (extendSelectedOrient selected localOrient) j c :=
      sum_selectedEquiv selected
        (fun j ↦ orientedClassSize F
          (extendSelectedOrient selected localOrient) j c)

/-- After orientations are pasted across matching fibers, the local side
load is exactly the literal original-index sum on that physical fiber. -/
theorem sideLoad_matchingFiber_assembledOrient
    {b k : ℕ} (F : OrderedRootedForest b) (assign : Fin b → Fin k)
    (localOrient : ∀ e,
      Fin (matchingFiber assign e).card → Fin 2 ≃ Fin 2)
    (e : Fin k) (c : Fin 2) :
    sideLoad (selectedForest F (matchingFiber assign e)) (localOrient e) c =
      ∑ j ∈ matchingFiber assign e,
        orientedClassSize F
          (assembledOrient assign (fun f ↦
            extendSelectedOrient (matchingFiber assign f) (localOrient f)))
          j c := by
  rw [sideLoad_selectedForest F (matchingFiber assign e) (localOrient e) c]
  apply Finset.sum_congr rfl
  intro j hj
  have hje : assign j = e := (mem_matchingFiber assign e j).mp hj
  subst e
  unfold orientedClassSize
  simp only [assembledOrient]
  congr 1

/-- Pointwise normalization of a pasted fiber orientation at an original
branch index. -/
theorem assembledOrient_apply_eq_localOrient_assignmentIndex
    {b k : ℕ} (assign : Fin b → Fin k)
    (localOrient : ∀ e,
      Fin (matchingFiber assign e).card → Fin 2 ≃ Fin 2)
    (j : Fin b) :
    assembledOrient assign (fun e ↦
        extendSelectedOrient (matchingFiber assign e) (localOrient e)) j =
      localOrient (assign j) (assignmentIndex assign j) := by
  have hidx := selectedEquiv_assignmentIndex assign j
  change extendSelectedOrient (matchingFiber assign (assign j))
      (localOrient (assign j)) j = _
  calc
    _ = extendSelectedOrient (matchingFiber assign (assign j))
        (localOrient (assign j))
        (OrderedBranchForest.selectedEquiv
          (matchingFiber assign (assign j)) (assignmentIndex assign j)) :=
      congrArg (extendSelectedOrient (matchingFiber assign (assign j))
        (localOrient (assign j))) hidx.symm
    _ = _ := extendSelectedOrient_selectedEquiv _ _ _

end Erdos547b.ZhaoLemma58SelectedOrientationReindex

#print axioms Erdos547b.ZhaoLemma58SelectedOrientationReindex.orientedClassSize_selectedForest
#print axioms Erdos547b.ZhaoLemma58SelectedOrientationReindex.selectedForest_order
#print axioms Erdos547b.ZhaoLemma58SelectedOrientationReindex.sideLoad_selectedForest
#print axioms Erdos547b.ZhaoLemma58SelectedOrientationReindex.sideLoad_matchingFiber_assembledOrient
#print axioms Erdos547b.ZhaoLemma58SelectedOrientationReindex.assembledOrient_apply_eq_localOrient_assignmentIndex
