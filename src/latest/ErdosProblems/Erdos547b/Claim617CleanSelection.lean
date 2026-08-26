/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim617CleanLoss
import ErdosProblems.Erdos547b.RootTwoPathSelection

/-!
# Selected clean major-half paths and their actual rooted core

Selection is injective on the clean branches themselves. In particular it
retains their common major parity, not merely the number of usable middles.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoClaim617CleanSelection

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoClaim617CleanLoss Erdos547b.ZhaoClaim617RootPaths
open Erdos547b.ZhaoClaim68 Erdos547b.ZhaoClaim68ParityHalf

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small p : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

def selectedBranch (hp : p ≤ (cleanBranches P).card) (i : Fin p) :
    {j // j ∈ cleanBranches P} :=
  (cleanBranches P).equivFin.symm ⟨i.val, by simpa using lt_of_lt_of_le i.isLt hp⟩

theorem selectedBranch_injective (hp : p ≤ (cleanBranches P).card) :
    Function.Injective (selectedBranch P hp) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg (cleanBranches P).equivFin hij
  simpa only [selectedBranch, Equiv.apply_symm_apply] using congrArg Fin.val h

def selectedPaths (hp : p ≤ (cleanBranches P).card) : RootTwoPathSystem T (Fin p) :=
  (cleanPaths P).reindex (selectedBranch P hp) (selectedBranch_injective P hp)

def selectedRootIndex (hp : p ≤ (cleanBranches P).card) (i : Fin p) : Fin P.numParts :=
  cleanRootIndex P (selectedBranch P hp i)

theorem selectedPaths_parent (hp : p ≤ (cleanBranches P).card) (i : Fin p) :
    (selectedPaths P hp).parent i = P.roots (selectedRootIndex P hp i) := rfl

theorem selectedPaths_parent_parity (hp : p ≤ (cleanBranches P).card) (i : Fin p) :
    T.dist globalRoot ((selectedPaths P hp).parent i) % 2 = (majorParity P).val :=
  cleanPaths_parent_parity P (selectedBranch P hp i)

theorem selectedPaths_middle_not_root (hp : p ≤ (cleanBranches P).card) (i : Fin p) :
    (selectedPaths P hp).middle i ∉ partitionRoots P :=
  cleanPaths_middle_not_root P (selectedBranch P hp i)

theorem selectedPaths_leaf_not_root (hp : p ≤ (cleanBranches P).card) (i : Fin p) :
    (selectedPaths P hp).leaf i ∉ partitionRoots P :=
  cleanPaths_leaf_not_root P (selectedBranch P hp i)

theorem selectedPaths_middle_not_parent (hp : p ≤ (cleanBranches P).card) (i : Fin p) :
    (selectedPaths P hp).middle i ∉ partitionParents P :=
  cleanPaths_middle_not_parent P (selectedBranch P hp i)

theorem selectedPaths_leaf_not_parent (hp : p ≤ (cleanBranches P).card) (i : Fin p) :
    (selectedPaths P hp).leaf i ∉ partitionParents P :=
  cleanPaths_leaf_not_parent P (selectedBranch P hp i)

private theorem globalRoot_mem (P : ZhaoForestPartition T globalRoot small) :
    globalRoot ∈ partitionRoots P :=
  Finset.mem_image.mpr ⟨⟨0, P.numParts_pos⟩, Finset.mem_univ _, P.first_root⟩

theorem selectedPaths_leafDist (hT : T.IsTree) (hp : p ≤ (cleanBranches P).card) :
    ∀ i, T.dist globalRoot ((selectedPaths P hp).middle i) + 1 =
      T.dist globalRoot ((selectedPaths P hp).leaf i) := by
  apply RootTwoPathSystem.leafDist_of_ne_root _ hT
  intro i h
  exact selectedPaths_leaf_not_root P hp i
    (Eq.mpr (congrArg (fun x : V => x ∈ partitionRoots P) h) (globalRoot_mem P))

theorem selectedPaths_parentDist (hT : T.IsTree) (hp : p ≤ (cleanBranches P).card) :
    ∀ i, T.dist globalRoot ((selectedPaths P hp).parent i) + 1 =
      T.dist globalRoot ((selectedPaths P hp).middle i) := by
  apply RootTwoPathSystem.parentDist_of_ne_root _ hT
  · intro i h
    exact selectedPaths_middle_not_root P hp i
      (Eq.mpr (congrArg (fun x : V => x ∈ partitionRoots P) h) (globalRoot_mem P))
  · intro i h
    exact selectedPaths_leaf_not_root P hp i
      (Eq.mpr (congrArg (fun x : V => x ∈ partitionRoots P) h) (globalRoot_mem P))

def selectedCoreRoot (hT : T.IsTree) (hp : p ≤ (cleanBranches P).card) :
    {x // x ∉ (selectedPaths P hp).middleSet} :=
  (selectedPaths P hp).coreRootOfOriented hT globalRoot
    (selectedPaths_parentDist P hT hp) (selectedPaths_leafDist P hT hp)

theorem selectedCore_isTree (hT : T.IsTree) (hp : p ≤ (cleanBranches P).card) :
    (selectedPaths P hp).core.IsTree :=
  (selectedPaths P hp).core_isTree_of_oriented hT globalRoot
    (selectedPaths_parentDist P hT hp) (selectedPaths_leafDist P hT hp)

theorem selectedCore_card (hp : p ≤ (cleanBranches P).card) :
    Fintype.card {x // x ∉ (selectedPaths P hp).middleSet} + 2 * p = Fintype.card V := by
  simpa only [Fintype.card_fin] using (selectedPaths P hp).core_card_add_twice

end Erdos547b.ZhaoClaim617CleanSelection

#print axioms Erdos547b.ZhaoClaim617CleanSelection.selectedPaths
#print axioms Erdos547b.ZhaoClaim617CleanSelection.selectedPaths_parent_parity
#print axioms Erdos547b.ZhaoClaim617CleanSelection.selectedCore_isTree
#print axioms Erdos547b.ZhaoClaim617CleanSelection.selectedCore_card
