/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceChosenAppendFacts
import ErdosProblems.Erdos547b.SourcePendingOwnerInterval

/-!
# Exact owner successor for a chosen-orientation chunk

The local input is one actual current-owner batch in the literal residual
sets. Reparenting the old prefix and reindexing the new batch change no
copy. The resulting used sets and all earlier maps are exposed exactly.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoLemma58ChosenOwnerBatches

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58OnlineOwnerReparent Erdos547b.ZhaoSourcePendingInterval
open Erdos547b.ZhaoSourcePendingOwnerInterval
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest

variable {b r : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
variable (F : OrderedRootedForest b) (H : SimpleGraph V)

def castChosenSelected (parent : Fin b → V) (available : Fin 2 → Finset V)
    {s t : Finset (Fin b)} (hst : s = t)
    (E : ChosenPartialDynamicEmbedding F H parent available s) :
    ChosenPartialDynamicEmbedding F H parent available t where
  orient := E.orient
  state := castPartialSelected F H parent E.orient available hst E.state

theorem used_castChosenSelected (parent : Fin b → V) (available : Fin 2 → Finset V)
    {s t : Finset (Fin b)} (hst : s = t)
    (E : ChosenPartialDynamicEmbedding F H parent available s) (c : Fin 2) :
    (castChosenSelected F H parent available hst E).used c = E.used c := by
  subst t
  rfl

theorem exists_chosen_owner_advance
    (owner : Fin b → Fin r) (hmono : Monotone owner)
    (whole available : Fin 2 → Finset V)
    (havailable : ∀ c, available c ⊆ whole c) (hwhole : Disjoint (whole 0) (whole 1))
    (rootImage : Fin r → V) (n : Fin r)
    (E : ChosenPartialDynamicEmbedding F H (fun i => rootImage (owner i)) available
      (branchPrefix (ownerCutoff owner n.val)))
    (z : V) (localOrient : Fin (ownerBatch Finset.univ owner n).card → Fin 2 ≃ Fin 2)
    (Ebatch : DynamicAttachedForestEmbedding (selectedForest F (ownerBatch Finset.univ owner n)) H
      (fun _ => z) localOrient (fun c => available c \ E.used c)) :
    ∃ E' : ChosenPartialDynamicEmbedding F H
        (fun i => Function.update rootImage n z (owner i)) available
        (branchPrefix (ownerCutoff owner (n.val + 1))),
      (∀ c, E'.used c = E.used c ∪ Ebatch.used c) ∧
      (∀ i (hi : i ∈ branchPrefix (ownerCutoff owner n.val)),
        E'.state.forestCopy.componentCopy i
            (branchPrefix_mono (ownerCutoff_mono owner (Nat.le_succ n.val)) hi) =
          E.state.forestCopy.componentCopy i hi) ∧
      ∀ i ∈ branchPrefix (ownerCutoff owner n.val), E'.orient i = E.orient i := by
  let parent' := fun i => Function.update rootImage n z (owner i)
  let s : Finset (Fin b) := branchPrefix (ownerCutoff owner n.val)
  let t := ownerBatch Finset.univ owner n
  have hagrees : ∀ i ∈ s, parent' i = rootImage (owner i) := by
    intro i hi
    exact update_rootMap_agrees_on_ownerPrefix Finset.univ owner rootImage n.val n.isLt z i
      (by simpa only [s, branchPrefix_ownerCutoff owner hmono] using hi)
  let old := chosenReparent F H (fun i => rootImage (owner i)) parent' available s E hagrees
  have hparent (k : Fin t.card) : parent' (selectedEquiv t k) = z := by
    have ho := (Finset.mem_filter.mp (selectedEquiv t k).property).2
    change Function.update rootImage n z (owner (selectedEquiv t k)) = z
    rw [ho, Function.update_self]
  let localCopy : DynamicAttachedForestEmbedding (selectedForest F t) H
      (fun k => parent' (selectedEquiv t k)) localOrient (fun c => available c \ old.used c) := {
    embedding := Ebatch.embedding
    attach := by
      intro k
      rw [hparent]
      exact Ebatch.attach k
    map_side := Ebatch.map_side }
  let batch := chosenPartialOfSelectedForest F H parent' (fun c => available c \ old.used c)
    t localOrient localCopy
  have hst : Disjoint s t := by
    simpa only [s, t, branchPrefix_ownerCutoff owner hmono] using
      ownerPrefix_disjoint_ownerBatch Finset.univ owner n.val n.isLt
  let joined := appendChosen F H parent' whole available havailable hwhole s t hst old batch
  have hselected : s ∪ t = branchPrefix (ownerCutoff owner (n.val + 1)) := by
    simpa only [s, t, branchPrefix_ownerCutoff owner hmono] using
      ownerPrefix_succ Finset.univ owner n.val n.isLt
  let out := castChosenSelected F H parent' available hselected joined
  refine ⟨out, ?_, ?_, ?_⟩
  · intro c
    rw [used_castChosenSelected, used_appendChosen, used_chosenPartialOfSelectedForest]
    rfl
  · intro i hi
    change joined.state.forestCopy.componentCopy i (Finset.mem_union_left t hi) =
      E.state.forestCopy.componentCopy i hi
    exact appendChosen_copy_left F H parent' whole available havailable hwhole s t hst old batch i hi
  · intro i hi
    exact appendChosen_orient_left F H parent' whole available havailable hwhole s t hst old batch i hi

end Erdos547b.ZhaoLemma58ChosenOwnerBatches

#print axioms Erdos547b.ZhaoLemma58ChosenOwnerBatches.used_castChosenSelected
#print axioms Erdos547b.ZhaoLemma58ChosenOwnerBatches.exists_chosen_owner_advance
