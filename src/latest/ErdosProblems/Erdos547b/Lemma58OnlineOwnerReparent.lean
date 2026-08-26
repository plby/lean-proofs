/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58ChosenOwnerBatches

/-!
# Reparenting a partial dynamic Lemma 5.8 state

In the cut-aware online construction the distinguished component roots are
chosen one at a time.  After root `n` is chosen, the total root map is updated
at `n`; every matching-edge state built from owners `< n` must then be viewed
under that extended map.  This file supplies the exact transport.  The graph
copies, orientations, side placements, and hence the literal used endpoint
sets are unchanged.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58OnlineOwnerReparent

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches

universe v

/-- Change the external-parent function of a selected partial embedding when
the two functions agree on every selected source component. -/
noncomputable def partialReparent
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent externalParent' : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (available : Fin 2 → Finset B) (selected : Finset (Fin b))
    (E : PartialDynamicAttachedForestEmbedding
      F G externalParent orient available selected)
    (hagrees : ∀ i, i ∈ selected →
      externalParent' i = externalParent i) :
    PartialDynamicAttachedForestEmbedding
      F G externalParent' orient available selected where
  forestCopy := E.forestCopy
  attach := by
    intro i hi
    rw [hagrees i hi]
    exact E.attach i hi
  map_side := E.map_side

/-- Reparenting does not change the exact set used on either physical side. -/
theorem used_partialReparent
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent externalParent' : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (available : Fin 2 → Finset B) (selected : Finset (Fin b))
    (E : PartialDynamicAttachedForestEmbedding
      F G externalParent orient available selected)
    (hagrees : ∀ i, i ∈ selected →
      externalParent' i = externalParent i) (c : Fin 2) :
    (partialReparent F G externalParent externalParent' orient available
      selected E hagrees).used c =
      E.used c := by
  rfl

/-- Chosen-orientation counterpart of `PartialDynamicAttachedForestEmbedding.reparent`. -/
noncomputable def chosenReparent
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent externalParent' : Fin b → B)
    (available : Fin 2 → Finset B) (selected : Finset (Fin b))
    (E : ChosenPartialDynamicEmbedding
      F G externalParent available selected)
    (hagrees : ∀ i, i ∈ selected →
      externalParent' i = externalParent i) :
    ChosenPartialDynamicEmbedding
      F G externalParent' available selected where
  orient := E.orient
  state := partialReparent F G externalParent externalParent' E.orient
    available selected E.state hagrees

/-- The chosen-state endpoint usage is also literal under reparenting. -/
theorem used_chosenReparent
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent externalParent' : Fin b → B)
    (available : Fin 2 → Finset B) (selected : Finset (Fin b))
    (E : ChosenPartialDynamicEmbedding
      F G externalParent available selected)
    (hagrees : ∀ i, i ∈ selected →
      externalParent' i = externalParent i) (c : Fin 2) :
    (chosenReparent F G externalParent externalParent' available selected E
      hagrees).used c = E.used c := by
  rfl

/-- Updating a total root map at owner `n` leaves every parent belonging to
the strict owner prefix `< n` unchanged. -/
theorem update_rootMap_agrees_on_ownerPrefix
    {b r : ℕ} {B : Type v} [DecidableEq B]
    (selected : Finset (Fin b)) (owner : Fin b → Fin r)
    (rootImage : Fin r → B) (n : ℕ) (hn : n < r) (z : B) :
    ∀ i, i ∈ ownerPrefix selected owner n →
      Function.update rootImage ⟨n, hn⟩ z (owner i) = rootImage (owner i) := by
  intro i hi
  have hlt : (owner i).val < n := (Finset.mem_filter.mp hi).2
  have hne : owner i ≠ ⟨n, hn⟩ := by
    intro h
    have hval : (owner i).val = n := congrArg Fin.val h
    exact (Nat.ne_of_lt hlt) hval
  exact Function.update_of_ne hne z rootImage

end Erdos547b.ZhaoLemma58OnlineOwnerReparent

#print axioms Erdos547b.ZhaoLemma58OnlineOwnerReparent.partialReparent
#print axioms Erdos547b.ZhaoLemma58OnlineOwnerReparent.chosenReparent
#print axioms Erdos547b.ZhaoLemma58OnlineOwnerReparent.update_rootMap_agrees_on_ownerPrefix
