/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58DynamicBatchAppend

/-!
# Owner batching with dynamically chosen orientations in Zhao Lemma 5.8

Appendix A.2 chooses the orientation of the forest below one outer root from
the endpoint capacities that remain when that owner is processed.  Hence a
Part-3 edge fiber cannot be passed to the fixed-orientation batch theorem in
one shot.  This module keeps the already chosen orientations in the state,
pastes a newly realized owner batch on its disjoint source indices, and
threads the exact used endpoint sets.

The final theorem returns one orientation and one concrete dynamic embedding
of the whole edge fiber.  Its local callback is the place where the concrete
owner-coherent `exists_partThreeDynamicGroupEmbedding` theorem is invoked;
there is no independent embedding or copy premise at the final boundary.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58ChosenOwnerBatches

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58DynamicBatchAppend

universe v

/-- A partial same-edge realization together with the orientations already
chosen for its literal original component indices. -/
structure ChosenPartialDynamicEmbedding
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (available : Fin 2 → Finset B)
    (selected : Finset (Fin b)) where
  orient : Fin b → Fin 2 ≃ Fin 2
  state : PartialDynamicAttachedForestEmbedding
    F G externalParent orient available selected

/-- Exact endpoint vertices used by a chosen-orientation state. -/
def ChosenPartialDynamicEmbedding.used
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    {F : OrderedRootedForest b} {G : SimpleGraph B}
    {externalParent : Fin b → B}
    {available : Fin 2 → Finset B} {selected : Finset (Fin b)}
    (E : ChosenPartialDynamicEmbedding
      F G externalParent available selected) (c : Fin 2) : Finset B :=
  E.state.used c

/-- Change the irrelevant orientations outside a partial state's selected
indices, or replace them by propositionally equal orientations on those
indices. -/
noncomputable def reorientPartial
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (available : Fin 2 → Finset B) (selected : Finset (Fin b))
    (orient orient' : Fin b → Fin 2 ≃ Fin 2)
    (E : PartialDynamicAttachedForestEmbedding
      F G externalParent orient available selected)
    (hagrees : ∀ i, i ∈ selected → orient' i = orient i) :
    PartialDynamicAttachedForestEmbedding
      F G externalParent orient' available selected where
  forestCopy := E.forestCopy
  attach := E.attach
  map_side := by
    intro i hi a
    rw [hagrees i hi]
    exact E.map_side i hi a

theorem used_reorientPartial
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (available : Fin 2 → Finset B) (selected : Finset (Fin b))
    (orient orient' : Fin b → Fin 2 ≃ Fin 2)
    (E : PartialDynamicAttachedForestEmbedding
      F G externalParent orient available selected)
    (hagrees : ∀ i, i ∈ selected → orient' i = orient i)
    (c : Fin 2) :
    (reorientPartial F G externalParent available selected orient orient'
      E hagrees).used c = E.used c := by
  ext x
  simp only [PartialDynamicAttachedForestEmbedding.used,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hxi⟩
    refine ⟨i, ?_⟩
    simpa only [reorientPartial, hagrees i.1 i.2] using hxi
  · rintro ⟨i, hxi⟩
    refine ⟨i, ?_⟩
    simpa only [reorientPartial, hagrees i.1 i.2] using hxi

/-- Paste two orientation functions, using the first on the already
processed source indices and the second everywhere else. -/
def pasteOrient {b : ℕ} (s : Finset (Fin b))
    (first second : Fin b → Fin 2 ≃ Fin 2) :
    Fin b → Fin 2 ≃ Fin 2 :=
  fun i ↦ if i ∈ s then first i else second i

/-- Append a dynamically oriented owner batch to the exact residual state.
This is the chosen-orientation counterpart of `appendPartial`. -/
noncomputable def appendChosen
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (s t : Finset (Fin b)) (hst : Disjoint s t)
    (E₁ : ChosenPartialDynamicEmbedding
      F G externalParent available s)
    (E₂ : ChosenPartialDynamicEmbedding F G externalParent
      (fun c ↦ available c \ E₁.used c) t) :
    ChosenPartialDynamicEmbedding F G externalParent available (s ∪ t) := by
  classical
  let combined := pasteOrient s E₁.orient E₂.orient
  have hfirst : ∀ i, i ∈ s → combined i = E₁.orient i := by
    intro i hi
    simp only [combined, pasteOrient, hi, if_true]
  have hsecond : ∀ i, i ∈ t → combined i = E₂.orient i := by
    intro i hi
    have his : i ∉ s := by
      intro his
      exact Finset.disjoint_left.mp hst his hi
    simp only [combined, pasteOrient, his, if_false]
  let P₁ := reorientPartial F G externalParent available s E₁.orient
    combined E₁.state hfirst
  have hused (c : Fin 2) : P₁.used c = E₁.used c := by
    exact used_reorientPartial F G externalParent available s E₁.orient
      combined E₁.state hfirst c
  let P₂raw := reorientPartial F G externalParent
    (fun c ↦ available c \ E₁.used c) t E₂.orient combined
    E₂.state hsecond
  let P₂ : PartialDynamicAttachedForestEmbedding F G externalParent combined
      (fun c ↦ available c \ P₁.used c) t := {
    forestCopy := P₂raw.forestCopy
    attach := P₂raw.attach
    map_side := by
      intro i hi a
      have hm := P₂raw.map_side i hi a
      simpa only [hused] using hm
  }
  exact {
    orient := combined
    state := appendPartial F G externalParent combined whole available
      havailable hwholeDisjoint s t hst P₁ P₂
  }

/-- Extend a locally chosen selected-family orientation to all original
component indices.  Values outside the selected family are irrelevant. -/
noncomputable def extendSelectedOrient
    {b : ℕ} (selected : Finset (Fin b))
    (localOrient : Fin selected.card → Fin 2 ≃ Fin 2) :
    Fin b → Fin 2 ≃ Fin 2 :=
  fun i ↦ if hi : i ∈ selected then
    localOrient (selectedIndex selected i hi) else Equiv.refl _

@[simp] theorem selectedIndex_selectedEquiv
    {b : ℕ} (selected : Finset (Fin b)) (k : Fin selected.card) :
    selectedIndex selected
      (OrderedBranchForest.selectedEquiv selected k)
      (OrderedBranchForest.selectedEquiv selected k).property = k := by
  apply (OrderedBranchForest.selectedEquiv selected).injective
  simp [selectedIndex]

@[simp] theorem extendSelectedOrient_selectedEquiv
    {b : ℕ} (selected : Finset (Fin b))
    (localOrient : Fin selected.card → Fin 2 ≃ Fin 2)
    (k : Fin selected.card) :
    extendSelectedOrient selected localOrient
        (OrderedBranchForest.selectedEquiv selected k) = localOrient k := by
  simp [extendSelectedOrient]

/-- Reinterpret a dynamic selected-family embedding under a pointwise equal
orientation function. -/
noncomputable def reorientDynamic
    {m : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest m) (G : SimpleGraph B)
    (externalParent : Fin m → B) (available : Fin 2 → Finset B)
    (orient orient' : Fin m → Fin 2 ≃ Fin 2)
    (E : DynamicAttachedForestEmbedding F G externalParent orient available)
    (hagrees : ∀ i, orient' i = orient i) :
    DynamicAttachedForestEmbedding F G externalParent orient' available where
  embedding := E.embedding
  attach := E.attach
  map_side := by
    intro i a
    rw [hagrees i]
    exact E.map_side i a

/-- Pull a locally oriented selected-family embedding back to a chosen state
on the literal original indices. -/
noncomputable def chosenPartialOfSelectedForest
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (available : Fin 2 → Finset B) (selected : Finset (Fin b))
    (localOrient : Fin selected.card → Fin 2 ≃ Fin 2)
    (E : DynamicAttachedForestEmbedding (selectedForest F selected) G
      (fun k ↦ externalParent
        (OrderedBranchForest.selectedEquiv selected k))
      localOrient available) :
    ChosenPartialDynamicEmbedding F G externalParent available selected := by
  let globalOrient := extendSelectedOrient selected localOrient
  let E' : DynamicAttachedForestEmbedding (selectedForest F selected) G
      (fun k ↦ externalParent
        (OrderedBranchForest.selectedEquiv selected k))
      (fun k ↦ globalOrient
        (OrderedBranchForest.selectedEquiv selected k)) available :=
    reorientDynamic (selectedForest F selected) G
      (fun k ↦ externalParent
        (OrderedBranchForest.selectedEquiv selected k)) available
      localOrient
      (fun k ↦ globalOrient
        (OrderedBranchForest.selectedEquiv selected k)) E
      (fun k ↦ by
        simp only [globalOrient, extendSelectedOrient_selectedEquiv])
  exact {
    orient := globalOrient
    state := partialOfSelectedForest F G externalParent globalOrient
      available selected E'
  }

/-- Owner-by-owner realization in which each local callback may choose the
orientation dictated by the current Appendix A.2 capacities. -/
theorem exists_chosenPartialDynamicEmbedding_of_ownerBatches
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (selected : Finset (Fin b)) (owner : Fin b → Fin r)
    (hstep : ∀ n (hn : n < r)
      (Eprefix : ChosenPartialDynamicEmbedding F G externalParent available
        (ownerPrefix selected owner n)),
      ∃ localOrient :
          Fin (ownerBatch selected owner ⟨n, hn⟩).card → Fin 2 ≃ Fin 2,
        Nonempty (DynamicAttachedForestEmbedding
          (selectedForest F (ownerBatch selected owner ⟨n, hn⟩)) G
          (fun k ↦ externalParent
            (OrderedBranchForest.selectedEquiv
              (ownerBatch selected owner ⟨n, hn⟩) k))
          localOrient (fun c ↦ available c \ Eprefix.used c))) :
    Nonempty (ChosenPartialDynamicEmbedding
      F G externalParent available selected) := by
  classical
  have hbuild : ∀ n, n ≤ r →
      Nonempty (ChosenPartialDynamicEmbedding F G externalParent available
        (ownerPrefix selected owner n)) := by
    intro n hnr
    induction n with
    | zero =>
        rw [ownerPrefix_zero]
        exact ⟨{
          orient := fun _ ↦ Equiv.refl _
          state := emptyPartial F G externalParent (fun _ ↦ Equiv.refl _)
            available
        }⟩
    | succ n ih =>
        have hn : n < r := Nat.lt_of_succ_le hnr
        obtain ⟨Eprefix⟩ := ih (Nat.le_of_lt hn)
        obtain ⟨localOrient, ⟨Ebatch⟩⟩ := hstep n hn Eprefix
        let Cbatch := chosenPartialOfSelectedForest F G externalParent
          (fun c ↦ available c \ Eprefix.used c)
          (ownerBatch selected owner ⟨n, hn⟩) localOrient Ebatch
        have Eunion := appendChosen F G externalParent whole available
          havailable hwholeDisjoint (ownerPrefix selected owner n)
          (ownerBatch selected owner ⟨n, hn⟩)
          (ownerPrefix_disjoint_ownerBatch selected owner n hn)
          Eprefix Cbatch
        rw [ownerPrefix_succ selected owner n hn] at Eunion
        exact ⟨Eunion⟩
  obtain ⟨E⟩ := hbuild r le_rfl
  rw [ownerPrefix_all selected owner] at E
  exact ⟨E⟩

/-- Full edge-fiber output with its dynamically chosen global orientation. -/
theorem exists_dynamicAttachedForestEmbedding_of_chosenOwnerBatches
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (owner : Fin b → Fin r)
    (hstep : ∀ n (hn : n < r)
      (Eprefix : ChosenPartialDynamicEmbedding F G externalParent available
        (ownerPrefix Finset.univ owner n)),
      ∃ localOrient :
          Fin (ownerBatch Finset.univ owner ⟨n, hn⟩).card → Fin 2 ≃ Fin 2,
        Nonempty (DynamicAttachedForestEmbedding
          (selectedForest F (ownerBatch Finset.univ owner ⟨n, hn⟩)) G
          (fun k ↦ externalParent
            (OrderedBranchForest.selectedEquiv
              (ownerBatch Finset.univ owner ⟨n, hn⟩) k))
          localOrient (fun c ↦ available c \ Eprefix.used c))) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        F G externalParent orient available) := by
  obtain ⟨E⟩ := exists_chosenPartialDynamicEmbedding_of_ownerBatches
    F G externalParent whole available havailable hwholeDisjoint
    Finset.univ owner hstep
  exact ⟨E.orient,
    ⟨E.state.toDynamic F G externalParent E.orient available⟩⟩

end Erdos547b.ZhaoLemma58ChosenOwnerBatches

#print axioms Erdos547b.ZhaoLemma58ChosenOwnerBatches.appendChosen
#print axioms Erdos547b.ZhaoLemma58ChosenOwnerBatches.exists_dynamicAttachedForestEmbedding_of_chosenOwnerBatches
