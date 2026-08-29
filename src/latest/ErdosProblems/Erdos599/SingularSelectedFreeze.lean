/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularPendingReentry

/-!
# Selecting a singular row and freezing its complement

The future-safe singular successor continues only the still-pending
components whose initials belong to the next requested source set.  Every
other component is frozen.  This file packages the elementary decomposition
and the target-link bookkeeping independently of the safety construction
which chooses the new quotient family.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSelectedFreeze

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- The components of `W` whose initial vertices are selected by `B`. -/
def selectedRow (G : DWeb V) (W : Set G.DPath) (B : Set V) : Set G.DPath :=
  initialRestriction G W B

/-- The selected components which have not yet reached the ambient target. -/
def selectedPending (G : DWeb V) (W : Set G.DPath) (B : Set V) :
    Set G.DPath :=
  pendingPart G (selectedRow G W B)

/-- Freeze every component except the selected pending components. -/
def frozenComplement (G : DWeb V) (W : Set G.DPath) (B : Set V) :
    Set G.DPath :=
  W \ selectedPending G W B

theorem selectedRow_subset (G : DWeb V) (W : Set G.DPath) (B : Set V) :
    selectedRow G W B ⊆ W :=
  fun _ hp => hp.1

theorem selectedPending_subset (G : DWeb V) (W : Set G.DPath) (B : Set V) :
    selectedPending G W B ⊆ W :=
  fun _ hp => hp.1.1

theorem frozenComplement_subset (G : DWeb V) (W : Set G.DPath)
    (B : Set V) : frozenComplement G W B ⊆ W :=
  fun _ hp => hp.1

/-- The frozen complement and selected pending part are exactly the old row. -/
theorem frozenComplement_union_selectedPending
    (G : DWeb V) (W : Set G.DPath) (B : Set V) :
    frozenComplement G W B ∪ selectedPending G W B = W := by
  apply Set.Subset.antisymm
  · exact Set.union_subset (frozenComplement_subset G W B)
      (selectedPending_subset G W B)
  · intro p hp
    by_cases hpPending : p ∈ selectedPending G W B
    · exact Or.inr hpPending
    · exact Or.inl ⟨hp, hpPending⟩

theorem disjoint_frozenComplement_selectedPending
    (G : DWeb V) (W : Set G.DPath) (B : Set V) :
    Disjoint (frozenComplement G W B) (selectedPending G W B) :=
  Set.disjoint_sdiff_left

/-- Restricting a full-source row to `B` gives exactly the initials in `B`. -/
theorem initialSet_selectedRow
    {G : DWeb V} {W : Set G.DPath} {B : Set V}
    (hinitial : G.initialSet W = G.source) (hB : B ⊆ G.source) :
    G.initialSet (selectedRow G W B) = B := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, hpx⟩
    exact hpx ▸ hp.2
  · intro x hxB
    have hxInitial : x ∈ G.initialSet W := hinitial.symm ▸ hB hxB
    obtain ⟨p, hpW, hpx⟩ := hxInitial
    exact ⟨p, ⟨hpW, hpx ▸ hxB⟩, hpx⟩

/-- The selected initials split between completed and pending components. -/
theorem initialSet_completed_union_pending_selectedRow
    {G : DWeb V} {W : Set G.DPath} {B : Set V}
    (hinitial : G.initialSet W = G.source) (hB : B ⊆ G.source) :
    G.initialSet (completedPart G (selectedRow G W B)) ∪
        G.initialSet (selectedPending G W B) = B := by
  calc
    G.initialSet (completedPart G (selectedRow G W B)) ∪
          G.initialSet (selectedPending G W B) =
        G.initialSet (selectedRow G W B) := by
      apply Set.Subset.antisymm
      · rintro x (hx | hx)
        · obtain ⟨p, hp, hpx⟩ := hx
          exact ⟨p, hp.1, hpx⟩
        · obtain ⟨p, hp, hpx⟩ := hx
          exact ⟨p, hp.1, hpx⟩
      · rintro x ⟨p, hp, hpx⟩
        rw [← completedPart_union_pendingPart G (selectedRow G W B)] at hp
        rcases hp with hp | hp
        · exact Or.inl ⟨p, hp, hpx⟩
        · exact Or.inr ⟨p, hp, hpx⟩
    _ = B := initialSet_selectedRow hinitial hB

/-- The initials of a completed subfamily are linked to the target by the
same completed components, viewed inside any containing finite row. -/
theorem linksToTarget_initialSet_completedPart
    {G : DWeb V} (hNorm : G.IsNormalized)
    {R W : Set G.DPath} (hRsub : R ⊆ W)
    (hWfinite : G.HasFiniteCharacter W)
    (hRsource : G.initialSet R ⊆ G.source) :
    LinksToTarget G W (G.initialSet (completedPart G R)) := by
  intro a ha
  obtain ⟨p, hpCompleted, hpInitial⟩ := ha
  obtain ⟨q, hpq⟩ := hWfinite (hRsub hpCompleted.1)
  subst p
  obtain ⟨b, hbTarget, hqTerminal⟩ := hpCompleted.2
  have hqStart : q.start = a := hpInitial
  have hcompletedSource : G.initialSet (completedPart G R) ⊆ G.source := by
    rintro x ⟨r, hr, hrx⟩
    apply hRsource
    exact ⟨r, hr.1, hrx⟩
  have hpure : q.support ∩ G.initialSet (completedPart G R) = {a} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxInitial⟩
      have hxStart : x = q.start :=
        hNorm.eq_initial_of_mem_path (.inl q) hxq
          (hcompletedSource hxInitial)
      exact Set.mem_singleton_iff.2 (hxStart.trans hqStart)
    · intro x hx
      have hxa : x = a := Set.mem_singleton_iff.1 hx
      subst x
      refine ⟨?_, ⟨.inl q, hpCompleted, hpInitial⟩⟩
      simpa only [hqStart] using q.start_mem_support
  have hqFinish : q.finish = b := Option.some.inj hqTerminal
  refine ⟨.inl q, hRsub hpCompleted.1, q, rfl, hpure, ?_⟩
  refine ⟨[], q.walk.support.tail, ?_, b, hbTarget, ?_⟩
  · simp only [List.nil_append]
    calc
      q.walk.support =
          q.walk.support.head q.walk.support_ne_nil :: q.walk.support.tail :=
        (q.walk.support.cons_head_tail q.walk.support_ne_nil).symm
      _ = a :: q.walk.support.tail := by
        exact congrArg (fun x => x :: q.walk.support.tail)
          (q.walk.head_support.trans hqStart)
  · have hcons : a :: q.walk.support.tail = q.walk.support := by
      calc
        a :: q.walk.support.tail =
            q.walk.support.head q.walk.support_ne_nil ::
              q.walk.support.tail := by
          exact congrArg (fun x => x :: q.walk.support.tail)
            (hqStart.symm.trans q.walk.head_support.symm)
        _ = q.walk.support :=
          q.walk.support.cons_head_tail q.walk.support_ne_nil
    change b ∈ a :: q.walk.support.tail
    rw [hcons, ← hqFinish]
    exact q.finish_mem_support

/-- In a normalized web, target-link certificates for two sets of source
vertices combine.  Normalization upgrades the purity of either witness from
its original request set to the union: a directed path can contain only its
initial ambient source vertex. -/
theorem linksToTarget_union_of_normalized
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {A B : Set V}
    (hA : A ⊆ G.source) (hB : B ⊆ G.source)
    (hlinksA : LinksToTarget G W A)
    (hlinksB : LinksToTarget G W B) :
    LinksToTarget G W (A ∪ B) := by
  intro a ha
  rcases ha with ha | ha
  · obtain ⟨p, hpW, q, hpq, hpure, hsuffix⟩ := hlinksA a ha
    have haSupport : a ∈ q.support := by
      have haInter : a ∈ q.support ∩ A := by
        rw [hpure]
        exact Set.mem_singleton a
      exact haInter.1
    have haStart : a = q.start :=
      hNorm.eq_initial_of_mem_path (.inl q) haSupport (hA ha)
    refine ⟨p, hpW, q, hpq, ?_, hsuffix⟩
    apply Set.Subset.antisymm
    · rintro x ⟨hxSupport, hxA | hxB⟩
      · exact Set.mem_singleton_iff.2
          ((hNorm.eq_initial_of_mem_path (.inl q) hxSupport (hA hxA)).trans
            haStart.symm)
      · exact Set.mem_singleton_iff.2
          ((hNorm.eq_initial_of_mem_path (.inl q) hxSupport (hB hxB)).trans
            haStart.symm)
    · intro x hx
      have hxa : x = a := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨haSupport, Or.inl ha⟩
  · obtain ⟨p, hpW, q, hpq, hpure, hsuffix⟩ := hlinksB a ha
    have haSupport : a ∈ q.support := by
      have haInter : a ∈ q.support ∩ B := by
        rw [hpure]
        exact Set.mem_singleton a
      exact haInter.1
    have haStart : a = q.start :=
      hNorm.eq_initial_of_mem_path (.inl q) haSupport (hB ha)
    refine ⟨p, hpW, q, hpq, ?_, hsuffix⟩
    apply Set.Subset.antisymm
    · rintro x ⟨hxSupport, hxA | hxB⟩
      · exact Set.mem_singleton_iff.2
          ((hNorm.eq_initial_of_mem_path (.inl q) hxSupport (hA hxA)).trans
            haStart.symm)
      · exact Set.mem_singleton_iff.2
          ((hNorm.eq_initial_of_mem_path (.inl q) hxSupport (hB hxB)).trans
            haStart.symm)
    · intro x hx
      have hxa : x = a := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨haSupport, Or.inr ha⟩

/-- To link all selected sources after a frozen-pending continuation, it is
enough to link the initials of the selected pending components.  Completed
selected components already contain target points, and target links survive
the forward extension. -/
theorem linksToTarget_of_selectedPending
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W T : Set G.DPath} {B : Set V}
    (hWfinite : G.HasFiniteCharacter W)
    (hTfinite : G.HasFiniteCharacter T)
    (hinitial : G.initialSet W = G.source)
    (hB : B ⊆ G.source)
    (hforward : G.ForwardExtension W T)
    (hPending : LinksToTarget G T
      (G.initialSet (selectedPending G W B))) :
    LinksToTarget G T B := by
  let R := selectedRow G W B
  have hRsub : R ⊆ W := selectedRow_subset G W B
  have hRsource : G.initialSet R ⊆ G.source := by
    rw [initialSet_selectedRow hinitial hB]
    exact hB
  have hCompletedW : LinksToTarget G W
      (G.initialSet (completedPart G R)) :=
    linksToTarget_initialSet_completedPart hNorm hRsub hWfinite hRsource
  have hCompletedSource :
      G.initialSet (completedPart G R) ⊆ G.source := by
    rintro x ⟨p, hp, hpx⟩
    exact hRsource ⟨p, hp.1, hpx⟩
  have hCompletedT : LinksToTarget G T
      (G.initialSet (completedPart G R)) :=
    SingularExtension.linksToTarget_of_forwardExtension hNorm
      hCompletedSource
      hCompletedW hforward hTfinite
  have hPendingSource :
      G.initialSet (selectedPending G W B) ⊆ G.source := by
    intro x hx
    apply hB
    rw [← initialSet_completed_union_pending_selectedRow hinitial hB]
    exact Or.inr hx
  have hUnion : LinksToTarget G T
      (G.initialSet (completedPart G R) ∪
        G.initialSet (selectedPending G W B)) :=
    linksToTarget_union_of_normalized hNorm hCompletedSource hPendingSource
      hCompletedT hPending
  rw [initialSet_completed_union_pending_selectedRow hinitial hB] at hUnion
  exact hUnion

end SingularSelectedFreeze
end CardinalInduction
end Erdos599
