/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureSegmentedRoof

/-!
# Whole-owner normalization of the post-closure interval row

The interval transaction first installs an arbitrary completed linkage on
the exceptional alternating components and retains the canonical interval
row elsewhere.  For later switching arguments it is useful to close that
exchange under the *full* canonical interval reference, including ordinary
owners rooted in the explicit exceptional set.

This file performs exactly that normalization.  It depends on the captured
pair of stages and the already selected safe path, but not on the final
closed set.  The resulting family is again an exact old-to-new linkage, its
changed owner component is `kappa`-small, and its carrier remains under the
captured roof.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace SliceCandidate

open DirectedPath ControlledSlices

universe u

variable {V : Type u}

/-- Whole-component mixing still preserves the full source boundary when
the reference family is absent only on a smaller exceptional set `E0`, all
of which is included in the component seed `E`. -/
theorem componentMixedFamily_isLinkageBetween_of_partial_complement
    (Q : DWeb V) {A B E0 E : Set V} {W Y : Set Q.DPath}
    (hW : IsLinkageBetween Q A B W)
    (hY : IsLinkageBetween Q (A \ E0) B Y)
    (hE0E : E0 ⊆ E) (_hEA : E ⊆ A) :
    IsLinkageBetween Q A B (componentMixedFamily Q W Y E) := by
  let D := exceptionalComponentVertices Q W Y E
  let WL := initialPart Q W D
  let YR := initialPart Q Y Dᶜ
  have hED : E ⊆ D := by
    intro x hx
    exact mem_exceptionalComponentVertices_of_mem Q W Y hx
  have hE0D : E0 ⊆ D := hE0E.trans hED
  have hWLsupport : ∀ p ∈ WL, p.support ⊆ D := by
    intro p hp
    exact path_support_subset_exceptionalComponents_left hW.finiteCharacter
      hp.1 p.initial_mem_support hp.2
  have hYRsupport : ∀ p ∈ YR, Disjoint p.support D := by
    intro p hp
    rw [Set.disjoint_left]
    intro x hxp hxD
    exact hp.2 (path_support_subset_exceptionalComponents_right
      hY.finiteCharacter hp.1 hxp hxD p.initial_mem_support)
  change IsLinkageBetween Q A B (WL ∪ YR)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hpWL | hpYR
    · rcases hq with hqWL | hqYR
      · exact hW.isWarp hpWL.1 hqWL.1 hpq
      · apply Set.disjoint_left.2
        intro x hxp hxq
        exact Set.disjoint_left.1 (hYRsupport q hqYR) hxq
          (hWLsupport p hpWL hxp)
    · rcases hq with hqWL | hqYR
      · apply Set.disjoint_left.2
        intro x hxp hxq
        exact Set.disjoint_left.1 (hYRsupport p hpYR) hxp
          (hWLsupport q hqWL hxq)
      · exact hY.isWarp hpYR.1 hqYR.1 hpq
  · intro p hp
    exact hp.elim
      (fun hpWL ↦ hW.finiteCharacter hpWL.1)
      (fun hpYR ↦ hY.finiteCharacter hpYR.1)
  · rw [Q.initialSet_union, initialSet_initialPart,
      initialSet_initialPart, hW.initialSet_eq, hY.initialSet_eq]
    ext x
    constructor
    · rintro (⟨hxA, _⟩ | ⟨⟨hxA, _hxE0⟩, _⟩)
      · exact hxA
      · exact hxA
    · intro hxA
      by_cases hxD : x ∈ D
      · exact Or.inl ⟨hxA, hxD⟩
      · refine Or.inr ⟨⟨hxA, ?_⟩, hxD⟩
        intro hxE0
        exact hxD (hE0D hxE0)
  · rw [Q.terminalFrontier_union]
    exact Set.union_subset
      (fun _ hx ↦ hW.terminalFrontier_subset
        ⟨hx.choose, hx.choose_spec.1.1, hx.choose_spec.2⟩)
      (fun _ hx ↦ hY.terminalFrontier_subset
        ⟨hx.choose, hx.choose_spec.1.1, hx.choose_spec.2⟩)
  · intro p hp
    rcases hp with hpWL | hpYR
    · exact hW.endpointPure p hpWL.1
    · obtain ⟨q, rfl, hends, hsource⟩ := hY.endpointPure p hpYR.1
      have havoidE0 : Disjoint q.support E0 :=
        (hYRsupport (.inl q) hpYR).mono_right hE0D
      have hsource' : q.support ∩ A = {q.start} := by
        apply Set.Subset.antisymm
        · rintro x ⟨hxq, hxA⟩
          have hxNotE0 : x ∉ E0 := by
            intro hxE0
            exact Set.disjoint_left.1 havoidE0 hxq hxE0
          have hx : x ∈ q.support ∩ (A \ E0) :=
            ⟨hxq, hxA, hxNotE0⟩
          exact hsource ▸ hx
        · intro x hx
          have hx' : x ∈ q.support ∩ (A \ E0) := hsource.symm ▸ hx
          exact ⟨hx'.1, hx'.2.1⟩
      have hends' : q.support ∩ (A ∪ B) = {q.start, q.finish} := by
        apply Set.Subset.antisymm
        · rintro x ⟨hxq, hxA | hxB⟩
          · have hxNotE0 : x ∉ E0 := by
              intro hxE0
              exact Set.disjoint_left.1 havoidE0 hxq hxE0
            exact hends ▸ (⟨hxq, Or.inl ⟨hxA, hxNotE0⟩⟩ :
              x ∈ q.support ∩ ((A \ E0) ∪ B))
          · exact hends ▸ (⟨hxq, Or.inr hxB⟩ :
              x ∈ q.support ∩ ((A \ E0) ∪ B))
        · intro x hx
          have hx' : x ∈ q.support ∩ ((A \ E0) ∪ B) :=
            hends.symm ▸ hx
          exact ⟨hx'.1, hx'.2.elim (fun h ↦ Or.inl h.1) Or.inr⟩
      exact ⟨q, rfl, hends', hsource'⟩

#print axioms componentMixedFamily_isLinkageBetween_of_partial_complement

end SliceCandidate
end CardinalInduction

namespace Blueprint.LinkageBlueprint

open DirectedPath
open _root_.Erdos599.CardinalInduction
open _root_.Erdos599.CardinalInduction.SliceCandidate

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

namespace PostClosureIntervalTransaction

/-- The explicit roots at which the completed interval may differ from the
canonical ordinary interval row.  This depends only on the two captured
stages and the preselected safe path. -/
def wholeOwnerIntervalSeed
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) : Set V :=
  (Rlimit.capturedGeometry.deferredOldStageExceptional ∪ {z}) ∪
    oldStageContactInitials Rlimit.capturedGeometry T.interval.safe

/-- Close the explicit exceptional roots under whole owners of the completed
interval row and the full canonical finite interval reference. -/
def wholeOwnerIntervalComponent
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) : Set V :=
  exceptionalComponentVertices Gamma T.interval.ambientInterval
    T.intervalReference T.wholeOwnerIntervalSeed

/-- The normalized old-to-new row: use the completed interval on the entire
selected owner component and the canonical reference row outside it. -/
def wholeOwnerInterval
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) : Set Gamma.DPath :=
  componentMixedFamily Gamma T.interval.ambientInterval
    T.intervalReference T.wholeOwnerIntervalSeed

theorem wholeOwnerIntervalSeed_subset_exceptionalComponents
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) :
    T.wholeOwnerIntervalSeed ⊆ T.interval.exceptionalComponents := by
  simpa only [wholeOwnerIntervalSeed] using
    T.interval.excludedInitials_subset_exceptional

theorem wholeOwnerIntervalSeed_card_le
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) :
    #T.wholeOwnerIntervalSeed ≤ kappa := by
  exact (Cardinal.mk_subtype_mono
    T.wholeOwnerIntervalSeed_subset_exceptionalComponents).trans
      T.interval.exceptionalComponents_card

theorem wholeOwnerIntervalSeed_subset_oldSlice
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) :
    T.wholeOwnerIntervalSeed ⊆ Rlimit.capturedGeometry.oldSlice := by
  rintro x ((hxExceptional | hxz) | hxContact)
  · exact hxExceptional.1
  · exact Set.mem_singleton_iff.1 hxz ▸ T.interval.source_mem
  · simp only [oldStageContactInitials] at hxContact
    obtain ⟨p, hpMeeting, rfl⟩ := hxContact
    have hpInitial : p.initial ∈
        (Rlimit.capturedGeometry.ladder.stageWeb
          Rlimit.capturedGeometry.oldStage).initialSet
          Rlimit.capturedGeometry.deferredOldStageOrdinaryFamily :=
      ⟨p, hpMeeting.1, rfl⟩
    rw [Rlimit.capturedGeometry.deferredOldStageOrdinaryFamily_isLinkageBetween.initialSet_eq]
      at hpInitial
    exact hpInitial.1

/-- The whole-owner normalized row keeps the exact captured old/new frontier
boundary. -/
theorem wholeOwnerInterval_isLinkageBetween
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) :
    IsLinkageBetween Gamma Rlimit.capturedGeometry.oldSlice
      Rlimit.capturedGeometry.newSlice T.wholeOwnerInterval := by
  apply componentMixedFamily_isLinkageBetween_of_partial_complement Gamma
    T.interval.ambientInterval_linkage
    T.intervalReference_isLinkageBetween
  · intro x hx
    exact Or.inl (Or.inl hx)
  · exact T.wholeOwnerIntervalSeed_subset_oldSlice

/-- The owner component on which normalization changes the row is still
`kappa`-small. -/
theorem wholeOwnerIntervalComponent_card_le
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) :
    #T.wholeOwnerIntervalComponent ≤ kappa := by
  apply lt_succ_iff.mp
  apply mk_exceptionalComponentVertices_lt
    (Cardinal.isRegular_succ C.capacity_infinite)
    (C.capacity_infinite.trans_lt (lt_succ kappa))
    T.interval.ambientInterval_linkage.isWarp
    T.intervalReference_isLinkageBetween.isWarp
    T.interval.ambientInterval_linkage.finiteCharacter
    T.intervalReference_isLinkageBetween.finiteCharacter
  exact lt_succ_iff.mpr T.wholeOwnerIntervalSeed_card_le

/-- Every path of the normalized row comes from one of the two concrete
captured-roof linkages. -/
theorem wholeOwnerInterval_subset_union
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) :
    T.wholeOwnerInterval ⊆
      T.interval.ambientInterval ∪ T.intervalReference := by
  rintro p (hp | hp)
  · exact Or.inl hp.1
  · exact Or.inr hp.1

/-- Whole-owner normalization introduces no vertex beyond the captured
later roof. -/
theorem wholeOwnerInterval_vertices_subset_capturedRoof
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) :
    Gamma.vertexSet T.wholeOwnerInterval ⊆
      Rlimit.capturedGeometry.outerRoof := by
  rintro x ⟨p, hp, hxp⟩
  rcases T.wholeOwnerInterval_subset_union hp with hpW | hpY
  · exact T.interval.ambientInterval_in_outerRoof p hpW hxp
  · exact T.intervalReference_vertices_subset_capturedRoof ⟨p, hpY, hxp⟩

/-- Every normalized-row member meets the captured later frontier only at
its terminal.  Both sides of the whole-owner mixture have this property. -/
theorem wholeOwnerInterval_meetsOnlyAtTerminal
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) :
    SliceSpliceSource.MeetsOnlyAtTerminal Gamma T.wholeOwnerInterval
      Rlimit.capturedGeometry.newSlice := by
  intro p hp x hxp hxSlice
  rcases hp with hpW | hpY
  · exact T.interval.ambientInterval_meetsOnlyAtTerminal p hpW.1 x hxp hxSlice
  · exact T.intervalReference_target_pure p hpY.1 x hxp hxSlice

/-- The scheduled safe front remains a literal member after whole-owner
normalization. -/
theorem front_mem_wholeOwnerInterval
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) :
    (Sum.inl T.interval.front : Gamma.DPath) ∈ T.wholeOwnerInterval := by
  apply Or.inl
  refine ⟨T.interval.front_mem_interval, ?_⟩
  apply mem_exceptionalComponentVertices_of_mem
  change T.interval.front.start ∈ T.wholeOwnerIntervalSeed
  rw [T.interval.front_start]
  exact Or.inl (Or.inr (Set.mem_singleton z))

/-- Any canonical interval-reference member meeting the retained target tail
is rooted in the explicit contact seed.  This is why closing the exchange
under whole owners does not reintroduce a path crossing that tail. -/
theorem intervalReference_initial_mem_wholeOwnerIntervalSeed_of_meets_tail
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure)
    {p : Gamma.DPath} (hp : p ∈ T.intervalReference)
    {x : V} (hxp : x ∈ p.support) (hxTail : x ∈ T.interval.tail.support) :
    p.initial ∈ T.wholeOwnerIntervalSeed := by
  apply Or.inr
  simp only [oldStageContactInitials]
  obtain ⟨pH, hpOrdinary, hpLift⟩ := hp
  refine ⟨pH, ?_, ?_⟩
  refine ⟨hpOrdinary, ?_⟩
  have hpathSafe : (Sum.inl T.interval.path : Gamma.DPath) ∈
      T.interval.safe.ambientFamily := T.interval.path_mem_safe
  rw [T.interval.safe.ambient_eq_lift] at hpathSafe
  obtain ⟨qH, hqSafe, hqLift⟩ := hpathSafe
  refine ⟨qH, hqSafe, ?_⟩
  rw [Set.not_disjoint_iff]
  refine ⟨x, ?_, ?_⟩
  · have hxpLift : x ∈
        (Rlimit.capturedGeometry.ladder.liftStagePath
          Rlimit.capturedGeometry.oldStage pH).support := by
      rw [hpLift]
      exact hxp
    simpa only [Rlimit.capturedGeometry.ladder.support_liftStagePath]
      using hxpLift
  · have hxPath : x ∈ T.interval.path.support :=
      T.interval.tail_support_subset_path hxTail
    have hxqLift : x ∈
        (Rlimit.capturedGeometry.ladder.liftStagePath
          Rlimit.capturedGeometry.oldStage qH).support := by
      rw [hqLift]
      exact hxPath
    simpa only [Rlimit.capturedGeometry.ladder.support_liftStagePath]
      using hxqLift
  simpa only [SliceSegmentCore.liftStagePath_initial] using
    congrArg Path.initial hpLift

/-- The normalized interval still meets the selected ambient target tail
only at the scheduled splice vertex.  The left-family part inherits the
original interval-tail equality; a retained reference member meeting the
tail would have its initial in the switched owner component. -/
theorem wholeOwnerInterval_tail_inter
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) :
    Gamma.vertexSet T.wholeOwnerInterval ∩ T.interval.tail.support =
      {T.interval.front.finish} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨p, hpMixed, hxp⟩, hxTail⟩
    rcases hpMixed with hpW | hpY
    · have hx : x ∈ Gamma.vertexSet T.interval.ambientInterval ∩
          T.interval.tail.support := ⟨⟨p, hpW.1, hxp⟩, hxTail⟩
      rw [T.interval.interval_tail_inter] at hx
      exact hx
    · exfalso
      apply hpY.2
      apply mem_exceptionalComponentVertices_of_mem
      exact T.intervalReference_initial_mem_wholeOwnerIntervalSeed_of_meets_tail
        hpY.1 hxp hxTail
  · intro x hx
    have hxeq : x = T.interval.front.finish := Set.mem_singleton_iff.1 hx
    subst x
    refine ⟨⟨Sum.inl T.interval.front,
      T.front_mem_wholeOwnerInterval, T.interval.front.finish_mem_support⟩, ?_⟩
    rw [← T.interval.tail_start]
    exact T.interval.tail.start_mem_support

#print axioms wholeOwnerInterval_isLinkageBetween
#print axioms wholeOwnerIntervalComponent_card_le
#print axioms wholeOwnerInterval_vertices_subset_capturedRoof
#print axioms wholeOwnerInterval_meetsOnlyAtTerminal
#print axioms front_mem_wholeOwnerInterval
#print axioms
  intervalReference_initial_mem_wholeOwnerIntervalSeed_of_meets_tail
#print axioms wholeOwnerInterval_tail_inter

end PostClosureIntervalTransaction
end Blueprint.LinkageBlueprint
end Erdos599
