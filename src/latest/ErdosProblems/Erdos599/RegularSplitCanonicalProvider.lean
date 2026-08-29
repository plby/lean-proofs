/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularPersistentSource915Producer
import ErdosProblems.Erdos599.RegularSplitCanonicalHistoryBase
import ErdosProblems.Erdos599.RegularSplitProtectedComparisonAdapter
import ErdosProblems.Erdos599.RegularRoofedAnnularSuccessor

/-!
# The persistent/movable canonical stage provider

This module connects the genuine pending-tight zero/successor/limit history
base to the source-faithful split successor.  The remaining geometric input
is stated only for these certified history bases; it is not quantified over
arbitrary recursive payloads.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularSplitCanonicalProvider

open SingularExtension

universe u

variable {V : Type u}

private theorem transport_slice_union
    {G : DWeb V} {left right U U' : Set V}
    (h : U = U')
    (S : RegularCompletedPendingSplice.CleanTargetSlice G left right U) :
    (h ▸ S).target ∪ (h ▸ S).clean = S.target ∪ S.clean := by
  cases h
  rfl

private theorem transport_freeze_below_roof
    {G : DWeb V} {old T T' : Set G.DPath} {C : Set V}
    (h : T = T') (hcompat : G.StarCompatible (pendingPart G old) T)
    (hroof : G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G old T hcompat) ⊆
        G.roof C) :
    G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G old T'
        (h ▸ hcompat)) ⊆ G.roof C := by
  cases h
  exact hroof

/-- The exact source-9.15 output at a certified weak history base.  The two
equalities record that the local stage uses the canonical persistent/movable
partition of the full required pending-terminal request. -/
structure Source915Output
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (B : RegularSplitCanonicalHistoryBase.HistoryBase
      G L Sigma Z A request i previous) where
  stage : RegularSplitTargetedComparison.SplitTargetedComparisonStage
    G L Sigma Z B.base B.baseStage
      (RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous B.base)
  persistent_eq : stage.persistent =
    RegularPersistentRequestSplit.persistentPart G L
      (RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous B.base)
  movable_eq : stage.movable =
    RegularPersistentRequestSplit.movablePart G L
      (RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous B.base)

/-- Protected-comparison presentation of the same output.  The used family
and the unused suffix shadows are selected together in the genuine residual
web, without identifying deletion followed by quotient with the reverse
order. -/
structure ProtectedSource915Output
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (B : RegularSplitCanonicalHistoryBase.HistoryBase
      G L Sigma Z A request i previous) where
  stage : RegularSplitProtectedComparisonAdapter.ProtectedSplitTargetedComparisonStage
    G L Sigma Z B.base B.baseStage
      (RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous B.base)
  persistent_eq : stage.persistent =
    RegularPersistentRequestSplit.persistentPart G L
      (RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous B.base)
  movable_eq : stage.movable =
    RegularPersistentRequestSplit.movablePart G L
      (RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous B.base)

/-- Minimal source-9.15 output for a canonical roofed history.  The one
weak annular comparison contains both installed tracks, and therefore
proves both clean installation and preservation of the whole-row roof
invariant.  No protected deletion frame or suffix-shadow comparison is
part of this interface. -/
structure RoofedAnnularSource915Output
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (B : RegularSplitCanonicalHistoryBase.HistoryBase
      G L Sigma Z A request i previous) where
  stage :
    RegularSplitProtectedComparisonAdapter.RoofedAnnularSplitTargetedComparisonStage
      G L Sigma Z B.base B.baseStage
        (RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma Z A request i previous B.base)
  persistent_eq : stage.persistent =
    RegularPersistentRequestSplit.persistentPart G L
      (RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous B.base)
  movable_eq : stage.movable =
    RegularPersistentRequestSplit.movablePart G L
      (RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous B.base)

/-- Most general source-9.15 output used by the diagonal weak-split table.
The chosen table request may strictly contain the currently required
coordinates, so the target track is indexed by an arbitrary selected set.
The input itself records that every unselected required coordinate is
linked by the clean track. -/
structure SelectedRoofedSource915Output
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (_B : RegularSplitCanonicalHistoryBase.HistoryBase
      G L Sigma Z A request i previous) where
  input :
    RegularDirectPersistentCanonicalSuccessor.DirectSelectedSplitInput
      G L Sigma Z A request i previous
  result_below_roof : G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G input.base
        (input.slice.target ∪ input.slice.clean) input.compatible) ⊆
    G.roof (L.frontier input.stageIndex)

/-- The exact remaining source-9.15 selection problem on certified
pending-tight histories. -/
def HasProtectedSource915Provider
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A) : Prop :=
  ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
      (_hprevious : ∀ j (hji : j < i),
        RegularCompletedPendingSplice.IsValidRecursiveStage request j
          (fun l hlj ↦ previous l (lt_trans hlj hji))
          (previous j hji))
      (B : RegularSplitCanonicalHistoryBase.HistoryBase
        G L Sigma Z A request i previous),
    Nonempty (ProtectedSource915Output G L Sigma Z A
      request i previous B)

/-- Minimal provider boundary for the canonical whole-row roof invariant.
Only the weak annular comparison and the persistent/movable two-track split
are selected at each certified history. -/
def HasRoofedAnnularSource915Provider
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A) : Prop :=
  ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
      (_hprevious : ∀ j (hji : j < i),
        RegularCompletedPendingSplice.IsValidRecursiveStage request j
          (fun l hlj ↦ previous l (lt_trans hlj hji))
          (previous j hji))
      (B : RegularSplitCanonicalHistoryBase.HistoryBase
        G L Sigma Z A request i previous),
    Nonempty (RoofedAnnularSource915Output G L Sigma Z A
      request i previous B)

/-- Certified-history provider for arbitrary selected target coordinates. -/
def HasSelectedRoofedSource915Provider
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A) : Prop :=
  ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
      (_hprevious : ∀ j (hji : j < i),
        RegularCompletedPendingSplice.IsValidRecursiveStage request j
          (fun l hlj ↦ previous l (lt_trans hlj hji))
          (previous j hji))
      (B : RegularSplitCanonicalHistoryBase.HistoryBase
        G L Sigma Z A request i previous),
    Nonempty (SelectedRoofedSource915Output G L Sigma Z A
      request i previous B)

/-- A source-9.15 split at every certified history base supplies the exact
canonical stage provider used by the completed/pending recursion. -/
theorem hasCanonicalStageProvider_of_source915
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (request : Ladder.Stage kappa → Option ↑(G.source ∩ Z))
    (hsource915 : ∀ (i : Ladder.Stage kappa)
        (previous : ∀ j : Ladder.Stage kappa, j < i →
          RegularCompletedPendingSplice.RecursivePayload
            G L Sigma Z (G.source ∩ Z))
        (hprevious : ∀ j (hji : j < i),
          RegularCompletedPendingSplice.IsValidRecursiveStage request j
            (fun l hlj ↦ previous l (lt_trans hlj hji))
            (previous j hji))
        (B : RegularSplitCanonicalHistoryBase.HistoryBase
          G L Sigma Z (G.source ∩ Z) request i previous),
      Nonempty (Source915Output G L Sigma Z (G.source ∩ Z)
        request i previous B)) :
    RegularSplitCanonicalRecursion.HasCanonicalStageProvider
      G L Sigma Z (G.source ∩ Z) request := by
  intro i previous hcanonical
  let projected := RegularSplitCanonicalRecursion.projectedHistory i previous
  have hprevious : ∀ j (hji : j < i),
      RegularCompletedPendingSplice.IsValidRecursiveStage request j
        (fun l hlj ↦ projected l (lt_trans hlj hji))
        (projected j hji) := by
    intro j hji
    obtain ⟨S, hS⟩ := hcanonical j hji
    dsimp only [projected,
      RegularSplitCanonicalRecursion.projectedHistory]
    rw [hS]
    exact S.payload_valid
  have hrowRoof : ∀ j (hji : j < i),
      G.vertexSet (projected j hji).row ⊆
        G.roof (L.frontier (projected j hji).stageIndex) := by
    intro j hji
    obtain ⟨S, hS⟩ := hcanonical j hji
    dsimp only [projected,
      RegularSplitCanonicalRecursion.projectedHistory]
    rw [hS]
    exact S.result_below_roof
  let B := RegularSplitCanonicalHistoryBase.historyBase request hNorm
    hUnhindered hL hSigma havoid i projected hprevious hrowRoof
  obtain ⟨O⟩ := hsource915 i projected hprevious B
  have hindex : ∀ j (hji : j < i),
      (projected j hji).stageIndex < O.stage.stageIndex := by
    intro j hji
    exact lt_of_le_of_lt (B.index_le_base j hji)
      O.stage.index_lt_stageIndex
  let I := RegularPersistentSource915Producer.persistentSplitInput
    hL B.base_finite B.base_initial B.base_extends B.base_freezes
      B.pending_tight B.pending_below_roof O.stage hindex
        O.persistent_eq O.movable_eq B.old_pending_status
  let D := RegularDirectInstalledStage.DirectInstalledStage.ofInstalledComparisonStage
    (I.toInstalledComparisonStage hNorm hL Set.inter_subset_left)
  have hresult : G.vertexSet D.payload.row ⊆
      G.roof (L.frontier D.stageIndex) := by
    have h := RegularRoofedAnnularSuccessor.freezeCompletedStar_vertexSet_subset_roof_of_annular
      hL O.stage.index_lt_stageIndex B.base_below_roof
        O.stage.comparison_annular O.stage.installed_subset O.stage.compatible
    have hunion : I.slice.target ∪ I.slice.clean =
        O.stage.slice.target ∪ O.stage.slice.clean := by
      exact transport_slice_union O.persistent_eq O.stage.slice
    have h' := transport_freeze_below_roof hunion.symm
      O.stage.compatible h
    change G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G I.base
        (I.slice.target ∪ I.slice.clean) I.compatible) ⊆
          G.roof (L.frontier I.stageIndex)
    change G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G B.base
        (I.slice.target ∪ I.slice.clean) _) ⊆
          G.roof (L.frontier O.stage.stageIndex)
    exact h'
  exact ⟨⟨D, hresult⟩⟩

/-- A minimal roofed-annular stage at every certified history base supplies
the canonical recursion directly.  The recursive roof witness is recovered
from the same annular comparison which proves the clean step. -/
theorem hasCanonicalStageProvider_of_roofedAnnularSource915
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (request : Ladder.Stage kappa → Option ↑(G.source ∩ Z))
    (hsource915 : ∀ (i : Ladder.Stage kappa)
        (previous : ∀ j : Ladder.Stage kappa, j < i →
          RegularCompletedPendingSplice.RecursivePayload
            G L Sigma Z (G.source ∩ Z))
        (hprevious : ∀ j (hji : j < i),
          RegularCompletedPendingSplice.IsValidRecursiveStage request j
            (fun l hlj ↦ previous l (lt_trans hlj hji))
            (previous j hji))
        (B : RegularSplitCanonicalHistoryBase.HistoryBase
          G L Sigma Z (G.source ∩ Z) request i previous),
      Nonempty (RoofedAnnularSource915Output G L Sigma Z
        (G.source ∩ Z) request i previous B)) :
    RegularSplitCanonicalRecursion.HasCanonicalStageProvider
      G L Sigma Z (G.source ∩ Z) request := by
  intro i previous hcanonical
  let projected := RegularSplitCanonicalRecursion.projectedHistory i previous
  have hprevious : ∀ j (hji : j < i),
      RegularCompletedPendingSplice.IsValidRecursiveStage request j
        (fun l hlj ↦ projected l (lt_trans hlj hji))
        (projected j hji) := by
    intro j hji
    obtain ⟨S, hS⟩ := hcanonical j hji
    dsimp only [projected,
      RegularSplitCanonicalRecursion.projectedHistory]
    rw [hS]
    exact S.payload_valid
  have hrowRoof : ∀ j (hji : j < i),
      G.vertexSet (projected j hji).row ⊆
        G.roof (L.frontier (projected j hji).stageIndex) := by
    intro j hji
    obtain ⟨S, hS⟩ := hcanonical j hji
    dsimp only [projected,
      RegularSplitCanonicalRecursion.projectedHistory]
    rw [hS]
    exact S.result_below_roof
  let B := RegularSplitCanonicalHistoryBase.historyBase request hNorm
    hUnhindered hL hSigma havoid i projected hprevious hrowRoof
  obtain ⟨O⟩ := hsource915 i projected hprevious B
  have hindex : ∀ j (hji : j < i),
      (projected j hji).stageIndex < O.stage.stageIndex := by
    intro j hji
    exact lt_of_le_of_lt (B.index_le_base j hji)
      O.stage.index_lt_stageIndex
  let I := O.stage.directPersistentSplitInput
    hL B.base_finite B.base_initial B.base_extends B.base_freezes
      B.pending_tight B.pending_below_roof hindex
        O.persistent_eq O.movable_eq B.old_pending_status
  let D := I.toDirectInstalledStage hNorm hL Set.inter_subset_left
  have hresultOriginal := (O.stage.cleanStep_and_result_below_roof hL).2
  have hunion : (O.persistent_eq ▸ O.stage.slice).target ∪
        (O.persistent_eq ▸ O.stage.slice).clean =
      O.stage.slice.target ∪ O.stage.slice.clean := by
    exact transport_slice_union O.persistent_eq O.stage.slice
  have hresult : G.vertexSet D.payload.row ⊆
      G.roof (L.frontier D.stageIndex) := by
    have h' := transport_freeze_below_roof hunion.symm
      O.stage.compatible hresultOriginal
    simpa only [D, I,
      RegularDirectInstalledStage.DirectInstalledStage.payload,
      RegularDirectPersistentCanonicalSuccessor.DirectPersistentSplitInput.toDirectInstalledStage,
      RegularSplitProtectedComparisonAdapter.RoofedAnnularSplitTargetedComparisonStage.directPersistentSplitInput]
      using h'
  exact ⟨⟨D, hresult⟩⟩

/-- Arbitrary-selected source-9.15 output supplies the canonical recursion.
This is the exact bridge used by the weak diagonal candidate table. -/
theorem hasCanonicalStageProvider_of_selectedRoofedSource915
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (request : Ladder.Stage kappa → Option ↑(G.source ∩ Z))
    (hsource915 : HasSelectedRoofedSource915Provider G L Sigma Z
      (G.source ∩ Z) request) :
    RegularSplitCanonicalRecursion.HasCanonicalStageProvider
      G L Sigma Z (G.source ∩ Z) request := by
  intro i previous hcanonical
  let projected := RegularSplitCanonicalRecursion.projectedHistory i previous
  have hprevious : ∀ j (hji : j < i),
      RegularCompletedPendingSplice.IsValidRecursiveStage request j
        (fun l hlj ↦ projected l (lt_trans hlj hji))
        (projected j hji) := by
    intro j hji
    obtain ⟨S, hS⟩ := hcanonical j hji
    dsimp only [projected,
      RegularSplitCanonicalRecursion.projectedHistory]
    rw [hS]
    exact S.payload_valid
  have hrowRoof : ∀ j (hji : j < i),
      G.vertexSet (projected j hji).row ⊆
        G.roof (L.frontier (projected j hji).stageIndex) := by
    intro j hji
    obtain ⟨S, hS⟩ := hcanonical j hji
    dsimp only [projected,
      RegularSplitCanonicalRecursion.projectedHistory]
    rw [hS]
    exact S.result_below_roof
  let B := RegularSplitCanonicalHistoryBase.historyBase request hNorm
    hUnhindered hL hSigma havoid i projected hprevious hrowRoof
  obtain ⟨O⟩ := hsource915 i projected hprevious B
  let D := O.input.toDirectInstalledStage hNorm hL Set.inter_subset_left
  have hresult : G.vertexSet D.payload.row ⊆
      G.roof (L.frontier D.stageIndex) := by
    simpa only [D,
      RegularDirectInstalledStage.DirectInstalledStage.payload,
      RegularDirectPersistentCanonicalSuccessor.DirectSelectedSplitInput.toDirectInstalledStage]
      using O.result_below_roof
  exact ⟨⟨D, hresult⟩⟩

/-- Protected-comparison form of the canonical provider.  This is the exact
source-9.15 boundary used by the sound global construction: completed
components are protected by unused suffix shadows in one full comparison
warp. -/
theorem hasCanonicalStageProvider_of_protectedSource915
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (request : Ladder.Stage kappa → Option ↑(G.source ∩ Z))
    (hsource915 : ∀ (i : Ladder.Stage kappa)
        (previous : ∀ j : Ladder.Stage kappa, j < i →
          RegularCompletedPendingSplice.RecursivePayload
            G L Sigma Z (G.source ∩ Z))
        (hprevious : ∀ j (hji : j < i),
          RegularCompletedPendingSplice.IsValidRecursiveStage request j
            (fun l hlj ↦ previous l (lt_trans hlj hji))
            (previous j hji))
        (B : RegularSplitCanonicalHistoryBase.HistoryBase
          G L Sigma Z (G.source ∩ Z) request i previous),
      Nonempty (ProtectedSource915Output G L Sigma Z (G.source ∩ Z)
        request i previous B)) :
    RegularSplitCanonicalRecursion.HasCanonicalStageProvider
      G L Sigma Z (G.source ∩ Z) request := by
  intro i previous hcanonical
  let projected := RegularSplitCanonicalRecursion.projectedHistory i previous
  have hprevious : ∀ j (hji : j < i),
      RegularCompletedPendingSplice.IsValidRecursiveStage request j
        (fun l hlj ↦ projected l (lt_trans hlj hji))
        (projected j hji) := by
    intro j hji
    obtain ⟨S, hS⟩ := hcanonical j hji
    dsimp only [projected,
      RegularSplitCanonicalRecursion.projectedHistory]
    rw [hS]
    exact S.payload_valid
  have hrowRoof : ∀ j (hji : j < i),
      G.vertexSet (projected j hji).row ⊆
        G.roof (L.frontier (projected j hji).stageIndex) := by
    intro j hji
    obtain ⟨S, hS⟩ := hcanonical j hji
    dsimp only [projected,
      RegularSplitCanonicalRecursion.projectedHistory]
    rw [hS]
    exact S.result_below_roof
  let B := RegularSplitCanonicalHistoryBase.historyBase request hNorm
    hUnhindered hL hSigma havoid i projected hprevious hrowRoof
  obtain ⟨O⟩ := hsource915 i projected hprevious B
  have hindex : ∀ j (hji : j < i),
      (projected j hji).stageIndex < O.stage.stageIndex := by
    intro j hji
    exact lt_of_le_of_lt (B.index_le_base j hji)
      O.stage.index_lt_stageIndex
  let I := O.stage.persistentSplitInput
    hL B.base_finite B.base_initial B.base_extends B.base_freezes
      B.pending_tight B.pending_below_roof hindex
        O.persistent_eq O.movable_eq B.old_pending_status
  let D := RegularDirectInstalledStage.DirectInstalledStage.ofInstalledComparisonStage
    (I.toInstalledComparisonStage hNorm hL Set.inter_subset_left)
  have hresult : G.vertexSet D.payload.row ⊆
      G.roof (L.frontier D.stageIndex) := by
    have h := RegularRoofedAnnularSuccessor.freezeCompletedStar_vertexSet_subset_roof_of_annular
      hL O.stage.index_lt_stageIndex B.base_below_roof
        O.stage.annularComparison_annular O.stage.installed_subset_annular
          O.stage.compatible
    have hunion : I.slice.target ∪ I.slice.clean =
        O.stage.slice.target ∪ O.stage.slice.clean := by
      exact transport_slice_union O.persistent_eq O.stage.slice
    have h' := transport_freeze_below_roof hunion.symm
      O.stage.compatible h
    change G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G I.base
        (I.slice.target ∪ I.slice.clean) I.compatible) ⊆
          G.roof (L.frontier I.stageIndex)
    change G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G B.base
        (I.slice.target ∪ I.slice.clean) _) ⊆
          G.roof (L.frontier O.stage.stageIndex)
    exact h'
  exact ⟨⟨D, hresult⟩⟩

/-- Abbreviated provider-facing form of
`hasCanonicalStageProvider_of_protectedSource915`. -/
theorem HasProtectedSource915Provider.hasCanonicalStageProvider
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (request : Ladder.Stage kappa → Option ↑(G.source ∩ Z))
    (hsource915 : HasProtectedSource915Provider G L Sigma Z
      (G.source ∩ Z) request) :
    RegularSplitCanonicalRecursion.HasCanonicalStageProvider
      G L Sigma Z (G.source ∩ Z) request :=
  hasCanonicalStageProvider_of_protectedSource915 hNorm hUnhindered hL
    hSigma havoid request hsource915

/-- Abbreviated provider-facing form of
`hasCanonicalStageProvider_of_roofedAnnularSource915`. -/
theorem HasRoofedAnnularSource915Provider.hasCanonicalStageProvider
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (request : Ladder.Stage kappa → Option ↑(G.source ∩ Z))
    (hsource915 : HasRoofedAnnularSource915Provider G L Sigma Z
      (G.source ∩ Z) request) :
    RegularSplitCanonicalRecursion.HasCanonicalStageProvider
      G L Sigma Z (G.source ∩ Z) request :=
  hasCanonicalStageProvider_of_roofedAnnularSource915 hNorm hUnhindered hL
    hSigma havoid request hsource915

/-- Abbreviated arbitrary-selected weak-table provider bridge. -/
theorem HasSelectedRoofedSource915Provider.hasCanonicalStageProvider
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (request : Ladder.Stage kappa → Option ↑(G.source ∩ Z))
    (hsource915 : HasSelectedRoofedSource915Provider G L Sigma Z
      (G.source ∩ Z) request) :
    RegularSplitCanonicalRecursion.HasCanonicalStageProvider
      G L Sigma Z (G.source ∩ Z) request :=
  hasCanonicalStageProvider_of_selectedRoofedSource915 hNorm hUnhindered hL
    hSigma havoid request hsource915

end RegularSplitCanonicalProvider
end CardinalInduction
end Erdos599
