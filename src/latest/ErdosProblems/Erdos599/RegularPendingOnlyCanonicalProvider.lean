/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularPendingOnlyCanonicalRecursion
import ErdosProblems.Erdos599.RegularPendingOnlyHistoryBase
import ErdosProblems.Erdos599.RegularDirectPersistentCanonicalSuccessor

/-!
# Canonical provider boundary with pending-only histories

This is the sound scheduler-facing form of the regular source-9.15 step.
The provider is queried only along the canonical recursion.  Its history
base retains tightness and roof containment of the pending row, while the
returned direct selected input contains the genuinely history-sensitive
clean-step certificate.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace RegularPendingOnlyCanonicalProvider

universe u

variable {V : Type u}

/-- Exact geometric output required at one canonical pending-only history. -/
structure Source915Output
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (B : RegularPendingOnlyHistoryBase.HistoryBase
      G L Sigma Z A request i previous) where
  input :
    RegularDirectPersistentCanonicalSuccessor.DirectSelectedSplitInput
      G L Sigma Z A request i previous
  base_eq : input.base = B.base

/-- A source-9.15 output on every recursively generated canonical history.
No assertion is made for unrelated abstract valid histories. -/
def HasSource915Provider
    {kappa : Cardinal.{u}} (G : DWeb V)
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (hL : L.IsLegal) (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (Z : Set V)
    (request : Ladder.Stage kappa → Option ↑(G.source ∩ Z)) : Prop :=
  ∀ (i : Ladder.Stage kappa)
      (previousState : ∀ j : Ladder.Stage kappa, j < i →
        RegularPendingOnlyCanonicalRecursion.CanonicalState
          G L Sigma Z (G.source ∩ Z) request)
      (_hcanonical : ∀ j (hji : j < i),
        RegularPendingOnlyCanonicalRecursion.IsCanonicalAt j
          (fun l hlj ↦ previousState l (lt_trans hlj hji))
          (previousState j hji)),
    let previous :=
      RegularPendingOnlyCanonicalRecursion.projectedHistory i previousState
    let hprevious : ∀ j (hji : j < i),
        RegularCompletedPendingSplice.IsValidRecursiveStage request j
          (fun l hlj ↦ previous l (lt_trans hlj hji))
          (previous j hji) := fun j hji ↦ by
      obtain ⟨S, hS⟩ := _hcanonical j hji
      dsimp only [previous,
        RegularPendingOnlyCanonicalRecursion.projectedHistory]
      rw [hS]
      exact S.payload_valid
    let B := RegularPendingOnlyHistoryBase.historyBase request hNorm
      hUnhindered hL hSigma havoid i previous hprevious
    Nonempty (Source915Output G L Sigma Z (G.source ∩ Z)
      request i previous B)

/-- A canonical-only source-9.15 provider produces the pending-only
canonical stage provider. -/
theorem hasCanonicalStageProvider_of_source915
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    {L : G.KappaLadder kappa} (hL : L.IsLegal)
    {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (request : Ladder.Stage kappa → Option ↑(G.source ∩ Z))
    (hsource915 : HasSource915Provider G hNorm hUnhindered L Sigma
      hL hSigma havoid Z request) :
    RegularPendingOnlyCanonicalRecursion.HasCanonicalStageProvider
      G L Sigma Z (G.source ∩ Z) request := by
  intro i previousState hcanonical
  let previous :=
    RegularPendingOnlyCanonicalRecursion.projectedHistory i previousState
  obtain ⟨O⟩ := hsource915 i previousState hcanonical
  let D := O.input.toDirectInstalledStage
    hNorm hL Set.inter_subset_left
  exact ⟨⟨D⟩⟩

end RegularPendingOnlyCanonicalProvider
end CardinalInduction
end Erdos599
