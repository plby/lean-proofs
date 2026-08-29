/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCanonicalLimitBase
import ErdosProblems.Erdos599.RegularCanonicalSource915

/-!
# The unconditional canonical regular-stage provider

This module closes the history-dependent provider boundary.  Earlier
canonical stages retain the strong tight/roof invariant; the zero,
successor, and genuine-limit base constructor preserves it; and the exact
source-9.15 tracked slice constructs the next canonical stage.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularCanonicalProviderFinal

open SliceSpliceSource

universe u

variable {V : Type u}

namespace RegularCanonicalAdmissibleProvider.CanonicalStage

/-- The strong whole-row invariant stored in a canonical producer is the
same invariant on its projected ordinary payload. -/
theorem payload_tight
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : RegularCanonicalAdmissibleProvider.CanonicalStage
      G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized) :
    TightLinkageBetween G A (L.frontier (S.payload hNorm).stageIndex)
      (S.payload hNorm).row := by
  exact S.result_tight

/-- The roof half of the strong invariant also survives payload
projection definitionally. -/
theorem payload_below_roof
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : RegularCanonicalAdmissibleProvider.CanonicalStage
      G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized) :
    G.vertexSet (S.payload hNorm).row ⊆
      G.roof (L.frontier (S.payload hNorm).stageIndex) := by
  exact S.result_below_roof

end RegularCanonicalAdmissibleProvider.CanonicalStage

/-- The exact source-9.15 tables provide the next stage on every certified
canonical history. -/
theorem hasCanonicalStageProvider
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    {L : G.KappaLadder kappa} (hL : L.IsLegal)
    {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (hclosed : SliceSplice.IsLimitWarpClosed G L Z)
    (hslices : SliceCandidate.HasTrackedTightAnnularControlledSlices
      G L Sigma Z)
    (hfirst : ∀ U : Set V,
      U ⊆ L.frontier ⟨0, hL.regular.ord_pos⟩ ∩ Z → #U < kappa →
        ∃ beta ∈ Sigma, ⟨0, hL.regular.ord_pos⟩ < beta ∧
          ∃ T, SliceCandidate.IsTrackedTightAnnularControlledSlice
            G L Z ⟨0, hL.regular.ord_pos⟩ beta U T)
    (request : Ladder.Stage kappa → Option ↑(G.source ∩ Z)) :
    RegularCanonicalAdmissibleProvider.HasCanonicalStageProvider
      G hNorm L Sigma Z (G.source ∩ Z) request := by
  intro i previous hcanonical
  let projected := RegularCanonicalAdmissibleProvider.projectedHistory
    hNorm i previous
  have hprevious : ∀ j (hji : j < i),
      RegularCompletedPendingSplice.IsValidRecursiveStage request j
        (fun l hlj ↦ projected l (lt_trans hlj hji))
        (projected j hji) := by
    intro j hji
    obtain ⟨S, hS⟩ := hcanonical j hji
    dsimp only [projected,
      RegularCanonicalAdmissibleProvider.projectedHistory]
    rw [hS]
    exact S.payload_valid hNorm
  have hstrong : ∀ j (hji : j < i),
      TightLinkageBetween G (G.source ∩ Z)
          (L.frontier (projected j hji).stageIndex) (projected j hji).row ∧
        G.vertexSet (projected j hji).row ⊆
          G.roof (L.frontier (projected j hji).stageIndex) := by
    intro j hji
    obtain ⟨S, hS⟩ := hcanonical j hji
    dsimp only [projected,
      RegularCanonicalAdmissibleProvider.projectedHistory]
    rw [hS]
    exact ⟨RegularCanonicalProviderFinal.RegularCanonicalAdmissibleProvider.CanonicalStage.payload_tight
        S hNorm,
      RegularCanonicalProviderFinal.RegularCanonicalAdmissibleProvider.CanonicalStage.payload_below_roof
        S hNorm⟩
  let B := RegularCanonicalLimitBase.historyBase request hNorm hUnhindered
    hL hSigma havoid i projected hprevious hstrong
  obtain ⟨S⟩ := RegularCanonicalSource915.exists_strongInput
    hNorm hL Set.inter_subset_left hclosed hslices hfirst B
  exact ⟨S.canonicalStage hNorm hL Set.inter_subset_left⟩

end RegularCanonicalProviderFinal
end CardinalInduction
end Erdos599
