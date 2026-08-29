/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayDeferredFrontierHeight
import ErdosProblems.Erdos599.HalfwayTerminalBoundaryClause
import ErdosProblems.Erdos599.HeightRoofBridge

/-!
# Terminal-boundary output at an actual ladder stage

Legal ladder geometry supplies separation, trimmedness, and the bounded
height witness.  Unhinderedness of the selected stage supplies
unhinderedness after quotienting by its essential frontier.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace IndexedTerminalResolutionState
namespace ReachableResolutionRecursor
namespace ResolutionChain

universe u v w

variable {V : Type u} {Gamma : DWeb V}
variable {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder (succ kappa)}
variable {persistent : Set V}
variable {Stage : Type w} [LinearOrder Stage]
variable {slice closure : Stage → Set V}
variable {I : Type v} [LinearOrder I] [Nonempty I]
variable {C : ResolutionChain
  (Gamma := Gamma) (Y := L.limitWarp) (kappa := kappa)
  (persistent := persistent) (B := Gamma.target)
  (slice := slice) (closure := closure) I}
variable {seed : IndexedTerminalResolutionState
  (Gamma := Gamma) (Y := L.limitWarp) (kappa := kappa)
  (persistent := persistent) (B := Gamma.target) slice closure}

namespace FairResolutionLimit

/-- Actual ladder-geometry specialization of the endpoint-independent
terminal-boundary conclusion. -/
theorem exists_localizedTerminalBoundaryHalfway_of_ladder
    (R : FairResolutionLimit C seed)
    (a : Ladder.Stage (succ kappa))
    (hslice : slice R.limit.stageIndex = L.frontier a)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hGamma : Gamma.IsNormalized)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    (hkappa : aleph0 ≤ kappa)
    (hstage : (L.stageWeb a).IsUnhindered)
    {A0 : Set V}
    (hA0source : A0 ⊆ Gamma.source)
    (hA0initial : A0 ⊆ R.limit.blueprint.initialSet) :
    ∃ W : Set Gamma.DPath,
      CardinalInduction.IsSeparatingTerminalBoundaryStopover
        Gamma W (L.frontier a) ∧
      CardinalInduction.LinksToTarget Gamma W A0 ∧
      CardinalInduction.HeightAtMost Gamma (L.frontier a) kappa := by
  obtain ⟨X, ⟨hXsource, Q, hQwave, hroofed⟩, hXcard⟩ :=
    CardinalInduction.DeferredHalfwayFrontierHeight.frontier_heightAtMost
      hGamma hL hkappa a
  have hseparator : Gamma.source ⊆ Gamma.roof (L.frontier a) := by
    rw [L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages a, Gamma.roof_essential]
    exact hL.roofsSourceAtStages (Ladder.Stage.toExtended a)
  have hunhindered : (Gamma.quotient (L.frontier a)).IsUnhindered := by
    let T := Gamma.terminalFrontier (L.warpAt a)
    have hroofT : Gamma.source ⊆ Gamma.roof T :=
      hL.roofsSourceAtStages (Ladder.Stage.toExtended a)
    have hfrontier : L.frontier a = Gamma.essential T :=
      L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages a
    have hquotient : Gamma.quotient (L.frontier a) = Gamma.quotient T := by
      rw [hfrontier]
      exact Gamma.quotient_essential_eq_of_subset_roof T hroofT
    have hsource :
        (Gamma.quotient (L.frontier a)).essentialPart.source =
          (Gamma.quotient (L.frontier a)).source := by
      rw [hquotient]
      have hleft : (Gamma.quotient T).essentialPart.source =
          Gamma.essential T :=
        Gamma.quotientEssentialPart_source_eq_essential_of_roofsSource hroofT
      have hright : (Gamma.quotient T).source = Gamma.essential T := by
        rw [DWeb.quotient_source, Set.union_comm]
        exact RelationalRoof.essential_union_eq_of_subset_roof
          Gamma.graph.Adj Gamma.target hroofT
      exact hleft.trans hright.symm
    have hessential :
        (Gamma.quotient (L.frontier a)).essentialPart.IsUnhindered := by
      rw [hquotient]
      exact hstage
    rw [(Gamma.quotient (L.frontier a)).isUnhindered_iff]
    intro W hW
    let U := CardinalInduction.SliceCandidate.restrictEssentialWarpPartFamily
      (Gamma.quotient (L.frontier a)) W
    have hU : (Gamma.quotient (L.frontier a)).essentialPart.IsWave U :=
      CardinalInduction.SliceCandidate.isWave_restrictEssentialWarpPartFamily
        (Gamma.quotient (L.frontier a)) hW
    have hUinitial :
        (Gamma.quotient (L.frontier a)).essentialPart.initialSet U =
          (Gamma.quotient (L.frontier a)).essentialPart.source :=
      (Gamma.quotient (L.frontier a)).essentialPart.isUnhindered_iff.mp
        hessential U hU
    apply Set.Subset.antisymm hW.2.1
    intro x hx
    have hxEssential :
        x ∈ (Gamma.quotient (L.frontier a)).essentialPart.source :=
      hsource.symm ▸ hx
    have hxInitial :
        x ∈ (Gamma.quotient (L.frontier a)).essentialPart.initialSet U :=
      hUinitial.symm ▸ hxEssential
    obtain ⟨q, ⟨p, rfl⟩, hqx⟩ := hxInitial
    refine ⟨p.1, p.2.1, ?_⟩
    simpa only [CardinalInduction.SliceCandidate.initial_restrictEssentialPartPath]
      using hqx
  exact R.exists_localizedTerminalBoundaryHalfway a hslice hL hGamma
    hinc hkappa hA0source hA0initial
    hseparator
    (hL.frontiersEssential a)
    hunhindered
    X Q hXsource hQwave hroofed hXcard

end FairResolutionLimit
end ResolutionChain
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
