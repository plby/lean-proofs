/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualTerminalCut

/-!
# Final rooted compiler for the split equal branch

All selection, collision, source-omission, incidence, separation, and
antichain facts are internal.  The sole remaining geometric input is that
the selected repaired relation reaches each source-relevant point of the
essential terminal cut from some original source.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open GroundingEqualActiveSelection
open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace SplitReservedStationaryEqualSelection

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {P : Popular.XSWarp
    (L.splitPopularAuxiliaryInput hL.legal).lambda
    (L.splitPopularAuxiliaryInput hL.legal).lambda.target}

/-- Source-root coverage of the source-reachable terminal cut closes the
split equal branch. -/
theorem exists_hindrance_of_sourceRooted
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (hroot : ∀ b ∈ splitReachableTerminalCut L hL,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (L.splitPopularAuxiliaryInput hL.legal) S.routes) a b) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  apply S.parent.exists_hindrance_of_splitReachableTerminalCut_sourceRooted
    S.routes S.decodedCarriers_pairwiseDisjoint S.routes_avoid_reserved
  · intro b hb c hc hbc
    exact splitTerminalCut_isReachabilityAntichain_canonicalErasedRepairedEdges
      L hL S.routes hb.1 hc.1 hbc
  · exact hroot

end SplitReservedStationaryEqualSelection
end KappaLadder
end DWeb
end Erdos599

