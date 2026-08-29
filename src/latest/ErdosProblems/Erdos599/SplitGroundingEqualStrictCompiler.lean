/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualCompiler
import ErdosProblems.Erdos599.SplitGroundingEqualStrictSelection

/-!
# Final rooted compiler for the strict split-equal family

The strict collision-free restriction retains the carrier disjointness and
reserved-parent avoidance required by the rooted reachability compiler.  Thus
whole-family absorption only has to root the source-reachable terminal cut in
the repaired relation of `strictRoutes`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open GroundingEqualActiveSelection

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace SplitReservedStationaryEqualSelection

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {P : Popular.XSWarp
    (L.splitPopularAuxiliaryInput hL.legal).lambda
    (L.splitPopularAuxiliaryInput hL.legal).lambda.target}

/-- Source-root coverage in the repaired relation of the strict selected
family closes the split equal branch. -/
theorem strictRoutes_exists_hindrance_of_sourceRooted
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (hroot : ∀ b ∈ splitReachableTerminalCut L hL,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (L.splitPopularAuxiliaryInput hL.legal) S.strictRoutes) a b) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  apply S.parent.exists_hindrance_of_splitReachableTerminalCut_sourceRooted
    S.strictRoutes S.strictRoutes_decodedCarriers_pairwiseDisjoint
      S.strictRoutes_avoid_reserved
  · intro b hb c hc hbc
    exact splitTerminalCut_isReachabilityAntichain_canonicalErasedRepairedEdges
      L hL S.strictRoutes hb.1 hc.1 hbc
  · exact hroot

end SplitReservedStationaryEqualSelection
end KappaLadder
end DWeb
end Erdos599
