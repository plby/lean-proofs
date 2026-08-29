/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingBBGeometry
import ErdosProblems.Erdos599.GroundingErasedEndpointBoundary
import ErdosProblems.Erdos599.GroundingFiniteSourceBoundary
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# Exact remaining cases for the grounding-boundary antichain

Finite old cut sources and active old requests are sinks of the corrected
switched relation.  This file packages those facts into the precise
reduction needed for the `BB` reachability antichain: only inactive old
requests and blocking points remain.
-/

noncomputable section

open Set

namespace Erdos599

namespace GroundingErasedEndpointBoundary

open Alternating

universe u

variable {V : Type u}

/-- A directed reachability chain starting at a sink is reflexive. -/
theorem eq_of_reflTransGen_of_noOutgoing
    {E : Set (V × V)} {b c : V} (hno : ¬ HasOutgoing E b)
    (hbc : Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) b c) :
    b = c := by
  rcases hbc.cases_head with hbc | ⟨d, hbd, _hdc⟩
  · exact hbc
  · exact False.elim <| hno ⟨d, hbd⟩

end GroundingErasedEndpointBoundary

namespace DWeb.KappaLadder

open Alternating PopularGroundingBridge GroundingErasedDecode
open GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Exact case reduction for the concrete `BB` reachability antichain.
The two premises are the genuinely non-sink cases left by the selected
simultaneous switch: an inactive old control already absorbed by an earlier
active route, and a retained fragment's blocking point. -/
theorem bb_reachabilityAntichain_of_inactiveOld_and_blocking
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (hinactive : ∀ r : oldRequests
        (L.popularAuxiliaryInput hL.legal) S.cut,
      ¬ IsActiveControl (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S) (oldRequestControl r) →
      ∀ c ∈ GroundingCut.BB
          (L.popularAuxiliaryInput hL.legal) S.cut,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges
            (L.popularAuxiliaryIndexed hL) S
              (L.groundedConcreteControls hL S)) r.1 c →
        r.1 = c)
    (hblocking : ∀ P : (L.popularAuxiliaryInput hL.legal).Fragment,
      P ∈ GroundingCut.G0 (L.popularAuxiliaryInput hL.legal) S.cut →
      GroundingCut.IsBlockable
          (L.popularAuxiliaryInput hL.legal) S.cut P →
      ∀ c ∈ GroundingCut.BB
          (L.popularAuxiliaryInput hL.legal) S.cut,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges
            (L.popularAuxiliaryIndexed hL) S
              (L.groundedConcreteControls hL S))
          (GroundingCut.blockingPoint
            (L.popularAuxiliaryInput hL.legal) S.cut P) c →
        GroundingCut.blockingPoint
          (L.popularAuxiliaryInput hL.legal) S.cut P = c) :
    IsReachabilityAntichain
      (erasedSelectedSwitchedEdges (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S))
      (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut) := by
  intro b hb c hc hbc
  rcases GroundingBBGeometry.mem_BB_finiteSourceWithCut_or_oldRequestExit_or_blockingPoint
      hb with ⟨hbFinite, hbCut⟩ | hold | hblock
  · exact GroundingErasedEndpointBoundary.eq_of_reflTransGen_of_noOutgoing
      (L.finiteSource_noOutgoing_switched_of_mem_cut
        hL S hbFinite hbCut) hbc
  · obtain ⟨r, hrAux, hrExit⟩ := hold
    cases r with
    | inl r =>
        have hrb : r.1 = b :=
          PopularAuxiliary.Input.LambdaVertex.old.inj hrAux
        by_cases hrActive : IsActiveControl
            (L.popularAuxiliaryIndexed hL) S
              (L.groundedConcreteControls hL S) (oldRequestControl r)
        · have hno := activeOldRequest_noOutgoing_switched
            (L.popularAuxiliaryIndexed hL) S
              (L.groundedConcreteControls hL S)
              (L.popularAuxiliary_proxyPathsFaithful hL) r hrActive
          exact hrb.symm.trans <|
            GroundingErasedEndpointBoundary.eq_of_reflTransGen_of_noOutgoing
              hno <| by simpa [hrb] using hbc
        · exact hrb.symm.trans <| hinactive r hrActive c hc <| by
            simpa [hrb] using hbc
    | inr r => cases hrAux
  · obtain ⟨P, hP, hPblockable, hPb, _hbSupport⟩ := hblock
    exact hPb.symm.trans <| hblocking P hP hPblockable c hc <| by
      simpa [hPb] using hbc

/-- With the final forward endpoint cut, old requests are sinks whether or
not their controls are active.  Hence the sole remaining concrete
reachability-antichain obligation is the blocking-point case. -/
theorem bb_reachabilityAntichain_of_blocking
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (hblocking : ∀ P : (L.popularAuxiliaryInput hL.legal).Fragment,
      P ∈ GroundingCut.G0 (L.popularAuxiliaryInput hL.legal) S.cut →
      GroundingCut.IsBlockable
          (L.popularAuxiliaryInput hL.legal) S.cut P →
      ∀ c ∈ GroundingCut.BB
          (L.popularAuxiliaryInput hL.legal) S.cut,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges
            (L.popularAuxiliaryIndexed hL) S
              (L.groundedConcreteControls hL S))
          (GroundingCut.blockingPoint
            (L.popularAuxiliaryInput hL.legal) S.cut P) c →
        GroundingCut.blockingPoint
          (L.popularAuxiliaryInput hL.legal) S.cut P = c) :
    IsReachabilityAntichain
      (erasedSelectedSwitchedEdges (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S))
      (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut) := by
  apply L.bb_reachabilityAntichain_of_inactiveOld_and_blocking hL S
  · intro r _hrInactive c _hc hrc
    exact GroundingErasedEndpointBoundary.eq_of_reflTransGen_of_noOutgoing
      (GroundingOldExitOutgoingObstruction.oldRequest_noOutgoing
        (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S) r) hrc
  · exact hblocking

end DWeb.KappaLadder
end Erdos599
