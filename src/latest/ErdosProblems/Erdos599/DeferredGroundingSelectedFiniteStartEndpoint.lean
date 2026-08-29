/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingStrongSelectedRootPrefix
import ErdosProblems.Erdos599.GroundingErasedEndpointBoundary
import ErdosProblems.Erdos599.TerminalContactSwitchGeometry

/-!
# Exact finite starting endpoint of a final deferred selected route

When the actual final strong-selected auxiliary source represents a finite
record, its decoded route begins at the old terminal of that very record.
This is the non-boundary terminal which a source-correct whole-owner
transaction is allowed to trade.  The result below also extracts the honest
finite alternating compression, with its terminal equal to the request exit.

No switching or realization premise is introduced here: these are literal
properties of the canonical deferred selector and decoder.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
open PopularGroundingBridge GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S
local notation "T" =>
  reservedStrongSelectedRelevantBB (L := L) (hL := hL) (S := S)

/-- If the final selected source represents a finite record, the endpoint
decoder starts exactly at that record's old terminal. -/
theorem reservedStrongSelectedRequestTrace_initial_eq_finish_of_record_eq_finite
    (r : Request J S.cut) (p : FinitePath Gamma.graph)
    (hrecord : (reservedStrongSelectedStartingRecord r).record =
      (.inl p : Gamma.DPath)) :
    (selectedRequestTrace U S K r).initial = p.finish := by
  let R := reservedStrongSelectedStartingRecord r
  let q := strongSelectedPath U S K r
  have hqMem : q ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hqSource : q.start ∈ (J).lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hqMem
  rcases R.represents with ⟨p', hp', hsource⟩ | ⟨i, hi, hsource⟩
  · have hpp : p' = p := by
      exact Sum.inl.inj (hp'.symm.trans hrecord)
    subst p'
    have hstart : q.start = .old p.finish := by
      change (reservedStrongSelectedSource r).1 = .old p.finish
      exact hsource
    cases r with
    | inl x =>
        change ((popularAuxiliaryInput L hL.legal).decodeFinitePathToExit
          q hqSource x.1 _).initial = p.finish
        apply (popularAuxiliaryInput L hL.legal).decodeFinitePathToExit_initial_of_start_old
        exact hstart
    | inr e =>
        change ((popularAuxiliaryInput L hL.legal).decodeFinitePathToEdgeEntry
          q hqSource e.1.1 e.1.2 _).initial = p.finish
        apply (popularAuxiliaryInput L hL.legal).decodeFinitePathToEdgeEntry_initial_of_start_old
        exact hstart
  · obtain ⟨ray, hiray⟩ :=
      (popularAuxiliaryInput L hL.legal).proxy_isRay i
    have himpossible : (Sum.inl p : Gamma.DPath) = .inr ray :=
      hrecord.symm.trans (hi.trans hiray)
    cases himpossible

/-- Exact endpoint data of the finite compressed selected route.  The old
starting terminal lies outside the final relevant boundary, while the
route terminates at the literal request exit. -/
theorem exists_reservedStrongSelected_finiteStartCompression
    (r : Request J S.cut) (p : FinitePath Gamma.graph)
    (hrecord : (reservedStrongSelectedStartingRecord r).record =
      (.inl p : Gamma.DPath))
    (hne : p.finish ≠ requestExit r) :
    ∃ Q : Alternating.FiniteTrace Gamma.graph,
      (selectedErasedCompression U S K r).path = .finite Q ∧
        Q.initial = p.finish ∧
        Q.terminal = requestExit r ∧
        p.start ∈ Gamma.source ∧
        p.finish ∈ Gamma.terminalFrontier L.limitWarp ∧
        p.finish ∉ T ∧
        (Sum.inl p : Gamma.DPath) ∈
          Gamma.inessentialPaths L.limitWarp := by
  let C := selectedErasedCompression U S K r
  have hCInitial : C.path.initial = p.finish := by
    rw [C.initial_eq]
    exact
      reservedStrongSelectedRequestTrace_initial_eq_finish_of_record_eq_finite
        r p hrecord
  have hCTerminal : C.path.terminal? = some (requestExit r) := C.terminal_eq
  have hpInessential : (Sum.inl p : Gamma.DPath) ∈
      Gamma.inessentialPaths L.limitWarp := by
    rw [← hrecord]
    exact (reservedStrongSelectedStartingRecord r).limit_inessential
  have hpSource : p.start ∈ Gamma.source := by
    simpa only [hrecord, DirectedPath.Path.initial,
      DirectedPath.Path.support] using
        (reservedStrongSelectedStartingRecord_grounded r)
  have hpTerminal : p.finish ∈ Gamma.terminalFrontier L.limitWarp := by
    exact ⟨.inl p, hpInessential.1, rfl⟩
  have hpNotT : p.finish ∉ T := by
    intro hpT
    exact Set.disjoint_left.mp
      (reservedStrongSelectedStartingRecord_disjoint_relevantBB r)
      hpT (by
        rw [hrecord]
        exact p.finish_mem_support)
  cases hpath : C.path with
  | trivial x =>
      have hstart : x = p.finish := by
        simpa [hpath] using hCInitial
      have hfinish : x = requestExit r := by
        exact Option.some.inj (by simpa [hpath] using hCTerminal)
      exact False.elim (hne (hstart.symm.trans hfinish))
  | finite Q =>
      have hinitial : Q.initial = p.finish := by
        rw [hpath] at hCInitial
        simpa only [Alternating.AltPath.initial] using hCInitial
      have hterminal : Q.terminal = requestExit r := by
        rw [hpath] at hCTerminal
        exact Option.some.inj (by
          simpa only [Alternating.AltPath.terminal?] using hCTerminal)
      exact ⟨Q, rfl, hinitial, hterminal, hpSource, hpTerminal,
        hpNotT, hpInessential⟩
  | infinite ray =>
      have himpossible : (none : Option V) = some (requestExit r) := by
        simpa [hpath] using hCTerminal
      cases himpossible

/-- Total source-correct terminal-contact geometry for the actual final
selected route with a finite starting record and an exit at the initial of
a displayed limiting component.  All endpoint conditions are discharged
canonically; the only non-switching cases are the two genuine internal
contact failures. -/
theorem reservedStrongSelected_finiteStart_terminalContactGeometryOutcome
    (r : Request J S.cut) (p : FinitePath Gamma.graph)
    (hrecord : (reservedStrongSelectedStartingRecord r).record =
      (.inl p : Gamma.DPath))
    (Y : Gamma.DPath) (hY : Y ∈ L.limitWarp)
    (hexit : requestExit r = Y.initial)
    (hne : p.finish ≠ requestExit r) :
    ∃ Q : Alternating.FiniteTrace Gamma.graph,
      (selectedErasedCompression U S K r).path = .finite Q ∧
        Q.initial = p.finish ∧
        Q.terminal = requestExit r ∧
        p.finish ∉ T ∧
        Alternating.TerminalContactGeometryOutcome
          L.limitWarp Q (requestExit r) := by
  obtain ⟨Q, hQ, hQInitial, hQTerminal, _hpSource,
    _hpTerminal, hpNotT, _hpInessential⟩ :=
    exists_reservedStrongSelected_finiteStartCompression r p hrecord hne
  have hwarp : Gamma.IsWarp L.limitWarp :=
    (popularAuxiliaryInput L hL.legal).ladder.disjoint
  have hback : Alternating.BackwardLinksOn L.limitWarp (.finite Q) := by
    have h := selectedErasedCompression_backwardLinksOn U S K r
    rw [hQ] at h
    exact h
  have hpMem : (Sum.inl p : Gamma.DPath) ∈ L.limitWarp := by
    rw [← hrecord]
    exact (reservedStrongSelectedStartingRecord r).record_mem_ladder
  have hQInitialMem : Q.initial ∈ Gamma.vertexSet L.limitWarp := by
    exact ⟨.inl p, hpMem, hQInitial ▸ p.finish_mem_support⟩
  have hExitInitial : requestExit r ∈ Gamma.initialSet L.limitWarp := by
    exact ⟨Y, hY, hexit.symm⟩
  have hnoForward : ∀ z,
      (requestExit r, z) ∉
        (Alternating.AltPath.finite Q).directionEdges .forward := by
    intro z hz
    have hno := selectedErasedCompression_noOutgoing_forward_at_requestExit
      U S K r
    apply hno
    refine ⟨z, ?_⟩
    rw [hQ]
    exact hz
  have hneQ : Q.initial ≠ requestExit r := by
    rw [hQInitial]
    exact hne
  have hout := Alternating.finiteSourceTerminalOutcome_of_geometry
    hwarp hback hQInitialMem hExitInitial hneQ hQTerminal hnoForward
  exact ⟨Q, hQ, hQInitial, hQTerminal, hpNotT, hout⟩

#print axioms
  reservedStrongSelectedRequestTrace_initial_eq_finish_of_record_eq_finite
#print axioms exists_reservedStrongSelected_finiteStartCompression
#print axioms
  reservedStrongSelected_finiteStart_terminalContactGeometryOutcome

end Deferred
end KappaLadder
end DWeb
end Erdos599
