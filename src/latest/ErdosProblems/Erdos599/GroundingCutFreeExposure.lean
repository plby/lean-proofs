/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedSwitchRelation
import ErdosProblems.Erdos599.GroundingGroundedRecordTraceReachability

/-!
# Unique exposure of cut-free reference components

The actual strong selection excludes later ordinary and hidden-proxy
contacts with earlier exposed components away from the later apex. If a
component's whole trace avoids the cut, that apex exception is impossible.
These statements concern raw decoded carriers, not loop-erased routes.
-/

noncomputable section

namespace Erdos599.GroundingCutFreeExposure

open Set DirectedPath PopularAuxiliary.Input PopularGroundingBridge
open PopularSwitching GroundingSimultaneousDecode GroundingGroundedRecordTraceReachability

universe u

variable {V I : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : PopularAuxiliary.Input Gamma I}

/-- The actual record represented at a path's source is exposed by that path. -/
theorem represented_mem_exposed {H : Gamma.DPath} (hH : H ∈ L.ladder.paths)
    (p : FinitePath L.lambda.graph) (hrep : Represents L H p.start) :
    H ∈ exposedLadderPaths L p := by
  rcases hrep with ⟨q, howner, hstart⟩ | ⟨i, howner, hstart⟩
  · left
    refine ⟨hH, p.start, p.start_mem_support, ?_⟩
    rw [hstart, old_mem_ladderTrace_iff, howner]
    exact q.finish_mem_support
  · right
    simp [hstart, howner]

variable (U : Popular.KappaIndexed L.lambda kappa)
variable (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)

/-- A cut-free component exposed earlier cannot be exposed later, including
through a starting proxy which has no old gadget on the auxiliary path. -/
theorem not_exposed_later_of_cutFree
    (hfaith : ProxyPathsFaithful L) {H : Gamma.DPath}
    (hcut : Disjoint (ladderTrace L H) S.cut)
    (r s : Request L S.cut)
    (hrs : GroundingAssembly.requestRank U S r < GroundingAssembly.requestRank U S s)
    (hr : H ∈ exposedLadderPaths L (strongSelectedPath U S K r)) :
    H ∉ exposedLadderPaths L (strongSelectedPath U S K s) := by
  rintro (hmet | hproxy)
  · obtain ⟨_hH, z, hzPath, hzTrace⟩ := hmet
    have hmetEarlier : z ∈
        GroundingSimultaneousDecode.metLadderTrace L (strongSelectedPath U S K r) :=
      (mem_metLadderTrace_iff L _ z).2 ⟨H, hr, hzTrace⟩
    have hne : z ≠ requestAuxVertex s := fun h ↦
      Set.disjoint_left.1 hcut hzTrace (h.symm ▸ requestAuxVertex_mem_cut s)
    exact Set.disjoint_left.1
      (strongSelectedPath_avoids_earlier_components U S K r s hrs)
      hzPath ⟨hmetEarlier, by simpa using hne⟩
  · cases hstart : (strongSelectedPath U S K s).start with
    | old x => simp [hstart] at hproxy
    | edge x y => simp [hstart] at hproxy
    | proxy i =>
        have hHi : H = L.proxyPath i := by simpa [hstart] using hproxy
        have htrace : LambdaVertex.old H.initial ∈ ladderTrace L H :=
          (old_mem_ladderTrace_iff L H H.initial).2 H.initial_mem_support
        have hmetEarlier : LambdaVertex.old H.initial ∈
            GroundingSimultaneousDecode.metLadderTrace L (strongSelectedPath U S K r) :=
          (mem_metLadderTrace_iff L _ _).2 ⟨H, hr, htrace⟩
        have hne : LambdaVertex.old H.initial ≠ requestAuxVertex s := fun h ↦
          Set.disjoint_left.1 hcut htrace (h.symm ▸ requestAuxVertex_mem_cut s)
        have hstarting : LambdaVertex.old H.initial ∈
            startingProxyTrace L (strongSelectedPath U S K s) := by
          simpa only [startingProxyTrace, hstart, ← hHi] using htrace
        apply strongSelectedPath_proxy_avoids_earlier_components U S K r s hrs
        rw [certifiedProxyComponentCollidingPaths, dif_pos hfaith]
        exact ⟨strongSelectedPath_mem_controlledRequestFan U S K s,
          .old H.initial, ⟨hmetEarlier, by simpa using hne⟩, hstarting⟩

/-- A component whose whole trace avoids the cut is exposed by at most one request. -/
theorem exposed_request_unique_of_cutFree
    (hfaith : ProxyPathsFaithful L) {H : Gamma.DPath}
    (hcut : Disjoint (ladderTrace L H) S.cut)
    (r s : Request L S.cut)
    (hr : H ∈ exposedLadderPaths L (strongSelectedPath U S K r))
    (hs : H ∈ exposedLadderPaths L (strongSelectedPath U S K s)) : r = s := by
  rcases lt_trichotomy (GroundingAssembly.requestRank U S r)
      (GroundingAssembly.requestRank U S s) with hlt | heq | hgt
  · exact False.elim (not_exposed_later_of_cutFree U S K hfaith hcut r s hlt hr hs)
  · exact (GroundingAssembly.requestRank U S).injective heq
  · exact False.elim (not_exposed_later_of_cutFree U S K hfaith hcut s r hgt hs hr)

/-- A represented cut-free starting owner avoids the entire decoded carrier
of every different selected request. -/
theorem represented_owner_disjoint_other_carrier
    (hfaith : ProxyPathsFaithful L) {H : Gamma.DPath} (hH : H ∈ L.ladder.paths)
    (hcut : Disjoint (ladderTrace L H) S.cut)
    (r s : Request L S.cut) (hrs : r ≠ s)
    (hrep : Represents L H (strongSelectedPath U S K r).start) :
    Disjoint H.support (L.decodedVertexCarrier (strongSelectedPath U S K s)) := by
  apply Set.disjoint_left.2
  intro x hxH hxCarrier
  apply hrs
  apply exposed_request_unique_of_cutFree U S K hfaith hcut r s
  · exact represented_mem_exposed hH _ hrep
  · exact L.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support hfaith
      (strongSelectedPath U S K s)
      ((strongSelectedWarp U S K).starts_in_source ⟨s, rfl⟩) hH hxCarrier hxH

#print axioms exposed_request_unique_of_cutFree
#print axioms represented_owner_disjoint_other_carrier

end Erdos599.GroundingCutFreeExposure
