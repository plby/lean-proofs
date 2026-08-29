/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredLimitHitClosure

/-!
# The missed-limit-frontier lemma for the canonical deferred ladder

This file discharges the path-local direct-limit premise left explicit in
`DeferredLimitHitClosure`.  The argument is the formal core of source
Lemmas 7.26 and 7.28.  An earlier hit of a final ladder component supplies
an essential component of the earlier accumulated warp.  The genuine
direct-limit chain transports it to the supremum stage.  If the final
component misses the essential frontier there, that transported component
is inessential.  Canonical inessential-path persistence makes it occur
literally in the final warp; final-warp disjointness then identifies it with
the original limiting component.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- A limiting component of the canonical deferred ladder which misses the
frontier at the supremum of a nonempty family of earlier hits is already an
inessential component at that supremum.  This is the path-local form of the
missed-frontier input in source Lemma 7.28. -/
theorem canonicalDeferredLadder_limitMissIsInessential
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular)
    (hkappaUncountable : Cardinal.aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (Sigma : Set (Ladder.Stage kappa))
    {p : G.DPath}
    (hp : p ∈ (canonicalDeferredLadder G kappa preferred).limitWarp) :
    (canonicalDeferredLadder G kappa preferred).LimitMissIsInessential
      Sigma p := by
  let L := canonicalDeferredLadder G kappa preferred
  have hL : HalfwayGeometry L :=
    canonicalDeferredLadder_isDeferredLegal preferred hkappa
      hkappaUncountable hNoEnter
  intro d a hd hdn _hdir ha hmiss
  obtain ⟨c, hc⟩ := hdn
  have hca : c ≤ a := ha.1 hc
  obtain ⟨q, hqEssential, hpq⟩ :=
    hL.limitWarp_hitStages_essential_prefix hp Sigma c (hd hc)
  have hfinalLimit : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hkappa.aleph0_le
  obtain ⟨C, hstage, hlimit⟩ :=
    hL.limitStages (Ladder.finalStage kappa) hfinalLimit
  let ci : Set.Iio kappa.ord := ⟨c.1, c.2⟩
  let ai : Set.Iio kappa.ord := ⟨a.1, a.2⟩
  have hqC : q ∈ C.stage ci := by
    rw [hstage ci]
    exact hqEssential.1
  obtain ⟨r, hrC, hqr⟩ := C.grows (show ci ≤ ai from hca) q hqC
  have hrA : r ∈ L.warpAt a := by
    have hrC' := hrC
    rw [hstage ai] at hrC'
    exact hrC'
  obtain ⟨s, hsC, hrs⟩ := C.grows_limitPaths G ai r hrC
  have hsFinal : s ∈ L.limitWarp := by
    change s ∈ L.accumulated (Ladder.finalStage kappa)
    rw [hlimit]
    exact hsC
  have hspMeet : (s.support ∩ p.support).Nonempty := by
    obtain ⟨x, hxp, hxq⟩ := hpq
    exact ⟨x, G.support_mono_of_extends hrs
      (G.support_mono_of_extends hqr hxq), hxp⟩
  have hsp : s = p := by
    by_contra hne
    obtain ⟨x, hxs, hxp⟩ := hspMeet
    exact Set.disjoint_left.1
      (hL.warpStages (Ladder.finalStage kappa) hsFinal hp hne)
      hxs hxp
  have hrpExtends : G.Extends r p := by
    rwa [hsp] at hrs
  have hmissEssential :
      ¬ (G.essential (G.terminalFrontier (L.warpAt a)) ∩
          p.support).Nonempty := by
    rw [L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages a] at hmiss
    exact hmiss
  have hmissR :
      ¬ (G.essential (G.terminalFrontier (L.warpAt a)) ∩
          r.support).Nonempty := by
    intro hmeet
    obtain ⟨x, hxEssential, hxr⟩ := hmeet
    apply hmissEssential
    exact ⟨x, hxEssential,
      G.support_mono_of_extends hrpExtends hxr⟩
  have hrIE : r ∈ G.inessentialPaths (L.warpAt a) :=
    G.mem_inessentialPaths_of_misses_essentialFrontier hrA hmissR
  have hrFinal : r ∈ G.inessentialPaths L.limitWarp := by
    change r ∈ G.inessentialPaths
      (G.canonicalLadderAccumulated kappa preferred
        (Ladder.finalStage kappa))
    apply canonicalAccumulated_inessential_mono preferred hNoEnter
      (a := Ladder.Stage.toExtended a)
      (b := Ladder.finalStage kappa)
    · exact a.2.le
    · exact hrIE
  have hrpMeet : (r.support ∩ p.support).Nonempty := by
    obtain ⟨x, hxp, hxq⟩ := hpq
    exact ⟨x, G.support_mono_of_extends hqr hxq, hxp⟩
  have hrp : r = p := by
    by_contra hne
    obtain ⟨x, hxr, hxp⟩ := hrpMeet
    exact Set.disjoint_left.1
      (hL.warpStages (Ladder.finalStage kappa) hrFinal.1 hp hne)
      hxr hxp
  rwa [← hrp]

/-- Every limiting component of the canonical deferred ladder satisfies the
missed-frontier premise needed by deferred limit-hit closure. -/
theorem canonicalDeferredLadder_limitMissesAreInessential
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular)
    (hkappaUncountable : Cardinal.aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (Sigma : Set (Ladder.Stage kappa)) :
    LimitMissesAreInessential G
      (canonicalDeferredLadder G kappa preferred) Sigma := by
  intro p hp
  exact canonicalDeferredLadder_limitMissIsInessential
    preferred hkappa hkappaUncountable hNoEnter Sigma hp

end Deferred
end KappaLadder
end DWeb
end Erdos599
