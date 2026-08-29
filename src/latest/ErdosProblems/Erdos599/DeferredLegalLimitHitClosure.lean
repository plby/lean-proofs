/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredStageSafeConvexity
import ErdosProblems.Erdos599.DeferredLimitHitClosure
import ErdosProblems.Erdos599.DeferredLadderRoofTransport
import ErdosProblems.Erdos599.HalfwayStageGeometryCore

/-!
# Limit-hit closure from deferred legality alone

The missed-limit-frontier argument is geometric: an essential earlier
prefix extends to the supremum stage; if its limiting owner misses that
frontier, the prefix is inessential there and hence already equals the
literal limiting path.  No identification with a fixed preferred-marker
construction is needed.  Fresh-marker geometry also supplies the old-warp
exclusion required by the deferred bookkeeping contradiction.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder.Deferred

variable {L : Gamma.KappaLadder kappa}

/-- A missed limiting frontier forces the global owner to be inessential
at that very stage. -/
theorem HalfwayGeometry.limitMissIsInessential
    (hL : HalfwayGeometry L) (Sigma : Set (Ladder.Stage kappa))
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp) :
    L.LimitMissIsInessential Sigma p := by
  intro d a hd hdn _hdir ha hmiss
  obtain ⟨c, hc⟩ := hdn
  obtain ⟨q, hq, x, hxp, hxq⟩ :=
    hL.limitWarp_hitStages_essential_prefix hp Sigma c (hd hc)
  obtain ⟨r, hr, hqr⟩ :=
    CardinalInduction.DeferredStageInterval.warpAt_grows_of_le hL (ha.1 hc) q hq.1
  obtain ⟨s, hs, hrs⟩ := hL.exists_limitWarp_owner a ⟨r, hr⟩
  have hxs : x ∈ s.support :=
    Gamma.support_mono_of_extends hrs (Gamma.support_mono_of_extends hqr hxq)
  have hsp : s = p :=
    DWeb.IsWarp.eq_of_mem_support
      (hL.warpStages (Ladder.finalStage kappa)) hs hp hxs hxp
  have hrp : Gamma.Extends r p := hsp ▸ hrs
  have hrIE : r ∈ Gamma.inessentialPaths (L.warpAt a) := by
    apply Gamma.mem_inessentialPaths_of_misses_essentialFrontier hr
    rintro ⟨y, hyEssential, hyr⟩
    apply hmiss
    refine ⟨y, ?_, Gamma.support_mono_of_extends hrp hyr⟩
    rwa [L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages a]
  have hrFinal : r ∈ L.limitWarp := hL.mem_limitWarp_of_mem_inessential hrIE
  have hrEq : r = p :=
    DWeb.IsWarp.eq_of_mem_support
      (hL.warpStages (Ladder.finalStage kappa)) hrFinal hp
      (Gamma.support_mono_of_extends hqr hxq) hxp
  exact hrEq ▸ hrIE

theorem HalfwayGeometry.limitMissesAreInessential
    (hL : HalfwayGeometry L) (Sigma : Set (Ladder.Stage kappa)) :
    LimitMissesAreInessential Gamma L Sigma :=
  fun _ hp ↦ hL.limitMissIsInessential Sigma hp

/-- The one-sided marker law excludes the current frontier roof. -/
theorem HalfwayGeometry.marker_not_mem_roof_frontier
    (hL : HalfwayGeometry L) {a : Ladder.Stage kappa} {y : V}
    (hy : L.marker a = some y) : y ∉ Gamma.roof (L.frontier a) :=
  hL.markerOutsideRoof a y hy

/-- Current marker exclusion follows from fresh candidates and current
self-roofing, not from a separate canonical-ladder assumption. -/
theorem HalfwayGeometry.markersOutsideCurrentWarp
    (hL : HalfwayGeometry L) : MarkersOutsideCurrentWarp Gamma L := by
  intro a y hy hyCurrent
  apply hL.marker_not_mem_roof_frontier hy
  have hroof := vertexSet_warpAt_subset_roof_terminalFrontier hL a hyCurrent
  simpa only [L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages a,
    Gamma.roof_essential] using hroof

/-- The complete corrected limit-hit theorem for a club avoiding the
deferred obstruction set. -/
theorem HalfwayGeometry.limitHitClosure
    (hL : HalfwayGeometry L) (Sigma : Set (Ladder.Stage kappa))
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma (phi L)) :
    LimitHitClosure Gamma L Sigma :=
  limitHitClosure_of_club hL Sigma hSigma hL.markersOutsideCurrentWarp
    (hL.limitMissesAreInessential Sigma) havoid

#print axioms HalfwayGeometry.limitMissIsInessential
#print axioms HalfwayGeometry.limitHitClosure

end DWeb.KappaLadder.Deferred

namespace Blueprint.LinkageBlueprint.ClubStageGeometry

variable {Y : Set Gamma.DPath} {theta : Cardinal.{u}}

/-- The club-stage package already contains every hypothesis of limit-hit
closure; callers need not supply this continuity theorem again. -/
theorem limitHitClosure (C : ClubStageGeometry Gamma Y kappa theta) :
    DWeb.KappaLadder.Deferred.LimitHitClosure Gamma C.ladder C.club :=
  C.legal.limitHitClosure C.club C.club_isClub C.club_avoids_phi

#print axioms limitHitClosure

end Blueprint.LinkageBlueprint.ClubStageGeometry
end Erdos599
