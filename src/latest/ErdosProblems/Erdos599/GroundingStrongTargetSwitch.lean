/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualSubwarpSwitch
import ErdosProblems.Erdos599.GroundingErasedDecode

/-!
# The simultaneous strong-target switch

The equal-index branch of the auxiliary popularity dichotomy cannot be
discharged by switching along a single decoded path: another hanging
component of the limiting ladder warp would remain hanging.  The required
object is therefore a simultaneous switch along the whole equal subwarp.

This file fixes the literal graph relation used by that switch.  Each
auxiliary path is decoded, chronologically loop-erased, and maximally
compressed before its retained edges are added to the simultaneous route
set.  Thus the construction never assumes that the raw projected walk is
simple.

The equal subwarp is only the seed of the global switch.  It need not cover
every hanging initial of the limiting ladder warp, so switching exactly its
routes need not produce a wave.  `StrongTargetSwitch` therefore also records
the recursively closed family of alternating routes used by the actual
construction and requires every erased equal-subwarp route to occur in that
family.  Besides realizing the literal symmetric difference along the closed
family, its output starts in the original source, has separating terminal
frontier, and retains an inessential component for every grounded stage
represented by the equal subwarp.  The final theorem proves that a stationary
equal subwarp together with this output yields an ordinary hindrance.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

namespace StrongTargetSwitch

variable (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
  (P : Popular.XSWarp
    (L.popularAuxiliaryInput hL.legal).lambda
    (L.popularAuxiliaryInput hL.legal).lambda.target)

private abbrev Input := L.popularAuxiliaryInput hL.legal

private abbrev EqualWarp :=
  (L.popularAuxiliaryIndexed hL).equalSubwarp P

/-- The lossless signed trace of one member of the equal subwarp. -/
noncomputable def trace
    (p : FinitePath (Input L hL).lambda.graph)
    (hp : p ∈ (EqualWarp L hL P).paths) : (Input L hL).MicroTrace p :=
  (Input L hL).decodeFinitePath p
    ((EqualWarp L hL P).starts_in_source hp)
    ((EqualWarp L hL P).ends_in_target hp)

/-- The canonical simple alternating route obtained from one equal-subwarp
member.  Loop erasure is performed before maximal-run compression. -/
noncomputable def erasedCompression
    (p : FinitePath (Input L hL).lambda.graph)
    (hp : p ∈ (EqualWarp L hL P).paths) :
    PopularAuxiliary.Input.ErasedSignedRoute.ErasedCompression
      (Gamma := Gamma) (trace L hL P p hp).runs.erasedSignedRoute :=
  (trace L hL P p hp).erasedCompression

/-- All retained original-web edges of the loop-erased equal-subwarp
routes.  The proof argument `hp` occurs only to build the certified decoder;
proof irrelevance makes the union independent of its presentation. -/
def routeEdges : Set (V × V) :=
  ⋃ (p : FinitePath (Input L hL).lambda.graph)
    (hp : p ∈ (EqualWarp L hL P).paths),
      (erasedCompression L hL P p hp).path.edgeSet

theorem routeEdges_subset_adj :
    routeEdges L hL P ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  simp only [routeEdges, Set.mem_iUnion] at he
  obtain ⟨p, hp, he⟩ := he
  exact (erasedCompression L hL P p hp).path.edgeSet_subset_adj he

/-- The literal simultaneous symmetric difference with the limiting ladder
warp.  This is an erased relation, rather than the generally unsound union
of all raw decoded walks. -/
def switchedEdges : Set (V × V) :=
  Alternating.edgeSymmDiff
    (Alternating.familyEdges (Input L hL).ladder.paths)
    (routeEdges L hL P)

theorem switchedEdges_subset_adj :
    switchedEdges L hL P ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with he | he
  · exact Alternating.familyEdges_subset_adj
      (Input L hL).ladder.paths he.1
  · exact routeEdges_subset_adj L hL P he.1

/-- Exact graph data of the simultaneous loop-erased equal-subwarp switch. -/
def switchData : Alternating.SwitchData Gamma where
  edges := switchedEdges L hL P
  edges_in_graph := switchedEdges_subset_adj L hL P
  isolated := Alternating.isolatedVertices (Input L hL).ladder.paths

@[simp] theorem switchData_edges :
    (switchData L hL P).edges = switchedEdges L hL P := rfl

@[simp] theorem switchData_isolated :
    (switchData L hL P).isolated =
      Alternating.isolatedVertices (Input L hL).ladder.paths := rfl

/-- Stages represented by the equal subwarp which are grounded obstruction
stages.  Under stationarity of the equal-subwarp initial indices, this set
is stationary by the repaired equal-stage reduction. -/
def groundedStages : Set (Ladder.Stage kappa) :=
  Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
      (EqualWarp L hL P).paths (EqualWarp L hL P).starts_in_source ∩
    L.phiGround

/-- Edge union of a recursively closed family of honest alternating routes.
The equal-subwarp erasures will be required to form a subfamily of `R`. -/
def closedRouteEdges (R : Set (Alternating.AltPath Gamma.graph)) :
    Set (V × V) :=
  ⋃ q ∈ R, q.edgeSet

theorem closedRouteEdges_subset_adj
    (R : Set (Alternating.AltPath Gamma.graph)) :
    closedRouteEdges R ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  simp only [closedRouteEdges, Set.mem_iUnion] at he
  obtain ⟨q, _hq, he⟩ := he
  exact q.edgeSet_subset_adj he

/-- Literal simultaneous switch along a recursively closed route family. -/
def closedSwitchedEdges
    (R : Set (Alternating.AltPath Gamma.graph)) : Set (V × V) :=
  Alternating.edgeSymmDiff
    (Alternating.familyEdges (Input L hL).ladder.paths)
    (closedRouteEdges R)

theorem closedSwitchedEdges_subset_adj
    (R : Set (Alternating.AltPath Gamma.graph)) :
    closedSwitchedEdges L hL R ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with he | he
  · exact Alternating.familyEdges_subset_adj
      (Input L hL).ladder.paths he.1
  · exact closedRouteEdges_subset_adj R he.1

/-- Exact graph data of the recursively closed simultaneous switch. -/
def closedSwitchData
    (R : Set (Alternating.AltPath Gamma.graph)) :
    Alternating.SwitchData Gamma where
  edges := closedSwitchedEdges L hL R
  edges_in_graph := closedSwitchedEdges_subset_adj L hL R
  isolated := Alternating.isolatedVertices (Input L hL).ladder.paths

@[simp] theorem closedSwitchData_edges
    (R : Set (Alternating.AltPath Gamma.graph)) :
    (closedSwitchData L hL R).edges = closedSwitchedEdges L hL R := rfl

@[simp] theorem closedSwitchData_isolated
    (R : Set (Alternating.AltPath Gamma.graph)) :
    (closedSwitchData L hL R).isolated =
      Alternating.isolatedVertices (Input L hL).ladder.paths := rfl

end StrongTargetSwitch

/-- The exact whole-family output required from the simultaneous
equal-subwarp switch.

`seedRoutes_subset` says the simultaneous closure really extends every
canonical loop-erased route supplied by the equal subwarp.  `realized` pins
the output to the literal symmetric difference along that closure, so the
structure cannot be inhabited by an unrelated wave.  The next two fields
are precisely the wave geometry produced after grounding and pruning.
Finally, `componentAt` records the surviving inessential component associated
with every grounded equal stage; stationarity will supply at least one such
stage. -/
structure StrongTargetSwitch
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target) where
  routes : Set (Alternating.AltPath Gamma.graph)
  seedRoutes_subset : ∀
    (p : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph)
    (hp : p ∈ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths),
    (StrongTargetSwitch.erasedCompression L hL P p hp).path ∈ routes
  family : Set Gamma.DPath
  realized : Alternating.SwitchData.RealizedBy
    (StrongTargetSwitch.closedSwitchData L hL routes) family
  initial_subset_source : Gamma.initialSet family ⊆ Gamma.source
  terminalFrontier_isSeparator :
    Popular.IsSeparator Gamma (Gamma.terminalFrontier family)
  componentAt : ∀ a : Ladder.Stage kappa,
    a ∈ StrongTargetSwitch.groundedStages L hL P → Gamma.DPath
  componentAt_inessential : ∀ (a : Ladder.Stage kappa)
    (ha : a ∈ StrongTargetSwitch.groundedStages L hL P),
    componentAt a ha ∈ Gamma.inessentialPaths family

namespace StrongTargetSwitch

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {P : Popular.XSWarp
    (L.popularAuxiliaryInput hL.legal).lambda
    (L.popularAuxiliaryInput hL.legal).lambda.target}

/-- Every canonical erased seed edge is genuinely present in the recursive
closure used by a strong target switch. -/
theorem routeEdges_subset_closedRouteEdges
    (S : L.StrongTargetSwitch hL P) :
    routeEdges L hL P ⊆ closedRouteEdges S.routes := by
  intro e he
  simp only [routeEdges, Set.mem_iUnion] at he
  obtain ⟨p, hp, he⟩ := he
  simp only [closedRouteEdges, Set.mem_iUnion]
  exact ⟨(erasedCompression L hL P p hp).path,
    S.seedRoutes_subset p hp, he⟩

/-- A completed simultaneous equal-subwarp switch is a grounding warp as
soon as one grounded represented stage is available. -/
theorem exists_hindrance_of_groundedStage
    (S : L.StrongTargetSwitch hL P)
    {a : Ladder.Stage kappa}
    (ha : a ∈ groundedStages L hL P) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  exact exists_hindrance_of_groundingWarp
    S.realized.1 S.initial_subset_source S.terminalFrontier_isSeparator
    ⟨S.componentAt a ha, S.componentAt_inessential a ha⟩

/-- Exact simultaneous-switch conclusion for the stationary equal branch.
The repaired equal-stage theorem first intersects the stationary represented
indices with `phiGround`; the switched output then provides an inessential
component at any member of that stationary intersection, and essential
trimming gives an ordinary hindrance. -/
theorem exists_hindrance_of_stationary_equalSubwarp
    (S : L.StrongTargetSwitch hL P)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  have hground :=
    L.equalSubwarp_grounded_initialIndices_isStationary hL P hstat
  obtain ⟨a, ha⟩ := hground.nonempty
  exact S.exists_hindrance_of_groundedStage ha

end StrongTargetSwitch

end KappaLadder
end DWeb
end Erdos599
