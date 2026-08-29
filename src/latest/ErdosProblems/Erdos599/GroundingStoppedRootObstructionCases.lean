/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedRealization
import ErdosProblems.Erdos599.GroundingReservedRootProvenance

/-!
# Case split for a stranded stopped-boundary point

The switch stopped at the complete literal boundary has automatic local
geometry, but a later boundary point can be stranded behind an earlier one.
This file classifies such a root obstruction by the three concrete pieces of
`BB`: a cut finite source, an old request control, or a blocking point.

The resulting repair compiler deliberately keeps all three callbacks.  In
particular, the finite-source duplicate exchange does not by itself prove
that old request exits or blocking points remain rooted after full-boundary
stopping.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating PopularGroundingBridge GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Every root obstruction for the switch stopped at the literal `BB` belongs
to exactly one of the three concrete classes used by the grounding decoder.
The alternatives retain the equality with the displayed obstruction vertex,
so a repair can rewrite its `not_rooted` field without reopening `BB`. -/
theorem Assertion822StoppedRootObstruction.boundary_cases
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822StoppedRootObstruction hL S R) :
    (o.boundary ∈ (L.popularAuxiliaryInput hL.legal).finiteSource ∧
      (PopularAuxiliary.Input.LambdaVertex.old o.boundary :
        (L.popularAuxiliaryInput hL.legal).LV) ∈ S.cut) ∨
    (∃ c : ControlRequest
        (L.popularAuxiliaryInput hL.legal) S.cut,
      c.1 = o.boundary) ∨
    ∃ P : (L.popularAuxiliaryInput hL.legal).Fragment,
      P ∈ GroundingCut.G0
        (L.popularAuxiliaryInput hL.legal) S.cut ∧
      GroundingCut.IsBlockable
        (L.popularAuxiliaryInput hL.legal) S.cut P ∧
      GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = o.boundary := by
  rcases
      GroundingBBGeometry.mem_BB_finiteSourceWithCut_or_oldRequestExit_or_blockingPoint
        o.boundary_mem with hfinite | hold | hblocking
  · exact Or.inl hfinite
  · right
    left
    obtain ⟨r, haux, hexit⟩ := hold
    cases r with
    | inl r =>
        refine ⟨oldRequestControl r, ?_⟩
        simpa only [oldRequestControl_val, requestExit] using hexit
    | inr r => cases haux
  · right
    right
    obtain ⟨P, hPG0, hPblockable, hPt, _htSupport⟩ := hblocking
    exact ⟨P, hPG0, hPblockable, hPt⟩

/-- A stranded boundary point is not itself an allowed original source.
Otherwise reflexivity would already supply the prohibited root witness. -/
theorem Assertion822StoppedRootObstruction.boundary_not_mem_allowedSource
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822StoppedRootObstruction hL S R) :
    o.boundary ∉ Gamma.source \ {R.record.initial} := by
  intro hsource
  exact o.not_rooted ⟨o.boundary, hsource, Relation.ReflTransGen.refl⟩

/-- Thus an obstructing boundary point which is an original source must be
the single source reserved by the stationary bookkeeping step. -/
theorem Assertion822StoppedRootObstruction.boundary_eq_reserved_of_mem_source
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822StoppedRootObstruction hL S R)
    (hsource : o.boundary ∈ Gamma.source) :
    o.boundary = R.record.initial := by
  by_contra hne
  exact o.boundary_not_mem_allowedSource ⟨hsource, hne⟩

/-- Three-branch repair compiler for the complete-boundary-stopped switch.
Each callback receives the original obstruction, so it may use the literal
negated reachability statement in addition to the geometric classification. -/
theorem assertion822Output_or_hindrance_of_stoppedRootCaseRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairFinite : ∀ (R : L.UnusedGroundedRecord hL S)
      (o : L.Assertion822StoppedRootObstruction hL S R),
      o.boundary ∈ (L.popularAuxiliaryInput hL.legal).finiteSource →
      (PopularAuxiliary.Input.LambdaVertex.old o.boundary :
        (L.popularAuxiliaryInput hL.legal).LV) ∈ S.cut →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairControl : ∀ (R : L.UnusedGroundedRecord hL S)
      (o : L.Assertion822StoppedRootObstruction hL S R)
      (c : ControlRequest (L.popularAuxiliaryInput hL.legal) S.cut),
      c.1 = o.boundary →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBlocking : ∀ (R : L.UnusedGroundedRecord hL S)
      (o : L.Assertion822StoppedRootObstruction hL S R)
      (P : (L.popularAuxiliaryInput hL.legal).Fragment),
      P ∈ GroundingCut.G0
        (L.popularAuxiliaryInput hL.legal) S.cut →
      GroundingCut.IsBlockable
        (L.popularAuxiliaryInput hL.legal) S.cut P →
      GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = o.boundary →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_stoppedRootRepair hL S
  intro R o
  rcases o.boundary_cases with hfinite | ⟨c, hc⟩ | ⟨P, hPG0, hPblockable, hP⟩
  · exact repairFinite R o hfinite.1 hfinite.2
  · exact repairControl R o c hc
  · exact repairBlocking R o P hPG0 hPblockable hP

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.Assertion822StoppedRootObstruction.boundary_cases
#print axioms Erdos599.DWeb.KappaLadder.Assertion822StoppedRootObstruction.boundary_not_mem_allowedSource
#print axioms Erdos599.DWeb.KappaLadder.Assertion822StoppedRootObstruction.boundary_eq_reserved_of_mem_source
#print axioms Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_stoppedRootCaseRepairs
