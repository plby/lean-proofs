/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedRealization

/-!
# Concrete cases for a pre-stopped root obstruction

The pre-stopped Assertion 8.22 reduction has two honest failure modes.  This
file resolves the unstructured root-failure mode into the three literal
pieces of `BB`: a cut finite source, an old control request, or a blocking
point.  The ordered two-boundary collision remains a separate exchange
obligation.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open GroundingErasedDecode PopularGroundingBridge

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A pre-stopped root obstruction belongs to one of the three concrete
classes used to define the literal boundary `BB`. -/
theorem Assertion822PreStoppedRootObstruction.boundary_cases
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedRootObstruction hL S R) :
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

/-- Concrete repair compiler for the root half of the pre-stopped
construction.  The ordered-boundary callback is kept separate because a
root repair alone cannot make two comparable boundary points orthogonal. -/
theorem assertion822Output_or_hindrance_of_preStoppedRootCaseRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairFinite : ∀ (R : L.UnusedGroundedRecord hL S)
      (o : L.Assertion822PreStoppedRootObstruction hL S R),
      o.boundary ∈ (L.popularAuxiliaryInput hL.legal).finiteSource →
      (PopularAuxiliary.Input.LambdaVertex.old o.boundary :
        (L.popularAuxiliaryInput hL.legal).LV) ∈ S.cut →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairControl : ∀ (R : L.UnusedGroundedRecord hL S)
      (o : L.Assertion822PreStoppedRootObstruction hL S R)
      (c : ControlRequest (L.popularAuxiliaryInput hL.legal) S.cut),
      c.1 = o.boundary →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBlocking : ∀ (R : L.UnusedGroundedRecord hL S)
      (o : L.Assertion822PreStoppedRootObstruction hL S R)
      (P : (L.popularAuxiliaryInput hL.legal).Fragment),
      P ∈ GroundingCut.G0
        (L.popularAuxiliaryInput hL.legal) S.cut →
      GroundingCut.IsBlockable
        (L.popularAuxiliaryInput hL.legal) S.cut P →
      GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = o.boundary →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ R : L.UnusedGroundedRecord hL S,
      L.Assertion822PreStoppedBoundaryObstruction hL S R →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedRepairs' hL S
  · intro R o
    rcases o.boundary_cases with
      hfinite | ⟨c, hc⟩ | ⟨P, hPG0, hPblockable, hP⟩
    · exact repairFinite R o hfinite.1 hfinite.2
    · exact repairControl R o c hc
    · exact repairBlocking R o P hPG0 hPblockable hP
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.boundary_cases
#print axioms Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedRootCaseRepairs
