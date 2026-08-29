/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantRootNormalization

/-!
# Rooting an escape-free essential first fragment

The relevant-cut normal form puts the initial vertex of an escape-free
essential hanging first fragment in `C_V`.  Such a point cannot be a
grounded finite auxiliary source: its finite-source parent is inessential,
whereas the fragment parent is essential, and the limiting warp is
disjoint.  It is therefore the exit of an old-vertex request and is rooted
by the control-root hypothesis.  This eliminates the
`hangingEssentialTerminal` leaf of the relevant root normal form.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev EssentialRootInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev EssentialRootIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev EssentialRootEdges (T : Set V) : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (EssentialRootIndexed (L := L) (hL := hL) (hground := hground)) S K T

namespace SplitGroundedUnusedRecord

/-- An essential limiting component whose first vertex lies in `C_V` is
rooted by the old-request controls.  The apparent finite-source alternative
would identify an inessential grounded record with the essential component
inside the disjoint limiting warp. -/
theorem essentialFirst_initial_rootedAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (P : (EssentialRootInput (L := L) (hL := hL)).Fragment)
    (hessential : P.parent ∈
      (EssentialRootInput (L := L) (hL := hL)).essentialLadder)
    (hfirst : P.path.initial = P.parent.initial)
    (hCV : P.path.initial ∈ GroundingCut.CV
      (EssentialRootInput (L := L) (hL := hL)) S.cut)
    (hcontrol : ∀ c : ControlRequest
        (EssentialRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ EssentialRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a c.1) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ EssentialRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a P.path.initial := by
  rcases GroundingBBGeometry.mem_CV_finiteSource_or_oldRequestExit hCV with
    hfinite | ⟨r, _hrOld, hrExit⟩
  · have hcut : (PopularAuxiliary.Input.LambdaVertex.old P.path.initial :
        (EssentialRootInput (L := L) (hL := hL)).LV) ∈ S.cut :=
      GroundingCut.mem_CV.mp hCV
    obtain ⟨p, _hpChosen, hpFinish, _hpStart, hpInessential⟩ :=
      R.exists_cutFiniteSource_parent_with_allowed_root hfinite hcut
    have hxFinite : P.path.initial ∈
        _root_.Erdos599.DirectedPath.Path.support
          (.inl p : Gamma.DPath) := by
      change P.path.initial ∈ p.support
      rw [← hpFinish]
      exact p.finish_mem_support
    have hxParent : P.path.initial ∈ P.parent.support := by
      rw [hfirst]
      exact P.parent.initial_mem_support
    have hparentEq : (.inl p : Gamma.DPath) = P.parent :=
      Alternating.DWeb.IsWarp.eq_of_mem_support
        (EssentialRootInput (L := L) (hL := hL)).ladder.disjoint
          hpInessential.1 P.parent_mem hxFinite hxParent
    have hparentInessential : P.parent ∈
        Gamma.inessentialPaths L.limitWarp := hparentEq ▸ hpInessential
    exact (hparentInessential.2 hessential).elim
  · cases r with
    | inl old =>
        simpa only [requestExit, ← hrExit, oldRequestControl_val] using
          hcontrol (oldRequestControl old)
    | inr edge => cases _hrOld

end SplitGroundedUnusedRecord
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.essentialFirst_initial_rootedAt
