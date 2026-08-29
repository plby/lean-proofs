/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingFreshMarkerMaximal
import ErdosProblems.Erdos599.SplitGroundingFreshEqualSelection
import ErdosProblems.Erdos599.SplitGroundingEqualTargetComponent

/-!
# The fresh equal-index branch is empty

For a canonical split ladder, an equal auxiliary route whose source index
is genuinely fresh would have to run from either the finite fresh record or
its ray proxy to the marker born at the same stage.  The maximal-rung
exclusions rule out both cases.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- No target-pure member of an equal subwarp can have a genuinely fresh
grounded source index in the canonical ladder. -/
theorem canonicalLadder_no_fresh_equalSubwarp_path
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hL : (canonicalLadder G kappa preferred).IsSplitKappaHindrance)
    (P : Popular.XSWarp
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        hL.legal).lambda
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        hL.legal).lambda.target)
    (p : FinitePath
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        hL.legal).lambda.graph)
    (hp : p ∈
      (((canonicalLadder G kappa preferred).splitPopularAuxiliaryIndexed hL)
        |>.equalSubwarp P).paths)
    (hpure :
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        hL.legal).IsTargetPure p)
    (hfresh :
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryIndexed hL).f
          ⟨p.start,
            (((canonicalLadder G kappa preferred)
              |>.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
                |>.starts_in_source hp⟩ ∈
        (canonicalLadder G kappa preferred).freshInessentialGroundStages) :
    False := by
  let L := canonicalLadder G kappa preferred
  let hlegal : L.IsSplitLegal := hL.legal
  let I := L.splitPopularAuxiliaryInput hlegal
  let U := L.splitPopularAuxiliaryIndexed hL
  let R := U.equalSubwarp P
  let a : Ladder.Stage kappa := U.f ⟨p.start, R.starts_in_source hp⟩
  let afresh : L.freshInessentialGroundStages := ⟨a, hfresh⟩
  have hpSource : p.start ∈ I.lambda.source := R.starts_in_source hp
  rcases L.splitEqualSubwarp_path_sameStage hL P hp with
      ⟨x, y, hstart, hfinish, hstage⟩ |
      ⟨i, y, hstart, hfinish, hstage⟩
  · have hxa : L.finiteTerminalStage x = a := by
      dsimp only [a]
      have hs :
          (⟨p.start, R.starts_in_source hp⟩ : I.lambda.source) =
            ⟨.old x.1, (I.mem_lambda_source_old x.1).2 x.2⟩ :=
        Subtype.ext hstart
      rw [hs]
      rfl
    obtain ⟨q, hqChosen, hqTerminal⟩ :=
      (L.finiteTerminalStage_spec x).2
    have hqChosenA : L.chosen a = some q := by
      rw [← hxa]
      exact hqChosen
    have hqRecord : q = L.freshGroundRecordPath hlegal afresh :=
      Option.some.inj (hqChosenA.symm.trans
        (L.chosen_freshGroundRecordPath hlegal afresh))
    have hmarkerA : L.marker a = some y.1 := by
      rw [← hxa, ← hstage]
      exact L.markerStage_spec ⟨y.1, y.2.1⟩
    cases hrec : L.freshGroundRecordPath hlegal afresh with
    | inl f =>
        have hqf : q = (Sum.inl f : G.DPath) := hqRecord.trans hrec
        have hfx : f.finish = x.1 := by
          rw [hqf] at hqTerminal
          exact Option.some.inj hqTerminal
        exact canonicalLadder_no_freshFinite_equalTargetPureRoute
          preferred hkappa huncountable hNoEnter afresh f hrec p hpSource
          hpure (by simpa only [hfx] using hstart) hfinish hmarkerA y.2
    | inr r =>
        have hqr : q = (Sum.inr r : G.DPath) := hqRecord.trans hrec
        rw [hqr] at hqTerminal
        cases hqTerminal
  · have hia : L.splitInfiniteStage i = a := by
      dsimp only [a]
      have hs :
          (⟨p.start, R.starts_in_source hp⟩ : I.lambda.source) =
            ⟨.proxy i, I.mem_lambda_source_proxy i⟩ :=
        Subtype.ext hstart
      rw [hs]
      rfl
    have hiChosenA : L.chosen a = some i.1 := by
      rw [← hia]
      exact (L.splitInfiniteStage_spec i).2
    have hiRecord : i.1 = L.freshGroundRecordPath hlegal afresh :=
      Option.some.inj (hiChosenA.symm.trans
        (L.chosen_freshGroundRecordPath hlegal afresh))
    obtain ⟨r, hir⟩ := L.splitInfinitePath_isRay hlegal i
    have hrecord : L.freshGroundRecordPath hlegal afresh =
        (Sum.inr r : G.DPath) := by
      change i.1 = (Sum.inr r : G.DPath) at hir
      exact hiRecord.symm.trans hir
    have hmarkerA : L.marker a = some y.1 := by
      rw [← hia, ← hstage]
      exact L.markerStage_spec ⟨y.1, y.2.1⟩
    exact canonicalLadder_no_freshRay_equalTargetPureRoute
      preferred hkappa huncountable hNoEnter afresh r hrecord p hpSource
      hpure i hstart hfinish hia hmarkerA y.2

/-- Consequently the bundled stationary fresh equal selection cannot exist
for the canonical ladder. -/
theorem canonicalLadder_splitReservedStationaryFreshEqualSelection_isEmpty
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hL : (canonicalLadder G kappa preferred).IsSplitKappaHindrance)
    (P : Popular.XSWarp
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        hL.legal).lambda
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        hL.legal).lambda.target) :
    IsEmpty ((canonicalLadder G kappa preferred)
      |>.SplitReservedStationaryFreshEqualSelection hL P) := by
  let L := canonicalLadder G kappa preferred
  let U := L.splitPopularAuxiliaryIndexed hL
  refine ⟨fun S ↦ ?_⟩
  obtain ⟨a, p, hp, hpa⟩ := S.equal_indices_stationary.nonempty
  have hpRoutes : p ∈ S.routes.paths := U.equalPaths_subset S.routes hp
  have hpP : p ∈ (U.equalSubwarp P).paths := S.routes_subset hpRoutes
  apply canonicalLadder_no_fresh_equalSubwarp_path
    preferred hkappa huncountable hNoEnter hL P p hpP
      (S.routes_targetPure p hpRoutes)
  have hs :
      (⟨p.start, (U.equalSubwarp P).starts_in_source hpP⟩ :
        (L.splitPopularAuxiliaryInput hL.legal).lambda.source) =
      ⟨p.start, S.routes.starts_in_source hpRoutes⟩ := Subtype.ext rfl
  rw [hs]
  exact S.routes_fresh p hpRoutes

/-- The canonical geometry-preserving trichotomy therefore has only the
prior-equal and popular-separator alternatives. -/
theorem canonicalLadder_splitPopularAuxiliary_priorEqual_or_separator
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hL : (canonicalLadder G kappa preferred).IsSplitKappaHindrance) :
    (∃ P : Popular.XSWarp
        ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
          hL.legal).lambda
        ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
          hL.legal).lambda.target,
      (∀ p (_hp : p ∈ P.paths),
        ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
          hL.legal).IsTargetPure p) ∧
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf
            ((canonicalLadder G kappa preferred)
              |>.splitPopularAuxiliaryIndexed hL)
            ((((canonicalLadder G kappa preferred)
              |>.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths)
            ((((canonicalLadder G kappa preferred)
              |>.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
                |>.starts_in_source) ∩
          (canonicalLadder G kappa preferred).priorInessentialGroundStages)) ∨
      Nonempty (Popular.PopularSeparator
        ((canonicalLadder G kappa preferred).splitPopularAuxiliaryIndexed hL)) := by
  rcases (canonicalLadder G kappa preferred)
      |>.splitPopularAuxiliary_priorEqual_or_freshSelection_or_separator hL with
      hprior | ⟨P, hPfresh⟩ | hseparator
  · exact Or.inl hprior
  · exact False.elim
      ((canonicalLadder_splitReservedStationaryFreshEqualSelection_isEmpty
        preferred hkappa huncountable hNoEnter hL P).false hPfresh.some)
  · exact Or.inr hseparator

end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.canonicalLadder_no_fresh_equalSubwarp_path
#print axioms
  Erdos599.DWeb.KappaLadder.canonicalLadder_splitPopularAuxiliary_priorEqual_or_separator
