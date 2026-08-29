/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingTargetPureDichotomy
import ErdosProblems.Erdos599.GroundingEqualStageReduction

/-!
# Target-pure equal paths are genuinely successor-new

First-target normalization gives more than weak source--target chronology.
If a same-index auxiliary path started from a record which was already
inessential at its named stage, the record endpoint (or the chosen grounded
ray) would lie in the strict roof of that stage.  Target-pure transport would
then put the terminal marker in the roof of the same frontier, contradicting
freshness of a marker born at that stage.

Thus every index represented by a target-pure equal subwarp belongs to the
genuinely successor-new part of the bookkeeping.  Passing from that conclusion
to the hindrance-rung/new-ray exceptional set requires a separate diagonal
classification theorem; it does not follow from ladder legality alone.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open _root_.Erdos599.DirectedPath Ladder Stationary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- A target-pure member of the equal subwarp cannot have a source index
whose chosen record was already inessential at that stage. -/
theorem targetPure_equalSubwarp_initialIndex_not_prior
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hpure : ∀ p (_hp : p ∈ P.paths),
      (L.popularAuxiliaryInput hL.legal).IsTargetPure p)
    {a : Stage kappa}
    (ha : a ∈ Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source) :
    a ∉ L.priorInessentialRecordStages := by
  let I := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  obtain ⟨p, hp, hpa⟩ := ha
  have hs : p.start ∈ I.lambda.source :=
    (U.equalSubwarp P).starts_in_source hp
  have ht : p.finish ∈ I.lambda.target :=
    (U.equalSubwarp P).ends_in_target hp
  have hpP : p ∈ P.paths := hp.1
  intro haPrior
  rcases L.equalSubwarp_path_sameStage hL P hp with
      ⟨x, y, hstart, hfinish, hstage⟩ |
      ⟨i, y, hstart, hfinish, hstage⟩
  · let xs : L.finiteTerminalSet :=
      ⟨x.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet x.2⟩
    have hindex :
        U.f ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ =
          L.finiteTerminalIndex x := by
      have heq :
          (⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ :
              I.lambda.source) =
            ⟨.old x.1, (I.mem_lambda_source_old x.1).2 x.2⟩ :=
        Subtype.ext hstart
      rw [heq]
      rfl
    have haeq : a = L.finiteTerminalIndex x := hpa.symm.trans hindex
    have hprior : L.finiteTerminalIndex x ∈
        L.priorInessentialRecordStages := haeq ▸ haPrior
    obtain ⟨_hphi, q, hchosen, hterminal⟩ :=
      L.finiteTerminalStage_spec xs
    have hxStrict : x.1 ∈ Gamma.strictRoof
        (L.frontier (L.finiteTerminalIndex x)) :=
      L.priorInessential_finite_terminal_mem_strictRoof_frontier
        hL.legal hprior hchosen hterminal
    have hentry : I.gadgetEntry p.start = some x.1 :=
      (I.start_old_gadget p hstart).1
    have hexit : I.gadgetExit p.finish = some y.1 :=
      (I.finish_old_gadget p hfinish).2
    have hrun : PopularAuxiliary.Input.RunsFromTo x.1 y.1
        (I.decodeWalkSteps p.walk) :=
      I.decodeWalkSteps_runs_from_entry p.walk hentry hexit
    have hyRoof : y.1 ∈ Gamma.roof
        (L.frontier (L.finiteTerminalIndex x)) :=
      hL.legal.targetPure_run_terminal_mem_roof
        (L.finiteTerminalIndex x) p hs (hpure p hpP) hrun hxStrict
    have hmarker : L.marker (L.finiteTerminalIndex x) = some y.1 := by
      rw [← hstage]
      exact L.markerStage_spec ⟨y.1, y.2.1⟩
    exact L.marker_not_mem_roof_frontier hL.legal hmarker hyRoof
  · have hindex :
        U.f ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ =
          L.groundedInfiniteStage i := by
      have heq :
          (⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ :
              I.lambda.source) =
            ⟨.proxy i, I.mem_lambda_source_proxy i⟩ :=
        Subtype.ext hstart
      rw [heq]
      rfl
    have haeq : a = L.groundedInfiniteStage i := hpa.symm.trans hindex
    have hprior : L.groundedInfiniteStage i ∈
        L.priorInessentialRecordStages := haeq ▸ haPrior
    have hchosen : L.chosen (L.groundedInfiniteStage i) = some i.1 :=
      (L.groundedInfiniteStage_spec i).2
    obtain ⟨r, hr⟩ := I.proxy_isRay i
    have hir : (i.1 : Gamma.DPath) = .inr r := by
      simpa [I, KappaLadder.popularAuxiliaryInput,
        KappaLadder.groundedInfinitePath] using hr
    have hsupport : i.1.support ⊆ Gamma.strictRoof
        (L.frontier (L.groundedInfiniteStage i)) := by
      rw [hir]
      exact L.priorInessentialGround_ray_support_subset_strictRoof_frontier
        hL.legal ⟨(L.groundedInfiniteStage_spec i).1.1, hprior⟩
        (by simpa [hir] using hchosen)
    obtain ⟨z, hz, hrun⟩ :=
      I.decodeWalkSteps_runs_from_eq_proxy p.walk hstart
        ((I.finish_old_gadget p hfinish).2)
    have hzStrict : z ∈ Gamma.strictRoof
        (L.frontier (L.groundedInfiniteStage i)) := by
      apply hsupport
      simpa [I, KappaLadder.popularAuxiliaryInput,
        KappaLadder.groundedInfinitePath] using hz
    have hyRoof : y.1 ∈ Gamma.roof
        (L.frontier (L.groundedInfiniteStage i)) :=
      hL.legal.targetPure_run_terminal_mem_roof
        (L.groundedInfiniteStage i) p hs (hpure p hpP) hrun hzStrict
    have hmarker : L.marker (L.groundedInfiniteStage i) = some y.1 := by
      rw [← hstage]
      exact L.markerStage_spec ⟨y.1, y.2.1⟩
    exact L.marker_not_mem_roof_frontier hL.legal hmarker hyRoof

/-- Every ordinal represented by a target-pure equal subwarp is a genuinely
successor-new obstruction stage. -/
theorem targetPure_equalSubwarp_initialIndices_subset_fresh
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hpure : ∀ p (_hp : p ∈ P.paths),
      (L.popularAuxiliaryInput hL.legal).IsTargetPure p) :
    Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ⊆
      L.freshInessentialRecordStages := by
  intro a ha
  exact ⟨L.equalSubwarp_initialIndices_subset_phi hL P ha,
    L.targetPure_equalSubwarp_initialIndex_not_prior hL P hpure ha⟩

/-- Consequently, stationarity of a target-pure equal subwarp forces
stationarily many genuinely successor-new records. -/
theorem freshInessentialRecordStages_isStationary_of_targetPure_equalSubwarp
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hpure : ∀ p (_hp : p ∈ P.paths),
      (L.popularAuxiliaryInput hL.legal).IsTargetPure p)
    (hstat : IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    IsStationaryBelow kappa L.freshInessentialRecordStages := by
  apply hstat.mono
  exact L.targetPure_equalSubwarp_initialIndices_subset_fresh hL P hpure

/-- The entire strong-target side of the first-target dichotomy is absorbed
by the source-faithful fresh-record set.  This is the unconditional high-level
form available before the separate diagonal classifier is supplied. -/
theorem popularAuxiliary_fresh_or_separator_targetPure
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) :
    IsStationaryBelow kappa L.freshInessentialRecordStages ∨
      Nonempty (Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) := by
  rcases L.popularAuxiliary_targetPure_equal_or_separator hL with
      ⟨P, hpure, hstat⟩ | hseparator
  · exact Or.inl
      (L.freshInessentialRecordStages_isStationary_of_targetPure_equalSubwarp
        hL P hpure hstat)
  · exact Or.inr hseparator

end KappaLadder
end DWeb
end Erdos599
