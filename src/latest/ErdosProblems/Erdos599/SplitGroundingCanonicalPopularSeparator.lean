/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingFreshEqualImpossible
import ErdosProblems.Erdos599.SplitGroundingEqualPriorCollision

/-!
# The canonical split auxiliary has a popular separator

The geometry-preserving split of the target-pure alternative has two
equal-index branches.  The genuinely successor-new branch is excluded by
canonical rung maximality.  This file supplies the complementary, purely
chronological exclusion: a target-pure equal route cannot start at a grounded
record which was already inessential in the current stage warp.

Together the two exclusions leave the popular-separator alternative without
any additional provider hypothesis.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Ladder Stationary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A target-pure member of a split equal subwarp cannot be indexed by a
grounded record which was already inessential in the current stage warp. -/
theorem splitTargetPure_equalSubwarp_initialIndex_not_priorGround
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target)
    {p : FinitePath
      (L.splitPopularAuxiliaryInput hL.legal).lambda.graph}
    (hp : p ∈ ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths)
    (hpure : (L.splitPopularAuxiliaryInput hL.legal).IsTargetPure p) :
    (L.splitPopularAuxiliaryIndexed hL).f
        ⟨p.start,
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
            |>.starts_in_source hp⟩ ∉
      L.priorInessentialGroundStages := by
  let I := L.splitPopularAuxiliaryInput hL.legal
  let U := L.splitPopularAuxiliaryIndexed hL
  let R := U.equalSubwarp P
  let a : Stage kappa := U.f ⟨p.start, R.starts_in_source hp⟩
  have hpSource : p.start ∈ I.lambda.source := R.starts_in_source hp
  intro haPriorGround
  have haGround : a ∈ L.phiGround := haPriorGround.1
  have haPrior : a ∈ L.priorInessentialRecordStages := haPriorGround.2
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
    have hxStrict : x.1 ∈ Gamma.strictRoof (L.frontier a) := by
      rw [← hxa]
      exact L.splitPriorInessential_finite_terminal_mem_strictRoof_frontier
        hL.legal (hxa ▸ haPrior) hqChosen hqTerminal
    have hrun : PopularAuxiliary.Input.RunsFromTo x.1 y.1
        (I.decodeWalkSteps p.walk) :=
      I.decodeWalkSteps_runs_from_entry p.walk
        (by rw [hstart]; rfl) (by rw [hfinish]; rfl)
    have hyRoof : y.1 ∈ Gamma.roof (L.frontier a) :=
      hL.legal.splitTargetPure_run_terminal_mem_roof
        a p hpSource hpure hrun hxStrict
    have hmarker : L.marker a = some y.1 := by
      rw [← hxa, ← hstage]
      exact L.markerStage_spec ⟨y.1, y.2.1⟩
    exact L.splitMarker_not_mem_roof_frontier hL.legal hmarker hyRoof
  · have hia : L.splitInfiniteStage i = a := by
      dsimp only [a]
      have hs :
          (⟨p.start, R.starts_in_source hp⟩ : I.lambda.source) =
            ⟨.proxy i, I.mem_lambda_source_proxy i⟩ :=
        Subtype.ext hstart
      rw [hs]
      rfl
    have hiChosen : L.chosen a = some i.1 := by
      rw [← hia]
      exact (L.splitInfiniteStage_spec i).2
    obtain ⟨r, hir⟩ := L.splitInfinitePath_isRay hL.legal i
    have hiRay : (i.1 : Gamma.DPath) = .inr r := by
      exact hir
    obtain ⟨sourcePath, hsourceChosen, hsourceGround⟩ := haGround
    have hsourceEq : sourcePath = i.1 :=
      Option.some.inj (hsourceChosen.symm.trans hiChosen)
    have hrGround : r.initial ∈ Gamma.source := by
      rw [hsourceEq, hiRay] at hsourceGround
      exact hsourceGround
    have hsupport : r.support ⊆ Gamma.strictRoof (L.frontier a) := by
      apply L.splitPriorInessential_grounded_ray_support_subset_strictRoof_frontier
        hL.legal haPrior
      · simpa only [hiRay] using hiChosen
      · exact hrGround
    obtain ⟨z, hzProxy, hrun⟩ :=
      I.decodeWalkSteps_runs_from_eq_proxy p.walk hstart
        (by rw [hfinish]; rfl)
    have hzStrict : z ∈ Gamma.strictRoof (L.frontier a) := by
      apply hsupport
      have hzPath : z ∈
          DirectedPath.Path.support (Sum.inr r : Gamma.DPath) := by
        simpa only [I, KappaLadder.splitPopularAuxiliaryInput,
          KappaLadder.splitInfinitePath, hiRay] using hzProxy
      exact hzPath
    have hyRoof : y.1 ∈ Gamma.roof (L.frontier a) :=
      hL.legal.splitTargetPure_run_terminal_mem_roof
        a p hpSource hpure hrun hzStrict
    have hmarker : L.marker a = some y.1 := by
      rw [← hia, ← hstage]
      exact L.markerStage_spec ⟨y.1, y.2.1⟩
    exact L.splitMarker_not_mem_roof_frontier hL.legal hmarker hyRoof

variable {G : DWeb V}

/-- For a canonical split ladder the normalized auxiliary therefore has an
actual popular separator: both target-pure equal-index alternatives are
impossible. -/
theorem canonicalLadder_splitPopularAuxiliary_popularSeparator_nonempty
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hL : (canonicalLadder G kappa preferred).IsSplitKappaHindrance) :
    Nonempty (Popular.PopularSeparator
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryIndexed hL)) := by
  let L := canonicalLadder G kappa preferred
  rcases canonicalLadder_splitPopularAuxiliary_priorEqual_or_separator
      preferred hkappa huncountable hNoEnter hL with
      ⟨P, hPpure, hprior⟩ | hseparator
  · obtain ⟨a, haInitial, haPriorGround⟩ := hprior.nonempty
    obtain ⟨p, hp, hpa⟩ := haInitial
    have hnot := L.splitTargetPure_equalSubwarp_initialIndex_not_priorGround
      hL P hp (hPpure p ((L.splitPopularAuxiliaryIndexed hL).equalPaths_subset P hp))
    exact False.elim (hnot (hpa ▸ haPriorGround))
  · exact hseparator

end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitTargetPure_equalSubwarp_initialIndex_not_priorGround
#print axioms
  Erdos599.DWeb.KappaLadder.canonicalLadder_splitPopularAuxiliary_popularSeparator_nonempty
