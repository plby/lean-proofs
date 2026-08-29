/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualStageReduction
import ErdosProblems.Erdos599.GroundingPointwiseSwitch
import ErdosProblems.Erdos599.SafeSwitchingAssembly

/-!
# The equal-subwarp switching interface

The same-index branch of the repaired Section 8 popularity dichotomy does
not disappear by pressing down.  This file records exactly what it gives
before the global simultaneous switch is constructed.

A stationary equal subwarp contains a path whose source index is a grounded
obstruction stage.  The corresponding original ladder component was selected
at that stage, is grounded, and, by persistence of recorded paths, is an
inessential member of the limiting ladder warp.  Its auxiliary target is a
marker born at the very same stage.

The final section isolates the remaining switch geometry.  A reduced Lambda
route and the switching-safety certificate give an exact finite-character
realization of the decoded switch.  If that realization is a wave and has an
inessential grounded component, essential trimming is an ordinary hindrance.
Neither wavehood nor the existence of such a component follows from raw
edge-set realization alone; those are the precise whole-family obligations
left to the grounding switch.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- The exact original component and same-stage marker exposed by one
grounded member of an equal-index auxiliary subwarp. -/
structure EqualSwitchSeed (L : Gamma.KappaLadder kappa)
    (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target) where
  stage : Ladder.Stage kappa
  auxiliaryPath : FinitePath
    (L.popularAuxiliaryInput hL.legal).lambda.graph
  auxiliary_mem : auxiliaryPath ∈
    ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
  source_index :
    (L.popularAuxiliaryIndexed hL).f
        ⟨auxiliaryPath.start,
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
            auxiliary_mem⟩ = stage
  stage_ground : stage ∈ L.phiGround
  originalPath : Gamma.DPath
  chosen : L.chosen stage = some originalPath
  original_grounded : PopularAuxiliary.IsGroundedPath Gamma originalPath
  original_inessential :
    originalPath ∈ Gamma.inessentialPaths L.limitWarp
  targetMarker : (L.popularAuxiliaryInput hL.legal).targetMarkers
  auxiliary_finish : auxiliaryPath.finish = .old targetMarker.1
  marker_stage : L.markerStage ⟨targetMarker.1, targetMarker.2.1⟩ = stage
  source_description :
    (∃ x : L.finiteTerminalSet,
      auxiliaryPath.start = .old x.1 ∧
        Gamma.terminal? originalPath = some x.1) ∨
    (∃ i : L.groundedInfiniteRecords,
      auxiliaryPath.start = .proxy i ∧ originalPath = i.1)

/-- Every recorded component belongs to the inessential part of the limiting
warp.  This is the final-stage specialization of source Lemma 7.4. -/
theorem recorded_mem_limitWarp_inessential
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {a : Ladder.Stage kappa} {p : Gamma.DPath}
    (hp : L.chosen a = some p) :
    p ∈ Gamma.inessentialPaths L.limitWarp := by
  apply L.recorded_mem_inessential hlegal.recordedPathsPersist hp
  change a.1 + 1 ≤ kappa.ord
  exact (Order.add_one_le_iff).2 a.2

/-- A stationary equal-index subwarp supplies a grounded recorded component
which is already inessential in the limiting ladder warp, together with the
same-stage marker reached by its auxiliary path. -/
theorem exists_equalSwitchSeed_of_stationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    Nonempty (L.EqualSwitchSeed hL P) := by
  let U := L.popularAuxiliaryIndexed hL
  let Q := U.equalSubwarp P
  have hground :=
    L.equalSubwarp_grounded_initialIndices_isStationary hL P hstat
  obtain ⟨a, ⟨p, hp, hpa⟩, haGround⟩ := hground.nonempty
  rcases L.equalSubwarp_path_sameStage hL P hp with
      hfinite | hproxy
  · obtain ⟨x, y, hstart, hfinish, hmarker⟩ := hfinite
    let xs : L.finiteTerminalSet :=
      ⟨x.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet x.2⟩
    have hsourceIndex :
        U.f ⟨p.start, Q.starts_in_source hp⟩ =
          L.finiteTerminalIndex x := by
      have hs :
          U.f ⟨p.start, Q.starts_in_source hp⟩ =
            U.f ⟨.old x.1,
              ((L.popularAuxiliaryInput hL.legal).mem_lambda_source_old
                x.1).2 x.2⟩ := by
        apply congrArg U.f
        exact Subtype.ext hstart
      exact hs
    have hxa : L.finiteTerminalIndex x = a :=
      hsourceIndex.symm.trans hpa
    have hxsa : L.finiteTerminalStage xs = a := hxa
    obtain ⟨_hxPhi, q, hqChosen, hqTerminal⟩ :=
      L.finiteTerminalStage_spec xs
    have hqChosenA : L.chosen a = some q := by
      simpa only [hxsa] using hqChosen
    obtain ⟨r, hrChosen, hrGround⟩ := haGround
    have hqr : q = r := Option.some.inj (hqChosenA.symm.trans hrChosen)
    have hqGround : PopularAuxiliary.IsGroundedPath Gamma q := by
      exact hqr ▸ hrGround
    refine ⟨{
      stage := a
      auxiliaryPath := p
      auxiliary_mem := hp
      source_index := hpa
      stage_ground := ⟨q, hqChosenA, hqGround⟩
      originalPath := q
      chosen := hqChosenA
      original_grounded := hqGround
      original_inessential :=
        L.recorded_mem_limitWarp_inessential hL.legal hqChosenA
      targetMarker := y
      auxiliary_finish := hfinish
      marker_stage := hmarker.trans hxa
      source_description := Or.inl ⟨xs, hstart, hqTerminal⟩ }⟩
  · obtain ⟨i, y, hstart, hfinish, hmarker⟩ := hproxy
    have hsourceIndex :
        U.f ⟨p.start, Q.starts_in_source hp⟩ =
          L.groundedInfiniteStage i := by
      have hs :
          U.f ⟨p.start, Q.starts_in_source hp⟩ =
            U.f ⟨.proxy i,
              (L.popularAuxiliaryInput hL.legal).mem_lambda_source_proxy i⟩ := by
        apply congrArg U.f
        exact Subtype.ext hstart
      exact hs
    have hia : L.groundedInfiniteStage i = a :=
      hsourceIndex.symm.trans hpa
    have hiChosen : L.chosen a = some i.1 := by
      simpa only [hia] using (L.groundedInfiniteStage_spec i).2
    obtain ⟨r, hrChosen, hrGround⟩ := haGround
    have hir : i.1 = r := Option.some.inj (hiChosen.symm.trans hrChosen)
    have hiGround : PopularAuxiliary.IsGroundedPath Gamma i.1 := by
      exact hir ▸ hrGround
    refine ⟨{
      stage := a
      auxiliaryPath := p
      auxiliary_mem := hp
      source_index := hpa
      stage_ground := ⟨i.1, hiChosen, hiGround⟩
      originalPath := i.1
      chosen := hiChosen
      original_grounded := hiGround
      original_inessential :=
        L.recorded_mem_limitWarp_inessential hL.legal hiChosen
      targetMarker := y
      auxiliary_finish := hfinish
      marker_stage := hmarker.trans hia
      source_description := Or.inr ⟨i, hstart, rfl⟩ }⟩

namespace EqualSwitchSeed

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {P : Popular.XSWarp
    (L.popularAuxiliaryInput hL.legal).lambda
    (L.popularAuxiliaryInput hL.legal).lambda.target}

/-- The lossless decoded micro-trace attached to an equal-subwarp seed. -/
noncomputable def trace (E : L.EqualSwitchSeed hL P) :
    (L.popularAuxiliaryInput hL.legal).MicroTrace E.auxiliaryPath :=
  (L.popularAuxiliaryInput hL.legal).decodeFinitePath E.auxiliaryPath
    (((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
      E.auxiliary_mem)
    (((L.popularAuxiliaryIndexed hL).equalSubwarp P).ends_in_target
      E.auxiliary_mem)

/-- The exact positive output required from the per-path switching layer.

`compression` is the reduced maximal-link presentation of the lossless
Lambda trace.  `application_realized` says that its literal switched edge
and singleton data are realized by an honest warp.  The last two fields are
the genuinely global geometric facts: the realization is a wave and has an
inessential grounded component.  The component is not required to be
literally the old recorded path, since switching may splice that path. -/
structure DecodedSwitchedWave (E : L.EqualSwitchSeed hL P) where
  compression :
    (L.popularAuxiliaryInput hL.legal).AlternatingCompression
      E.auxiliaryPath E.trace
  family : Set Gamma.DPath
  application_realized :
    (Alternating.Cyclowarp.application
      (L.popularAuxiliaryInput hL.legal).ladder.paths
      compression.path).RealizedBy family
  isWave : Gamma.IsWave family
  inessentialComponent : Gamma.DPath
  component_inessential :
    inessentialComponent ∈ Gamma.inessentialPaths family

/-- A decoded switched-wave witness realizes not merely the compressed
application, but the literal raw switch data computed from the auxiliary
path. -/
theorem DecodedSwitchedWave.decodedSwitchData_realizedBy
    {E : L.EqualSwitchSeed hL P} (S : E.DecodedSwitchedWave) :
    Alternating.SwitchData.RealizedBy
      ((L.popularAuxiliaryInput hL.legal).decodedSwitchData E.auxiliaryPath)
      S.family := by
  exact S.compression.realizedBy
    (L := L.popularAuxiliaryInput hL.legal) S.family
    S.application_realized

/-- Every inessential component of the switched wave is automatically
grounded, since all members of a wave start in the original source. -/
theorem DecodedSwitchedWave.component_grounded
    {E : L.EqualSwitchSeed hL P} (S : E.DecodedSwitchedWave) :
    PopularAuxiliary.IsGroundedPath Gamma S.inessentialComponent := by
  exact S.isWave.2.1
    ⟨S.inessentialComponent, S.component_inessential.1, rfl⟩

/-- When a decoded equal-subwarp route is reducing, its realized pointwise
switch has the exact source and terminal frontiers predicted by the
edge-balance calculation.  This theorem permits rays in the reference warp.

It still does not say that a family of such pointwise switches is compatible
or that one pointwise switch repairs every hanging component. -/
theorem DecodedSwitchedWave.frontiers_of_reducing
    {E : L.EqualSwitchSeed hL P} (S : E.DecodedSwitchedWave)
    (hSwitch : Alternating.IsSwitchingAlternating
      (L.popularAuxiliaryInput hL.legal).ladder.paths S.compression.path)
    (hx : E.trace.initial ∈ Gamma.terminalFrontier
      (L.popularAuxiliaryInput hL.legal).ladder.paths)
    (hy : E.trace.terminal ∈ Gamma.initialSet
      (L.popularAuxiliaryInput hL.legal).ladder.paths)
    (hxy : E.trace.initial ≠ E.trace.terminal) :
    Gamma.initialSet S.family =
        Gamma.initialSet
          (L.popularAuxiliaryInput hL.legal).ladder.paths \
          {E.trace.terminal} ∧
      Gamma.terminalFrontier S.family =
        Gamma.terminalFrontier
          (L.popularAuxiliaryInput hL.legal).ladder.paths \
          {E.trace.initial} := by
  exact S.compression.realizedBy_frontiers_of_reducing
    hSwitch hx hy hxy S.decodedSwitchData_realizedBy

/-- Formal obstruction to finishing the equal branch by one pointwise
switch.  If the limiting warp has another hanging initial vertex, distinct
from the initial deleted by the reducing switch, exact frontier accounting
shows that the switched realization still starts outside the original
source and hence cannot be a wave. -/
theorem pointwise_realization_not_isWave_of_other_hanging
    (E : L.EqualSwitchSeed hL P)
    (C : (L.popularAuxiliaryInput hL.legal).AlternatingCompression
      E.auxiliaryPath E.trace)
    (hSwitch : Alternating.IsSwitchingAlternating
      (L.popularAuxiliaryInput hL.legal).ladder.paths C.path)
    (hx : E.trace.initial ∈ Gamma.terminalFrontier
      (L.popularAuxiliaryInput hL.legal).ladder.paths)
    (hy : E.trace.terminal ∈ Gamma.initialSet
      (L.popularAuxiliaryInput hL.legal).ladder.paths)
    (hxy : E.trace.initial ≠ E.trace.terminal)
    {W : Set Gamma.DPath}
    (hW : Alternating.SwitchData.RealizedBy
      ((L.popularAuxiliaryInput hL.legal).decodedSwitchData E.auxiliaryPath)
      W)
    {z : V}
    (hzInitial : z ∈ Gamma.initialSet
      (L.popularAuxiliaryInput hL.legal).ladder.paths)
    (hzHanging : z ∉ Gamma.source)
    (hzOther : z ≠ E.trace.terminal) :
    ¬ Gamma.IsWave W := by
  intro hWave
  have hfront := C.realizedBy_frontiers_of_reducing
    hSwitch hx hy hxy hW
  apply hzHanging
  apply hWave.2.1
  rw [hfront.1]
  exact ⟨hzInitial, by simpa using hzOther⟩

/-- The strongest automatic per-path switching consequence currently
available from the decoder.  Under a genuine compression, finite character
of the reference warp, and the switching-ready safety certificate, the raw
decoded switch has an exact finite-warp realization.

For a general ladder limit the finite-character premise need not hold (the
limit may contain rays), so this theorem deliberately does not fabricate it. -/
theorem decodedSwitchData_hasFiniteWarpRealization
    (E : L.EqualSwitchSeed hL P)
    (C : (L.popularAuxiliaryInput hL.legal).AlternatingCompression
      E.auxiliaryPath E.trace)
    (hfinite : Gamma.HasFiniteCharacter
      (L.popularAuxiliaryInput hL.legal).ladder.paths)
    (hsafe : Alternating.IsSwitchingSafe
      (L.popularAuxiliaryInput hL.legal).ladder.paths C.path) :
    Alternating.SwitchData.HasFiniteWarpRealization
      ((L.popularAuxiliaryInput hL.legal).decodedSwitchData
        E.auxiliaryPath) := by
  rw [C.switchData_eq]
  exact Alternating.isSwitchingSafe_hasFiniteWarpRealization
    (L.popularAuxiliaryInput hL.legal).ladder.paths C.path hfinite hsafe

/-- Once the equal-subwarp switch has produced a wave with an inessential
grounded component, essential trimming is an ordinary hindrance. -/
theorem DecodedSwitchedWave.exists_hindrance
    {E : L.EqualSwitchSeed hL P} (S : E.DecodedSwitchedWave) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W :=
  ⟨Gamma.essentialWarpPart S.family,
    essentialWarpPart_isHindrance_of_inessentialPath
      S.isWave S.component_inessential⟩

/-- The equal branch is already finished when the limiting ladder warp is
a wave: the seed's recorded component is inessential in that wave. -/
theorem exists_hindrance_of_limitWarp_isWave
    (E : L.EqualSwitchSeed hL P) (hlimit : Gamma.IsWave L.limitWarp) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W :=
  ⟨Gamma.essentialWarpPart L.limitWarp,
    essentialWarpPart_isHindrance_of_inessentialPath
      hlimit E.original_inessential⟩

end EqualSwitchSeed

/-- Exact reduction of the stationary equal-index branch to the missing
switch geometry.  It is enough to construct the decoded switched wave for
the single grounded seed extracted above; the conclusion is then an
ordinary hindrance in the original web. -/
theorem exists_hindrance_of_stationary_equalSubwarp_of_switch
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source))
    (hswitch : ∀ E : L.EqualSwitchSeed hL P,
      Nonempty E.DecodedSwitchedWave) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  let E := (L.exists_equalSwitchSeed_of_stationary hL P hstat).some
  exact (hswitch E).some.exists_hindrance

/-- Immediate limiting-wave specialization of the equal-index reduction. -/
theorem exists_hindrance_of_stationary_equalSubwarp_of_limitWarp_isWave
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source))
    (hlimit : Gamma.IsWave L.limitWarp) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  let E := (L.exists_equalSwitchSeed_of_stationary hL P hstat).some
  exact E.exists_hindrance_of_limitWarp_isWave hlimit

/-- Applying the repaired popularity dichotomy, the non-separator branch
already carries the exact grounded, inessential same-stage switch seed. -/
theorem popularAuxiliary_equalSwitchSeed_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hmono : L.AuxiliaryNonincreasing hL) :
    (∃ (P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      Nonempty (L.EqualSwitchSeed hL P)) ∨
      Nonempty (Popular.PopularSeparator
        (L.popularAuxiliaryIndexed hL)) := by
  rcases L.popularAuxiliary_equal_or_separator hL hmono with
      ⟨P, hP⟩ | hseparator
  · exact Or.inl ⟨P, L.exists_equalSwitchSeed_of_stationary hL P hP⟩
  · exact Or.inr hseparator

/-- End-to-end equal-branch reduction.  Once the remaining switch geometry
is supplied for every same-index seed, the repaired dichotomy produces
either an ordinary hindrance or the popular separator used by the Section 8
grounding construction. -/
theorem popularAuxiliary_hindrance_or_separator_of_equalSwitch
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hmono : L.AuxiliaryNonincreasing hL)
    (hswitch : ∀
      (P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target)
      (E : L.EqualSwitchSeed hL P),
        Nonempty E.DecodedSwitchedWave) :
    (∃ W : Set Gamma.DPath, Gamma.IsHindrance W) ∨
      Nonempty (Popular.PopularSeparator
        (L.popularAuxiliaryIndexed hL)) := by
  rcases L.popularAuxiliary_equalSwitchSeed_or_separator hL hmono with
      ⟨P, hseed⟩ | hseparator
  · exact Or.inl (hswitch P hseed.some).some.exists_hindrance
  · exact Or.inr hseparator

end KappaLadder
end DWeb
end Erdos599
