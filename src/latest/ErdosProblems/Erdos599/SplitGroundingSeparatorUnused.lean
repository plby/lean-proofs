/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingSelectedNonstationarity
import ErdosProblems.Erdos599.GroundingAssertion822Stationarity

/-!
# The unused grounded record in the split separator branch

The split auxiliary represents every obstruction record, including the
genuine successor same-stage records.  The missing-source argument at the
end of Assertion 8.22 must nevertheless reserve a *grounded* record.  This
file performs that reservation under the exact local invariant supplied by
the grounded side of `phiGround_or_freshSameStage_isStationary`.

The construction is uniform in the control package used by the simultaneous
selector.  In particular it can later be instantiated with the genuine
Assertions 8.19--8.20 controls; it does not rely on the empty compatibility
controls used by the preliminary split incidence compiler.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Stationary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A grounded split record whose canonical auxiliary source is absent from
both the simultaneous selector and the auxiliary sources already contained
in the popular cut. -/
structure SplitUnusedGroundedRecord
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL))
    (K : GroundingSelection.Controls S) where
  stage : Ladder.Stage kappa
  stage_ground : stage ∈ L.phiGround
  stage_unused :
    stage ∉ Popular.initialIndicesOf
      (L.splitPopularAuxiliaryIndexed hL)
      (GroundingSimultaneousDecode.strongSelectedWarp
        (L.splitPopularAuxiliaryIndexed hL) S K).paths
      (GroundingSimultaneousDecode.strongSelectedWarp
        (L.splitPopularAuxiliaryIndexed hL) S K).starts_in_source
  record : Gamma.DPath
  chosen : L.chosen stage = some record
  grounded : PopularAuxiliary.IsGroundedPath Gamma record
  limit_inessential : record ∈ Gamma.inessentialPaths L.limitWarp
  auxiliarySource :
    (L.splitPopularAuxiliaryInput hL.legal).lambda.source
  source_index :
    (L.splitPopularAuxiliaryIndexed hL).f auxiliarySource = stage
  auxiliarySource_not_mem_cut : auxiliarySource.1 ∉ S.cut
  source_represents :
    (∃ p : FinitePath Gamma.graph,
      record = .inl p ∧ auxiliarySource.1 = .old p.finish) ∨
    (∃ i : L.splitInfiniteRecords,
      record = i.1 ∧ auxiliarySource.1 = .proxy i)

/-- Removing the selected and cut-source index sets from a stationary family
of grounded stages leaves a grounded stage of neither kind. -/
theorem exists_splitGroundedStage_not_mem_selected_or_cutSourceInitialIndices
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL))
    (K : GroundingSelection.Controls S)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround) :
    ∃ a : Ladder.Stage kappa,
      a ∈ L.phiGround ∧
      a ∉ Popular.initialIndicesOf
        (L.splitPopularAuxiliaryIndexed hL)
        (GroundingSimultaneousDecode.strongSelectedWarp
          (L.splitPopularAuxiliaryIndexed hL) S K).paths
        (GroundingSimultaneousDecode.strongSelectedWarp
          (L.splitPopularAuxiliaryIndexed hL) S K).starts_in_source ∧
      a ∉ Popular.initialIndicesOf
        (L.splitPopularAuxiliaryIndexed hL)
        (GroundingSimultaneousDecode.sourceCutWarp
          (L.splitPopularAuxiliaryInput hL.legal).lambda S.cut).paths
        (GroundingSimultaneousDecode.sourceCutWarp
          (L.splitPopularAuxiliaryInput hL.legal).lambda S.cut).starts_in_source := by
  let Nselected := Popular.initialIndicesOf
    (L.splitPopularAuxiliaryIndexed hL)
    (GroundingSimultaneousDecode.strongSelectedWarp
      (L.splitPopularAuxiliaryIndexed hL) S K).paths
    (GroundingSimultaneousDecode.strongSelectedWarp
      (L.splitPopularAuxiliaryIndexed hL) S K).starts_in_source
  let NcutSource := Popular.initialIndicesOf
    (L.splitPopularAuxiliaryIndexed hL)
    (GroundingSimultaneousDecode.sourceCutWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda S.cut).paths
    (GroundingSimultaneousDecode.sourceCutWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda S.cut).starts_in_source
  have hselected : ¬ IsStationaryBelow kappa Nselected :=
    GroundingSimultaneousDecode.strongSelectedWarp_initialIndices_nonstationary
      (L.splitPopularAuxiliaryIndexed hL) S K
  have hcutSource : ¬ IsStationaryBelow kappa NcutSource :=
    GroundingSimultaneousDecode.sourceCutWarp_initialIndices_nonstationary
      (L.splitPopularAuxiliaryIndexed hL) S
  have hfirst : IsStationaryBelow kappa (L.phiGround \ Nselected) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      hL.legal.regular hL.legal.uncountable hground hselected
  have hsecond :
      IsStationaryBelow kappa ((L.phiGround \ Nselected) \ NcutSource) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      hL.legal.regular hL.legal.uncountable hfirst hcutSource
  obtain ⟨a, ⟨haGround, haSelected⟩, haCutSource⟩ := hsecond.nonempty
  exact ⟨a, haGround, haSelected, haCutSource⟩

/-- Decode one unused grounded split stage into its selected record and its
canonical source of the all-record split auxiliary. -/
theorem exists_splitUnusedGroundedRecord_at
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL))
    (K : GroundingSelection.Controls S)
    (a : Ladder.Stage kappa) (haGround : a ∈ L.phiGround)
    (haUnused :
      a ∉ Popular.initialIndicesOf
        (L.splitPopularAuxiliaryIndexed hL)
        (GroundingSimultaneousDecode.strongSelectedWarp
          (L.splitPopularAuxiliaryIndexed hL) S K).paths
        (GroundingSimultaneousDecode.strongSelectedWarp
          (L.splitPopularAuxiliaryIndexed hL) S K).starts_in_source)
    (haCutSourceUnused :
      a ∉ Popular.initialIndicesOf
        (L.splitPopularAuxiliaryIndexed hL)
        (GroundingSimultaneousDecode.sourceCutWarp
          (L.splitPopularAuxiliaryInput hL.legal).lambda S.cut).paths
        (GroundingSimultaneousDecode.sourceCutWarp
          (L.splitPopularAuxiliaryInput hL.legal).lambda S.cut).starts_in_source) :
    Nonempty (SplitUnusedGroundedRecord L hL S K) := by
  have haGroundCopy := haGround
  obtain ⟨p, hchosen, hpGround⟩ := haGround
  have haPhi : a ∈ L.phi :=
    (L.bookkeeping.mem_phi_iff_exists_chosen
      hL.legal.validBookkeeping).2 ⟨p, hchosen⟩
  have hpInessential : p ∈ Gamma.inessentialPaths L.limitWarp := by
    apply L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
    change a.1 + 1 ≤ kappa.ord
    exact (Order.add_one_le_iff).2 a.2
  rcases p with p | r
  · have haFinite : a ∈ L.phiFinite := by
      refine ⟨haPhi, ?_⟩
      intro haInfinite
      obtain ⟨q, hq, hqRay⟩ :=
        L.bookkeeping.chosen_isRay_of_mem_phiInfinite
          hL.legal.validBookkeeping haInfinite
      have hqp : q = (.inl p : Gamma.DPath) :=
        Option.some.inj (hq.symm.trans hchosen)
      subst q
      change (some p.finish : Option V) = none at hqRay
      cases hqRay
    let x : L.finiteTerminalSet :=
      ⟨p.finish, a, haFinite, .inl p, hchosen, rfl⟩
    let source :
        (L.splitPopularAuxiliaryInput hL.legal).lambda.source :=
      ⟨.old x.1,
        ((L.splitPopularAuxiliaryInput hL.legal).mem_lambda_source_old x.1).2
          x.2⟩
    have hindex :
        (L.splitPopularAuxiliaryIndexed hL).f source = a := by
      change L.finiteTerminalStage x = a
      exact L.finiteTerminalStage_eq_of_split hL.legal hchosen rfl x.2
    have hsourceNotCut : source.1 ∉ S.cut := by
      intro hsourceCut
      apply haCutSourceUnused
      rw [← hindex]
      exact GroundingSimultaneousDecode.source_mem_sourceCutWarp_initialIndices
        (L.splitPopularAuxiliaryIndexed hL) S.cut source hsourceCut
    exact ⟨{
      stage := a
      stage_ground := haGroundCopy
      stage_unused := haUnused
      record := .inl p
      chosen := hchosen
      grounded := hpGround
      limit_inessential := hpInessential
      auxiliarySource := source
      source_index := hindex
      auxiliarySource_not_mem_cut := hsourceNotCut
      source_represents := Or.inl ⟨p, rfl, rfl⟩ }⟩
  · have haInfinite : a ∈ L.phiInfinite := by
      refine ⟨haPhi, .inr r, ?_, rfl⟩
      exact L.bookkeeping.chosen_mem_available
        hL.legal.validBookkeeping hchosen
    let i : L.splitInfiniteRecords :=
      ⟨.inr r, ⟨a, haInfinite, hchosen⟩⟩
    let source :
        (L.splitPopularAuxiliaryInput hL.legal).lambda.source :=
      ⟨.proxy i,
        (L.splitPopularAuxiliaryInput hL.legal).mem_lambda_source_proxy i⟩
    have hindex :
        (L.splitPopularAuxiliaryIndexed hL).f source = a := by
      change L.splitInfiniteStage i = a
      exact L.splitInfiniteStage_eq hL.legal i hchosen
    have hsourceNotCut : source.1 ∉ S.cut := by
      intro hsourceCut
      apply haCutSourceUnused
      rw [← hindex]
      exact GroundingSimultaneousDecode.source_mem_sourceCutWarp_initialIndices
        (L.splitPopularAuxiliaryIndexed hL) S.cut source hsourceCut
    exact ⟨{
      stage := a
      stage_ground := haGroundCopy
      stage_unused := haUnused
      record := .inr r
      chosen := hchosen
      grounded := hpGround
      limit_inessential := hpInessential
      auxiliarySource := source
      source_index := hindex
      auxiliarySource_not_mem_cut := hsourceNotCut
      source_represents := Or.inr ⟨i, rfl, rfl⟩ }⟩

/-- The grounded-stationary separator branch has a concrete unused grounded
record for every honest control package. -/
theorem exists_splitUnusedGroundedRecord
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL))
    (K : GroundingSelection.Controls S)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround) :
    Nonempty (SplitUnusedGroundedRecord L hL S K) := by
  obtain ⟨a, haGround, haUnused, haCutSourceUnused⟩ :=
    L.exists_splitGroundedStage_not_mem_selected_or_cutSourceInitialIndices
      hL S K hground
  exact L.exists_splitUnusedGroundedRecord_at hL S K a haGround haUnused
    haCutSourceUnused

namespace SplitUnusedGroundedRecord

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL)}
  {K : GroundingSelection.Controls S}

/-- The root reserved by the stationary subtraction is a genuine source of
the original web. -/
theorem record_initial_mem_source
    (R : SplitUnusedGroundedRecord L hL S K) :
    R.record.initial ∈ Gamma.source :=
  R.grounded

/-- No selected auxiliary route starts at the canonical source of the
reserved grounded record. -/
theorem auxiliarySource_ne_strongSelectedPath_start
    (R : SplitUnusedGroundedRecord L hL S K)
    (r : PopularGroundingBridge.Request
      (L.splitPopularAuxiliaryInput hL.legal) S.cut) :
    R.auxiliarySource.1 ≠
      (GroundingSimultaneousDecode.strongSelectedPath
        (L.splitPopularAuxiliaryIndexed hL) S K r).start := by
  intro heq
  let P := GroundingSimultaneousDecode.strongSelectedWarp
    (L.splitPopularAuxiliaryIndexed hL) S K
  let q := GroundingSimultaneousDecode.strongSelectedPath
    (L.splitPopularAuxiliaryIndexed hL) S K r
  have hqP : q ∈ P.paths := ⟨r, rfl⟩
  apply R.stage_unused
  refine ⟨q, hqP, ?_⟩
  have hs :
      (⟨q.start, P.starts_in_source hqP⟩ :
        (L.splitPopularAuxiliaryInput hL.legal).lambda.source) =
        R.auxiliarySource := by
    apply Subtype.ext
    exact heq.symm
  calc
    (L.splitPopularAuxiliaryIndexed hL).f
        ⟨q.start, P.starts_in_source hqP⟩ =
      (L.splitPopularAuxiliaryIndexed hL).f R.auxiliarySource :=
        congrArg (L.splitPopularAuxiliaryIndexed hL).f hs
    _ = R.stage := R.source_index

/-- Any completed source-rooted wave which omits the reserved genuine root
is already an ordinary hindrance. -/
theorem isHindrance_of_record_initial_not_mem_initialSet
    (R : SplitUnusedGroundedRecord L hL S K) {W : Set Gamma.DPath}
    (hW : Gamma.IsWave W)
    (hmiss : R.record.initial ∉ Gamma.initialSet W) :
    Gamma.IsHindrance W := by
  refine ⟨hW, ?_⟩
  intro heq
  apply hmiss
  rw [heq]
  exact R.record_initial_mem_source

end SplitUnusedGroundedRecord
end KappaLadder
end DWeb
end Erdos599
