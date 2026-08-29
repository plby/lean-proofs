import ErdosProblems.Erdos599.SplitGroundingGroundedAuxiliary
import ErdosProblems.Erdos599.GroundingSimultaneousDecode
import ErdosProblems.Erdos599.GroundingAssertion822Stationarity

/-!
# The unused source for the grounded split separator

The source auxiliary used in the grounded branch contains only genuinely
grounded records.  Stationary subtraction therefore reserves an omitted
original source directly, without coercing split legality to legacy
legality and without inspecting any hanging record.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Stationary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A grounded record whose canonical source is absent from both the
simultaneous selector and the auxiliary sources already in the cut. -/
structure SplitGroundedUnusedRecord
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (K : GroundingSelection.Controls S) where
  stage : Ladder.Stage kappa
  stage_ground : stage ∈ L.phiGround
  stage_unused :
    stage ∉ Popular.initialIndicesOf
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)
      (GroundingSimultaneousDecode.strongSelectedWarp
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K).paths
      (GroundingSimultaneousDecode.strongSelectedWarp
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K).starts_in_source
  record : Gamma.DPath
  chosen : L.chosen stage = some record
  grounded : record.initial ∈ Gamma.source
  limit_inessential : record ∈ Gamma.inessentialPaths L.limitWarp
  auxiliarySource :
    (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source
  source_index :
    (L.splitGroundedPopularAuxiliaryIndexed hL hground).f auxiliarySource = stage
  auxiliarySource_not_mem_cut : auxiliarySource.1 ∉ S.cut
  source_represents :
    (∃ p : FinitePath Gamma.graph,
      record = .inl p ∧ auxiliarySource.1 = .old p.finish) ∨
    (∃ i : L.groundedInfiniteRecords,
      record = i.1 ∧ auxiliarySource.1 = .proxy i)

/-- Removing the selected and cut-source index sets from the stationary
grounded stages leaves an index of neither kind. -/
theorem exists_splitGroundedStage_not_mem_selected_or_cutSource
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (K : GroundingSelection.Controls S) :
    ∃ a : Ladder.Stage kappa,
      a ∈ L.phiGround ∧
      a ∉ Popular.initialIndicesOf
        (L.splitGroundedPopularAuxiliaryIndexed hL hground)
        (GroundingSimultaneousDecode.strongSelectedWarp
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K).paths
        (GroundingSimultaneousDecode.strongSelectedWarp
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K).starts_in_source ∧
      a ∉ Popular.initialIndicesOf
        (L.splitGroundedPopularAuxiliaryIndexed hL hground)
        (GroundingSimultaneousDecode.sourceCutWarp
          (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda S.cut).paths
        (GroundingSimultaneousDecode.sourceCutWarp
          (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda S.cut).starts_in_source := by
  let U := L.splitGroundedPopularAuxiliaryIndexed hL hground
  let Nselected := Popular.initialIndicesOf U
    (GroundingSimultaneousDecode.strongSelectedWarp U S K).paths
    (GroundingSimultaneousDecode.strongSelectedWarp U S K).starts_in_source
  let NcutSource := Popular.initialIndicesOf U
    (GroundingSimultaneousDecode.sourceCutWarp
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda S.cut).paths
    (GroundingSimultaneousDecode.sourceCutWarp
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda S.cut).starts_in_source
  have hselected : ¬ IsStationaryBelow kappa Nselected :=
    GroundingSimultaneousDecode.strongSelectedWarp_initialIndices_nonstationary
      U S K
  have hcutSource : ¬ IsStationaryBelow kappa NcutSource :=
    GroundingSimultaneousDecode.sourceCutWarp_initialIndices_nonstationary U S
  have hfirst : IsStationaryBelow kappa (L.phiGround \ Nselected) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      hL.legal.regular hL.legal.uncountable hground hselected
  have hsecond :
      IsStationaryBelow kappa ((L.phiGround \ Nselected) \ NcutSource) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      hL.legal.regular hL.legal.uncountable hfirst hcutSource
  obtain ⟨a, ⟨haGround, haSelected⟩, haCut⟩ := hsecond.nonempty
  exact ⟨a, haGround, haSelected, haCut⟩

/-- Decode one reserved grounded stage into the corresponding source of the
grounded split auxiliary. -/
theorem exists_splitGroundedUnusedRecord_at
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (K : GroundingSelection.Controls S)
    (a : Ladder.Stage kappa) (haGround : a ∈ L.phiGround)
    (haUnused :
      a ∉ Popular.initialIndicesOf
        (L.splitGroundedPopularAuxiliaryIndexed hL hground)
        (GroundingSimultaneousDecode.strongSelectedWarp
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K).paths
        (GroundingSimultaneousDecode.strongSelectedWarp
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K).starts_in_source)
    (haCutUnused :
      a ∉ Popular.initialIndicesOf
        (L.splitGroundedPopularAuxiliaryIndexed hL hground)
        (GroundingSimultaneousDecode.sourceCutWarp
          (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda S.cut).paths
        (GroundingSimultaneousDecode.sourceCutWarp
          (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda S.cut).starts_in_source) :
    Nonempty (SplitGroundedUnusedRecord L hL hground S K) := by
  obtain ⟨record, hchosen, hsource⟩ := haGround
  have haPhi : a ∈ L.phi :=
    (L.bookkeeping.mem_phi_iff_exists_chosen
      hL.legal.validBookkeeping).2 ⟨record, hchosen⟩
  have hinessential : record ∈ Gamma.inessentialPaths L.limitWarp := by
    apply L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
    change a.1 + 1 ≤ kappa.ord
    exact (Order.add_one_le_iff).2 a.2
  rcases record with p | r
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
    let x : L.groundedFiniteTerminalSet :=
      ⟨p.finish, a, ⟨⟨.inl p, hchosen, hsource⟩, haFinite⟩,
        .inl p, hchosen, rfl⟩
    let source :
        (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source :=
      ⟨.old x.1,
        ((L.splitGroundedPopularAuxiliaryInput hL.legal)
          |>.mem_lambda_source_old x.1).2 x.2⟩
    have hindex :
        (L.splitGroundedPopularAuxiliaryIndexed hL hground).f source = a := by
      change L.finiteTerminalIndex x = a
      exact L.finiteTerminalStage_eq_of_split hL.legal hchosen rfl
        (L.groundedFiniteTerminalSet_subset_finiteTerminalSet x.2)
    have hsourceNotCut : source.1 ∉ S.cut := by
      intro hsCut
      apply haCutUnused
      rw [← hindex]
      exact GroundingSimultaneousDecode.source_mem_sourceCutWarp_initialIndices
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S.cut source hsCut
    exact ⟨{
      stage := a
      stage_ground := ⟨.inl p, hchosen, hsource⟩
      stage_unused := haUnused
      record := .inl p
      chosen := hchosen
      grounded := hsource
      limit_inessential := hinessential
      auxiliarySource := source
      source_index := hindex
      auxiliarySource_not_mem_cut := hsourceNotCut
      source_represents := Or.inl ⟨p, rfl, rfl⟩ }⟩
  · have haInfinite : a ∈ L.phiInfinite := by
      refine ⟨haPhi, .inr r, ?_, rfl⟩
      exact L.bookkeeping.chosen_mem_available
        hL.legal.validBookkeeping hchosen
    let i : L.groundedInfiniteRecords :=
      ⟨.inr r, ⟨a, ⟨⟨.inr r, hchosen, hsource⟩, haInfinite⟩,
        hchosen⟩⟩
    let source :
        (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source :=
      ⟨.proxy i,
        (L.splitGroundedPopularAuxiliaryInput hL.legal)
          |>.mem_lambda_source_proxy i⟩
    have hindex :
        (L.splitGroundedPopularAuxiliaryIndexed hL hground).f source = a := by
      change L.groundedInfiniteStage i = a
      exact L.groundedInfiniteStage_eq_of_split hL.legal i hchosen
    have hsourceNotCut : source.1 ∉ S.cut := by
      intro hsCut
      apply haCutUnused
      rw [← hindex]
      exact GroundingSimultaneousDecode.source_mem_sourceCutWarp_initialIndices
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S.cut source hsCut
    exact ⟨{
      stage := a
      stage_ground := ⟨.inr r, hchosen, hsource⟩
      stage_unused := haUnused
      record := .inr r
      chosen := hchosen
      grounded := hsource
      limit_inessential := hinessential
      auxiliarySource := source
      source_index := hindex
      auxiliarySource_not_mem_cut := hsourceNotCut
      source_represents := Or.inr ⟨i, rfl, rfl⟩ }⟩

/-- The grounded separator branch always has a concrete reserved source for
any honest control package. -/
theorem exists_splitGroundedUnusedRecord
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (K : GroundingSelection.Controls S) :
    Nonempty (SplitGroundedUnusedRecord L hL hground S K) := by
  obtain ⟨a, haGround, haUnused, haCut⟩ :=
    L.exists_splitGroundedStage_not_mem_selected_or_cutSource
      hL hground S K
  exact L.exists_splitGroundedUnusedRecord_at
    hL hground S K a haGround haUnused haCut

namespace SplitGroundedUnusedRecord

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

/-- Any completed source-rooted wave omitting the reserved source is an
ordinary hindrance. -/
theorem isHindrance_of_initial_not_mem
    (R : SplitGroundedUnusedRecord L hL hground S K)
    {W : Set Gamma.DPath} (hW : Gamma.IsWave W)
    (hmiss : R.record.initial ∉ Gamma.initialSet W) :
    Gamma.IsHindrance W := by
  refine ⟨hW, ?_⟩
  intro heq
  exact hmiss (heq.symm ▸ R.grounded)

end SplitGroundedUnusedRecord
end KappaLadder
end DWeb
end Erdos599
