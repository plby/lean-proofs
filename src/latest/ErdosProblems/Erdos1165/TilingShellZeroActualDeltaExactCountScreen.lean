/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZShellZeroFiniteRankExactCountScreen
import ErdosProblems.Erdos1165.TilingShellZeroActualDeltaScreenedSpec

/-!
# Source-correct exact-count shell screen with actual endpoint increments

The finite stopped-coordinate comparison is unchanged.  Its replacement
atom is split into measurable pieces according to the actual endpoint-count
increment.  For each fixed increment the oriented external/static-support
atoms are pairwise disjoint.  Summing the finite increments gives the
rank-union central tail.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.TilingShellZeroActualDeltaExactCountScreen

open HLOZProposition48Candidates HLOZShellZeroCentralCount
open HLOZShellZeroCentralTail HLOZShellZeroExactCountScreen
open HLOZShellZeroFiniteRankExactCountScreen
open HLOZShellZeroReplacementWindows
open HLOZShellZeroRankUnionCentralTail LazyDecomposition
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroActualDeltaPartition
open TilingShellZeroActualDeltaScreenedSpec
open TilingShellZeroExternalStaticSupportPartition
open TilingShellZeroFactoredCapScreen
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Cap family for one exact source count on one supported `(z,S)` index. -/
noncomputable def literalShellZeroActualDeltaCapFamily
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (data : ∀ eta : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total,
      LiteralShellZeroActualDeltaScreenedSpec t o m k low externalLow
        externalHigh total eta.1.1 eta.1.2) :
    MonotoneCapStoppedFiberReplacementAtomFamily
      (SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
        externalLow externalHigh total)
      (centralReplacementRatio shellZeroLocalRatioConstant total) where
  sourceCap := fun cap eta ↦
    walkLift (prefixedTilingPreStoppingFiberEvent
      ((data eta).sourceStoppingTime cap) eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained ((data eta).coordinateCap cap)
        eta.1.1.tail.1 ((data eta).sourcePredicate cap))
  replacementCap := fun cap eta ↦
    walkLift (prefixedTilingPreStoppingFiberEvent
      ((data eta).replacementStoppingTime cap) eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained ((data eta).coordinateCap cap)
        eta.1.1.tail.1 ((data eta).replacementPredicate cap))
  measurable_replacementCap := fun cap eta ↦ by
    apply measurableSet_walkLift
    exact measurableSet_prefixedTilingPreStoppingFiberEvent
      ((data eta).replacementIsStoppingTime cap) eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained ((data eta).coordinateCap cap)
      eta.1.1.tail.1 ((data eta).replacementPredicate cap)
  cap_le := fun cap eta ↦ by
    simp only [OrientedTilingTypedExternalWordCode.start]
    rw [simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
        ((data eta).sourceIsStoppingTime cap),
      simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
        ((data eta).replacementIsStoppingTime cap),
      ← ENNReal.ofReal_mul
        (centralReplacementRatio_nonneg
          shellZeroLocalRatioConstant_pos.le total)]
    apply ENNReal.ofReal_le_ofReal
    have hcommon : 0 ≤ prefixedPrefixFiberConstant eta.1.1.initial.1
        eta.1.1.retainedCount eta.1.1.tail.1 :=
      prefixedPrefixFiberConstant_nonneg _ _ _
    calc
      prefixedPrefixFiberConstant eta.1.1.initial.1 eta.1.1.retainedCount
            eta.1.1.tail.1 *
          prefixedTilingStoppedAcceptedGeometricMass
            ((data eta).sourceStoppingTime cap) eta.1.1.initial.1 t
            eta.1.1.start eta.1.1.retained ((data eta).coordinateCap cap)
            eta.1.1.tail.1 ((data eta).sourcePredicate cap) ≤
        prefixedPrefixFiberConstant eta.1.1.initial.1 eta.1.1.retainedCount
            eta.1.1.tail.1 *
          (centralReplacementRatio shellZeroLocalRatioConstant total *
            prefixedTilingStoppedAcceptedGeometricMass
              ((data eta).replacementStoppingTime cap) eta.1.1.initial.1 t
              eta.1.1.start eta.1.1.retained ((data eta).coordinateCap cap)
              eta.1.1.tail.1 ((data eta).replacementPredicate cap)) :=
        mul_le_mul_of_nonneg_left ((data eta).coordinate_bound cap) hcommon
      _ = centralReplacementRatio shellZeroLocalRatioConstant total *
          (prefixedPrefixFiberConstant eta.1.1.initial.1
              eta.1.1.retainedCount eta.1.1.tail.1 *
            prefixedTilingStoppedAcceptedGeometricMass
              ((data eta).replacementStoppingTime cap) eta.1.1.initial.1 t
              eta.1.1.start eta.1.1.retained ((data eta).coordinateCap cap)
              eta.1.1.tail.1 ((data eta).replacementPredicate cap)) := by
        ring
  source_monotone := fun eta ↦ (data eta).source_monotone

theorem literalShellZeroActualDeltaCapFamily_sourceAtom
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (data : ∀ eta : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total,
      LiteralShellZeroActualDeltaScreenedSpec t o m k low externalLow
        externalHigh total eta.1.1 eta.1.2)
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) :
    (literalShellZeroActualDeltaCapFamily t o m k low externalLow
      externalHigh total data).sourceAtom eta =
      orientedValidShellZeroExactSourceStaticSupportAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total
        eta.1.1 eta.1.2 := by
  apply Set.Subset.antisymm
  · intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨cap, hcap⟩
    exact (data eta).source_sound cap hcap
  · exact (data eta).source_complete

/-- Increasing-cap union of one actual-increment replacement piece. -/
def literalShellZeroActualDeltaRankPiece
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (data : ∀ eta : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total,
      LiteralShellZeroActualDeltaScreenedSpec t o m k low externalLow
        externalHigh total eta.1.1 eta.1.2)
    (delta : ReplacementEndpointIncrement total
      (centralReplacementUpperCount shellZeroLocalRatioConstant total))
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) : Set WalkPath :=
  ⋃ cap, (data eta).replacementPiece cap delta

theorem literalShellZeroActualDeltaCapFamily_replacement_subset
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (data : ∀ eta : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total,
      LiteralShellZeroActualDeltaScreenedSpec t o m k low externalLow
        externalHigh total eta.1.1 eta.1.2)
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) :
    (literalShellZeroActualDeltaCapFamily t o m k low externalLow
      externalHigh total data).replacementAtom eta ⊆
      ⋃ delta, literalShellZeroActualDeltaRankPiece t o m k low externalLow
        externalHigh total data delta eta := by
  intro s hs
  rcases Set.mem_iUnion.mp hs with ⟨cap, hcap⟩
  rcases Set.mem_iUnion.mp ((data eta).replacement_cover cap hcap) with
    ⟨delta, hdelta⟩
  exact Set.mem_iUnion.mpr ⟨delta, Set.mem_iUnion.mpr ⟨cap, hdelta⟩⟩

theorem measurableSet_literalShellZeroActualDeltaRankPiece
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (data : ∀ eta : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total,
      LiteralShellZeroActualDeltaScreenedSpec t o m k low externalLow
        externalHigh total eta.1.1 eta.1.2)
    (delta : ReplacementEndpointIncrement total
      (centralReplacementUpperCount shellZeroLocalRatioConstant total))
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) :
    MeasurableSet (literalShellZeroActualDeltaRankPiece t o m k low
      externalLow externalHigh total data delta eta) := by
  exact MeasurableSet.iUnion fun cap ↦
    (data eta).measurable_replacementPiece cap delta

theorem pairwise_disjoint_literalShellZeroActualDeltaRankPiece
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (data : ∀ eta : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total,
      LiteralShellZeroActualDeltaScreenedSpec t o m k low externalLow
        externalHigh total eta.1.1 eta.1.2)
    (delta : ReplacementEndpointIncrement total
      (centralReplacementUpperCount shellZeroLocalRatioConstant total)) :
    Pairwise fun eta eta' : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total ↦
      Disjoint
        (literalShellZeroActualDeltaRankPiece t o m k low externalLow
          externalHigh total data delta eta)
        (literalShellZeroActualDeltaRankPiece t o m k low externalLow
          externalHigh total data delta eta') := by
  intro eta eta' hne
  rw [Set.disjoint_left]
  intro s hs ht
  rcases Set.mem_iUnion.mp hs with ⟨cap, hcap⟩
  rcases Set.mem_iUnion.mp ht with ⟨cap', hcap'⟩
  have hsound := (data eta).replacement_piece_sound cap delta hcap
  have hsound' := (data eta').replacement_piece_sound cap' delta hcap'
  exact Set.disjoint_left.mp
    (pairwise_disjoint_actualDeltaReplacementStaticSupportAtom
      t o m k (shellWidth48 m) low externalLow externalHigh total
      (centralReplacementUpperCount shellZeroLocalRatioConstant total)
      delta (fun h ↦ hne (Subtype.ext h))) hsound hsound'

/-- Exact-count cap screen at an arbitrary oriented source cut, with the
safe actual endpoint-increment range. -/
noncomputable def literalShellZeroActualDeltaExactCountScreenAtCut
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh sourceCut : ℕ)
    (data : ∀ (n : ℕ),
      ∀ eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m)
        low externalLow externalHigh (sourceCut + 1 + n),
      LiteralShellZeroActualDeltaScreenedSpec t o m k low externalLow
        externalHigh (sourceCut + 1 + n) eta.1.1 eta.1.2) :
    LiteralShellZeroExactCountFiniteRankCapScreen
      (orientedValidShellZeroSourceEvent t o m k (shellWidth48 m) low
        externalLow externalHigh sourceCut)
      shellZeroLocalRatioConstant sourceCut where
  Index := fun n ↦ SupportedSourceStaticSupportIndex t o m k
    (shellWidth48 m) low externalLow externalHigh (sourceCut + 1 + n)
  indexCountable := fun _ ↦ inferInstance
  Delta := fun n ↦ ReplacementEndpointIncrement (sourceCut + 1 + n)
    (centralReplacementUpperCount shellZeroLocalRatioConstant
      (sourceCut + 1 + n))
  deltaFintype := fun _ ↦ inferInstance
  family := fun n ↦ literalShellZeroActualDeltaCapFamily t o m k low
    externalLow externalHigh (sourceCut + 1 + n) (data n)
  rankPiece := fun n ↦ literalShellZeroActualDeltaRankPiece t o m k low
    externalLow externalHigh (sourceCut + 1 + n) (data n)
  source_subset := by
    intro s hs
    rcases hs with ⟨⟨hreach, hD, htheta, hcut⟩, hvalid⟩
    let total := (orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) s
        (creationTimeNat m k s)).card
    have htotal : sourceCut + 1 ≤ total := by
      dsimp only [total]
      omega
    let n := total - (sourceCut + 1)
    have htotalEq : sourceCut + 1 + n = total :=
      Nat.add_sub_of_le htotal
    let z := fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s
    let S := sourceStaticSupport t o m k (shellWidth48 m) s
    have hsatom : s ∈ orientedValidShellZeroExactSourceStaticSupportAtom
        t o m k (shellWidth48 m) low externalLow externalHigh
          (sourceCut + 1 + n) z S := by
      refine ⟨⟨⟨⟨hreach, hD, htheta, ?_⟩, rfl⟩, hvalid⟩, rfl⟩
      change total = sourceCut + 1 + n
      exact htotalEq.symm
    let eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m)
        low externalLow externalHigh (sourceCut + 1 + n) :=
      ⟨(z, S), ⟨s, hsatom⟩⟩
    apply Set.mem_iUnion.mpr
    refine ⟨n, Set.mem_iUnion.mpr ⟨eta, ?_⟩⟩
    rw [literalShellZeroActualDeltaCapFamily_sourceAtom]
    exact hsatom
  replacement_subset := fun n ↦
    literalShellZeroActualDeltaCapFamily_replacement_subset t o m k low
      externalLow externalHigh (sourceCut + 1 + n) (data n)
  measurable_rankPiece := fun n ↦
    measurableSet_literalShellZeroActualDeltaRankPiece t o m k low
      externalLow externalHigh (sourceCut + 1 + n) (data n)
  disjoint_rankPiece := fun n ↦
    pairwise_disjoint_literalShellZeroActualDeltaRankPiece t o m k low
      externalLow externalHigh (sourceCut + 1 + n) (data n)
  delta_card := fun n ↦ by
    simp [centralReplacementRankMultiplicity, replacementMovedCount]

/-- Final source-correct oriented shell-zero bound with actual endpoint
increments and no fixed replacement-rank premise. -/
theorem simpleRandomWalk_orientedShellZeroSourceEvent_le_of_actualDeltaScreenedSpecAtCut
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh sourceCut : ℕ)
    (data : ∀ (n : ℕ),
      ∀ eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m)
        low externalLow externalHigh (sourceCut + 1 + n),
      LiteralShellZeroActualDeltaScreenedSpec t o m k low externalLow
        externalHigh (sourceCut + 1 + n) eta.1.1 eta.1.2) :
    simpleRandomWalk
        (orientedShellZeroSourceEvent t o m k (shellWidth48 m) low
          externalLow externalHigh sourceCut) ≤
      centralReplacementRankUnionTailCost shellZeroLocalRatioConstant
        sourceCut := by
  rw [← simpleRandomWalk_orientedValidShellZeroSourceEvent]
  exact (literalShellZeroActualDeltaExactCountScreenAtCut t o m k low
    externalLow externalHigh sourceCut data).measure_le

end

end Erdos1165.TilingShellZeroActualDeltaExactCountScreen
