/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroCutFactoredCapScreen
import ErdosProblems.Erdos1165.TilingShellZeroStaticSupportScreenedSpec

/-!
# Exact-count shell-zero screen on the external/static-support carrier

This is the cap-union and exact-count closure for the source-correct carrier
`(z,S)`.  The external word `z` is common across the two creation clocks,
while `S` is read as `V₂(I₁)` at the source clock and as
`V₂(I₁) ∪ V₂(I₀)` at the replacement clock.  Thus no current-favorite trace
is identified across clocks.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.TilingShellZeroStaticSupportExactCountScreen

open HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroCentralTail
open HLOZShellZeroExactCountScreen
open HLOZShellZeroReplacementWindows
open LazyDecomposition
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroCutFactoredCapScreen
open TilingShellZeroExternalStaticSupportPartition
open TilingShellZeroFactoredCapScreen
open TilingShellZeroSourcePartition
open TilingShellZeroStaticSupportScreenedSpec
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The increasing cap family on one exact source count, indexed only by
nonempty source `(external word, static support)` atoms. -/
noncomputable def literalShellZeroStaticSupportCapFamily
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (data : ∀ eta : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total,
      LiteralShellZeroStaticSupportScreenedSpec t o m k low externalLow
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

theorem literalShellZeroStaticSupportCapFamily_sourceAtom
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (data : ∀ eta : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total,
      LiteralShellZeroStaticSupportScreenedSpec t o m k low externalLow
        externalHigh total eta.1.1 eta.1.2)
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) :
    (literalShellZeroStaticSupportCapFamily t o m k low externalLow
      externalHigh total data).sourceAtom eta =
      orientedValidShellZeroExactSourceStaticSupportAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total
        eta.1.1 eta.1.2 := by
  apply Set.Subset.antisymm
  · intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨cap, hcap⟩
    exact (data eta).source_sound cap hcap
  · exact (data eta).source_complete

theorem literalShellZeroStaticSupportCapFamily_replacementAtom
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (data : ∀ eta : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total,
      LiteralShellZeroStaticSupportScreenedSpec t o m k low externalLow
        externalHigh total eta.1.1 eta.1.2)
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) :
    (literalShellZeroStaticSupportCapFamily t o m k low externalLow
      externalHigh total data).replacementAtom eta =
      orientedValidShellZeroReplacementStaticSupportAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total
        (centralReplacementUpperCount shellZeroLocalRatioConstant total)
        eta.1.1 eta.1.2 := by
  apply Set.Subset.antisymm
  · intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨cap, hcap⟩
    exact (data eta).replacement_sound cap hcap
  · exact (data eta).replacement_complete

/-- Exact-count cap screen at an arbitrary source cut, using the corrected
external/static-support atoms. -/
noncomputable def literalShellZeroStaticSupportExactCountScreenAtCut
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh sourceCut : ℕ)
    (data : ∀ (n : ℕ),
      ∀ eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m)
        low externalLow externalHigh (sourceCut + 1 + n),
      LiteralShellZeroStaticSupportScreenedSpec t o m k low externalLow
        externalHigh (sourceCut + 1 + n) eta.1.1 eta.1.2) :
    LiteralShellZeroExactCountCutCapStoppedFiberScreen
      (orientedValidShellZeroSourceEvent t o m k (shellWidth48 m) low
        externalLow externalHigh sourceCut) sourceCut where
  sourceRank := k
  Index := fun n ↦ SupportedSourceStaticSupportIndex t o m k
    (shellWidth48 m) low externalLow externalHigh (sourceCut + 1 + n)
  indexCountable := fun _ ↦ inferInstance
  family := fun n ↦ literalShellZeroStaticSupportCapFamily t o m k low
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
    rw [literalShellZeroStaticSupportCapFamily_sourceAtom]
    exact hsatom
  disjoint_replacement := by
    intro n eta eta' hne
    rw [literalShellZeroStaticSupportCapFamily_replacementAtom,
      literalShellZeroStaticSupportCapFamily_replacementAtom]
    exact pairwise_disjoint_replacementStaticSupportAtom t o m k
      (shellWidth48 m) low externalLow externalHigh (sourceCut + 1 + n)
      (centralReplacementUpperCount shellZeroLocalRatioConstant
        (sourceCut + 1 + n))
      (fun h ↦ hne (Subtype.ext h))

/-- Source-correct shell-zero tail bound at an arbitrary oriented source
cut.  Its only fibre input is the honest screened `(z,S)` stopped-coordinate
specification; no event-probability inequality is assumed. -/
theorem simpleRandomWalk_orientedShellZeroSourceEvent_le_of_staticSupportScreenedSpecAtCut
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh sourceCut : ℕ)
    (data : ∀ (n : ℕ),
      ∀ eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m)
        low externalLow externalHigh (sourceCut + 1 + n),
      LiteralShellZeroStaticSupportScreenedSpec t o m k low externalLow
        externalHigh (sourceCut + 1 + n) eta.1.1 eta.1.2) :
    simpleRandomWalk
        (orientedShellZeroSourceEvent t o m k (shellWidth48 m) low
          externalLow externalHigh sourceCut) ≤
      centralReplacementTailCost shellZeroLocalRatioConstant sourceCut := by
  rw [← simpleRandomWalk_orientedValidShellZeroSourceEvent]
  exact (literalShellZeroStaticSupportExactCountScreenAtCut t o m k low
    externalLow externalHigh sourceCut data).measure_le

end

end Erdos1165.TilingShellZeroStaticSupportExactCountScreen
