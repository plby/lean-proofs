/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZShellZeroDeltaIndexedExactCountScreen
import ErdosProblems.Erdos1165.TilingShellZeroDeltaIndexedStoppedCoordinateSpec
import ErdosProblems.Erdos1165.TilingShellZeroFactoredCapScreen

/-!
# Oriented shell-zero closure with fixed clocks indexed by actual increment

This is the source-event adapter for the delta-indexed stopped-coordinate
API.  It contains no guessed replacement rank and no variable-rank stopping
time.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.TilingShellZeroDeltaIndexedExactCountScreen

open HLOZProposition48Candidates HLOZShellZeroCentralCount
open HLOZShellZeroDeltaIndexedCapScreen
open HLOZShellZeroDeltaIndexedExactCountScreen
open HLOZShellZeroRankUnionCentralTail HLOZShellZeroReplacementWindows
open LazyDecomposition TilingOrientedShellZeroSourcePartition
open TilingShellZeroActualDeltaPartition
open TilingShellZeroDeltaIndexedStoppedCoordinateSpec
open TilingShellZeroExternalStaticSupportPartition
open TilingShellZeroFactoredCapScreen TilingShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

theorem literalShellZeroDeltaIndexedCapFamily_sourceAtom
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (data : ∀ eta : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total,
      LiteralShellZeroDeltaIndexedStoppedCoordinateSpec t o m k low
        externalLow externalHigh total eta.1.1 eta.1.2)
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) :
    (literalShellZeroDeltaIndexedCapFamily t o m k low externalLow
      externalHigh total data).sourceAtom eta =
      orientedValidShellZeroExactSourceStaticSupportAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total
        eta.1.1 eta.1.2 := by
  apply Set.Subset.antisymm
  · intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨cap, hcap⟩
    exact (data eta).source_sound cap hcap
  · exact (data eta).source_complete

theorem literalShellZeroDeltaIndexedCapFamily_rankPiece_subset
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (data : ∀ eta : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total,
      LiteralShellZeroDeltaIndexedStoppedCoordinateSpec t o m k low
        externalLow externalHigh total eta.1.1 eta.1.2)
    (delta : ReplacementEndpointIncrement total
      (centralReplacementUpperCount shellZeroLocalRatioConstant total))
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) :
    (literalShellZeroDeltaIndexedCapFamily t o m k low externalLow
      externalHigh total data).rankPiece delta eta ⊆
      orientedValidShellZeroActualDeltaReplacementStaticSupportAtom
        t o m k (shellWidth48 m) low externalLow externalHigh total
        (centralReplacementUpperCount shellZeroLocalRatioConstant total)
        delta eta.1.1 eta.1.2 := by
  intro s hs
  rcases Set.mem_iUnion.mp hs with ⟨cap, hcap⟩
  exact (data eta).replacement_sound delta cap hcap

theorem pairwise_disjoint_literalShellZeroDeltaIndexedCapFamily_rankPiece
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (data : ∀ eta : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total,
      LiteralShellZeroDeltaIndexedStoppedCoordinateSpec t o m k low
        externalLow externalHigh total eta.1.1 eta.1.2)
    (delta : ReplacementEndpointIncrement total
      (centralReplacementUpperCount shellZeroLocalRatioConstant total)) :
    Pairwise fun eta eta' : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total ↦
      Disjoint
        ((literalShellZeroDeltaIndexedCapFamily t o m k low externalLow
          externalHigh total data).rankPiece delta eta)
        ((literalShellZeroDeltaIndexedCapFamily t o m k low externalLow
          externalHigh total data).rankPiece delta eta') := by
  intro eta eta' hne
  rw [Set.disjoint_left]
  intro s hs ht
  have hsound := literalShellZeroDeltaIndexedCapFamily_rankPiece_subset
    t o m k low externalLow externalHigh total data delta eta hs
  have hsound' := literalShellZeroDeltaIndexedCapFamily_rankPiece_subset
    t o m k low externalLow externalHigh total data delta eta' ht
  exact Set.disjoint_left.mp
    (pairwise_disjoint_actualDeltaReplacementStaticSupportAtom
      t o m k (shellWidth48 m) low externalLow externalHigh total
      (centralReplacementUpperCount shellZeroLocalRatioConstant total)
      delta (fun h ↦ hne (Subtype.ext h))) hsound hsound'

noncomputable def literalShellZeroDeltaIndexedExactCountScreenAtCut
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh sourceCut : ℕ)
    (data : ∀ (n : ℕ),
      ∀ eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m)
        low externalLow externalHigh (sourceCut + 1 + n),
      LiteralShellZeroDeltaIndexedStoppedCoordinateSpec t o m k low
        externalLow externalHigh (sourceCut + 1 + n) eta.1.1 eta.1.2) :
    LiteralShellZeroExactCountDeltaIndexedCapScreen
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
  family := fun n ↦ literalShellZeroDeltaIndexedCapFamily t o m k low
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
    rw [literalShellZeroDeltaIndexedCapFamily_sourceAtom]
    exact hsatom
  disjoint_rankPiece := fun n ↦
    pairwise_disjoint_literalShellZeroDeltaIndexedCapFamily_rankPiece
      t o m k low externalLow externalHigh (sourceCut + 1 + n) (data n)
  delta_card := fun n ↦ by
    simp [centralReplacementRankMultiplicity, replacementMovedCount]

theorem simpleRandomWalk_orientedShellZeroSourceEvent_le_of_deltaIndexedSpecAtCut
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh sourceCut : ℕ)
    (data : ∀ (n : ℕ),
      ∀ eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m)
        low externalLow externalHigh (sourceCut + 1 + n),
      LiteralShellZeroDeltaIndexedStoppedCoordinateSpec t o m k low
        externalLow externalHigh (sourceCut + 1 + n) eta.1.1 eta.1.2) :
    simpleRandomWalk
        (orientedShellZeroSourceEvent t o m k (shellWidth48 m) low
          externalLow externalHigh sourceCut) ≤
      centralReplacementRankUnionTailCost shellZeroLocalRatioConstant
        sourceCut := by
  rw [← simpleRandomWalk_orientedValidShellZeroSourceEvent]
  exact (literalShellZeroDeltaIndexedExactCountScreenAtCut t o m k low
    externalLow externalHigh sourceCut data).measure_le

end

end Erdos1165.TilingShellZeroDeltaIndexedExactCountScreen
