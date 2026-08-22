/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroFactoredCapScreen

/-!
# Exact-count shell-zero screens at an arbitrary source cut

The public Proposition 4.8 candidate threshold is not the same as the
fixed-count source cut after the even/odd dominant-endpoint split.  This
module therefore records the source cut explicitly.  It changes only the
initial exact count; the literal stopped-coordinate construction and the
variable-clock replacement are unchanged.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.TilingShellZeroCutFactoredCapScreen

open HLOZPathEvents HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroCentralTail
open HLOZShellZeroExactCountScreen HLOZShellZeroReplacementWindows
open TilingShellZeroFactoredCapScreen TilingShellZeroSourcePartition
open TilingOrientedShellZeroSourcePartition
open LazyDecomposition
open TilingShellZeroLiteralScreen
open TilingTypedShellZeroReplacement
open TilingVariableStoppedTracePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A cap-coherent exact-count screen whose first exact count is
`sourceCut + 1`. -/
structure LiteralShellZeroExactCountCutCapStoppedFiberScreen
    (source : Set WalkPath) (sourceCut : ℕ) where
  sourceRank : ℕ
  Index : ℕ → Type*
  indexCountable : ∀ n, Countable (Index n)
  family : ∀ n, MonotoneCapStoppedFiberReplacementAtomFamily (Index n)
    (centralReplacementRatio shellZeroLocalRatioConstant
      (sourceCut + 1 + n))
  source_subset : source ⊆ ⋃ n : ℕ, ⋃ z : Index n,
    (family n).sourceAtom z
  disjoint_replacement : ∀ n, Pairwise fun z w ↦
    Disjoint ((family n).replacementAtom z)
      ((family n).replacementAtom w)

def LiteralShellZeroExactCountCutCapStoppedFiberScreen.sourceAt
    {source : Set WalkPath} {sourceCut : ℕ}
    (screen : LiteralShellZeroExactCountCutCapStoppedFiberScreen
      source sourceCut) (n : ℕ) : Set WalkPath :=
  ⋃ z : screen.Index n, (screen.family n).sourceAtom z

theorem LiteralShellZeroExactCountCutCapStoppedFiberScreen.sourceAt_measure_le
    {source : Set WalkPath} {sourceCut n : ℕ}
    (screen : LiteralShellZeroExactCountCutCapStoppedFiberScreen
      source sourceCut) :
    simpleRandomWalk (screen.sourceAt n) ≤
      ENNReal.ofReal (centralReplacementRatio shellZeroLocalRatioConstant
        (sourceCut + 1 + n)) := by
  let _ : Countable (screen.Index n) := screen.indexCountable n
  exact simpleRandomWalk_source_le_of_exactCountCapStoppedFibers
    (centralReplacementRatio shellZeroLocalRatioConstant
      (sourceCut + 1 + n))
    (screen.family n) (screen.sourceAt n) Subset.rfl
      (screen.disjoint_replacement n)

theorem LiteralShellZeroExactCountCutCapStoppedFiberScreen.measure_le
    {source : Set WalkPath} {sourceCut : ℕ}
    (screen : LiteralShellZeroExactCountCutCapStoppedFiberScreen
      source sourceCut) :
    simpleRandomWalk source ≤
      centralReplacementTailCost shellZeroLocalRatioConstant sourceCut := by
  calc
    simpleRandomWalk source ≤
        simpleRandomWalk (⋃ n : ℕ, screen.sourceAt n) :=
      measure_mono screen.source_subset
    _ ≤ ∑' n : ℕ, simpleRandomWalk (screen.sourceAt n) :=
      measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal
        (centralReplacementRatio shellZeroLocalRatioConstant
          (sourceCut + 1 + n)) := by
      exact ENNReal.tsum_le_tsum fun n ↦ screen.sourceAt_measure_le
    _ = centralReplacementTailCost shellZeroLocalRatioConstant sourceCut := rfl

/-- Construct the arbitrary-cut screen from literal cap factorizations. -/
noncomputable def literalShellZeroExactCountFactoredCapScreenAtCut
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh sourceCut : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : ∀ (n : ℕ),
      ∀ eta : LiteralShellZeroSupportedTraceIndex t o m k low externalLow
        externalHigh (sourceCut + 1 + n),
      LiteralShellZeroFactoredCapData t o m k low externalLow externalHigh
        (sourceCut + 1 + n) eta.1) :
    LiteralShellZeroExactCountCutCapStoppedFiberScreen
      (orientedValidShellZeroSourceEvent t o m k (shellWidth48 m) low externalLow
        externalHigh sourceCut) sourceCut where
  sourceRank := k
  Index := fun n ↦ LiteralShellZeroSupportedTraceIndex t o m k low
    externalLow externalHigh (sourceCut + 1 + n)
  indexCountable := fun _ ↦ inferInstance
  family := fun n ↦ literalShellZeroFactoredCapFamily t o m k low externalLow
    externalHigh (sourceCut + 1 + n) (data n) harithmetic
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
    have hsatom : s ∈ orientedValidShellZeroExactSourceTraceAtom t o m k
        (shellWidth48 m) low externalLow externalHigh (sourceCut + 1 + n)
          (orientedTypedCreationTraceCode t o m k (shellWidth48 m) s) := by
      refine ⟨⟨⟨hreach, hD, htheta, ?_⟩, rfl⟩, hvalid⟩
      change total = sourceCut + 1 + n
      exact htotalEq.symm
    let eta : LiteralShellZeroSupportedTraceIndex t o m k low externalLow
        externalHigh (sourceCut + 1 + n) :=
      ⟨orientedTypedCreationTraceCode t o m k (shellWidth48 m) s,
        ⟨s, hsatom⟩⟩
    apply Set.mem_iUnion.mpr
    refine ⟨n, Set.mem_iUnion.mpr ⟨eta, ?_⟩⟩
    rw [literalShellZeroFactoredCapFamily_sourceAtom t o m k low externalLow
      externalHigh _ harithmetic]
    exact hsatom
  disjoint_replacement := by
    intro n eta eta' hne
    rw [literalShellZeroFactoredCapFamily_replacementAtom
      t o m k low externalLow externalHigh (sourceCut + 1 + n)
        harithmetic (data n) eta,
      literalShellZeroFactoredCapFamily_replacementAtom
      t o m k low externalLow externalHigh (sourceCut + 1 + n)
        harithmetic (data n) eta']
    exact (pairwise_disjoint_of_variableClockThresholdJump
      (orientedShellZeroVariableClockJump t o m k (shellWidth48 m) low
        externalLow externalHigh (sourceCut + 1 + n)
        (centralReplacementUpperCount shellZeroLocalRatioConstant
          (sourceCut + 1 + n)) hm (by
            unfold replacementCreationRank replacementNewCount
            omega))
      (fun h ↦ hne (Subtype.ext h))).mono inter_subset_left
        inter_subset_left

/-- Literal fixed-count source estimate at an arbitrary source cut. -/
theorem simpleRandomWalk_shellZeroSourceEvent_le_of_factoredCapDataAtCut
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh sourceCut : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : ∀ (n : ℕ),
      ∀ eta : LiteralShellZeroSupportedTraceIndex t o m k low externalLow
        externalHigh (sourceCut + 1 + n),
      LiteralShellZeroFactoredCapData t o m k low externalLow externalHigh
        (sourceCut + 1 + n) eta.1) :
    simpleRandomWalk
        (orientedShellZeroSourceEvent t o m k (shellWidth48 m) low externalLow
          externalHigh sourceCut) ≤
      centralReplacementTailCost shellZeroLocalRatioConstant sourceCut := by
  rw [← simpleRandomWalk_orientedValidShellZeroSourceEvent]
  exact (literalShellZeroExactCountFactoredCapScreenAtCut t o m k low
    externalLow externalHigh sourceCut hm hk harithmetic data).measure_le

end

end Erdos1165.TilingShellZeroCutFactoredCapScreen
