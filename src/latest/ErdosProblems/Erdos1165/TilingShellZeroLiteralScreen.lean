/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZShellZeroExactCountScreen

/-!
# Literal construction of the shell-zero exact-count screen

This file is the source-facing adapter for HLOZ (4.49)--(4.54).  At every
fixed source count and retained external word, its input consists of the two
literal stopped fibres, their exact finite-product identities, and the
checked `I₁/I₀` coordinate windows.  The coordinate inequality, the source
partition, and global disjointness are all conclusions.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.TilingShellZeroLiteralScreen

open HLOZPathEvents HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroExactCountScreen
open HLOZShellZeroCentralTail
open HLOZShellZeroReplacementProduct HLOZShellZeroReplacementWindows
open TilingCappedMarginalization TilingLazyDecomposition
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber
open TilingStoppedProductDisintegration TilingTypedShellZeroReplacement
open TilingVariableStoppedTracePartition VariableStoppedFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Literal stopped-fibre data at one exact source count and one retained
external word.  The two displayed mass equalities are finite-sum/product
identities.  In particular, this structure contains no inequality between
probabilities or path-event measures. -/
structure LiteralShellZeroStoppedFiberData
    (t : DominoTiling) (m k low externalLow externalHigh total : ℕ)
    (eta : TilingExternalWordCode t) where
  retainedCount : ℕ
  start : Point
  retained : TilingRetainedWord t start retainedCount
  cap : ℕ
  tail : List Direction
  sourceStoppingTime : StepPath → ℕ
  replacementStoppingTime : StepPath → ℕ
  sourceIsStoppingTime : IsFiniteStoppingTime sourceStoppingTime
  replacementIsStoppingTime : IsFiniteStoppingTime replacementStoppingTime
  sourcePredicate : TilingCappedCoordinates retainedCount cap → Prop
  replacementPredicate : TilingCappedCoordinates retainedCount cap → Prop
  distinguished : Finset Point
  upper : TilingCappedMarginalization.TilingAwayDomino
    t start retained distinguished → ℕ
  windows : TilingShellZeroCoordinateWindowData
    (cap := cap) (m := m) (total := total)
      t start retained distinguished upper
  commonFactor : ℝ
  commonFactor_nonneg : 0 ≤ commonFactor
  sourceMass_eq :
    tilingStoppedAcceptedGeometricMass sourceStoppingTime
        t start retained cap tail sourcePredicate =
      tilingShellZeroAllSourceProductMass (cap := cap) (m := m)
        t start retained distinguished upper * commonFactor
  replacementMass_eq :
    tilingStoppedAcceptedGeometricMass replacementStoppingTime
        t start retained cap tail replacementPredicate =
      tilingShellZeroCentralReplacementProductMass (cap := cap) (m := m)
        t start retained distinguished upper
          (centralReplacementUpperCount shellZeroLocalRatioConstant total) *
        commonFactor
  sourceAtom_eq :
    walkLift (tilingPreStoppingFiberEvent sourceStoppingTime
      t start retained cap tail sourcePredicate) =
      shellZeroExactSourceTraceAtom t m k (shellWidth48 m) low
        externalLow externalHigh total eta
  replacementAtom_eq :
    walkLift (tilingPreStoppingFiberEvent replacementStoppingTime
      t start retained cap tail replacementPredicate) =
      shellZeroReplacementTraceAtom t m k (shellWidth48 m) low
        externalLow externalHigh total
          (centralReplacementUpperCount shellZeroLocalRatioConstant total) eta

/-- The only inequality in one literal stopped fibre is derived from the
checked coordinate-window theorem. -/
theorem LiteralShellZeroStoppedFiberData.coordinate_bound
    {t : DominoTiling} {m k low externalLow externalHigh total : ℕ}
    {eta : TilingExternalWordCode t}
    (data : LiteralShellZeroStoppedFiberData t m k low externalLow
      externalHigh total eta)
    (harithmetic : ShellZeroWindowArithmeticAt m) :
    tilingStoppedAcceptedGeometricMass data.sourceStoppingTime
        t data.start data.retained data.cap data.tail data.sourcePredicate ≤
      centralReplacementRatio shellZeroLocalRatioConstant total *
        tilingStoppedAcceptedGeometricMass data.replacementStoppingTime
          t data.start data.retained data.cap data.tail
            data.replacementPredicate := by
  have hproduct := tilingAllSourceProductMass_le_centralReplacement
    t data.start data.retained data.distinguished data.upper harithmetic data.windows
  rw [data.sourceMass_eq, data.replacementMass_eq]
  calc
    tilingShellZeroAllSourceProductMass (cap := data.cap) (m := m)
          t data.start data.retained data.distinguished data.upper *
        data.commonFactor ≤
      (centralReplacementRatio shellZeroLocalRatioConstant total *
          tilingShellZeroCentralReplacementProductMass
            (cap := data.cap) (m := m) t data.start data.retained
              data.distinguished data.upper
                (centralReplacementUpperCount
                  shellZeroLocalRatioConstant total)) * data.commonFactor :=
      mul_le_mul_of_nonneg_right hproduct data.commonFactor_nonneg
    _ = centralReplacementRatio shellZeroLocalRatioConstant total *
        (tilingShellZeroCentralReplacementProductMass
          (cap := data.cap) (m := m) t data.start data.retained
            data.distinguished data.upper
              (centralReplacementUpperCount shellZeroLocalRatioConstant total) *
          data.commonFactor) := by ring

/-- The stopped-fibre atom family at one exact count, constructed from
literal product identities rather than supplied as an abstract family. -/
noncomputable def literalShellZeroStoppedFiberFamily
    (t : DominoTiling) (m k low externalLow externalHigh total : ℕ)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : ∀ eta : TilingExternalWordCode t,
      LiteralShellZeroStoppedFiberData t m k low externalLow externalHigh
        total eta) :
    StoppedFiberReplacementAtomFamily (TilingExternalWordCode t)
      (centralReplacementRatio shellZeroLocalRatioConstant total) where
  tiling := fun _ ↦ t
  retainedCount := fun eta ↦ (data eta).retainedCount
  start := fun eta ↦ (data eta).start
  retained := fun eta ↦ (data eta).retained
  cap := fun eta ↦ (data eta).cap
  tail := fun eta ↦ (data eta).tail
  sourceStoppingTime := fun eta ↦ (data eta).sourceStoppingTime
  replacementStoppingTime := fun eta ↦ (data eta).replacementStoppingTime
  sourceIsStoppingTime := fun eta ↦ (data eta).sourceIsStoppingTime
  replacementIsStoppingTime := fun eta ↦
    (data eta).replacementIsStoppingTime
  sourcePredicate := fun eta ↦ (data eta).sourcePredicate
  replacementPredicate := fun eta ↦ (data eta).replacementPredicate
  q_nonneg := centralReplacementRatio_nonneg
    shellZeroLocalRatioConstant_pos.le total
  coordinate_bound := fun eta ↦ (data eta).coordinate_bound harithmetic

@[simp] theorem literalShellZeroStoppedFiberFamily_sourceAtom
    (t : DominoTiling) (m k low externalLow externalHigh total : ℕ)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : ∀ eta : TilingExternalWordCode t,
      LiteralShellZeroStoppedFiberData t m k low externalLow externalHigh
        total eta)
    (eta : TilingExternalWordCode t) :
    (literalShellZeroStoppedFiberFamily t m k low externalLow externalHigh
      total harithmetic data).sourceAtom eta =
        shellZeroExactSourceTraceAtom t m k (shellWidth48 m) low
          externalLow externalHigh total eta := by
  exact (data eta).sourceAtom_eq

@[simp] theorem literalShellZeroStoppedFiberFamily_replacementAtom
    (t : DominoTiling) (m k low externalLow externalHigh total : ℕ)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : ∀ eta : TilingExternalWordCode t,
      LiteralShellZeroStoppedFiberData t m k low externalLow externalHigh
        total eta)
    (eta : TilingExternalWordCode t) :
    (literalShellZeroStoppedFiberFamily t m k low externalLow externalHigh
      total harithmetic data).replacementAtom eta =
        shellZeroReplacementTraceAtom t m k (shellWidth48 m) low
          externalLow externalHigh total
            (centralReplacementUpperCount shellZeroLocalRatioConstant total)
              eta := by
  exact (data eta).replacementAtom_eq

/-- Transport variable-clock jump data along a pointwise equality of atom
families. -/
def variableClockThresholdJumpReplacementFamilyOfEq
    {Omega Index : Type*} [MeasurableSpace Omega]
    {replacement replacement' : Index → Set Omega}
    (h : ∀ z, replacement z = replacement' z)
    (jump : VariableClockThresholdJumpReplacementFamily replacement') :
    VariableClockThresholdJumpReplacementFamily replacement where
  clock := jump.clock
  traceAt := jump.traceAt
  thresholdCount := jump.thresholdCount
  monotone_thresholdCount := jump.monotone_thresholdCount
  rank := jump.rank
  trace_eq := fun z omega homega ↦ jump.trace_eq z omega (h z ▸ homega)
  count_before := fun z omega homega ↦
    jump.count_before z omega (h z ▸ homega)
  count_at := fun z omega homega ↦ jump.count_at z omega (h z ▸ homega)

/-- Exact source coverage by the literal stopped-fibre atoms at the
reindexed counts `cut + 1 + n`. -/
theorem shellZeroSourceEvent_subset_literalStoppedFibers
    (t : DominoTiling) (m k low externalLow externalHigh cut : ℕ)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : ∀ (n : ℕ) (eta : TilingExternalWordCode t),
      LiteralShellZeroStoppedFiberData t m k low externalLow externalHigh
        (cut + 1 + n) eta) :
    shellZeroSourceEvent t m k (shellWidth48 m) low externalLow
        externalHigh cut ⊆
      ⋃ n : ℕ, ⋃ eta : TilingExternalWordCode t,
        (literalShellZeroStoppedFiberFamily t m k low externalLow
          externalHigh (cut + 1 + n) harithmetic (data n)).sourceAtom eta := by
  intro s hs
  rcases hs with ⟨hreach, hD, htheta, hcut⟩
  let total := (tilingVTwoBases t
    (shellZeroSourceTotalWindow m (shellWidth48 m)) s
      (creationTimeNat m k s)).card
  have htotal : cut + 1 ≤ total := by
    dsimp only [total]
    omega
  let n := total - (cut + 1)
  have htotalEq : cut + 1 + n = total := by
    exact Nat.add_sub_of_le htotal
  apply Set.mem_iUnion.mpr
  refine ⟨n, Set.mem_iUnion.mpr ⟨tilingCreationExternalCode t m k s, ?_⟩⟩
  rw [literalShellZeroStoppedFiberFamily_sourceAtom]
  refine ⟨⟨hreach, hD, htheta, ?_⟩, rfl⟩
  change total = cut + 1 + n
  exact htotalEq.symm

/-- Concrete exact-count screen for the literal HLOZ shell-zero source.
The source partition and variable-clock global disjointness are derived;
neither appears as a premise. -/
noncomputable def literalShellZeroExactCountStoppedFiberScreen
    (t : DominoTiling) (m k low externalLow externalHigh shellScale : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : ∀ (n : ℕ) (eta : TilingExternalWordCode t),
      LiteralShellZeroStoppedFiberData t m k low externalLow externalHigh
        (initialBudget48 shellScale + 1 + n) eta) :
    LiteralShellZeroExactCountStoppedFiberScreen
      (shellZeroSourceEvent t m k (shellWidth48 m) low externalLow
        externalHigh (initialBudget48 shellScale)) shellScale where
  sourceRank := k
  Index := fun _ ↦ TilingExternalWordCode t
  indexCountable := fun _ ↦ inferInstance
  family := fun n ↦ literalShellZeroStoppedFiberFamily t m k low externalLow
    externalHigh (initialBudget48 shellScale + 1 + n) harithmetic (data n)
  source_subset := shellZeroSourceEvent_subset_literalStoppedFibers t m k low
    externalLow externalHigh (initialBudget48 shellScale) harithmetic data
  jump := fun n ↦
    variableClockThresholdJumpReplacementFamilyOfEq
      (fun eta ↦ literalShellZeroStoppedFiberFamily_replacementAtom
        t m k low externalLow externalHigh
          (initialBudget48 shellScale + 1 + n) harithmetic (data n) eta)
      (shellZeroVariableClockJump t m k (shellWidth48 m) low externalLow
        externalHigh (initialBudget48 shellScale + 1 + n)
          (centralReplacementUpperCount shellZeroLocalRatioConstant
            (initialBudget48 shellScale + 1 + n)) hm (by
              unfold replacementCreationRank replacementNewCount
              omega))
  jump_rank := fun _ ↦ rfl

/-- Consequently the literal shell-zero source has the exact geometric
central-count tail, with no screen or probability premise. -/
theorem simpleRandomWalk_shellZeroSourceEvent_le_centralReplacementTailCost
    (t : DominoTiling) (m k low externalLow externalHigh shellScale : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : ∀ (n : ℕ) (eta : TilingExternalWordCode t),
      LiteralShellZeroStoppedFiberData t m k low externalLow externalHigh
        (initialBudget48 shellScale + 1 + n) eta) :
    simpleRandomWalk
        (shellZeroSourceEvent t m k (shellWidth48 m) low externalLow
          externalHigh (initialBudget48 shellScale)) ≤
      centralReplacementTailCost shellZeroLocalRatioConstant
        (initialBudget48 shellScale) := by
  exact (literalShellZeroExactCountStoppedFiberScreen t m k low externalLow
    externalHigh shellScale hm hk harithmetic data).measure_le

/-- The source-correct event used by Proposition 4.8 is the shell-zero
overflow only on the rank stage where `D_eta` holds and `Theta_eta` is empty.
Keeping the preliminary event explicit makes it impossible to accidentally
apply the replacement estimate to an unconditional truncated-clock
overflow. -/
def filteredShellZeroSourceEvent (preliminary : Set WalkPath)
    (t : DominoTiling) (m k low externalLow externalHigh cut : ℕ) :
    Set WalkPath :=
  preliminary ∩
    shellZeroSourceEvent t m k (shellWidth48 m) low externalLow
      externalHigh cut

theorem simpleRandomWalk_filteredShellZeroSourceEvent_le_centralReplacementTailCost
    (preliminary : Set WalkPath)
    (t : DominoTiling) (m k low externalLow externalHigh shellScale : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : ∀ (n : ℕ) (eta : TilingExternalWordCode t),
      LiteralShellZeroStoppedFiberData t m k low externalLow externalHigh
        (initialBudget48 shellScale + 1 + n) eta) :
    simpleRandomWalk
        (filteredShellZeroSourceEvent preliminary t m k low externalLow
          externalHigh (initialBudget48 shellScale)) ≤
      centralReplacementTailCost shellZeroLocalRatioConstant
        (initialBudget48 shellScale) := by
  exact (measure_mono inter_subset_right).trans
    (simpleRandomWalk_shellZeroSourceEvent_le_centralReplacementTailCost
      t m k low externalLow externalHigh shellScale hm hk harithmetic data)

end

end Erdos1165.TilingShellZeroLiteralScreen
