/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZShellZeroCentralTail
import ErdosProblems.Erdos1165.TilingShellZeroCentralCoordinateBound
import ErdosProblems.Erdos1165.TilingShellZeroSourcePartition
import ErdosProblems.Erdos1165.TilingTypedShellZeroReplacement

/-!
# Global shell-zero screen from exact source counts

The index `n` below represents the exact source count
`initialBudget48 shellScale + 1 + n`.  At that count the finite product
comparison uses exactly

`floor (C / (1+C) * total)`

retained source-window coordinates.  Replacement atoms may have different
physical clocks; their disjointness is derived from the variable-clock
threshold jump at the fixed new rank for that exact count.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZShellZeroExactCountScreen

open HLOZPathEvents HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroCentralTail
open HLOZShellZeroReplacementProduct HLOZShellZeroReplacementWindows
open TilingShellZeroSourcePartition TilingTypedShellZeroReplacement

noncomputable section

/-- A stopped replacement atom obtained as the increasing union of its
finite coordinate caps.  The cap is not added to the global trace index:
finite-cap atoms overlap, whereas their union is the one retained-trace
atom to which the variable-clock disjointness argument applies. -/
structure MonotoneCapStoppedFiberReplacementAtomFamily
    (Index : Type*) (q : ℝ) where
  sourceCap : ℕ → Index → Set WalkPath
  replacementCap : ℕ → Index → Set WalkPath
  measurable_replacementCap : ∀ cap z,
    MeasurableSet (replacementCap cap z)
  cap_le : ∀ cap z,
    simpleRandomWalk (sourceCap cap z) ≤
      ENNReal.ofReal q * simpleRandomWalk (replacementCap cap z)
  source_monotone : ∀ z, Monotone fun cap ↦ sourceCap cap z

def MonotoneCapStoppedFiberReplacementAtomFamily.sourceAtom
    {Index : Type*} {q : ℝ}
  (data : MonotoneCapStoppedFiberReplacementAtomFamily Index q)
    (z : Index) : Set WalkPath :=
  ⋃ cap : ℕ, data.sourceCap cap z

def MonotoneCapStoppedFiberReplacementAtomFamily.replacementAtom
    {Index : Type*} {q : ℝ}
  (data : MonotoneCapStoppedFiberReplacementAtomFamily Index q)
    (z : Index) : Set WalkPath :=
  ⋃ cap : ℕ, data.replacementCap cap z

theorem MonotoneCapStoppedFiberReplacementAtomFamily.measurable_replacementAtom
    {Index : Type*} {q : ℝ}
    (data : MonotoneCapStoppedFiberReplacementAtomFamily Index q)
    (z : Index) :
    MeasurableSet (data.replacementAtom z) := by
  exact MeasurableSet.iUnion fun cap ↦
    data.measurable_replacementCap cap z

theorem MonotoneCapStoppedFiberReplacementAtomFamily.atom_le
    {Index : Type*} {q : ℝ}
    (data : MonotoneCapStoppedFiberReplacementAtomFamily Index q)
    (z : Index) :
    simpleRandomWalk (data.sourceAtom z) ≤
      ENNReal.ofReal q * simpleRandomWalk (data.replacementAtom z) := by
  have hlim := tendsto_measure_iUnion_atTop
    (μ := simpleRandomWalk) (data.source_monotone z)
  apply le_of_tendsto hlim
  filter_upwards [] with cap
  calc
    simpleRandomWalk (data.sourceCap cap z) ≤
        ENNReal.ofReal q *
          simpleRandomWalk (data.replacementCap cap z) :=
      data.cap_le cap z
    _ ≤ ENNReal.ofReal q *
        simpleRandomWalk (data.replacementAtom z) := by
      exact mul_le_mul_of_nonneg_left
        (measure_mono (Set.subset_iUnion
          (fun cap ↦ data.replacementCap cap z) cap)) bot_le

/-- Global certificate for cap-union atoms.  Continuity from below proves
the atomwise estimate; only the full trace unions enter the disjointness
certificate. -/
noncomputable def globalCapStoppedFiberReplacementCertificateOfPairwise
    {Index : Type*} [Countable Index] (q : ℝ)
    (data : MonotoneCapStoppedFiberReplacementAtomFamily Index q)
    (source : Set WalkPath)
    (hsource : source ⊆ ⋃ z, data.sourceAtom z)
    (hdisjoint : Pairwise fun z w ↦
      Disjoint (data.replacementAtom z) (data.replacementAtom w)) :
    GlobalDisjointReplacementCertificate
      (Index := Index) simpleRandomWalk source (ENNReal.ofReal q) where
  sourceAtom := data.sourceAtom
  replacement := data.replacementAtom
  source_subset := hsource
  atom_le := data.atom_le
  measurable_replacement := data.measurable_replacementAtom
  disjoint_replacement := hdisjoint

theorem simpleRandomWalk_source_le_of_exactCountCapStoppedFibers
    {Index : Type*} [Countable Index] (q : ℝ)
    (data : MonotoneCapStoppedFiberReplacementAtomFamily Index q)
    (source : Set WalkPath)
    (hsource : source ⊆ ⋃ z, data.sourceAtom z)
    (hdisjoint : Pairwise fun z w ↦
      Disjoint (data.replacementAtom z) (data.replacementAtom w)) :
    simpleRandomWalk source ≤ ENNReal.ofReal q := by
  exact measure_le_of_globalDisjointReplacementCertificate
    simpleRandomWalk source (ENNReal.ofReal q)
      (globalCapStoppedFiberReplacementCertificateOfPairwise
        q data source hsource hdisjoint)

/-- Exact-count shell-zero screen whose retained-trace atoms are increasing
unions of finite coordinate caps. -/
structure LiteralShellZeroExactCountCapStoppedFiberScreen
    (source : Set WalkPath) (shellScale : ℕ) where
  sourceRank : ℕ
  Index : ℕ → Type*
  indexCountable : ∀ n, Countable (Index n)
  family : ∀ n, MonotoneCapStoppedFiberReplacementAtomFamily (Index n)
    (centralReplacementRatio shellZeroLocalRatioConstant
      (initialBudget48 shellScale + 1 + n))
  source_subset : source ⊆ ⋃ n : ℕ, ⋃ z : Index n,
    (family n).sourceAtom z
  disjoint_replacement : ∀ n, Pairwise fun z w ↦
    Disjoint ((family n).replacementAtom z)
      ((family n).replacementAtom w)

def LiteralShellZeroExactCountCapStoppedFiberScreen.sourceAt
    {source : Set WalkPath} {shellScale : ℕ}
    (screen : LiteralShellZeroExactCountCapStoppedFiberScreen
      source shellScale) (n : ℕ) : Set WalkPath :=
  ⋃ z : screen.Index n, (screen.family n).sourceAtom z

theorem LiteralShellZeroExactCountCapStoppedFiberScreen.sourceAt_measure_le
    {source : Set WalkPath} {shellScale n : ℕ}
    (screen : LiteralShellZeroExactCountCapStoppedFiberScreen
      source shellScale) :
    simpleRandomWalk (screen.sourceAt n) ≤
      ENNReal.ofReal (centralReplacementRatio shellZeroLocalRatioConstant
        (initialBudget48 shellScale + 1 + n)) := by
  let _ : Countable (screen.Index n) := screen.indexCountable n
  exact simpleRandomWalk_source_le_of_exactCountCapStoppedFibers
    (centralReplacementRatio shellZeroLocalRatioConstant
      (initialBudget48 shellScale + 1 + n))
    (screen.family n) (screen.sourceAt n) Subset.rfl
      (screen.disjoint_replacement n)

theorem LiteralShellZeroExactCountCapStoppedFiberScreen.measure_le
    {source : Set WalkPath} {shellScale : ℕ}
    (screen : LiteralShellZeroExactCountCapStoppedFiberScreen
      source shellScale) :
    simpleRandomWalk source ≤
      centralReplacementTailCost shellZeroLocalRatioConstant
        (initialBudget48 shellScale) := by
  calc
    simpleRandomWalk source ≤
        simpleRandomWalk (⋃ n : ℕ, screen.sourceAt n) :=
      measure_mono screen.source_subset
    _ ≤ ∑' n : ℕ, simpleRandomWalk (screen.sourceAt n) :=
      measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal
        (centralReplacementRatio shellZeroLocalRatioConstant
          (initialBudget48 shellScale + 1 + n)) := by
      exact ENNReal.tsum_le_tsum fun n ↦ screen.sourceAt_measure_le
    _ = centralReplacementTailCost shellZeroLocalRatioConstant
        (initialBudget48 shellScale) := rfl

/-- Product certificates plus source coverage at every fixed count.  The
only quantitative field is the finite stopped-coordinate product bound in
`StoppedFiberReplacementAtomFamily`; no path-event probability inequality
is assumed. -/
structure LiteralShellZeroExactCountStoppedFiberScreen
    (source : Set WalkPath) (shellScale : ℕ) where
  sourceRank : ℕ
  Index : ℕ → Type*
  indexCountable : ∀ n, Countable (Index n)
  family : ∀ n, StoppedFiberReplacementAtomFamily (Index n)
    (centralReplacementRatio shellZeroLocalRatioConstant
      (initialBudget48 shellScale + 1 + n))
  source_subset : source ⊆ ⋃ n : ℕ, ⋃ z : Index n,
    (family n).sourceAtom z
  jump : ∀ n, VariableClockThresholdJumpReplacementFamily
    ((family n).replacementAtom)
  jump_rank : ∀ n, (jump n).rank =
    replacementCreationRank sourceRank
      (initialBudget48 shellScale + 1 + n)
      (centralReplacementUpperCount shellZeroLocalRatioConstant
        (initialBudget48 shellScale + 1 + n)) - 1

/-- Exact product identities and a variable-clock threshold jump give the
per-fixed-count global replacement certificate. -/
noncomputable def globalStoppedFiberReplacementCertificateOfVariableClock
    {Index : Type*} [Countable Index] (q : ℝ)
    (data : StoppedFiberReplacementAtomFamily Index q)
    (source : Set WalkPath)
    (hsource : source ⊆ ⋃ z, data.sourceAtom z)
    (jump : VariableClockThresholdJumpReplacementFamily
      data.replacementAtom) :
    GlobalDisjointReplacementCertificate
      (Index := Index) simpleRandomWalk source (ENNReal.ofReal q) :=
  globalDisjointReplacementCertificateOfAtomProducts
    simpleRandomWalk source data.sourceAtom data.replacementAtom q hsource
      data.measurable_replacementAtom
      (pairwise_disjoint_of_variableClockThresholdJump jump)
      data.atomProductCertificate

theorem simpleRandomWalk_source_le_of_exactCountStoppedFibers
    {Index : Type*} [Countable Index] (q : ℝ)
    (data : StoppedFiberReplacementAtomFamily Index q)
    (source : Set WalkPath)
    (hsource : source ⊆ ⋃ z, data.sourceAtom z)
    (jump : VariableClockThresholdJumpReplacementFamily
      data.replacementAtom) :
    simpleRandomWalk source ≤ ENNReal.ofReal q := by
  exact measure_le_of_globalDisjointReplacementCertificate
    simpleRandomWalk source (ENNReal.ofReal q)
      (globalStoppedFiberReplacementCertificateOfVariableClock
        q data source hsource jump)

/-- The fixed-count source union at reindexed count `n`. -/
def LiteralShellZeroExactCountStoppedFiberScreen.sourceAt
    {source : Set WalkPath} {shellScale : ℕ}
    (screen : LiteralShellZeroExactCountStoppedFiberScreen source shellScale)
    (n : ℕ) : Set WalkPath :=
  ⋃ z : screen.Index n, (screen.family n).sourceAtom z

theorem LiteralShellZeroExactCountStoppedFiberScreen.sourceAt_measure_le
    {source : Set WalkPath} {shellScale n : ℕ}
    (screen : LiteralShellZeroExactCountStoppedFiberScreen source shellScale) :
    simpleRandomWalk (screen.sourceAt n) ≤
      ENNReal.ofReal
        (centralReplacementRatio shellZeroLocalRatioConstant
          (initialBudget48 shellScale + 1 + n)) := by
  let _ : Countable (screen.Index n) := screen.indexCountable n
  exact simpleRandomWalk_source_le_of_exactCountStoppedFibers
    (centralReplacementRatio shellZeroLocalRatioConstant
      (initialBudget48 shellScale + 1 + n))
    (screen.family n) (screen.sourceAt n) Subset.rfl (screen.jump n)

/-- Global source-correct shell-zero estimate.  Counts are first fixed,
replacement atoms are summed only within that fixed count using their
common new rank, and the exact-count coefficients are then summed over
`r > initialBudget48 shellScale`. -/
theorem LiteralShellZeroExactCountStoppedFiberScreen.measure_le
    {source : Set WalkPath} {shellScale : ℕ}
    (screen : LiteralShellZeroExactCountStoppedFiberScreen source shellScale) :
    simpleRandomWalk source ≤
      centralReplacementTailCost shellZeroLocalRatioConstant
        (initialBudget48 shellScale) := by
  calc
    simpleRandomWalk source ≤
        simpleRandomWalk (⋃ n : ℕ, screen.sourceAt n) :=
      measure_mono screen.source_subset
    _ ≤ ∑' n : ℕ, simpleRandomWalk (screen.sourceAt n) :=
      measure_iUnion_le _
    _ ≤ ∑' n : ℕ,
        ENNReal.ofReal
          (centralReplacementRatio shellZeroLocalRatioConstant
            (initialBudget48 shellScale + 1 + n)) := by
      exact ENNReal.tsum_le_tsum fun n ↦ screen.sourceAt_measure_le
    _ = centralReplacementTailCost shellZeroLocalRatioConstant
        (initialBudget48 shellScale) := rfl

theorem tsum_simpleRandomWalk_source_ne_top_of_exactCountStoppedFibers
    (source : ℕ → Set WalkPath)
    (screen : ∀ m,
      LiteralShellZeroExactCountStoppedFiberScreen (source m) m) :
    ∑' m : ℕ, simpleRandomWalk (source m) ≠ ∞ := by
  apply ne_top_of_le_ne_top
    (tsum_centralReplacementTailCost_ne_top
      shellZeroLocalRatioConstant_pos)
  exact ENNReal.tsum_le_tsum fun m ↦ (screen m).measure_le

end

end Erdos1165.HLOZShellZeroExactCountScreen
