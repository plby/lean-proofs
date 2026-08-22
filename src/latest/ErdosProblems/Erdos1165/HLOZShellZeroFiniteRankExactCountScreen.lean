/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZShellZeroFiniteRankCapScreen
import ErdosProblems.Erdos1165.HLOZShellZeroRankUnionCentralTail

/-!
# Exact-count shell screen with actual-rank unions

This replaces the false common raised rank by a finite rank type at every
exact source count.  Its cardinality is the safe endpoint multiplicity
`2 * (r - s) + 1`.  The fixed-count finite product comparison is unchanged;
only the global disjoint summation pays this multiplicity.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZShellZeroFiniteRankExactCountScreen

open HLOZShellZeroCentralCount HLOZShellZeroCentralTail
open HLOZShellZeroExactCountScreen HLOZShellZeroFiniteRankCapScreen
open HLOZShellZeroRankUnionCentralTail

noncomputable section

/-- Full exact-source-count certificate with a finite actual-rank type at
each count. -/
structure LiteralShellZeroExactCountFiniteRankCapScreen
    (source : Set WalkPath) (C : ℝ) (sourceCut : ℕ) where
  Index : ℕ → Type*
  indexCountable : ∀ n, Countable (Index n)
  Delta : ℕ → Type*
  deltaFintype : ∀ n, Fintype (Delta n)
  family : ∀ n, MonotoneCapStoppedFiberReplacementAtomFamily (Index n)
    (centralReplacementRatio C (sourceCut + 1 + n))
  rankPiece : ∀ n, Delta n → Index n → Set WalkPath
  source_subset : source ⊆ ⋃ n : ℕ, ⋃ z : Index n,
    (family n).sourceAtom z
  replacement_subset : ∀ n z,
    (family n).replacementAtom z ⊆ ⋃ delta, rankPiece n delta z
  measurable_rankPiece : ∀ n delta z, MeasurableSet (rankPiece n delta z)
  disjoint_rankPiece : ∀ n delta, Pairwise fun z w ↦
    Disjoint (rankPiece n delta z) (rankPiece n delta w)
  delta_card : ∀ n, Fintype.card (Delta n) =
    centralReplacementRankMultiplicity C (sourceCut + 1 + n)

def LiteralShellZeroExactCountFiniteRankCapScreen.sourceAt
    {source : Set WalkPath} {C : ℝ} {sourceCut : ℕ}
    (screen : LiteralShellZeroExactCountFiniteRankCapScreen
      source C sourceCut) (n : ℕ) : Set WalkPath :=
  ⋃ z : screen.Index n, (screen.family n).sourceAtom z

noncomputable def LiteralShellZeroExactCountFiniteRankCapScreen.atCount
    {source : Set WalkPath} {C : ℝ} {sourceCut : ℕ}
    (screen : LiteralShellZeroExactCountFiniteRankCapScreen source C sourceCut)
    (n : ℕ) :
    let _ : Countable (screen.Index n) := screen.indexCountable n
    let _ : Fintype (screen.Delta n) := screen.deltaFintype n
    FiniteRankUnionCapStoppedFiberScreen
      (screen.Index n) (screen.Delta n) (screen.sourceAt n)
        (centralReplacementRatio C (sourceCut + 1 + n)) := by
  let _ : Countable (screen.Index n) := screen.indexCountable n
  let _ : Fintype (screen.Delta n) := screen.deltaFintype n
  exact {
    family := screen.family n
    source_subset := Subset.rfl
    rankPiece := screen.rankPiece n
    replacement_subset := screen.replacement_subset n
    measurable_rankPiece := screen.measurable_rankPiece n
    disjoint_rankPiece := screen.disjoint_rankPiece n }

theorem LiteralShellZeroExactCountFiniteRankCapScreen.sourceAt_measure_le
    {source : Set WalkPath} {C : ℝ} {sourceCut n : ℕ}
    (screen : LiteralShellZeroExactCountFiniteRankCapScreen
      source C sourceCut) :
    simpleRandomWalk (screen.sourceAt n) ≤
      ENNReal.ofReal
        (centralReplacementRankUnionRatio C (sourceCut + 1 + n)) := by
  let _ : Countable (screen.Index n) := screen.indexCountable n
  let _ : Fintype (screen.Delta n) := screen.deltaFintype n
  rw [ofReal_centralReplacementRankUnionRatio,
    ← screen.delta_card n]
  exact (screen.atCount n).measure_le

/-- Source-correct exact-count tail with the finite actual-rank
multiplicity included. -/
theorem LiteralShellZeroExactCountFiniteRankCapScreen.measure_le
    {source : Set WalkPath} {C : ℝ} {sourceCut : ℕ}
    (screen : LiteralShellZeroExactCountFiniteRankCapScreen
      source C sourceCut) :
    simpleRandomWalk source ≤
      centralReplacementRankUnionTailCost C sourceCut := by
  calc
    simpleRandomWalk source ≤
        simpleRandomWalk (⋃ n : ℕ, screen.sourceAt n) :=
      measure_mono screen.source_subset
    _ ≤ ∑' n : ℕ, simpleRandomWalk (screen.sourceAt n) :=
      measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal
        (centralReplacementRankUnionRatio C (sourceCut + 1 + n)) := by
      exact ENNReal.tsum_le_tsum fun n ↦ screen.sourceAt_measure_le
    _ = centralReplacementRankUnionTailCost C sourceCut := rfl

end

end Erdos1165.HLOZShellZeroFiniteRankExactCountScreen
