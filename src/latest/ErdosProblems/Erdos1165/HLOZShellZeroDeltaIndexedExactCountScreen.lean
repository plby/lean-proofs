/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZShellZeroDeltaIndexedCapScreen
import ErdosProblems.Erdos1165.HLOZShellZeroRankUnionCentralTail

/-!
# Exact-count closure for delta-indexed replacement clocks

At every exact source count, each possible endpoint increment has its own
fixed replacement clock.  The finite multiplicity is then absorbed by the
rank-union central tail.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZShellZeroDeltaIndexedExactCountScreen

open HLOZShellZeroCentralCount HLOZShellZeroDeltaIndexedCapScreen
open HLOZShellZeroRankUnionCentralTail

noncomputable section

structure LiteralShellZeroExactCountDeltaIndexedCapScreen
    (source : Set WalkPath) (C : ℝ) (sourceCut : ℕ) where
  Index : ℕ → Type*
  indexCountable : ∀ n, Countable (Index n)
  Delta : ℕ → Type*
  deltaFintype : ∀ n, Fintype (Delta n)
  family : ∀ n, DeltaIndexedMonotoneCapStoppedFiberFamily
    (Index n) (Delta n) (centralReplacementRatio C (sourceCut + 1 + n))
  source_subset : source ⊆ ⋃ n : ℕ, ⋃ z : Index n,
    (family n).sourceAtom z
  disjoint_rankPiece : ∀ n delta, Pairwise fun z w ↦
    Disjoint ((family n).rankPiece delta z)
      ((family n).rankPiece delta w)
  delta_card : ∀ n, Fintype.card (Delta n) =
    centralReplacementRankMultiplicity C (sourceCut + 1 + n)

def LiteralShellZeroExactCountDeltaIndexedCapScreen.sourceAt
    {source : Set WalkPath} {C : ℝ} {sourceCut : ℕ}
    (screen : LiteralShellZeroExactCountDeltaIndexedCapScreen
      source C sourceCut) (n : ℕ) : Set WalkPath :=
  let _ : Fintype (screen.Delta n) := screen.deltaFintype n
  ⋃ z : screen.Index n, (screen.family n).sourceAtom z

noncomputable def LiteralShellZeroExactCountDeltaIndexedCapScreen.atCount
    {source : Set WalkPath} {C : ℝ} {sourceCut : ℕ}
    (screen : LiteralShellZeroExactCountDeltaIndexedCapScreen
      source C sourceCut) (n : ℕ) :
    let _ : Countable (screen.Index n) := screen.indexCountable n
    let _ : Fintype (screen.Delta n) := screen.deltaFintype n
    DeltaIndexedCapStoppedFiberScreen (screen.Index n) (screen.Delta n)
      (screen.sourceAt n)
      (centralReplacementRatio C (sourceCut + 1 + n)) := by
  let _ : Countable (screen.Index n) := screen.indexCountable n
  let _ : Fintype (screen.Delta n) := screen.deltaFintype n
  exact {
    family := screen.family n
    source_subset := by
      change (⋃ z, (screen.family n).sourceAtom z) ⊆ _
      exact Subset.rfl
    disjoint_rankPiece := screen.disjoint_rankPiece n }

theorem LiteralShellZeroExactCountDeltaIndexedCapScreen.sourceAt_measure_le
    {source : Set WalkPath} {C : ℝ} {sourceCut n : ℕ}
    (screen : LiteralShellZeroExactCountDeltaIndexedCapScreen
      source C sourceCut) :
    simpleRandomWalk (screen.sourceAt n) ≤
      ENNReal.ofReal
        (centralReplacementRankUnionRatio C (sourceCut + 1 + n)) := by
  let _ : Countable (screen.Index n) := screen.indexCountable n
  let _ : Fintype (screen.Delta n) := screen.deltaFintype n
  rw [ofReal_centralReplacementRankUnionRatio,
    ← screen.delta_card n]
  exact (screen.atCount n).measure_le

theorem LiteralShellZeroExactCountDeltaIndexedCapScreen.measure_le
    {source : Set WalkPath} {C : ℝ} {sourceCut : ℕ}
    (screen : LiteralShellZeroExactCountDeltaIndexedCapScreen
      source C sourceCut) :
    simpleRandomWalk source ≤
      centralReplacementRankUnionTailCost C sourceCut := by
  calc
    simpleRandomWalk source ≤
        simpleRandomWalk (⋃ n : ℕ, screen.sourceAt n) :=
      measure_mono (by
        intro s hs
        rcases Set.mem_iUnion.mp (screen.source_subset hs) with ⟨n, hn⟩
        exact Set.mem_iUnion.mpr ⟨n, hn⟩)
    _ ≤ ∑' n : ℕ, simpleRandomWalk (screen.sourceAt n) :=
      measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal
        (centralReplacementRankUnionRatio C (sourceCut + 1 + n)) := by
      exact ENNReal.tsum_le_tsum fun n ↦ screen.sourceAt_measure_le
    _ = centralReplacementRankUnionTailCost C sourceCut := rfl

end

end Erdos1165.HLOZShellZeroDeltaIndexedExactCountScreen
