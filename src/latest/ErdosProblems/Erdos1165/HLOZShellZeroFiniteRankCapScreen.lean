/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZShellZeroExactCountScreen
import ErdosProblems.Erdos1165.HLOZShellZeroFiniteRankUnion

/-!
# Cap-union shell screen with finitely many replacement ranks

This is the minimal change to the old fixed-rank cap screen.  The finite
coordinate comparison still produces one replacement atom per source atom.
That replacement atom need only be covered by finitely many measurable rank
pieces.  Pairwise disjointness is required after fixing the rank label, and
the global estimate loses exactly the number of labels.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZShellZeroFiniteRankCapScreen

open HLOZShellZeroExactCountScreen HLOZShellZeroFiniteRankUnion

noncomputable section

/-- One exact-source-count cap screen with a finite actual-rank union. -/
structure FiniteRankUnionCapStoppedFiberScreen
    (Index Delta : Type*) [Countable Index] [Fintype Delta]
    (source : Set WalkPath) (q : ℝ) where
  family : MonotoneCapStoppedFiberReplacementAtomFamily Index q
  source_subset : source ⊆ ⋃ z, family.sourceAtom z
  rankPiece : Delta → Index → Set WalkPath
  replacement_subset : ∀ z,
    family.replacementAtom z ⊆ ⋃ delta, rankPiece delta z
  measurable_rankPiece : ∀ delta z, MeasurableSet (rankPiece delta z)
  disjoint_rankPiece : ∀ delta, Pairwise fun z w ↦
    Disjoint (rankPiece delta z) (rankPiece delta w)

noncomputable def FiniteRankUnionCapStoppedFiberScreen.toCertificate
    {Index Delta : Type*} [Countable Index] [Fintype Delta]
    {source : Set WalkPath} {q : ℝ}
    (screen : FiniteRankUnionCapStoppedFiberScreen Index Delta source q) :
    FiniteRankUnionReplacementCertificate
      (Index := Index) (Delta := Delta) simpleRandomWalk source
        (ENNReal.ofReal q) where
  sourceAtom := screen.family.sourceAtom
  replacement := screen.family.replacementAtom
  rankPiece := screen.rankPiece
  source_subset := screen.source_subset
  atom_le := screen.family.atom_le
  replacement_subset := screen.replacement_subset
  measurable_rankPiece := screen.measurable_rankPiece
  disjoint_rankPiece := screen.disjoint_rankPiece

/-- Exact-count probability estimate with the honest finite-rank
multiplicity. -/
theorem FiniteRankUnionCapStoppedFiberScreen.measure_le
    {Index Delta : Type*} [Countable Index] [Fintype Delta]
    {source : Set WalkPath} {q : ℝ}
    (screen : FiniteRankUnionCapStoppedFiberScreen Index Delta source q) :
    simpleRandomWalk source ≤
      (Fintype.card Delta : ℝ≥0∞) * ENNReal.ofReal q := by
  exact measure_le_rankMultiplicity_mul_of_finiteRankUnionCertificate
    (Index := Index) (Delta := Delta)
    simpleRandomWalk source (ENNReal.ofReal q) screen.toCertificate

end

end Erdos1165.HLOZShellZeroFiniteRankCapScreen
