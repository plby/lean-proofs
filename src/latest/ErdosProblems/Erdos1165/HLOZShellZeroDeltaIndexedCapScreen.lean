/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZShellZeroFiniteRankUnion
import ErdosProblems.Erdos1165.HLOZShellZeroExactCountScreen

/-!
# Cap unions with one fixed replacement clock per endpoint increment

A path-dependent replacement rank should not be hidden inside one stopping
time.  This module instead gives every finite increment its own replacement
cap atom.  The coordinate comparison is against their finite sum.  Global
disjointness is required only after fixing the increment.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZShellZeroDeltaIndexedCapScreen

open HLOZShellZeroExactCountScreen

noncomputable section

/-- A replacement certificate whose atomwise comparison already has the
finite increment sum on its right-hand side. -/
structure DeltaIndexedReplacementCertificate
    {Omega Index Delta : Type*} [MeasurableSpace Omega]
    [Countable Index] [Fintype Delta]
    (mu : Measure Omega) (source : Set Omega) (q : ℝ≥0∞) where
  sourceAtom : Index → Set Omega
  rankPiece : Delta → Index → Set Omega
  source_subset : source ⊆ ⋃ z, sourceAtom z
  atom_le : ∀ z, mu (sourceAtom z) ≤ q * ∑' delta, mu (rankPiece delta z)
  measurable_rankPiece : ∀ delta z, MeasurableSet (rankPiece delta z)
  disjoint_rankPiece : ∀ delta, Pairwise fun z w ↦
    Disjoint (rankPiece delta z) (rankPiece delta w)

theorem DeltaIndexedReplacementCertificate.rankPiece_tsum_le_univ
    {Omega Index Delta : Type*} [MeasurableSpace Omega]
    [Countable Index] [Fintype Delta]
    (mu : Measure Omega) (source : Set Omega) (q : ℝ≥0∞)
    (cert : DeltaIndexedReplacementCertificate
      (Index := Index) (Delta := Delta) mu source q)
    (delta : Delta) :
    (∑' z, mu (cert.rankPiece delta z)) ≤ mu Set.univ := by
  calc
    (∑' z, mu (cert.rankPiece delta z)) =
        mu (⋃ z, cert.rankPiece delta z) :=
      (measure_iUnion (cert.disjoint_rankPiece delta)
        (cert.measurable_rankPiece delta)).symm
    _ ≤ mu Set.univ := measure_mono (Set.subset_univ _)

/-- The honest finite-increment global summation.  No union over different
replacement ranks is asserted disjoint. -/
theorem measure_le_rankMultiplicity_mul_of_deltaIndexedCertificate
    {Omega Index Delta : Type*} [MeasurableSpace Omega]
    [Countable Index] [Fintype Delta]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (source : Set Omega) (q : ℝ≥0∞)
    (cert : DeltaIndexedReplacementCertificate
      (Index := Index) (Delta := Delta) mu source q) :
    mu source ≤ (Fintype.card Delta : ℝ≥0∞) * q := by
  calc
    mu source ≤ mu (⋃ z, cert.sourceAtom z) :=
      measure_mono cert.source_subset
    _ ≤ ∑' z, mu (cert.sourceAtom z) := measure_iUnion_le _
    _ ≤ ∑' z, q * ∑' delta, mu (cert.rankPiece delta z) :=
      ENNReal.tsum_le_tsum cert.atom_le
    _ = q * ∑' z, ∑' delta, mu (cert.rankPiece delta z) :=
      ENNReal.tsum_mul_left
    _ = q * ∑' delta, ∑' z, mu (cert.rankPiece delta z) := by
      congr 1
      exact ENNReal.tsum_comm
    _ ≤ q * ∑' _delta : Delta, (1 : ℝ≥0∞) := by
      apply mul_le_mul_of_nonneg_left
      · apply ENNReal.tsum_le_tsum
        intro delta
        simpa only [measure_univ] using
          cert.rankPiece_tsum_le_univ mu source q delta
      · exact bot_le
    _ = (Fintype.card Delta : ℝ≥0∞) * q := by
      rw [tsum_fintype]
      simp [mul_comm]

/-- Increasing source caps and a separate measurable replacement cap at
each fixed endpoint increment. -/
structure DeltaIndexedMonotoneCapStoppedFiberFamily
    (Index Delta : Type*) [Fintype Delta] (q : ℝ) where
  sourceCap : ℕ → Index → Set WalkPath
  replacementCap : ℕ → Delta → Index → Set WalkPath
  measurable_replacementCap : ∀ cap delta z,
    MeasurableSet (replacementCap cap delta z)
  cap_le : ∀ cap z,
    simpleRandomWalk (sourceCap cap z) ≤ ENNReal.ofReal q *
      ∑' delta, simpleRandomWalk (replacementCap cap delta z)
  source_monotone : ∀ z, Monotone fun cap ↦ sourceCap cap z

def DeltaIndexedMonotoneCapStoppedFiberFamily.sourceAtom
    {Index Delta : Type*} [Fintype Delta] {q : ℝ}
    (data : DeltaIndexedMonotoneCapStoppedFiberFamily Index Delta q)
    (z : Index) : Set WalkPath :=
  ⋃ cap, data.sourceCap cap z

def DeltaIndexedMonotoneCapStoppedFiberFamily.rankPiece
    {Index Delta : Type*} [Fintype Delta] {q : ℝ}
    (data : DeltaIndexedMonotoneCapStoppedFiberFamily Index Delta q)
    (delta : Delta) (z : Index) : Set WalkPath :=
  ⋃ cap, data.replacementCap cap delta z

theorem DeltaIndexedMonotoneCapStoppedFiberFamily.measurable_rankPiece
    {Index Delta : Type*} [Fintype Delta] {q : ℝ}
    (data : DeltaIndexedMonotoneCapStoppedFiberFamily Index Delta q)
    (delta : Delta) (z : Index) :
    MeasurableSet (data.rankPiece delta z) := by
  exact MeasurableSet.iUnion fun cap ↦
    data.measurable_replacementCap cap delta z

theorem DeltaIndexedMonotoneCapStoppedFiberFamily.atom_le
    {Index Delta : Type*} [Fintype Delta] {q : ℝ}
    (data : DeltaIndexedMonotoneCapStoppedFiberFamily Index Delta q)
    (z : Index) :
    simpleRandomWalk (data.sourceAtom z) ≤ ENNReal.ofReal q *
      ∑' delta, simpleRandomWalk (data.rankPiece delta z) := by
  have hlim := tendsto_measure_iUnion_atTop
    (μ := simpleRandomWalk) (data.source_monotone z)
  apply le_of_tendsto hlim
  filter_upwards [] with cap
  calc
    simpleRandomWalk (data.sourceCap cap z) ≤ ENNReal.ofReal q *
        ∑' delta, simpleRandomWalk (data.replacementCap cap delta z) :=
      data.cap_le cap z
    _ ≤ ENNReal.ofReal q *
        ∑' delta, simpleRandomWalk (data.rankPiece delta z) := by
      apply mul_le_mul_of_nonneg_left
      · apply ENNReal.tsum_le_tsum
        intro delta
        exact measure_mono (Set.subset_iUnion
          (fun cap ↦ data.replacementCap cap delta z) cap)
      · exact bot_le

/-- One exact-count screen with genuinely delta-indexed replacement clocks. -/
structure DeltaIndexedCapStoppedFiberScreen
    (Index Delta : Type*) [Countable Index] [Fintype Delta]
    (source : Set WalkPath) (q : ℝ) where
  family : DeltaIndexedMonotoneCapStoppedFiberFamily Index Delta q
  source_subset : source ⊆ ⋃ z, family.sourceAtom z
  disjoint_rankPiece : ∀ delta, Pairwise fun z w ↦
    Disjoint (family.rankPiece delta z) (family.rankPiece delta w)

noncomputable def DeltaIndexedCapStoppedFiberScreen.toCertificate
    {Index Delta : Type*} [Countable Index] [Fintype Delta]
    {source : Set WalkPath} {q : ℝ}
    (screen : DeltaIndexedCapStoppedFiberScreen Index Delta source q) :
    DeltaIndexedReplacementCertificate
      (Index := Index) (Delta := Delta) simpleRandomWalk source
        (ENNReal.ofReal q) where
  sourceAtom := screen.family.sourceAtom
  rankPiece := screen.family.rankPiece
  source_subset := screen.source_subset
  atom_le := screen.family.atom_le
  measurable_rankPiece := screen.family.measurable_rankPiece
  disjoint_rankPiece := screen.disjoint_rankPiece

theorem DeltaIndexedCapStoppedFiberScreen.measure_le
    {Index Delta : Type*} [Countable Index] [Fintype Delta]
    {source : Set WalkPath} {q : ℝ}
    (screen : DeltaIndexedCapStoppedFiberScreen Index Delta source q) :
    simpleRandomWalk source ≤
      (Fintype.card Delta : ℝ≥0∞) * ENNReal.ofReal q := by
  exact measure_le_rankMultiplicity_mul_of_deltaIndexedCertificate
    simpleRandomWalk source (ENNReal.ofReal q) screen.toCertificate

end

end Erdos1165.HLOZShellZeroDeltaIndexedCapScreen
