/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZShellZeroReplacementProduct

/-!
# Finite-rank-union replacement summation

When the replacement rank is not fixed, a replacement atom is partitioned
by a finite actual-rank label.  At each fixed label the trace atoms remain
pairwise disjoint.  Summing the labels costs exactly their finite
multiplicity and does not require the unions over different ranks to be
disjoint.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZShellZeroFiniteRankUnion

noncomputable section

/-- Global replacement certificate with disjointness only after fixing a
finite rank label. -/
structure FiniteRankUnionReplacementCertificate
    {Omega Index Delta : Type*} [MeasurableSpace Omega]
    [Countable Index] [Fintype Delta]
    (mu : Measure Omega) (source : Set Omega) (q : ℝ≥0∞) where
  sourceAtom : Index → Set Omega
  replacement : Index → Set Omega
  rankPiece : Delta → Index → Set Omega
  source_subset : source ⊆ ⋃ z, sourceAtom z
  atom_le : ∀ z, mu (sourceAtom z) ≤ q * mu (replacement z)
  replacement_subset : ∀ z, replacement z ⊆ ⋃ delta, rankPiece delta z
  measurable_rankPiece : ∀ delta z, MeasurableSet (rankPiece delta z)
  disjoint_rankPiece : ∀ delta, Pairwise fun z w ↦
    Disjoint (rankPiece delta z) (rankPiece delta w)

theorem rankPiece_tsum_le_univ
    {Omega Index Delta : Type*} [MeasurableSpace Omega]
    [Countable Index] [Fintype Delta]
    (mu : Measure Omega) (source : Set Omega) (q : ℝ≥0∞)
    (cert : FiniteRankUnionReplacementCertificate
      (Index := Index) (Delta := Delta) mu source q)
    (delta : Delta) :
    (∑' z, mu (cert.rankPiece delta z)) ≤ mu Set.univ := by
  calc
    (∑' z, mu (cert.rankPiece delta z)) =
        mu (⋃ z, cert.rankPiece delta z) :=
      (measure_iUnion (cert.disjoint_rankPiece delta)
        (cert.measurable_rankPiece delta)).symm
    _ ≤ mu Set.univ := measure_mono (Set.subset_univ _)

/-- Finite-rank-union analogue of global disjoint replacement summation.
The sole loss is the number of possible actual ranks. -/
theorem measure_le_rankMultiplicity_mul_of_finiteRankUnionCertificate
    {Omega Index Delta : Type*} [MeasurableSpace Omega]
    [Countable Index] [Fintype Delta]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (source : Set Omega) (q : ℝ≥0∞)
    (cert : FiniteRankUnionReplacementCertificate
      (Index := Index) (Delta := Delta) mu source q) :
    mu source ≤ (Fintype.card Delta : ℝ≥0∞) * q := by
  calc
    mu source ≤ mu (⋃ z, cert.sourceAtom z) :=
      measure_mono cert.source_subset
    _ ≤ ∑' z, mu (cert.sourceAtom z) := measure_iUnion_le _
    _ ≤ ∑' z, q * mu (cert.replacement z) :=
      ENNReal.tsum_le_tsum cert.atom_le
    _ = q * ∑' z, mu (cert.replacement z) := ENNReal.tsum_mul_left
    _ ≤ q * ∑' z, ∑' delta, mu (cert.rankPiece delta z) := by
      apply mul_le_mul_of_nonneg_left
      · apply ENNReal.tsum_le_tsum
        intro z
        exact (measure_mono (cert.replacement_subset z)).trans
          (measure_iUnion_le _)
      · exact bot_le
    _ = q * ∑' delta, ∑' z, mu (cert.rankPiece delta z) := by
      congr 1
      exact ENNReal.tsum_comm
    _ ≤ q * ∑' _delta : Delta, (1 : ℝ≥0∞) := by
      apply mul_le_mul_of_nonneg_left
      · apply ENNReal.tsum_le_tsum
        intro delta
        simpa only [measure_univ] using
          rankPiece_tsum_le_univ mu source q cert delta
      · exact bot_le
    _ = (Fintype.card Delta : ℝ≥0∞) * q := by
      rw [tsum_fintype]
      simp [mul_comm]

end

end Erdos1165.HLOZShellZeroFiniteRankUnion
