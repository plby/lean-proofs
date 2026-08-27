/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTBatchedSourceData
import ErdosProblems.Erdos4b.FGKMTNaturalBatches

/-! # The actual natural-stage family of disjoint prime batches -/

namespace Erdos4b.FGKMT.SourceGeometricPartition

noncomputable section

open FiniteEdgeFamily

variable {a c e : ℝ} {x : ℕ} {D : SourceProbabilityData c e x}
  {b : ResidueAssignment (sourceSmallPrimes a x)} {H : RegularSourceConditions D a b}
  (B : SourceGeometricPartition H)

def labels (j : ℕ) : Finset (commonPinnedPrimeSet (x / 2) x) :=
  numberedBatchLabels B.assignment j

def family (j : ℕ) :
    FiniteEdgeFamily (B.labels j) (integerWeightWindow (sourceIntervalLength c x)) ℕ :=
  H.edgeFamily.numberedBatchFamily B.assignment j

theorem labels_disjoint {j k : ℕ} (hjk : j ≠ k) : Disjoint (B.labels j) (B.labels k) :=
  numberedBatchLabels_disjoint B.assignment hjk

theorem labels_nonempty_of_lt {j : ℕ} (hj : j < sourceBatchCount x) :
    (B.labels j).Nonempty := by
  rw [labels, numberedBatchLabels_of_lt B.assignment hj]
  exact B.labels_nonempty ⟨j, hj⟩

theorem labels_card_pos {j : ℕ} (hj : j < sourceBatchCount x) :
    0 < Fintype.card (B.labels j) := by
  rw [Fintype.card_coe]
  exact Finset.card_pos.mpr (B.labels_nonempty_of_lt hj)

theorem labels_card_le (j : ℕ) : Fintype.card (B.labels j) ≤ x := by
  rw [Fintype.card_coe]
  exact (numberedBatchLabels_card_le B.assignment j).trans
    (by simpa only [Fintype.card_coe] using commonPinnedPrimeSet_card_le_endpoint x)

theorem family_vertices (j : ℕ) : (B.family j).vertices = H.edgeFamily.vertices := rfl

theorem family_rank (j : ℕ) : (B.family j).rank = D.dimension := rfl

theorem family_edge (j : ℕ) (p : B.labels j)
    (n : integerWeightWindow (sourceIntervalLength c x)) :
    (B.family j).edge p n = H.edgeFamily.edge p.val n := rfl

theorem family_mass (j : ℕ) (p : B.labels j)
    (n : integerWeightWindow (sourceIntervalLength c x)) :
    (B.family j).mass p n = H.edgeFamily.mass p.val n := rfl

theorem family_degree_error {j : ℕ} (hj : j < sourceBatchCount x)
    {q : ℕ} (hq : q ∈ H.edgeFamily.vertices) :
    |(B.family j).degree q - geometricBatchTarget j| ≤
      2 * (1 / Real.log (Real.log (x : ℝ)) ^ 2) := by
  change |(H.edgeFamily.restrictLabels (numberedBatchLabels B.assignment j)).degree q -
    geometricBatchTarget j| ≤ _
  rw [numberedBatchLabels_of_lt B.assignment hj]
  exact (B.degree_error q hq ⟨j, hj⟩).le

theorem family_vertexMass_le (j : ℕ) (p : B.labels j) (q : ℕ) :
    (B.family j).vertexMass p q ≤ (x : ℝ) ^ (-3 / 5 : ℝ) :=
  H.edgeFamily_sparse p.val q

theorem family_codegree_le (j : ℕ) {q q' : ℕ}
    (hq : q ∈ H.edgeFamily.vertices) (hq' : q' ∈ H.edgeFamily.vertices) (hne : q ≠ q') :
    (B.family j).codegree q q' ≤ (x : ℝ) ^ (-1 / 20 : ℝ) :=
  (H.edgeFamily.numberedBatchFamily_codegree_le B.assignment j q q').trans
    (H.edgeFamily_codegree_le hq hq' hne)

end

end Erdos4b.FGKMT.SourceGeometricPartition
