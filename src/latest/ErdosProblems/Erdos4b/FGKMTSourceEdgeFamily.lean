/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTRegularSourceData
import ErdosProblems.Erdos4b.FGKMTFiniteEdgeFamily

/-! # The independent edge family built from the actual source translations -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def RegularSourceConditions.edgeFamily {a c e : ℝ} {x : ℕ}
    {D : SourceProbabilityData c e x} {b : ResidueAssignment (sourceSmallPrimes a x)}
    (H : RegularSourceConditions D a b) :
    FiniteEdgeFamily (commonPinnedPrimeSet (x / 2) x)
      (integerWeightWindow (sourceIntervalLength c x)) ℕ where
  vertices := D.sourceRegularVertices a b
  rank := D.dimension
  edge := fun p n =>
    D.primeTupleEdge (sourceSmallPrimes a x) (D.sourceRegularVertices a b) b p.val n.val
  mass := fun p n => D.conditionedTupleMass (sourceSmallPrimes a x) b p.val n.val
  mass_nonneg := fun p n =>
    D.conditionedTupleMass_nonneg (sourceSmallPrimes a x) b p.property n.val
  mass_sum_one := by
    intro p
    exact (Finset.sum_coe_sort (integerWeightWindow (sourceIntervalLength c x))
      (D.conditionedTupleMass (sourceSmallPrimes a x) b p.val)).trans
        (D.conditionedTupleMass_sum_one (sourceSmallPrimes_prime a x) b p.property
          H.log_ge H.interval_nonneg)
  edge_subset := fun p n => D.primeTupleEdge_subset (sourceSmallPrimes a x)
    (D.sourceRegularVertices a b) b p.val n.val
  edge_card_le := fun p n => D.primeTupleEdge_card_le (sourceSmallPrimes a x)
    (D.sourceRegularVertices a b) b (mem_commonPinnedPrimeSet.mp p.property).2.2.pos n.val

theorem RegularSourceConditions.edgeFamily_vertexMass {a c e : ℝ} {x : ℕ}
    {D : SourceProbabilityData c e x} {b : ResidueAssignment (sourceSmallPrimes a x)}
    (H : RegularSourceConditions D a b) (p : commonPinnedPrimeSet (x / 2) x) (q : ℕ) :
    H.edgeFamily.vertexMass p q =
      D.primeTupleEdgeProbability (sourceSmallPrimes a x)
        (D.sourceRegularVertices a b) b p.val q := by
  classical
  exact Finset.sum_coe_sort (integerWeightWindow (sourceIntervalLength c x)) (fun n : ℤ =>
    if q ∈ D.primeTupleEdge (sourceSmallPrimes a x) (D.sourceRegularVertices a b) b p.val n
      then D.conditionedTupleMass (sourceSmallPrimes a x) b p.val n else 0)

theorem RegularSourceConditions.edgeFamily_pairMass {a c e : ℝ} {x : ℕ}
    {D : SourceProbabilityData c e x} {b : ResidueAssignment (sourceSmallPrimes a x)}
    (H : RegularSourceConditions D a b) (p : commonPinnedPrimeSet (x / 2) x) (q q' : ℕ) :
    H.edgeFamily.pairMass p q q' =
      D.primeTupleEdgePairProbability (sourceSmallPrimes a x)
        (D.sourceRegularVertices a b) b p.val q q' := by
  classical
  exact Finset.sum_coe_sort (integerWeightWindow (sourceIntervalLength c x)) (fun n : ℤ =>
    if q ∈ D.primeTupleEdge (sourceSmallPrimes a x) (D.sourceRegularVertices a b) b p.val n ∧
        q' ∈ D.primeTupleEdge (sourceSmallPrimes a x) (D.sourceRegularVertices a b) b p.val n
      then D.conditionedTupleMass (sourceSmallPrimes a x) b p.val n else 0)

theorem RegularSourceConditions.edgeFamily_degree {a c e : ℝ} {x : ℕ}
    {D : SourceProbabilityData c e x} {b : ResidueAssignment (sourceSmallPrimes a x)}
    (H : RegularSourceConditions D a b) (q : ℕ) :
    H.edgeFamily.degree q = D.primeTupleExpectedDegree (sourceSmallPrimes a x)
      (D.sourceRegularVertices a b) b q := by
  unfold FiniteEdgeFamily.degree
  simp_rw [H.edgeFamily_vertexMass]
  exact Finset.sum_coe_sort (commonPinnedPrimeSet (x / 2) x) (fun p =>
    D.primeTupleEdgeProbability (sourceSmallPrimes a x) (D.sourceRegularVertices a b) b p q)

theorem RegularSourceConditions.edgeFamily_codegree {a c e : ℝ} {x : ℕ}
    {D : SourceProbabilityData c e x} {b : ResidueAssignment (sourceSmallPrimes a x)}
    (H : RegularSourceConditions D a b) (q q' : ℕ) :
    H.edgeFamily.codegree q q' = ∑ p ∈ commonPinnedPrimeSet (x / 2) x,
      D.primeTupleEdgePairProbability (sourceSmallPrimes a x)
        (D.sourceRegularVertices a b) b p q q' := by
  unfold FiniteEdgeFamily.codegree
  simp_rw [H.edgeFamily_pairMass]
  exact Finset.sum_coe_sort (commonPinnedPrimeSet (x / 2) x) (fun p =>
    D.primeTupleEdgePairProbability (sourceSmallPrimes a x)
      (D.sourceRegularVertices a b) b p q q')

theorem RegularSourceConditions.edgeFamily_degree_error {a c e : ℝ} {x : ℕ}
    {D : SourceProbabilityData c e x} {b : ResidueAssignment (sourceSmallPrimes a x)}
    (H : RegularSourceConditions D a b) {q : ℕ} (hq : q ∈ H.edgeFamily.vertices) :
    |H.edgeFamily.degree q - D.expectedDegreeScale (sourceSmallPrimes a x)| ≤
      1 / Real.log (Real.log (x : ℝ)) ^ 2 := by
  rw [H.edgeFamily_degree]
  exact H.degree q hq

theorem RegularSourceConditions.edgeFamily_sparse {a c e : ℝ} {x : ℕ}
    {D : SourceProbabilityData c e x} {b : ResidueAssignment (sourceSmallPrimes a x)}
    (H : RegularSourceConditions D a b) (p : commonPinnedPrimeSet (x / 2) x) (q : ℕ) :
    H.edgeFamily.vertexMass p q ≤ (x : ℝ) ^ (-3 / 5 : ℝ) := by
  rw [H.edgeFamily_vertexMass]
  exact H.sparse p.val p.property q

theorem RegularSourceConditions.edgeFamily_codegree_le {a c e : ℝ} {x : ℕ}
    {D : SourceProbabilityData c e x} {b : ResidueAssignment (sourceSmallPrimes a x)}
    (H : RegularSourceConditions D a b) {q q' : ℕ}
    (hq : q ∈ H.edgeFamily.vertices) (hq' : q' ∈ H.edgeFamily.vertices) (hne : q ≠ q') :
    H.edgeFamily.codegree q q' ≤ (x : ℝ) ^ (-1 / 20 : ℝ) := by
  rw [H.edgeFamily_codegree]
  exact H.codegree q hq q' hq' hne

end

end Erdos4b.FGKMT
