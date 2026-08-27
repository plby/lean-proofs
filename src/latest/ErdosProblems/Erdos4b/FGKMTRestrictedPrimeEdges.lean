/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTRegularVertexBounds

/-! # Restricting the same source edge distributions to retained vertices -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

theorem SourceProbabilityData.primeTupleEdge_restrict {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S U Q : Finset ℕ) (b : ResidueAssignment S)
    (hU : U ⊆ Q) (p : ℕ) (n : ℤ) :
    D.primeTupleEdge S U b p n = U ∩ D.primeTupleEdge S Q b p n := by
  ext q
  rw [D.mem_primeTupleEdge, Finset.mem_inter, D.mem_primeTupleEdge]
  constructor
  · rintro ⟨hq, ht, hs⟩
    exact ⟨hq, hU hq, ht, hs⟩
  · rintro ⟨hq, _hqQ, ht, hs⟩
    exact ⟨hq, ht, hs⟩

theorem SourceProbabilityData.primeTupleEdgeProbability_restrict {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S U Q : Finset ℕ) (b : ResidueAssignment S)
    (hU : U ⊆ Q) {q : ℕ} (hq : q ∈ U) (p : ℕ) :
    D.primeTupleEdgeProbability S U b p q = D.primeTupleEdgeProbability S Q b p q := by
  classical
  unfold primeTupleEdgeProbability
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [D.primeTupleEdge_restrict S U Q b hU p n, Finset.mem_inter, hq, true_and]

theorem SourceProbabilityData.primeTupleExpectedDegree_restrict {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S U Q : Finset ℕ) (b : ResidueAssignment S)
    (hU : U ⊆ Q) {q : ℕ} (hq : q ∈ U) :
    D.primeTupleExpectedDegree S U b q = D.primeTupleExpectedDegree S Q b q := by
  unfold primeTupleExpectedDegree
  exact Finset.sum_congr rfl fun p _hp => D.primeTupleEdgeProbability_restrict S U Q b hU hq p

theorem SourceProbabilityData.primeTupleEdgePairProbability_restrict {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S U Q : Finset ℕ) (b : ResidueAssignment S)
    (hU : U ⊆ Q) {q q' : ℕ} (hq : q ∈ U) (hq' : q' ∈ U) (p : ℕ) :
    D.primeTupleEdgePairProbability S U b p q q' =
      D.primeTupleEdgePairProbability S Q b p q q' := by
  classical
  unfold primeTupleEdgePairProbability
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [D.primeTupleEdge_restrict S U Q b hU p n, Finset.mem_inter, hq, hq', true_and]

theorem eventually_sourceRegularVertices_degree {a c e : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x,
      ∀ b : ResidueAssignment (sourceSmallPrimes a x), ∀ q ∈ D.sourceRegularVertices a b,
        |D.primeTupleExpectedDegree (sourceSmallPrimes a x) (D.sourceRegularVertices a b) b q -
          D.expectedDegreeScale (sourceSmallPrimes a x)| ≤
            1 / Real.log (Real.log (x : ℝ)) ^ 2 := by
  filter_upwards [eventually_actualSource_expectedDegree_good_vertices (e := e) ha hc] with x hx
  intro D b q hq
  have hmem := (D.mem_sourceRegularVertices a b q).mp hq
  rw [D.primeTupleExpectedDegree_restrict (sourceSmallPrimes a x)
    (D.sourceRegularVertices a b) (sourceSievingPrimes c x) b
    (D.sourceRegularVertices_subset_source a b) hq]
  exact hx D b q hmem.1 hmem.2.1 hmem.2.2.1 hmem.2.2.2

theorem eventually_sourceRegularVertices_sparsity {a c e : ℝ}
    (ha : 0 < a) (he : e ≤ 1 / 120) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x,
      ∀ b : ResidueAssignment (sourceSmallPrimes a x),
      ∀ p ∈ commonPinnedPrimeSet (x / 2) x, ∀ q : ℕ,
        D.primeTupleEdgeProbability (sourceSmallPrimes a x) (D.sourceRegularVertices a b) b p q ≤
          (x : ℝ) ^ (-3 / 5 : ℝ) := by
  filter_upwards [eventually_primeTupleEdgeProbability_le (c := c) he,
    eventually_sourceSmallPrimes_le ha] with x hsparse hupper
  intro D b p hp q
  exact hsparse D (sourceSmallPrimes a x) (sourceSmallPrimes_prime a x) hupper
    (D.sourceRegularVertices a b) (D.sourceRegularVertices_prime a b) b p hp q

theorem eventually_sourceRegularVertices_codegree {a c e : ℝ}
    (ha : 0 < a) (hc : 0 < c) (he : e ≤ 1 / 120) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x,
      ∀ b : ResidueAssignment (sourceSmallPrimes a x), ∀ q ∈ D.sourceRegularVertices a b,
      ∀ q' ∈ D.sourceRegularVertices a b, q ≠ q' →
        (∑ p ∈ commonPinnedPrimeSet (x / 2) x,
          D.primeTupleEdgePairProbability (sourceSmallPrimes a x)
            (D.sourceRegularVertices a b) b p q q') ≤ (x : ℝ) ^ (-1 / 20 : ℝ) := by
  filter_upwards [eventually_source_primeTupleEdge_codegree_le hc he,
    eventually_sourceSmallPrimes_le ha] with x hcode hupper
  intro D b q hq q' hq' hne
  have hsub := D.sourceRegularVertices_subset_source a b
  calc
    _ = ∑ p ∈ commonPinnedPrimeSet (x / 2) x,
        D.primeTupleEdgePairProbability (sourceSmallPrimes a x)
          (sourceSievingPrimes c x) b p q q' :=
      Finset.sum_congr rfl fun p _hp => D.primeTupleEdgePairProbability_restrict
        (sourceSmallPrimes a x) (D.sourceRegularVertices a b)
          (sourceSievingPrimes c x) b hsub hq hq' p
    _ ≤ _ := hcode D (sourceSmallPrimes a x) (sourceSmallPrimes_prime a x) hupper
      b q (hsub hq) q' (hsub hq') hne

end

end Erdos4b.FGKMT
