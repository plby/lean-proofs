import ErdosProblems.Erdos88.GraphQuadratic
import ErdosProblems.Erdos88.RobustRank101

open scoped BigOperators

namespace Erdos88
namespace GraphQuadratic

open Classical

lemma graphSliceMatrix_diagonal {n : ℕ} (G : SimpleGraph (Fin n))
    (i : Fin n) : graphSliceMatrix G i i = 0 := by
  rw [graphSliceMatrix_apply]
  simp

lemma trace_graphSliceMatrix {n : ℕ} (G : SimpleGraph (Fin n)) :
    BooleanSlices.trace (graphSliceMatrix G) = 0 := by
  simp [BooleanSlices.trace, graphSliceMatrix_diagonal]

lemma frobeniusSq_graphSliceMatrix {n : ℕ} (G : SimpleGraph (Fin n)) :
    BooleanSlices.frobeniusSq (graphSliceMatrix G) =
      (G.edgeFinset.card : ℝ) / 32 := by
  have hcount :
      (∑ i : Fin n, ∑ j : Fin n,
        RobustRank.graphAdjacencyMatrix G i j) =
        2 * (G.edgeFinset.card : ℝ) := by
    simpa using
      (RobustRank.sum_graphAdjacencyMatrix_eq_twice_edgeCount G
        (Finset.univ : Finset (Fin n)))
  rw [BooleanSlices.frobeniusSq]
  simp only [graphSliceMatrix]
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        ((1 / 8 : ℝ) * RobustRank.graphAdjacencyMatrix G i j) ^ 2) =
        (1 / 64 : ℝ) *
          (∑ i : Fin n, ∑ j : Fin n,
            RobustRank.graphAdjacencyMatrix G i j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : G.Adj i j <;>
        simp [RobustRank.graphAdjacencyMatrix, hij] <;> norm_num
    _ = (G.edgeFinset.card : ℝ) / 32 := by rw [hcount]; ring

noncomputable def graphEffectiveLinear {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → ℝ) (i : Fin n) : ℝ :=
  c i + (G.degree i : ℝ) / 2

lemma graphSliceLinear_eq_half_effective {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → ℝ) (i : Fin n) :
    graphSliceLinear G c i = graphEffectiveLinear G c i / 2 := by
  simp [graphSliceLinear, graphEffectiveLinear]
  ring

lemma vectorSqNorm_graphSliceLinear {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → ℝ) :
    BooleanSlices.vectorSqNorm (graphSliceLinear G c) =
      (1 / 4 : ℝ) * ∑ i, (graphEffectiveLinear G c i) ^ 2 := by
  rw [BooleanSlices.vectorSqNorm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [graphSliceLinear_eq_half_effective]
  ring

lemma graphSliceConstant_eq_expectation_half {n : ℕ}
    (G : SimpleGraph (Fin n))
    (e₀ : ℝ) (c : Fin n → ℝ) :
    graphSliceConstant G e₀ c =
      Probability.expectation (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial G e₀ c) := by
  rw [Probability.expectation_perturbedEdgePolynomial G (by norm_num) (by norm_num)]
  simp [graphSliceConstant] <;> ring

lemma uniformVariance_finset_eq_probability_half {n : ℕ}
    (X : Finset (Fin n) → ℝ) :
    BooleanSlices.uniformVariance X =
      Probability.variance (1 / 2 : ℝ) X := by
  rw [BooleanSlices.uniformVariance, Probability.variance,
    BooleanSlices.uniformExpectation_finset_eq_probability_half]
  congr 1
  funext W
  rw [BooleanSlices.uniformExpectation_finset_eq_probability_half]

/-- Exact variance identity (4.34) for the perturbed induced-edge count. -/
theorem variance_half_perturbedEdgePolynomial {n : ℕ}
    (G : SimpleGraph (Fin n))
    (e₀ : ℝ) (c : Fin n → ℝ) :
    Probability.variance (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial G e₀ c) =
      (1 / 4 : ℝ) * ∑ i, (graphEffectiveLinear G c i) ^ 2 +
        (G.edgeFinset.card : ℝ) / 16 := by
  rw [← uniformVariance_finset_eq_probability_half]
  have hfun : Probability.perturbedEdgePolynomial G e₀ c =
      BooleanSlices.sliceQuadratic (graphSliceConstant G e₀ c)
        (graphSliceLinear G c) (graphSliceMatrix G) := by
    funext W
    exact (sliceQuadratic_graph_coefficients G e₀ c W).symm
  rw [hfun]
  rw [BooleanSlices.rademacher_sliceQuadratic_variance_symmetric]
  · rw [frobeniusSq_graphSliceMatrix, vectorSqNorm_graphSliceLinear]
    simp_rw [graphSliceMatrix_diagonal]
    simp
    ring
  · exact graphSliceMatrix_symmetric G

lemma sum_graphEffectiveLinear {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → ℝ) :
    (∑ i, graphEffectiveLinear G c i) =
      (∑ i, c i) + (G.edgeFinset.card : ℝ) := by
  have hdeg : (∑ i : Fin n, (G.degree i : ℝ)) =
      2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  simp only [graphEffectiveLinear, Finset.sum_add_distrib,
    ← Finset.sum_div]
  rw [hdeg]
  ring

/-- The linear Walsh part alone already has variance of order `n^3`
when the graph has positive quadratic edge density and the perturbation is
coordinatewise nonnegative. -/
theorem variance_half_perturbedEdgePolynomial_lower {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    {a : ℝ} (hn : 0 < n) (ha : 0 ≤ a)
    (hc : ∀ i, 0 ≤ c i)
    (hedge : a * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ)) :
    (a ^ 2 / 4) * (n : ℝ) ^ 3 ≤
      Probability.variance (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial G e₀ c) := by
  let d : Fin n → ℝ := graphEffectiveLinear G c
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    exact add_nonneg (hc i) (div_nonneg (by positivity) (by norm_num))
  have hsumNonneg : 0 ≤ ∑ i, d i := Finset.sum_nonneg fun i _ => hd i
  have hcSum : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  have hsum : (G.edgeFinset.card : ℝ) ≤ ∑ i, d i := by
    rw [sum_graphEffectiveLinear]
    linarith
  have hedgeNonneg : 0 ≤ (G.edgeFinset.card : ℝ) := by positivity
  have hedgeSq : (a * (n : ℝ) ^ 2) ^ 2 ≤
      ((G.edgeFinset.card : ℝ)) ^ 2 := by
    exact (sq_le_sq₀ (mul_nonneg ha (sq_nonneg _)) hedgeNonneg).2 hedge
  have hsumSq : ((G.edgeFinset.card : ℝ)) ^ 2 ≤
      (∑ i, d i) ^ 2 :=
    (sq_le_sq₀ hedgeNonneg hsumNonneg).2 hsum
  have hcauchy : (∑ i, d i) ^ 2 ≤
      (n : ℝ) * ∑ i, d i ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin n))) (f := d))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqLower : a ^ 2 * (n : ℝ) ^ 3 ≤ ∑ i, d i ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right hnR).mp
    calc
      a ^ 2 * (n : ℝ) ^ 3 * (n : ℝ) =
          (a * (n : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ ((G.edgeFinset.card : ℝ)) ^ 2 := hedgeSq
      _ ≤ (∑ i, d i) ^ 2 := hsumSq
      _ ≤ (n : ℝ) * ∑ i, d i ^ 2 := hcauchy
      _ = (∑ i, d i ^ 2) * (n : ℝ) := by ring
  rw [variance_half_perturbedEdgePolynomial]
  dsimp only [d] at hsqLower
  have hedgeTerm : 0 ≤ (G.edgeFinset.card : ℝ) / 16 := by positivity
  nlinarith

end GraphQuadratic
end Erdos88
