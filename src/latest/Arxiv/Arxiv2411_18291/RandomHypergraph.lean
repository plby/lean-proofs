import Arxiv.Arxiv2411_18291.BernoulliSubset
import Arxiv.Arxiv2411_18291.Neighborhood

/-!
# Counts in a random uniform hypergraph

Edge counts and common-neighborhood counts are sums of independent indicators.
The exact mean for a family `A` of faces is
`(n - |⋃ A|) * p ^ |A|`, retaining the finite-size correction in Lemma 5.3.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

open Classical in
def sampleGraph (ω : BernoulliSubset.Sample (Block V r)) : Hypergraph V r := univ.filter ω

omit [DecidableEq V] in
@[simp] theorem mem_sampleGraph (ω : BernoulliSubset.Sample (Block V r)) (e : Block V r) :
    e ∈ sampleGraph ω ↔ ω e := by
  classical
  simp [sampleGraph]

omit [DecidableEq V] in
theorem subset_sampleGraph (ω : BernoulliSubset.Sample (Block V r)) (s : Hypergraph V r) :
    s ⊆ sampleGraph ω ↔ ω ∈ BernoulliSubset.allPresent s := by
  simp [subset_iff, BernoulliSubset.allPresent]

omit [DecidableEq V] in
theorem sampleGraph_card_eq_sum (ω : BernoulliSubset.Sample (Block V r)) :
    ((sampleGraph ω).card : ℝ) = ∑ e, BernoulliSubset.present {e} ω := by
  classical
  rw [BernoulliSubset.sum_present_eq_card_filter]
  simp [sampleGraph, BernoulliSubset.allPresent]

omit [DecidableEq V] in
theorem sampleGraph_mean (p : unitInterval) :
    (∫ ω, ((sampleGraph ω : Hypergraph V r).card : ℝ)
      ∂BernoulliSubset.probability (Block V r) p) =
      (p : ℝ) * (Fintype.card V).choose r := by
  simp_rw [sampleGraph_card_eq_sum]
  rw [BernoulliSubset.count_mean]
  simp [Fintype.card_finset_len, mul_comm]

omit [DecidableEq V] in
/-- The edge-count use of corrected Lemma 5.1(1). -/
theorem sampleGraph_card_concentration (p : unitInterval) {c : ℝ} (hc : 0 ≤ c) :
    let μ := (p : ℝ) * (Fintype.card V).choose r
    (BernoulliSubset.probability (Block V r) p).real
      {ω | |((sampleGraph ω).card : ℝ) - μ| > c * μ} ≤
        2 * Real.exp (-(μ * c ^ 2 / (2 * (1 + 2 * c)))) := by
  have hdis : Pairwise fun e f : Block V r => Disjoint ({e} : Finset (Block V r)) {f} := by
    intro e f hef
    simpa only [disjoint_singleton] using hef
  simpa [← sampleGraph_card_eq_sum, Fintype.card_finset_len, mul_comm] using
    BernoulliSubset.count_concentration p univ (fun e : Block V r => {e}) hdis hc

theorem commonNeighbors_card_eq_sum (A : Finset (Block V r))
    (ω : BernoulliSubset.Sample (Block V (r + 1))) :
    ((commonNeighbors (sampleGraph ω) A).card : ℝ) =
      ∑ v : OutsideFaces A, BernoulliSubset.present (extensionEdges A v) ω := by
  classical
  rw [BernoulliSubset.sum_present_eq_card_filter, card_commonNeighbors_eq]
  simp_rw [subset_sampleGraph]

/-- The exact common-neighborhood expectation, before replacing `n - |⋃ A|` by `n`. -/
theorem commonNeighbors_mean (p : unitInterval) (A : Finset (Block V r)) :
    (∫ ω, ((commonNeighbors (sampleGraph ω) A).card : ℝ)
      ∂BernoulliSubset.probability (Block V (r + 1)) p) =
      ((Fintype.card V - (faceVertices A).card : ℕ) : ℝ) * (p : ℝ) ^ A.card := by
  simp_rw [commonNeighbors_card_eq_sum]
  rw [BernoulliSubset.count_mean]
  simp only [card_extensionEdges, sum_const, card_univ, nsmul_eq_mul, card_outsideFaces]

/-- The common-neighborhood use of corrected Lemma 5.1(1). Independence is
proved from disjointness of the edge sets used by distinct candidate vertices. -/
theorem commonNeighbors_concentration (p : unitInterval) (A : Finset (Block V r))
    {c : ℝ} (hc : 0 ≤ c) :
    let μ := ((Fintype.card V - (faceVertices A).card : ℕ) : ℝ) * (p : ℝ) ^ A.card
    (BernoulliSubset.probability (Block V (r + 1)) p).real
      {ω | |((commonNeighbors (sampleGraph ω) A).card : ℝ) - μ| > c * μ} ≤
        2 * Real.exp (-(μ * c ^ 2 / (2 * (1 + 2 * c)))) := by
  simpa only [← commonNeighbors_card_eq_sum, card_extensionEdges, sum_const,
    card_univ, nsmul_eq_mul, card_outsideFaces] using
    BernoulliSubset.count_concentration p univ (extensionEdges A) (extensionEdges_disjoint A) hc

end Arxiv2411_18291
