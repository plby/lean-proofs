import ErdosProblems.Erdos19.PoolPadding
import ErdosProblems.Erdos19.ApproximateDemandColoring

/-! # Covered sparse-list coloring from a total-incidence bound -/

namespace Erdos19

open Finset Erdos76 Erdos76.FiniteHypergraph

theorem bounded_approximate_covered_coloring_of_total_incidence
    (r C : ℕ) (hr : 0 < r) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ D₀ : ℕ,
      ∀ (V E A : Type) [DecidableEq V] [Fintype E] [DecidableEq E]
        [Fintype A] [DecidableEq A],
        ∀ (H : FiniteHypergraph V E) (D L T p : ℕ) (F : E → Finset A),
          D₀ ≤ D → 0 < L → (L : ℝ) < delta * (D : ℝ) →
          H.IsBounded r → H.vertexSet.card + p ≤ C * D →
          (∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) →
          (∑ e : E, (H.support e).card) ≤ T →
          (∀ x ∈ H.vertexSet, ∀ y ∈ H.vertexSet, x ≠ y → H.edgePairDegree x y ≤ L) →
          T / D + 2 * r + (2 * r) * ((2 * r) * D / L) < p →
          (∀ e, ((F e).card : ℝ) ≤ delta * (D : ℝ)) →
          (1 + epsilon) * (D : ℝ) ≤ Fintype.card A →
          ∃ c : H.conflictGraph.Coloring A, (∀ e, c e ∉ F e) ∧
            ∀ a, ((univ.filter fun e ↦ c e = a).biUnion H.support).card ≤ p := by
  classical
  obtain ⟨delta, hdelta, D₀, hcolor⟩ := bounded_approximate_capacity_coloring_of_demand_bound r C hr
    epsilon hepsilon
  refine ⟨delta, hdelta, D₀, ?_⟩
  intro V E A _ _ _ _ _ H D L T p F hD hL hLsmall hbound hvertices hdegree htotal
    hpair hroom hF hpalette
  let K := PoolPadding.withPool H p
  let B : Unit → Finset (V ⊕ Fin p) := fun _ ↦ PoolPadding.realVertices H p
  let P : Unit → Finset (V ⊕ Fin p) := fun _ ↦ PoolPadding.dummyVertices H p
  have hKbound : K.IsBounded r := by
    intro e
    simpa only [K, PoolPadding.support_card] using hbound e
  have hKvertices : K.vertexSet.card ≤ C * D := by
    simpa only [K, PoolPadding.vertexSet_card] using hvertices
  have hKdegree : ∀ v ∈ K.vertexSet, K.edgeDegree v ≤ D := by
    intro v hv
    rcases v with v | v
    · have hv' : v ∈ H.vertexSet := by
        simpa [K, PoolPadding.withPool, PoolPadding.realVertices, PoolPadding.dummyVertices] using hv
      simpa only [K, PoolPadding.edgeDegree_inl] using hdegree v hv'
    · simp only [K, PoolPadding.edgeDegree_inr, Nat.zero_le]
  have hKpair : ∀ x ∈ K.vertexSet, ∀ y ∈ K.vertexSet, x ≠ y → K.edgePairDegree x y ≤ L := by
    intro x hx y hy hxy
    rcases x with x | x <;> rcases y with y | y
    · have hx' : x ∈ H.vertexSet := by
        simpa [K, PoolPadding.withPool, PoolPadding.realVertices, PoolPadding.dummyVertices] using hx
      have hy' : y ∈ H.vertexSet := by
        simpa [K, PoolPadding.withPool, PoolPadding.realVertices, PoolPadding.dummyVertices] using hy
      simpa only [K, PoolPadding.edgePairDegree_inl_inl] using
        hpair x hx' y hy' (fun h ↦ hxy (congrArg Sum.inl h))
    · simp only [K, PoolPadding.edgePairDegree_inr_right, Nat.zero_le]
    · simp only [K, PoolPadding.edgePairDegree_inr_left, Nat.zero_le]
    · simp only [K, PoolPadding.edgePairDegree_inr_left, Nat.zero_le]
  have hB : Pairwise fun i j ↦ Disjoint (B i) (B j) := by
    intro i j hne
    exact (hne (Subsingleton.elim i j)).elim
  have hP : Pairwise fun i j ↦ Disjoint (P i) (P j) := by
    intro i j hne
    exact (hne (Subsingleton.elim i j)).elim
  have hpool : ∀ i, P i ⊆ K.vertexSet := fun _ ↦ Finset.subset_union_right
  have hunused : ∀ e i, Disjoint (K.support e) (P i) :=
    fun e _ ↦ PoolPadding.support_disjoint_dummy H p e
  have hload : ∀ i, (∑ e : E, (K.support e ∩ B i).card) ≤ T := by
    intro i
    have hinter (e : E) : K.support e ∩ B i = K.support e :=
      Finset.inter_eq_left.mpr (PoolPadding.support_subset_real H p e)
    simpa only [hinter, K, PoolPadding.support_card] using htotal
  have hroom' : ∀ i, T / D + 2 * r +
      (2 * r) * ((2 * r) * D / L) < (P i).card := by
    intro i
    simpa only [B, P, PoolPadding.card_realVertices, PoolPadding.card_dummyVertices] using hroom
  obtain ⟨c, hcF, hcover⟩ := hcolor (V ⊕ Fin p) E Unit A K D L B P (fun _ ↦ T) F
    hD hL hLsmall hKbound hKvertices hKdegree hKpair hB hP hpool hunused hload hroom' hF hpalette
  refine ⟨PoolPadding.restrictColoring H p c, hcF, ?_⟩
  intro a
  exact PoolPadding.covered_card_le_of_uncovered_bound H p
    (univ.filter fun e ↦ c e = a) (hcover () a)

#print axioms bounded_approximate_covered_coloring_of_total_incidence

end Erdos19
