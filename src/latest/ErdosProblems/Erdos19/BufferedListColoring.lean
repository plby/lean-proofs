import ErdosProblems.Erdos19.BufferPadding
import ErdosProblems.Erdos19.ApproximateDemandColoring

/-! # Sparse-list coloring leaving vertices unused in every disjoint buffer

The artificial capacity pools are constructed here. No dummy vertices or
unproved augmentation property are required from the caller.
-/

namespace Erdos19

open Finset Erdos76 Erdos76.FiniteHypergraph

theorem bounded_approximate_buffered_coloring (r C : ℕ) (hr : 0 < r)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ D₀ : ℕ,
      ∀ (V E I A : Type) [DecidableEq V] [Fintype E] [DecidableEq E]
        [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A],
        ∀ (H : FiniteHypergraph V E) (D L : ℕ) (B : I → Finset V)
          (p T : I → ℕ) (F : E → Finset A),
          D₀ ≤ D → 0 < L → (L : ℝ) < delta * D →
          H.IsBounded r → H.vertexSet.card + (∑ i : I, p i) ≤ C * D →
          (∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) →
          (∀ x ∈ H.vertexSet, ∀ y ∈ H.vertexSet, x ≠ y → H.edgePairDegree x y ≤ L) →
          (Pairwise fun i j ↦ Disjoint (B i) (B j)) →
          (∀ i, (∑ e : E, (H.support e ∩ B i).card) ≤ T i) →
          (∀ i, T i / D + 2 * r + (2 * r) * ((2 * r) * D / L) < p i) →
          (∀ e, ((F e).card : ℝ) ≤ delta * D) →
          (1 + epsilon) * (D : ℝ) ≤ Fintype.card A →
          ∃ c : H.conflictGraph.Coloring A, (∀ e, c e ∉ F e) ∧
            ∀ i a, (B i).card - p i ≤
              (B i \ ((univ.filter fun e ↦ c e = a).biUnion
                fun e ↦ H.support e ∩ B i)).card := by
  classical
  obtain ⟨delta, hdelta, D₀, hcolor⟩ :=
    bounded_approximate_capacity_coloring_of_demand_bound r C hr epsilon hepsilon
  refine ⟨delta, hdelta, D₀, ?_⟩
  intro V E I A _ _ _ _ _ _ _ H D L B p T F hD hL hLsmall hbound hvertices
    hdegree hpair hB htotal hroom hF hpalette
  let q := BufferPadding.poolSize p
  let K := PoolPadding.withPool H q
  let B' : I → Finset (V ⊕ Fin q) := fun i ↦ BufferPadding.buffer p (B i)
  let P : I → Finset (V ⊕ Fin q) := BufferPadding.pool p
  have hKbound : K.IsBounded r := by
    intro e
    simpa only [K, PoolPadding.support_card] using hbound e
  have hKvertices : K.vertexSet.card ≤ C * D := by
    simpa only [K, q, PoolPadding.vertexSet_card, BufferPadding.poolSize_eq_sum] using hvertices
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
  have hB' : Pairwise fun i j ↦ Disjoint (B' i) (B' j) :=
    BufferPadding.buffers_disjoint p B hB
  have hP : Pairwise fun i j ↦ Disjoint (P i) (P j) := BufferPadding.pools_disjoint p
  have hpool : ∀ i, P i ⊆ K.vertexSet := BufferPadding.pool_subset_vertexSet H p
  have hunused : ∀ e i, Disjoint (K.support e) (P i) :=
    BufferPadding.support_disjoint_pool H p
  have htotal' : ∀ i, (∑ e : E, (K.support e ∩ B' i).card) ≤ T i := by
    intro i
    simpa only [K, B', q, BufferPadding.support_inter_buffer_card] using htotal i
  have hroom' : ∀ i, T i / D + 2 * r + (2 * r) * ((2 * r) * D / L) < (P i).card := by
    intro i
    change T i / D + 2 * r + (2 * r) * ((2 * r) * D / L) <
      (BufferPadding.pool (V := V) p i).card
    rw [BufferPadding.pool_card]
    exact hroom i
  obtain ⟨c, hcF, hbuffer⟩ := hcolor (V ⊕ Fin q) E I A K D L B' P T F hD hL hLsmall
    hKbound hKvertices hKdegree hKpair hB' hP hpool hunused htotal' hroom' hF hpalette
  refine ⟨PoolPadding.restrictColoring H q c, hcF, ?_⟩
  intro i a
  change (B i).card - p i ≤
    (B i \ ((univ.filter fun e ↦ c e = a).biUnion fun e ↦ H.support e ∩ B i)).card
  simpa only [B', P, K, q, BufferPadding.buffer_card, BufferPadding.pool_card,
    BufferPadding.uncovered_buffer_card] using hbuffer i a

theorem buffered_coloring_total_demand_of_low_degree
    {V E I : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : FiniteHypergraph V E) (B : I → Finset V) (d : I → ℕ)
    (hlow : ∀ i v, v ∈ B i → H.edgeDegree v ≤ d i) :
    ∀ i, (∑ e : E, (H.support e ∩ B i).card) ≤ (B i).card * d i := by
  intro i
  rw [sum_support_inter_card_eq_sum_degree]
  calc
    _ ≤ ∑ _v ∈ B i, d i := sum_le_sum (hlow i)
    _ = _ := by simp

#print axioms bounded_approximate_buffered_coloring

end Erdos19
