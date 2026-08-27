import Arxiv.Arxiv2411_18291.BlockPairOrbits

/-!
# Joint probabilities in a uniformly permuted family

The two block events use the same vertex permutation. Their joint law is
uniform on ordered pairs with the prescribed intersection, rather than a
product of the marginal block laws.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {a b s : ℕ}

def blockPairFamily (G : Hypergraph V a) (H : Hypergraph V b) (s : ℕ) :
    Finset (IntersectingBlockPair V a b s) :=
  univ.filter fun P => P.val.1 ∈ G ∧ P.val.2 ∈ H

theorem mem_blockPairFamily (G : Hypergraph V a) (H : Hypergraph V b)
    (P : IntersectingBlockPair V a b s) :
    P ∈ blockPairFamily G H s ↔ P.val.1 ∈ G ∧ P.val.2 ∈ H := by
  simp only [blockPairFamily, mem_filter, mem_univ, true_and]

variable [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)]

theorem uniform_permutation_blockPair_probability (P : IntersectingBlockPair V a b s)
    (D : Finset (IntersectingBlockPair V a b s)) :
    (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
      {σ | mapBlockPair σ.toEmbedding P ∈ D} =
      D.card / (Fintype.card (IntersectingBlockPair V a b s) : ℝ) :=
  uniform_equal_fibers_probability (fun σ : Equiv.Perm V => mapBlockPair σ.toEmbedding P)
    P (fun Q => permutation_blockPair_fiber_card P Q P) D

theorem uniform_permuted_pair_probability (P : IntersectingBlockPair V a b s)
    (G : Hypergraph V a) (H : Hypergraph V b) :
    (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
      {σ | P.val.1 ∈ mapGraph σ.toEmbedding G ∧ P.val.2 ∈ mapGraph σ.toEmbedding H} =
      (blockPairFamily G H s).card / (Fintype.card (IntersectingBlockPair V a b s) : ℝ) := by
  have hevent : {σ : Equiv.Perm V | P.val.1 ∈ mapGraph σ.toEmbedding G ∧
      P.val.2 ∈ mapGraph σ.toEmbedding H} =
      {σ : Equiv.Perm V | mapBlockPair σ.symm.toEmbedding P ∈ blockPairFamily G H s} := by
    ext σ
    simp only [Set.mem_ofPred_eq, mem_mapGraph_equiv, mem_blockPairFamily, mapBlockPair]
  rw [hevent]
  have hf (Q : IntersectingBlockPair V a b s) :
      (univ.filter fun σ : Equiv.Perm V => mapBlockPair σ.symm.toEmbedding P = Q).card =
        (univ.filter fun σ : Equiv.Perm V => mapBlockPair σ.symm.toEmbedding P = P).card := by
    rw [permutation_inverse_blockPair_fiber_card, permutation_inverse_blockPair_fiber_card]
    exact permutation_blockPair_fiber_card P Q P
  exact uniform_equal_fibers_probability
    (fun σ : Equiv.Perm V => mapBlockPair σ.symm.toEmbedding P) P hf (blockPairFamily G H s)

end Arxiv2411_18291
