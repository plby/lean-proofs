import Arxiv.Arxiv2411_18291.CoefficientRelabeling
import Arxiv.Arxiv2411_18291.UniformFiniteFibers
import Mathlib.Logic.Equiv.Fintype

/-!
# Exact block probabilities under a random vertex permutation

Permutations act transitively on blocks of a fixed size. Composition gives
equal fibers, so a fixed block belongs to a random permuted family with
probability exactly the family's cardinality divided by the number of blocks.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}

omit [Fintype V] [DecidableEq V] in
theorem mapBlock_equiv_trans (σ τ : Equiv.Perm V) (Q : Block V q) :
    mapBlock (σ.trans τ).toEmbedding Q =
      mapBlock τ.toEmbedding (mapBlock σ.toEmbedding Q) :=
  (mapBlock_map σ.toEmbedding τ.toEmbedding Q).symm

omit [Fintype V] [DecidableEq V] in
theorem exists_perm_mapBlock (P Q : Block V q) :
    ∃ σ : Equiv.Perm V, mapBlock σ.toEmbedding P = Q := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq P.val Q.val (by rw [P.property, Q.property])
  exact ⟨σ, Subtype.ext hσ⟩

theorem permutation_block_fiber_card (Q P P' : Block V q) :
    (univ.filter fun σ : Equiv.Perm V => mapBlock σ.toEmbedding Q = P).card =
      (univ.filter fun σ : Equiv.Perm V => mapBlock σ.toEmbedding Q = P').card := by
  classical
  obtain ⟨τ, hτ⟩ := exists_perm_mapBlock P P'
  apply card_bij (fun σ _ => σ.trans τ)
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    rw [mapBlock_equiv_trans, hσ, hτ]
  · intro σ _ σ' _ he
    ext x
    exact τ.injective (congrArg (fun f : Equiv.Perm V => f x) he)
  · intro σ hσ
    refine ⟨σ.trans τ.symm, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hσ ⊢
      rw [mapBlock_equiv_trans, hσ, ← hτ]
      exact (blockEquiv τ).left_inv P
    · ext x
      simp

theorem permutation_inverse_block_fiber_card (Q P : Block V q) :
    (univ.filter fun σ : Equiv.Perm V => mapBlock σ.symm.toEmbedding Q = P).card =
      (univ.filter fun σ : Equiv.Perm V => mapBlock σ.toEmbedding Q = P).card := by
  classical
  apply card_bij (fun σ _ => σ.symm)
  · intro σ hσ
    simpa only [mem_filter, mem_univ, true_and] using hσ
  · intro σ _ τ _ he
    simpa using congrArg Equiv.symm he
  · intro σ hσ
    exact ⟨σ.symm, by simpa using hσ, by simp⟩

omit [Fintype V] [DecidableEq V] in
theorem mem_mapGraph_equiv (σ : Equiv.Perm V) (D : Finset (Block V q)) (Q : Block V q) :
    Q ∈ mapGraph σ.toEmbedding D ↔ mapBlock σ.symm.toEmbedding Q ∈ D := by
  rw [mem_mapGraph]
  constructor
  · rintro ⟨P, hP, hPQ⟩
    rw [← hPQ, show mapBlock σ.symm.toEmbedding (mapBlock σ.toEmbedding P) = P from
      (blockEquiv σ).left_inv P]
    exact hP
  · intro hQ
    exact ⟨mapBlock σ.symm.toEmbedding Q, hQ, (blockEquiv σ).right_inv Q⟩

variable [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)]

theorem uniform_permutation_block_probability (Q : Block V q) (D : Finset (Block V q)) :
    (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
      {σ | mapBlock σ.toEmbedding Q ∈ D} = D.card / ((Fintype.card V).choose q : ℝ) := by
  simpa only [Block, Fintype.card_finset_len] using uniform_equal_fibers_probability
    (fun σ : Equiv.Perm V => mapBlock σ.toEmbedding Q) Q
    (fun P => permutation_block_fiber_card Q P Q) D

theorem uniform_permuted_family_probability (Q : Block V q) (D : Finset (Block V q)) :
    (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
      {σ | Q ∈ mapGraph σ.toEmbedding D} = D.card / ((Fintype.card V).choose q : ℝ) := by
  have heq : {σ : Equiv.Perm V | Q ∈ mapGraph σ.toEmbedding D} =
      {σ : Equiv.Perm V | mapBlock σ.symm.toEmbedding Q ∈ D} := by
    ext σ
    exact mem_mapGraph_equiv σ D Q
  rw [heq]
  have hf (P : Block V q) :
      (univ.filter fun σ : Equiv.Perm V => mapBlock σ.symm.toEmbedding Q = P).card =
        (univ.filter fun σ : Equiv.Perm V => mapBlock σ.symm.toEmbedding Q = Q).card := by
    rw [permutation_inverse_block_fiber_card, permutation_inverse_block_fiber_card]
    exact permutation_block_fiber_card Q P Q
  simpa only [Block, Fintype.card_finset_len] using uniform_equal_fibers_probability
    (fun σ : Equiv.Perm V => mapBlock σ.symm.toEmbedding Q) Q hf D

end Arxiv2411_18291
