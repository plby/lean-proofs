import Arxiv.Arxiv2411_18291.EmbeddingCollisionGeometry
import Arxiv.Arxiv2411_18291.PermutationMomentBounds

/-!
# Moments of coloured root-preserving extensions

Each pattern block is assigned its own colour coordinate. The candidate
family may be any prescribed subset of root-preserving extensions. Pairs
without a free-vertex collision use the exact root-intersection orbit;
the remaining pairs have the proved collision-count bound.
-/

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {q : ℕ} {φ : F ↪ V}
variable [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)]

def extensionColourEvent (Q : Block W q) (f : EmbeddingExtension φ)
    (D : Finset (Block V q)) : Set (Equiv.Perm V) :=
  {σ | mapBlock f.val Q ∈ mapGraph σ.toEmbedding D}

def extensionColourCount (φ : F ↪ V) (s : Finset I) (Q : I → Block W q)
    (T : Finset (EmbeddingExtension φ)) (D : Finset (Block V q)) :
    RandomPermutation.Sample I V → ℝ :=
  RandomPermutation.eventCount s T (fun f i => extensionColourEvent (Q i) f D)

omit [Fintype W] [Fintype V] [DecidableEq W] [MeasurableSpace (Equiv.Perm V)]
    [MeasurableSingletonClass (Equiv.Perm V)] in
theorem extensionColourCount_eq_card (s : Finset I) (Q : I → Block W q)
    (T : Finset (EmbeddingExtension φ)) (D : Finset (Block V q))
    (ω : RandomPermutation.Sample I V) :
    extensionColourCount φ s Q T D ω =
      ((T.filter fun f => ∀ i ∈ s,
        mapBlock f.val (Q i) ∈ mapGraph (ω i).toEmbedding D).card : ℝ) := by
  classical
  have hind (f : EmbeddingExtension φ) :
      RandomPermutation.present s (fun i => extensionColourEvent (Q i) f D) ω =
        if ∀ i ∈ s, mapBlock f.val (Q i) ∈ mapGraph (ω i).toEmbedding D then (1 : ℝ) else 0 := by
    by_cases h : ∀ i ∈ s, mapBlock f.val (Q i) ∈ mapGraph (ω i).toEmbedding D
    · have hh : ω ∈ RandomPermutation.allConstraints s
          (fun i => extensionColourEvent (Q i) f D) := h
      simp only [RandomPermutation.present, Set.indicator_of_mem hh, if_pos h]
    · have hh : ω ∉ RandomPermutation.allConstraints s
          (fun i => extensionColourEvent (Q i) f D) := h
      simp only [RandomPermutation.present, Set.indicator_of_notMem hh, if_neg h]
  change (∑ f ∈ T, RandomPermutation.present s (fun i => extensionColourEvent (Q i) f D) ω) = _
  calc
    _ = ∑ _f ∈ T.filter (fun f => ∀ i ∈ s,
        mapBlock f.val (Q i) ∈ mapGraph (ω i).toEmbedding D), (1 : ℝ) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro f _
      by_cases hf : ∀ i ∈ s, mapBlock f.val (Q i) ∈ mapGraph (ω i).toEmbedding D
      · simpa only [if_pos hf] using hind f
      · simpa only [if_neg hf] using hind f
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, mul_one]
      apply congrArg (fun U : Finset (EmbeddingExtension φ) => (U.card : ℝ))
      ext f
      simp only [mem_filter]

omit [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
    [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)] in
theorem extensionColourCount_pos_iff (s : Finset I) (Q : I → Block W q)
    (T : Finset (EmbeddingExtension φ)) (D : Finset (Block V q))
    (ω : RandomPermutation.Sample I V) :
    0 < extensionColourCount φ s Q T D ω ↔
      ∃ f ∈ T, ∀ i ∈ s, mapBlock f.val (Q i) ∈ mapGraph (ω i).toEmbedding D := by
  classical
  rw [extensionColourCount_eq_card, Nat.cast_pos, card_pos]
  simp only [Finset.Nonempty, mem_filter]

omit [Fintype W] [DecidableEq W] in
theorem extensionColourCount_mean (s : Finset I) (Q : I → Block W q)
    (T : Finset (EmbeddingExtension φ)) (D : Finset (Block V q)) :
    (∫ ω, extensionColourCount φ s Q T D ω ∂RandomPermutation.probability I V) =
      (T.card : ℝ) * (D.card / ((Fintype.card V).choose q : ℝ)) ^ s.card := by
  apply RandomPermutation.eventCount_mean_of_uniform_marginals
  intro f _ i _
  exact uniform_permuted_family_probability (mapBlock f.val (Q i)) D

theorem extensionColourCount_second_moment_le (s : Finset I) (Q : I → Block W q)
    (T : Finset (EmbeddingExtension φ)) (D : Finset (Block V q)) (r : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (hroot : ∀ i ∈ s, ((Q i).val ∩ F).card < r)
    (hpair : ∀ a < r, ∀ P : IntersectingBlockPair V q q a,
      (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
        {σ | P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding D} ≤ t) :
    (∫ ω, extensionColourCount φ s Q T D ω ^ 2 ∂RandomPermutation.probability I V) ≤
      (T.card : ℝ) ^ 2 * t ^ s.card +
        (Fintype.card W - F.card : ℕ) ^ 2 * (T.card : ℝ) *
          (Fintype.card V : ℝ) ^ (Fintype.card W - F.card - 1) := by
  classical
  have hg (f : EmbeddingExtension φ) (hf : f ∈ T) (g : EmbeddingExtension φ) (hg : g ∈ T)
      (hfg : (f, g) ∉ collidingExtensionPairs φ T T) (i : I) (hi : i ∈ s) :
      (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
        (extensionColourEvent (Q i) f D ∩ extensionColourEvent (Q i) g D) ≤ t := by
    have hnocoll : ¬extensionsCollide φ f g := fun h =>
      hfg (mem_filter.mpr ⟨mem_product.mpr ⟨hf, hg⟩, h⟩)
    exact hpair _ (hroot i hi) (extensionBlockPair φ f g hnocoll (Q i))
  have hm := RandomPermutation.eventCount_second_moment_le s T
    (fun f i => extensionColourEvent (Q i) f D) (collidingExtensionPairs φ T T) ht hg
  have hc : ((collidingExtensionPairs φ T T).card : ℝ) ≤
      (Fintype.card W - F.card : ℕ) ^ 2 * (T.card : ℝ) *
        (Fintype.card V : ℝ) ^ (Fintype.card W - F.card - 1) := by
    exact_mod_cast collidingExtensionPairs_card_le φ T T
  exact hm.trans (add_le_add le_rfl hc)

end Arxiv2411_18291
