import Arxiv.Arxiv2411_18291.PermutationPairProbability
import Arxiv.Arxiv2411_18291.Decomposition

/-!
# Bounding pairs by rooted-family counts

For each first block, classify possible second blocks by their intersection
inside it. Uniform rooted-family bounds then control the entire pair count.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {a b s : ℕ}

theorem blockPairFamily_first_fiber (G : Hypergraph V a) (H : Hypergraph V b)
    (A : Block V a) (hA : A ∈ G) :
    ((blockPairFamily G H s).filter fun P => P.val.1 = A).card =
      (H.filter fun B => (A.val ∩ B.val).card = s).card := by
  apply card_bij (fun P _ => P.val.2)
  · intro P hP
    obtain ⟨hPGH, hPA⟩ := mem_filter.mp hP
    refine mem_filter.mpr ⟨(mem_blockPairFamily _ _ _ |>.mp hPGH).2, ?_⟩
    rw [← hPA]
    exact P.property
  · intro P hP Q hQ he
    have hPA := (mem_filter.mp hP).2
    have hQA := (mem_filter.mp hQ).2
    exact Subtype.ext (Prod.ext (hPA.trans hQA.symm) he)
  · intro B hB
    obtain ⟨hBH, hAB⟩ := mem_filter.mp hB
    let P : IntersectingBlockPair V a b s := ⟨(A, B), hAB⟩
    exact ⟨P, mem_filter.mpr ⟨(mem_blockPairFamily _ _ _).mpr ⟨hA, hBH⟩, rfl⟩, rfl⟩

theorem card_blockPairFamily_eq_sum (G : Hypergraph V a) (H : Hypergraph V b) (s : ℕ) :
    (blockPairFamily G H s).card =
      ∑ A ∈ G, (H.filter fun B => (A.val ∩ B.val).card = s).card := by
  rw [card_eq_sum_card_fiberwise (f := fun P : IntersectingBlockPair V a b s => P.val.1)
    (t := G) (fun P hP => (mem_blockPairFamily _ _ _ |>.mp hP).1)]
  exact sum_congr rfl (fun A hA => blockPairFamily_first_fiber G H A hA)

omit [Fintype V] in
theorem card_intersection_family_le [Finite V]
    (H : Hypergraph V b) (A : Block V a) (s : ℕ) {L : ℝ}
    (hL : ∀ I : Block V s, I.val ⊆ A.val → ((H.filter fun B => I.val ⊆ B.val).card : ℝ) ≤ L) :
    ((H.filter fun B => (A.val ∩ B.val).card = s).card : ℝ) ≤ (a.choose s : ℝ) * L := by
  let _ := Fintype.ofFinite V
  have hsub : (H.filter fun B => (A.val ∩ B.val).card = s) ⊆
      (cliqueEdges s A).biUnion (fun I => H.filter fun B => I.val ⊆ B.val) := by
    intro B hB
    obtain ⟨hBH, hAB⟩ := mem_filter.mp hB
    let I : Block V s := ⟨A.val ∩ B.val, hAB⟩
    exact mem_biUnion.mpr ⟨I, (mem_cliqueEdges _ _).mpr inter_subset_left,
      mem_filter.mpr ⟨hBH, inter_subset_right⟩⟩
  calc
    _ ≤ (((cliqueEdges s A).biUnion (fun I => H.filter fun B => I.val ⊆ B.val)).card : ℝ) :=
      by exact_mod_cast card_le_card hsub
    _ ≤ ∑ I ∈ cliqueEdges s A, ((H.filter fun B => I.val ⊆ B.val).card : ℝ) := by
      exact_mod_cast (card_biUnion_le (s := cliqueEdges s A)
        (t := fun I => H.filter fun B => I.val ⊆ B.val))
    _ ≤ ∑ _I ∈ cliqueEdges s A, L :=
      sum_le_sum (fun I hI => hL I ((mem_cliqueEdges _ _).mp hI))
    _ = _ := by rw [sum_const, card_cliqueEdges, nsmul_eq_mul]

theorem card_blockPairFamily_le (G : Hypergraph V a) (H : Hypergraph V b) (s : ℕ) {L : ℝ}
    (hL : ∀ I : Block V s, ((H.filter fun B => I.val ⊆ B.val).card : ℝ) ≤ L) :
    ((blockPairFamily G H s).card : ℝ) ≤ (G.card : ℝ) * a.choose s * L := by
  rw [card_blockPairFamily_eq_sum, Nat.cast_sum]
  calc
    _ ≤ ∑ _A ∈ G, (a.choose s : ℝ) * L :=
      sum_le_sum (fun A _ => card_intersection_family_le H A s (fun I _ => hL I))
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

end Arxiv2411_18291
