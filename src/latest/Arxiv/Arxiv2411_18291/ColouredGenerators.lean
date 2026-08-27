import Arxiv.Arxiv2411_18291.ModularRelabeling

/-!
# Generators in finitely many permuted copies

The union of the permuted generators spans every permuted unsaturated
clique over the same modular group. Its boundary bound grows only by the
number of colours, even when copies overlap.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
variable {q r N : ℕ}

def permutedUnion (σ : I → Equiv.Perm V) (G : Hypergraph V r) : Hypergraph V r :=
  univ.biUnion fun i => mapGraph (σ i).toEmbedding G

omit [Fintype V] in
theorem mem_permutedUnion (σ : I → Equiv.Perm V) (G : Hypergraph V r) (e : Block V r) :
    e ∈ permutedUnion σ G ↔ ∃ i, ∃ e' ∈ G, mapBlock (σ i).toEmbedding e' = e := by
  simp only [permutedUnion, mem_biUnion, mem_univ, true_and, mem_mapGraph]

omit [Fintype V] in
theorem mapGraph_subset_permutedUnion (σ : I → Equiv.Perm V) (G : Hypergraph V r) (i : I) :
    mapGraph (σ i).toEmbedding G ⊆ permutedUnion σ G :=
  subset_biUnion_of_mem (fun j => mapGraph (σ j).toEmbedding G) (mem_univ i)

omit [Fintype V] in
theorem card_permutedUnion_le (σ : I → Equiv.Perm V) (G : Hypergraph V r) :
    (permutedUnion σ G).card ≤ Fintype.card I * G.card := by
  unfold permutedUnion
  simpa only [card_mapGraph, sum_const, card_univ, smul_eq_mul] using
    card_biUnion_le (s := (univ : Finset I)) (t := fun i => mapGraph (σ i).toEmbedding G)

theorem IsCliqueFamilyBounded.permutedUnion [Nonempty I]
    {D : Finset (Block V q)} {θ : ℝ} (hD : IsCliqueFamilyBounded r D θ)
    (σ : I → Equiv.Perm V) :
    IsCliqueFamilyBounded r (permutedUnion σ D) (Fintype.card I * θ) := by
  unfold Arxiv2411_18291.permutedUnion
  simpa only [card_univ] using IsCliqueFamilyBounded.biUnion univ
    univ_nonempty (fun i => mapGraph (σ i).toEmbedding D) θ (fun i _ => hD.map (σ i))

omit [Fintype V] in
theorem containing_permutedUnion_le_sum (σ : I → Equiv.Perm V)
    (D : Finset (Block V q)) (e : Block V r) :
    ((permutedUnion σ D).filter fun Q => e.val ⊆ Q.val).card ≤
      ∑ i, (D.filter fun Q => ((blockEquiv (σ i)).symm e).val ⊆ Q.val).card := by
  classical
  rw [permutedUnion, filter_biUnion]
  apply card_biUnion_le.trans
  apply le_of_eq
  apply sum_congr rfl
  intro i _
  have he : mapBlock (σ i).toEmbedding ((blockEquiv (σ i)).symm e) = e :=
    (blockEquiv (σ i)).apply_symm_apply e
  simpa only [he] using card_mapGraph_containing (σ i).toEmbedding D
    ((blockEquiv (σ i)).symm e)

omit [Fintype V] in
theorem containing_permutedUnion_le (σ : I → Equiv.Perm V)
    (D : Finset (Block V q)) {m : ℝ}
    (hD : ∀ e : Block V r, ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ m)
    (e : Block V r) :
    (((permutedUnion σ D).filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
      Fintype.card I * m := by
  classical
  calc
    _ ≤ ∑ i, ((D.filter fun Q => ((blockEquiv (σ i)).symm e).val ⊆ Q.val).card : ℝ) :=
      by exact_mod_cast containing_permutedUnion_le_sum σ D e
    _ ≤ ∑ _i : I, m := sum_le_sum (fun i _ => hD ((blockEquiv (σ i)).symm e))
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

omit [Fintype V] in
theorem ModularGeneratingData.permuted_generates {K : Hypergraph V (r + 1)}
    {D : Finset (Block V q)} (C : ModularGeneratingData K D N)
    (σ : I → Equiv.Perm V) {Q : Block V q} (hQ : Q ∈ permutedUnion σ (D \ C.saturated)) :
    modularCliqueVector N (r + 1) Q ∈
      generatedSubgroup (modularCliqueVector N (r + 1)) (permutedUnion σ C.generators) := by
  obtain ⟨i, P, hP, hPQ⟩ := (mem_permutedUnion _ _ _).mp hQ
  rw [← hPQ]
  exact generatedSubgroup_mono _ (mapGraph_subset_permutedUnion σ C.generators i)
    (modularCliqueVector_generated_map (σ i) C.generators (C.generates P hP))

theorem permuted_clique_support (σ : I → Equiv.Perm V) (K : Hypergraph V r)
    (D : Finset (Block V q)) (hD : ∀ Q ∈ D, cliqueEdges r Q ⊆ K) :
    cliqueSupport r (permutedUnion σ D) ⊆ permutedUnion σ K := by
  intro e he
  obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
  obtain ⟨i, P, hP, hPQ⟩ := (mem_permutedUnion _ _ _).mp hQ
  rw [← hPQ] at heQ
  rw [← map_cliqueEdges] at heQ
  exact mapGraph_subset_permutedUnion σ K i (mapGraph_mono _ (hD P hP) heQ)

end Arxiv2411_18291
