import Arxiv.Arxiv2411_18291.WeightedGreedyExistence
import Arxiv.Arxiv2411_18291.RootedCliquePlacement

/-! # Weighted clique regions on prescribed roots

The finite greedy criterion constructs actual edge-disjoint punctured
cliques. Weighted degrees of their vertex sets are controlled by the sum
of the weighted degrees of their pattern edges.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype I] [Fintype W] [Fintype V]
variable [DecidableEq W] [DecidableEq V] {F : Finset W} {q r t : ℕ}

omit [Fintype I] [Fintype W] in
theorem IsWeightedGreedyFamily.all_edges_weighted {Φ : Fin t → F ↪ V} {w : Fin t → ℕ}
    {H : Hypergraph W (r + 1)} {B : Hypergraph V (r + 1)}
    {Ψ : (i : Fin t) → EmbeddingExtension (Φ i)} {L θ : ℝ}
    (hΨ : IsWeightedGreedyFamily Φ w H B Ψ L)
    (hroots : ∀ e ∈ H, ∀ he : e.val ⊆ F,
      IsWeightedFamilyBounded r (fun i => rootImage (Φ i) e he) w θ)
    (hθL : θ ≤ L) :
    ∀ e ∈ H, IsWeightedFamilyBounded r (fun i => mapBlock (Ψ i).val e) w L := by
  intro e he
  by_cases heF : e.val ⊆ F
  · have heq : (fun i => mapBlock (Ψ i).val e) = (fun i => rootImage (Φ i) e heF) :=
      funext fun i => EmbeddingExtension.map_rootBlock (Φ i) (Ψ i) e heF
    rw [heq]
    intro S
    exact (hroots e he heF S).trans_le (mul_le_mul_of_nonneg_right hθL (Nat.cast_nonneg _))
  · exact hΨ.weighted e ((mem_newEdges H e).mpr ⟨he, heF⟩)

omit [Fintype V] [DecidableEq W] in
theorem weighted_embeddingClique_degree_le [Finite V]
    (hW : Fintype.card W = q) (hqr : r + 1 ≤ q)
    (Ψ : I → W ↪ V) (w : I → ℕ) (S : Block V r) :
    weightedFamilyDegree (fun i => embeddingClique hW (Ψ i)) w S.val ≤
      ∑ e : Block W (r + 1), weightedFamilyDegree (fun i => mapBlock (Ψ i) e) w S.val := by
  classical
  let : Fintype V := Fintype.ofFinite V
  simp only [weightedFamilyDegree]
  rw [sum_comm]
  apply sum_le_sum
  intro i _
  by_cases hS : S.val ⊆ (embeddingClique hW (Ψ i)).val
  · rw [if_pos hS]
    obtain ⟨T, hST, hTQ, hT⟩ := exists_subsuperset_card_eq hS
      (by rw [S.property]; omega : S.val.card ≤ r + 1)
      (by rw [(embeddingClique hW (Ψ i)).property]; exact hqr)
    have hmem : (⟨T, hT⟩ : Block V (r + 1)) ∈ mapGraph (Ψ i) (complete W (r + 1)) := by
      rw [map_complete_eq_cliqueEdges hW]
      exact (mem_cliqueEdges _ _).mpr hTQ
    obtain ⟨e, _, he⟩ := (mem_mapGraph (Ψ i) _ _).mp hmem
    have hSe : S.val ⊆ (mapBlock (Ψ i) e).val := by rw [he]; exact hST
    have hh := single_le_sum (s := univ)
      (f := fun e : Block W (r + 1) => if S.val ⊆ (mapBlock (Ψ i) e).val then w i else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ e)
    simpa only [if_pos hSe] using hh
  · rw [if_neg hS]
    exact Nat.zero_le _

omit [DecidableEq W] in
theorem weighted_embeddingClique_bounded (F₀ : Block W (r + 1))
    (hW : Fintype.card W = q) (Ψ : I → W ↪ V) (w : I → ℕ) {L : ℝ}
    (hΨ : ∀ e : Block W (r + 1),
      IsWeightedFamilyBounded r (fun i => mapBlock (Ψ i) e) w L) :
    IsWeightedFamilyBounded r (fun i => embeddingClique hW (Ψ i)) w
      (q.choose (r + 1) * L) := by
  have hqr : r + 1 ≤ q := by
    rw [← hW, ← F₀.property]
    exact card_le_univ _
  intro S
  have hle : (weightedFamilyDegree (fun i => embeddingClique hW (Ψ i)) w S.val : ℝ) ≤
      ∑ e : Block W (r + 1), (weightedFamilyDegree (fun i => mapBlock (Ψ i) e) w S.val : ℝ) := by
    exact_mod_cast weighted_embeddingClique_degree_le hW hqr Ψ w S
  have hs : (∑ e : Block W (r + 1),
      (weightedFamilyDegree (fun i => mapBlock (Ψ i) e) w S.val : ℝ)) <
        ∑ _e : Block W (r + 1), L * Fintype.card V :=
    sum_lt_sum_of_nonempty ⟨F₀, mem_univ _⟩ (fun e _ => hΨ e S)
  apply hle.trans_lt
  simpa only [sum_const, nsmul_eq_mul, card_univ, Block, Fintype.card_finset_len, hW,
    mul_assoc] using hs

omit [Fintype I] [DecidableEq W] in
theorem exists_indexed_weighted_clique_placement (F₀ : Block W (r + 1))
    (hW : Fintype.card W = q) (t : ℕ) (E : ℕ → Block V (r + 1)) (w : ℕ → ℕ)
    (B : Hypergraph V (r + 1)) {θB θR C c : ℝ}
    (hB : IsGraphBounded B θB) (hθB : 0 ≤ θB) (hθR : 0 ≤ θR)
    (hC : 0 < C) (hc : 0 < c) (hn : 4 * q ^ 2 ≤ Fintype.card V)
    (hnpos : 0 < Fintype.card V)
    (hsmall : q.choose (r + 1) *
      (θB + q.choose (r + 1) * ((1 + c) * (2 * (r + 1).factorial * θR))) ≤ 1 / 4)
    (hw : ∀ i < t, 1 ≤ w i) (hCw : ∀ i < t, (w i : ℝ) ≤ C)
    (hE : Function.Injective (fun i : Fin t => E i)) (hEB : ∀ i < t, E i ∈ B)
    (hroot : IsWeightedFamilyBounded r (fun i : Fin t => E i) (fun i => w i) θR)
    (hfailure : q.choose (r + 1) * Fintype.card (Block V r) *
      Real.exp (-(2 * (r + 1).factorial * θR * Fintype.card V * c ^ 2 / ((2 + c) * C))) < 1) :
    ∃ Q : Fin t → Block V q,
      IsCliqueCover (complete V (r + 1) \ B) (fun i : Fin t => E i) Q ∧
      IsWeightedFamilyBounded r Q (fun i => w i)
        (q.choose (r + 1) * ((1 + c) * (2 * (r + 1).factorial * θR))) ∧
      IsGraphBounded (cliqueCoverGraph (r := r) Q)
        (θB + q.choose (r + 1) * ((1 + c) * (2 * (r + 1).factorial * θR))) := by
  classical
  let Φ : ℕ → F₀.val ↪ V := fun i => edgeRootMap F₀ (E i)
  let L : ℝ := (1 + c) * (2 * (r + 1).factorial * θR)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hθL : θR ≤ L := by
    have hf : (1 : ℝ) ≤ 2 * (r + 1).factorial := by
      have hh : (1 : ℝ) ≤ (r + 1).factorial := by
        exact_mod_cast (r + 1).factorial_pos
      linarith
    calc
      θR ≤ 2 * (r + 1).factorial * θR := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hf hθR
      _ ≤ L := le_mul_of_one_le_left (by positivity) (by linarith : (1 : ℝ) ≤ 1 + c)
  have hcH : (complete W (r + 1)).card = q.choose (r + 1) := by
    simp only [complete, card_univ, Block, Fintype.card_finset_len, hW]
  have hroots : ∀ f ∈ complete W (r + 1), ∀ hf : f.val ⊆ F₀.val,
      IsWeightedFamilyBounded r (fun i : Fin t => rootImage (Φ i) f hf) (fun i => w i) θR := by
    intro f _ hf
    have hf0 : f = F₀ :=
      Subtype.ext (eq_of_subset_of_card_le hf (by rw [f.property, F₀.property]))
    subst f
    simpa only [Φ, rootImage_edgeRootMap] using hroot
  obtain ⟨Ψ, hΨ⟩ := exists_weighted_greedy_family Φ w (complete W (r + 1)) B
    hB hθB hθR hC hc (by simpa only [hW] using hn) hnpos
    (by simpa only [hcH] using hsmall) t hw hCw (complete_root_admissible F₀) hroots
    (by simpa only [hcH] using hfailure)
  refine ⟨fun i => embeddingClique hW (Ψ i).val,
    hΨ.greedy.cliqueCover_complement F₀ hW (fun i => E i) B Ψ hE
      (fun i => hEB i i.isLt), ?_, ?_⟩
  · exact weighted_embeddingClique_bounded F₀ hW (fun i => (Ψ i).val) (fun i => w i)
      (fun e => hΨ.all_edges_weighted hroots hθL e (mem_univ _))
  · have hb := (hΨ.greedy.graphBounded hB hL).subgraph
      (cliqueGraph_subset_base_union_new F₀ hW (fun i => E i) B Ψ (fun i => hEB i i.isLt))
    simpa only [hcH, L] using hb

end Arxiv2411_18291
