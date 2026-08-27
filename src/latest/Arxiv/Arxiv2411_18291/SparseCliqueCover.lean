import Arxiv.Arxiv2411_18291.CoverExistence
import Arxiv.Arxiv2411_18291.RootedCliquePlacement

/-!
# Sparse clique covers with separate input and candidate exponents

Punctured-clique density `n^(-a)` and root degree scale `n^(-b)` suffice
when `2*a < b`. The chosen clique graph has degree scale `n^(-(b-a))`,
up to a fixed factor. No disjointness from a separate generating family
is needed or asserted.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {q r : ℕ}

omit [DecidableEq W] in
theorem exists_indexed_sparse_clique_cover_of_numerics (F₀ : Block W (r + 1))
    (hW : Fintype.card W = q) {a b : ℝ} {n : ℕ} (hn : 0 < n)
    (hsmall : (q.choose (r + 1) : ℝ) * ((n : ℝ) ^ (-b) + q.choose (r + 1) *
      (4 * (r + 1).factorial * (n : ℝ) ^ (-b) / (n : ℝ) ^ (-a))) ≤
        (n : ℝ) ^ (-a) / 2)
    (hfailure : (q.choose (r + 1) : ℝ) * n.choose r *
      Real.exp (-((2 * (r + 1).factorial * (n : ℝ) ^ (-b) * n /
        (n : ℝ) ^ (-a)) / 3)) < 1)
    (t : ℕ) (E : ℕ → Block (Fin n) (r + 1))
    (R B : Hypergraph (Fin n) (r + 1)) (hBR : Disjoint B R)
    (hB : IsGraphBounded B ((n : ℝ) ^ (-b)))
    (hE : Function.Injective (fun i : Fin t => E i)) (hEB : ∀ i < t, E i ∈ B)
    (hbound : IsEdgeFamilyBounded (fun i : Fin t => E i) ((n : ℝ) ^ (-b)))
    (hcount : ∀ i < t, (n : ℝ) ^ (-a) * (n : ℝ) ^ (q - (r + 1)) ≤
      (puncturedCliques R (E i) q).card) :
    ∃ Q : Fin t → Block (Fin n) q, IsCliqueCover R (fun i : Fin t => E i) Q ∧
      IsGraphBounded (cliqueCoverGraph (r := r) Q)
        ((n : ℝ) ^ (-b) + q.choose (r + 1) *
          (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a)))) := by
  classical
  let Φ : ℕ → F₀.val ↪ Fin n := fun i => edgeRootMap F₀ (E i)
  let A : (i : ℕ) → Finset (EmbeddingExtension (Φ i)) :=
    fun i => cliqueCandidateExtensions (Φ i) hW R (E i)
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have hempty : IsGraphBounded (∅ : Hypergraph (Fin n) (r + 1)) ((n : ℝ) ^ (-b)) :=
    isGraphBounded_empty (Real.rpow_pos_of_pos hx _) (by simpa only [Fintype.card_fin] using hn)
  have hroots : ∀ f ∈ complete W (r + 1), ∀ hf : f.val ⊆ F₀.val,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) ((n : ℝ) ^ (-b)) := by
    intro f _ hf
    have hf0 : f = F₀ :=
      Subtype.ext (eq_of_subset_of_card_le hf (by rw [f.property, F₀.property]))
    subst f
    simpa only [Φ, rootImage_edgeRootMap] using hbound
  have hsize : ∀ i < t, (n : ℝ) ^ (-a) *
      (n : ℝ) ^ (Fintype.card W - F₀.val.card) ≤ (A i).card := by
    intro i hi
    have hc : ((puncturedCliques R (E i) q).card : ℝ) ≤ (A i).card := by
      exact_mod_cast cliqueCandidateExtensions_card_ge (Φ i) hW R (E i)
        (edgeRootMap_usedVertices F₀ (E i))
    simpa only [hW, F₀.property] using (hcount i hi).trans hc
  have hc : (complete W (r + 1)).card = q.choose (r + 1) := by
    simp only [complete, card_univ, Block, Fintype.card_finset_len, hW]
  have hscale : 4 * ((r + 1).factorial : ℝ) * (n : ℝ) ^ (-b) / (n : ℝ) ^ (-a) =
      4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a)) := by
    rw [mul_div_assoc, rpow_density_ratio hx]
  obtain ⟨Ψ, hΨ, hmem⟩ := exists_greedy_family_in_candidates Φ A
    (complete W (r + 1)) ∅ hempty (by positivity) (by positivity)
    (Real.rpow_pos_of_pos hx _) (by simpa only [Fintype.card_fin] using hn)
    (by simpa only [hc] using hsmall) t
    (by simpa only [Fintype.card_fin] using hsize) (complete_root_admissible F₀) hroots
    (by simpa only [hc, Block, Fintype.card_finset_len, Fintype.card_fin] using hfailure)
  rw [hscale] at hΨ
  have hΨB : IsGreedyFamily (fun i => Φ i) (complete W (r + 1)) B Ψ
      (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a))) := by
    refine ⟨fun i => ?_, hΨ.disjoint, hΨ.bounded⟩
    have hp := (mem_cliqueCandidateExtensions _ _ _ _ _).mp (hmem i)
    have hrest := ((isPuncturedClique_iff _ _ _).mp hp).2
    rw [map_newEdges_complete_eq_erase F₀ hW _ _ (edgeRootMap_usedVertices F₀ (E i)) (Ψ i)]
    exact disjoint_of_subset_left hrest hBR.symm
  have hcover := hΨB.cliqueCover F₀ hW (fun i => E i) R B Ψ hE
    (fun i hi => disjoint_left.mp hBR (hEB i i.isLt) hi) hmem
  refine ⟨fun i => embeddingClique hW (Ψ i).val, hcover, ?_⟩
  have hbnd := (hΨB.graphBounded hB (by positivity)).subgraph
    (cliqueGraph_subset_base_union_new F₀ hW (fun i => E i) B Ψ (fun i => hEB i i.isLt))
  simpa only [hc] using hbnd

omit [Fintype W] [DecidableEq W] in
theorem exists_sparse_clique_cover_of_numerics (hq : r + 1 ≤ q) {a b : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hsmall : (q.choose (r + 1) : ℝ) * ((n : ℝ) ^ (-b) + q.choose (r + 1) *
      (4 * (r + 1).factorial * (n : ℝ) ^ (-b) / (n : ℝ) ^ (-a))) ≤
        (n : ℝ) ^ (-a) / 2)
    (hfailure : (q.choose (r + 1) : ℝ) * n.choose r *
      Real.exp (-((2 * (r + 1).factorial * (n : ℝ) ^ (-b) * n /
        (n : ℝ) ^ (-a)) / 3)) < 1)
    (R B : Hypergraph (Fin n) (r + 1)) (hBR : Disjoint B R)
    (hB : IsGraphBounded B ((n : ℝ) ^ (-b)))
    (hcount : ∀ e ∈ B, (n : ℝ) ^ (-a) * (n : ℝ) ^ (q - (r + 1)) ≤
      (puncturedCliques R e q).card) :
    ∃ Q : B → Block (Fin n) q, IsCliqueCover R (fun e => e.val) Q ∧
      IsGraphBounded (cliqueCoverGraph (r := r) Q)
        ((n : ℝ) ^ (-b) + q.choose (r + 1) *
          (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a)))) := by
  obtain ⟨s, _, hs⟩ := exists_subset_card_eq (s := (univ : Finset (Fin q)))
    (by simpa only [card_univ, Fintype.card_fin] using hq)
  let F₀ : Block (Fin q) (r + 1) := ⟨s, hs⟩
  have hcover := exists_indexed_sparse_clique_cover_of_numerics F₀
    (Fintype.card_fin q) hn hsmall hfailure
  rcases B.eq_empty_or_nonempty with hB0 | hBpos
  · subst B
    let Q : (∅ : Hypergraph (Fin n) (r + 1)) → Block (Fin n) q :=
      fun e => (notMem_empty _ e.property).elim
    have hQ : cliqueCoverGraph (r := r) Q = ∅ := by
      ext e
      simp only [cliqueCoverGraph, mem_biUnion, mem_univ, true_and, notMem_empty, iff_false]
      rintro ⟨i, _⟩
      exact notMem_empty _ i.property
    refine ⟨Q, ⟨fun e => (notMem_empty _ e.property).elim,
      fun i _ _ => (notMem_empty _ i.property).elim⟩, ?_⟩
    rw [hQ]
    have hx : (0 : ℝ) < n := by exact_mod_cast hn
    exact isGraphBounded_empty (by positivity) (by simpa only [Fintype.card_fin] using hn)
  · obtain ⟨e₀, _⟩ := hBpos
    let enum : Fin B.card ≃ B := B.equivFin.symm
    let E : ℕ → Block (Fin n) (r + 1) :=
      fun i => if hi : i < B.card then (enum ⟨i, hi⟩).val else e₀
    have hE (i : Fin B.card) : E i = (enum i).val := by
      dsimp only [E]
      rw [dif_pos i.isLt]
    have hEmem (i : Fin B.card) : E i ∈ B := hE i ▸ (enum i).property
    have hEinj : Function.Injective (fun i : Fin B.card => E i) := by
      intro i j hij
      exact enum.injective (Subtype.ext (by simpa only [hE] using hij))
    have hEcount : ∀ i < B.card, (n : ℝ) ^ (-a) * (n : ℝ) ^ (q - (r + 1)) ≤
        (puncturedCliques R (E i) q).card := fun i hi => hcount _ (hEmem ⟨i, hi⟩)
    obtain ⟨Q, hQ, hbnd⟩ := hcover B.card E R B hBR hB hEinj (fun i hi => hEmem ⟨i, hi⟩)
      (hB.edgeFamily (fun i : Fin B.card => E i) hEmem hEinj) hEcount
    refine ⟨fun e => Q (enum.symm e), ?_, ?_⟩
    · constructor
      · intro e
        have heq : E (enum.symm e) = e.val := by rw [hE, Equiv.apply_symm_apply]
        simpa only [heq] using hQ.punctured (enum.symm e)
      · intro e f hef
        exact hQ.disjoint (fun h => hef (enum.symm.injective h))
    · rw [cliqueCoverGraph_reindex]
      exact hbnd


omit [DecidableEq W] in
theorem eventually_exists_indexed_sparse_clique_cover (F₀ : Block W (r + 1))
    (hW : Fintype.card W = q) {a b : ℝ} (ha : 0 ≤ a) (hba : 2 * a < b)
    (hb1 : b - a < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, ∀ E : ℕ → Block (Fin n) (r + 1),
      ∀ R B : Hypergraph (Fin n) (r + 1), Disjoint B R →
      IsGraphBounded B ((n : ℝ) ^ (-b)) →
      Function.Injective (fun i : Fin t => E i) → (∀ i < t, E i ∈ B) →
      IsEdgeFamilyBounded (fun i : Fin t => E i) ((n : ℝ) ^ (-b)) →
      (∀ i < t, (n : ℝ) ^ (-a) * (n : ℝ) ^ (q - (r + 1)) ≤
        (puncturedCliques R (E i) q).card) →
      ∃ Q : Fin t → Block (Fin n) q, IsCliqueCover R (fun i : Fin t => E i) Q ∧
        IsGraphBounded (cliqueCoverGraph (r := r) Q)
          ((n : ℝ) ^ (-b) + q.choose (r + 1) *
            (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a)))) := by
  have hab : a < b := by linarith only [ha, hba]
  filter_upwards [eventually_prescribed_greedy_numerics (q.choose (r + 1)) r hba hab hb1]
    with n hn
  exact exists_indexed_sparse_clique_cover_of_numerics F₀ hW hn.1 hn.2.1 hn.2.2

omit [Fintype W] [DecidableEq W] in
theorem eventually_exists_sparse_clique_cover (hq : r + 1 ≤ q) {a b : ℝ}
    (ha : 0 ≤ a) (hba : 2 * a < b) (hb1 : b - a < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ R B : Hypergraph (Fin n) (r + 1), Disjoint B R →
      IsGraphBounded B ((n : ℝ) ^ (-b)) →
      (∀ e ∈ B, (n : ℝ) ^ (-a) * (n : ℝ) ^ (q - (r + 1)) ≤
        (puncturedCliques R e q).card) →
      ∃ Q : B → Block (Fin n) q, IsCliqueCover R (fun e => e.val) Q ∧
        IsGraphBounded (cliqueCoverGraph (r := r) Q)
          ((n : ℝ) ^ (-b) + q.choose (r + 1) *
            (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a)))) := by
  have hab : a < b := by linarith only [ha, hba]
  filter_upwards [eventually_prescribed_greedy_numerics (q.choose (r + 1)) r hba hab hb1]
    with n hn
  exact exists_sparse_clique_cover_of_numerics hq hn.1 hn.2.1 hn.2.2

end Arxiv2411_18291
