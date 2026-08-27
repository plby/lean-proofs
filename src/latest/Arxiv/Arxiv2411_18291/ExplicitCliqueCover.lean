import Arxiv.Arxiv2411_18291.CoverExistence
import Arxiv.Arxiv2411_18291.ExplicitCoverTail

/-! # The Cover lemma at the printed threshold -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] {q r n : ℕ}

theorem exists_indexed_clique_cover_paper_threshold (F₀ : Block W (r + 1))
    (hW : Fintype.card W = q) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (t : ℕ)
    (E : ℕ → Block (Fin n) (r + 1)) (R : Hypergraph (Fin n) (r + 1))
    (hE : Function.Injective (fun i : Fin t => E i)) (hER : ∀ i < t, E i ∉ R)
    (hbound : IsEdgeFamilyBounded (fun i : Fin t => E i)
      ((n : ℝ) ^ (-(3 * q.choose (r + 1) * paperRho q (r + 1)))))
    (hcount : ∀ i < t, (n : ℝ) ^ (-((q.choose (r + 1) : ℝ) * paperRho q (r + 1))) *
      (n : ℝ) ^ (q - (r + 1)) ≤ (puncturedCliques R (E i) q).card) :
    ∃ Q : Fin t → Block (Fin n) q, IsCliqueCover R (fun i : Fin t => E i) Q := by
  classical
  let K := q.choose (r + 1)
  let a : ℝ := K * paperRho q (r + 1)
  let θ := (n : ℝ) ^ (-(3 * a))
  let η := (n : ℝ) ^ (-a)
  let Φ : ℕ → F₀.val ↪ Fin n := fun i => edgeRootMap F₀ (E i)
  let A : (i : ℕ) → Finset (EmbeddingExtension (Φ i)) :=
    fun i => cliqueCandidateExtensions (Φ i) hW R (E i)
  have hnNat : 0 < n := Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hx : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hθ : 0 < θ := Real.rpow_pos_of_pos hx _
  have hη : 0 < η := Real.rpow_pos_of_pos hx _
  have hB : IsGraphBounded (∅ : Hypergraph (Fin n) (r + 1)) θ :=
    isGraphBounded_empty hθ (by simpa only [Fintype.card_fin] using hnNat)
  have hHcard : (complete W (r + 1)).card = K := by
    simp only [complete, card_univ, Block, Fintype.card_finset_len, hW, K]
  have hroots : ∀ f ∈ complete W (r + 1), ∀ hf : f.val ⊆ F₀.val,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ := by
    intro f _ hf
    have hf0 : f = F₀ :=
      Subtype.ext (eq_of_subset_of_card_le hf (by rw [f.property, F₀.property]))
    subst f
    simpa only [Φ, rootImage_edgeRootMap, θ, a, K, mul_assoc] using hbound
  have hsize : ∀ i < t, η *
      (Fintype.card (Fin n) : ℝ) ^ (Fintype.card W - F₀.val.card) ≤ (A i).card := by
    intro i hi
    have hc : ((puncturedCliques R (E i) q).card : ℝ) ≤ (A i).card := by
      exact_mod_cast cliqueCandidateExtensions_card_ge (Φ i) hW R (E i)
        (edgeRootMap_usedVertices F₀ (E i))
    simpa only [hW, F₀.property, Fintype.card_fin] using (hcount i hi).trans hc
  have hsmall : (complete W (r + 1)).card *
      (θ + (complete W (r + 1)).card * (4 * (r + 1).factorial * θ / η)) ≤ η / 2 := by
    simpa only [hHcard] using paper_cover_smallness hqr hn
  have hfailure : (complete W (r + 1)).card * Fintype.card (Block (Fin n) r) *
      Real.exp (-((2 * (r + 1).factorial * θ * Fintype.card (Fin n) / η) / 3)) < 1 := by
    simpa only [hHcard, Block, Fintype.card_finset_len, Fintype.card_fin] using
      paper_cover_failure_lt_one hqr hn
  obtain ⟨Ψ, hΨ, hmem⟩ := exists_greedy_family_in_candidates Φ A (complete W (r + 1)) ∅
    hB hθ.le hθ.le hη (by simpa only [Fintype.card_fin] using hnNat)
    hsmall t hsize (complete_root_admissible F₀) hroots hfailure
  exact ⟨fun i => embeddingClique hW (Ψ i).val,
    hΨ.cliqueCover F₀ hW (fun i => E i) R ∅ Ψ hE (fun i => hER i i.isLt) hmem⟩

omit [Fintype W] in
/-- Lemma 2.5, with no eventual size assumption and no separate degree
assumption on the reserve. Extension counts are needed only at leave edges. -/
theorem exists_clique_cover_paper_threshold (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (R L : Hypergraph (Fin n) (r + 1))
    (hLR : Disjoint L R)
    (hL : IsGraphBounded L ((n : ℝ) ^ (-(3 * q.choose (r + 1) * paperRho q (r + 1)))))
    (hcount : ∀ e ∈ L,
      (n : ℝ) ^ (-((q.choose (r + 1) : ℝ) * paperRho q (r + 1))) *
        (n : ℝ) ^ (q - (r + 1)) ≤ (puncturedCliques R e q).card) :
    ∃ Q : L → Block (Fin n) q, IsCliqueCover R (fun e => e.val) Q := by
  obtain ⟨s, _, hs⟩ := exists_subset_card_eq (s := (univ : Finset (Fin q)))
    (by simpa only [card_univ, Fintype.card_fin] using hqr.le)
  let F₀ : Block (Fin q) (r + 1) := ⟨s, hs⟩
  rcases L.eq_empty_or_nonempty with hL0 | hLpos
  · subst L
    exact ⟨fun e => (notMem_empty _ e.property).elim,
      ⟨fun e => (notMem_empty _ e.property).elim,
        fun i _ _ => (notMem_empty _ i.property).elim⟩⟩
  · obtain ⟨e₀, _⟩ := hLpos
    let enum : Fin L.card ≃ L := L.equivFin.symm
    let E : ℕ → Block (Fin n) (r + 1) :=
      fun i => if hi : i < L.card then (enum ⟨i, hi⟩).val else e₀
    have hE (i : Fin L.card) : E i = (enum i).val := by
      dsimp [E]
      rw [if_pos i.isLt]
    have hEmem (i : Fin L.card) : E i ∈ L := hE i ▸ (enum i).property
    have hEinj : Function.Injective (fun i : Fin L.card => E i) := by
      intro i j hij
      apply enum.injective
      apply Subtype.ext
      simpa only [hE] using hij
    have hER : ∀ i < L.card, E i ∉ R := by
      intro i hi
      exact fun hR => disjoint_left.mp hLR (hEmem ⟨i, hi⟩) hR
    have hEcount : ∀ i < L.card,
        (n : ℝ) ^ (-((q.choose (r + 1) : ℝ) * paperRho q (r + 1))) *
          (n : ℝ) ^ (q - (r + 1)) ≤ (puncturedCliques R (E i) q).card :=
      fun i hi => hcount (E i) (hEmem ⟨i, hi⟩)
    obtain ⟨Q, hQ⟩ := exists_indexed_clique_cover_paper_threshold F₀
      (Fintype.card_fin q) hqr hn L.card E R hEinj hER
      (hL.edgeFamily (fun i : Fin L.card => E i) hEmem hEinj) hEcount
    refine ⟨fun e => Q (enum.symm e), ?_⟩
    constructor
    · intro e
      have heq : E (enum.symm e) = e.val := by
        rw [hE, Equiv.apply_symm_apply]
      simpa only [heq] using hQ.punctured (enum.symm e)
    · intro e f hef
      exact hQ.disjoint (fun h => hef (enum.symm.injective h))

end Arxiv2411_18291
