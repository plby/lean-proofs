import Arxiv.Arxiv2411_18291.RainbowCliqueExistence
import Arxiv.Arxiv2411_18291.RainbowExchangePlacements
import Arxiv.Arxiv2411_18291.RainbowColourRelabeling

/-!
# One colour family with all three extension properties

Combining the separately constructed colour groups preserves their rainbow
witnesses. Relabelling the finite union by `Fin u` produces one fixed number
of colours, independent of the ambient size. This combines the first three
properties only; generation of every rainbow clique is a separate theorem.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {U W : Type*} [Fintype U] [Fintype W] [DecidableEq W]
variable {q r : ℕ}

theorem eventually_combined_rainbow_extensions (F₀ : Block U (r + 1))
    (hU : Fintype.card U = q) {S : ExchangeSystem W q (r + 1)}
    {N : Block W q} {e₀ : Block W (r + 1)} (hpair : IsEliminationPair S N e₀)
    (h : ℕ) (hqh : q.choose (r + 1) ≤ h) (hH : S.graph.card ≤ h)
    {α : ℝ} (hα : 0 < α) (hαh : α * h ≤ 1 / 4) :
    ∃ u : ℕ, ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h →
      (1 / 2 : ℝ) * (n : ℝ) ^ (-α) ≤ density K →
      ∀ G : Hypergraph (Fin n) (r + 1), G ⊆ K →
      ((K \ G).card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * K.card →
      ∃ σ : Fin u → Equiv.Perm (Fin n),
        (∀ e : Block (Fin n) (r + 1),
          ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) * (n : ℝ) ^ (q - (r + 1))) /
            (q - (r + 1)).factorial <
              (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card) ∧
        (∀ P : Block (Fin n) q, ∃ f : W ↪ Fin n, mapBlock f S.base = P ∧
          IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
            (mapGraph f S.graph \ cliqueEdges (r + 1) P)) ∧
        (∀ P Q : Block (Fin n) q, ∀ d : Block (Fin n) (r + 1), P.val ∩ Q.val = d.val →
          ∃ f : W ↪ Fin n, mapBlock f S.base = P ∧ mapBlock f N = Q ∧
            IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
              (mapGraph f S.graph \ (cliqueEdges (r + 1) P ∪ cliqueEdges (r + 1) Q))) := by
  classical
  have hqr : r + 1 ≤ q := by
    simpa only [F₀.property, hU] using card_le_univ F₀.val
  have hh : 1 ≤ h := (Nat.succ_le_iff.mpr (Nat.choose_pos hqr)).trans hqh
  obtain ⟨L₁, h₁⟩ := eventually_sparse_host_rainbow_cliques F₀ hU h hqh hα hαh
  obtain ⟨L₂, h₂⟩ :=
    eventually_sparse_host_rainbow_clique_roots S.graph S.base h hh hH hα hαh
  obtain ⟨L₃, h₃⟩ := eventually_sparse_host_rainbow_pair_roots hpair h hh hH hα hαh
  let J₁ := Option (Fin L₁ × ↥(newEdges F₀.val (complete U (r + 1))))
  let J₂ := Option (Fin L₂ × ↥(newEdges S.base.val S.graph))
  let J₃ := Option (Fin L₃ × ↥(newEdges (S.base.val ∪ N.val) S.graph))
  let J := J₁ ⊕ (J₂ ⊕ J₃)
  let p : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let e₁ : J₁ ↪ J := Function.Embedding.inl
  let e₂ : J₂ ↪ J := Function.Embedding.inl.trans Function.Embedding.inr
  let e₃ : J₃ ↪ J := Function.Embedding.inr.trans Function.Embedding.inr
  let η₁ := e₁.trans p.toEmbedding
  let η₂ := e₂.trans p.toEmbedding
  let η₃ := e₃.trans p.toEmbedding
  refine ⟨Fintype.card J, ?_⟩
  filter_upwards [h₁, h₂, h₃] with n hn₁ hn₂ hn₃
  intro K hT hd G hGK hloss
  obtain ⟨σ₁, hσ₁⟩ := hn₁ K hT hd G hGK hloss
  obtain ⟨σ₂, hσ₂⟩ := hn₂ K hT hd G hGK hloss
  obtain ⟨σ₃, hσ₃⟩ := hn₃ K hT hd G hGK hloss
  let σ : Fin (Fintype.card J) → Equiv.Perm (Fin n) :=
    fun i => Sum.elim σ₁ (Sum.elim σ₂ σ₃) (p.symm i)
  have hη₁ (i : J₁) : σ (η₁ i) = σ₁ i := by
    change Sum.elim σ₁ (Sum.elim σ₂ σ₃) (p.symm (p (Sum.inl i))) = σ₁ i
    rw [p.symm_apply_apply]
    rfl
  have hη₂ (i : J₂) : σ (η₂ i) = σ₂ i := by
    change Sum.elim σ₁ (Sum.elim σ₂ σ₃) (p.symm (p (Sum.inr (Sum.inl i)))) = σ₂ i
    rw [p.symm_apply_apply]
    rfl
  have hη₃ (i : J₃) : σ (η₃ i) = σ₃ i := by
    change Sum.elim σ₁ (Sum.elim σ₂ σ₃) (p.symm (p (Sum.inr (Sum.inr i)))) = σ₃ i
    rw [p.symm_apply_apply]
    rfl
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro e
    have hc := card_le_card (rainbowPuncturedCliques_subset_reindex σ₁ σ G η₁ hη₁ e (q := q))
    exact (hσ₁ e).trans_le (by exact_mod_cast hc)
  · intro P
    obtain ⟨f, hf, hcol⟩ := hσ₂ P
    exact ⟨f, hf, hcol.permutation_reindex η₂ hη₂⟩
  · intro P Q d hPQ
    obtain ⟨f, hfP, hfQ, hcol⟩ := hσ₃ P Q d hPQ
    exact ⟨f, hfP, hfQ, hcol.permutation_reindex η₃ hη₃⟩

end Arxiv2411_18291
