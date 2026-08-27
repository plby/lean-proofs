import Arxiv.Arxiv2411_18291.SparseRainbowGenerators
import Arxiv.Arxiv2411_18291.RainbowCliqueCounts

/-!
# Simultaneous rainbow punctured cliques

This gives the first coloured-extension property with a conservative
constant and the correct factorial for distinct cliques. All roots share
the same finite collection of permuted good subgraphs.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {q r : ℕ}

theorem card_newEdges_complete_root (F₀ : Block W (r + 1)) (hW : Fintype.card W = q) :
    (newEdges F₀.val (complete W (r + 1))).card = q.choose (r + 1) - 1 := by
  rw [newEdges_complete_root, complete, card_erase_of_mem (mem_univ F₀)]
  simp only [card_univ, Block, Fintype.card_finset_len, hW]

theorem eventually_sparse_host_rainbow_cliques (F₀ : Block W (r + 1))
    (hW : Fintype.card W = q) (h : ℕ) (hqh : q.choose (r + 1) ≤ h)
    {α : ℝ} (hα : 0 < α) (hαh : α * h ≤ 1 / 4) :
    ∃ L : ℕ, ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h →
      (1 / 2 : ℝ) * (n : ℝ) ^ (-α) ≤ density K →
      ∀ G : Hypergraph (Fin n) (r + 1), G ⊆ K →
      ((K \ G).card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * K.card →
      ∃ σ : Option (Fin L × ↥(newEdges F₀.val (complete W (r + 1)))) → Equiv.Perm (Fin n),
        ∀ e : Block (Fin n) (r + 1),
          ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) * (n : ℝ) ^ (q - (r + 1))) /
            (q - (r + 1)).factorial <
              (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card := by
  have hqr : r + 1 ≤ q := by
    simpa only [F₀.property, hW] using card_le_univ F₀.val
  have hh : 1 ≤ h := (Nat.succ_le_iff.mpr (Nat.choose_pos hqr)).trans hqh
  have hE := card_newEdges_complete_root F₀ hW
  have hEh : (newEdges F₀.val (complete W (r + 1))).card ≤ h := by
    rw [hE]
    exact (Nat.sub_le _ _).trans hqh
  obtain ⟨L, hL⟩ := eventually_sparse_host_rainbow_extensions F₀.val
    (newEdges F₀.val (complete W (r + 1))) (fun e he => ((mem_newEdges _ _).mp he).2)
      h hh hEh hα hαh
  refine ⟨L, ?_⟩
  filter_upwards [hL] with n hn
  intro K hT hd G hGK hloss
  obtain ⟨σ, hσ⟩ := hn K hT hd G hGK hloss
  refine ⟨σ, fun e => ?_⟩
  apply rainbow_cliques_card_lower F₀ hW σ G e
  simpa only [hE, hW, F₀.property] using hσ (edgeRootMap F₀ e)

end Arxiv2411_18291
