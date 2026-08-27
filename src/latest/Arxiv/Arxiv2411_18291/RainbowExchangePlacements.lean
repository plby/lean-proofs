import Arxiv.Arxiv2411_18291.SparseRainbowGenerators
import Arxiv.Arxiv2411_18291.EliminationPattern
import Arxiv.Arxiv2411_18291.RootedCliquePattern

/-!
# Rainbow copies with one or two prescribed root cliques

The simultaneous extension theorem gives the second and third coloured
extension properties. Root maps prescribe the actual image cliques. For
two roots, exchange locality identifies precisely the edges to remove.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ}

omit [Fintype W] [Fintype V] in
theorem mapGraph_sdiff (f : W ↪ V) (H D : Hypergraph W r) :
    mapGraph f (H \ D) = mapGraph f H \ mapGraph f D := map_sdiff _ _

omit [Fintype V] [DecidableEq V] in
theorem newEdges_clique_root (H : Hypergraph W (r + 1)) (P : Block W q) :
    newEdges P.val H = H \ cliqueEdges (r + 1) P := by
  classical
  ext e
  rw [mem_newEdges, Finset.mem_sdiff, mem_cliqueEdges]

theorem rainbow_clique_root_of_extensions (H : Hypergraph W (r + 1)) (P₀ : Block W q)
    (σ : I → Equiv.Perm V) (G : Hypergraph V (r + 1))
    (hext : ∀ φ : P₀.val ↪ V, (rainbowExtensions φ (newEdges P₀.val H) σ G).Nonempty)
    (P : Block V q) : ∃ f : W ↪ V, mapBlock f P₀ = P ∧
      IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
        (mapGraph f H \ cliqueEdges (r + 1) P) := by
  obtain ⟨f, hf⟩ := hext (edgeRootMap P₀ P)
  have hP : mapBlock f.val P₀ = P :=
    (f.map_rootBlock _ P₀ Subset.rfl).trans (rootImage_edgeRootMap P₀ P)
  refine ⟨f.val, hP, ?_⟩
  have hcol := (mem_rainbowExtensions _ _ _ _ f).mp hf
  rw [newEdges_clique_root, mapGraph_sdiff, map_cliqueEdges, hP] at hcol
  exact hcol

theorem rainbow_pair_roots_of_extensions {S : ExchangeSystem W q (r + 1)}
    {N : Block W q} {e : Block W (r + 1)} (hpair : IsEliminationPair S N e)
    (σ : I → Equiv.Perm V) (G : Hypergraph V (r + 1))
    (hext : ∀ φ : ↥(S.base.val ∪ N.val) ↪ V,
      (rainbowExtensions φ (newEdges (S.base.val ∪ N.val) S.graph) σ G).Nonempty)
    (P Q : Block V q) (d : Block V (r + 1)) (hPQ : P.val ∩ Q.val = d.val) :
    ∃ f : W ↪ V, mapBlock f S.base = P ∧ mapBlock f N = Q ∧
      IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
        (mapGraph f S.graph \ (cliqueEdges (r + 1) P ∪ cliqueEdges (r + 1) Q)) := by
  obtain ⟨φ, hP, hQ⟩ := hpair.root_map P Q d hPQ
  obtain ⟨f, hf⟩ := hext φ
  obtain ⟨hfP, hfQ⟩ := pair_extension_roots φ hP hQ f
  refine ⟨f.val, hfP, hfQ, ?_⟩
  have hcol := (mem_rainbowExtensions _ _ _ _ f).mp hf
  rw [hpair.new_edges, mapGraph_sdiff, mapGraph_union, map_cliqueEdges,
    map_cliqueEdges, hfP, hfQ] at hcol
  exact hcol

omit [Fintype W] [Fintype V] [DecidableEq V] in
theorem eventually_sparse_host_rainbow_clique_roots [Finite W] (H : Hypergraph W (r + 1))
    (P₀ : Block W q) (h : ℕ) (hh : 1 ≤ h) (hH : H.card ≤ h)
    {α : ℝ} (hα : 0 < α) (hαh : α * h ≤ 1 / 4) :
    ∃ L : ℕ, ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h →
      (1 / 2 : ℝ) * (n : ℝ) ^ (-α) ≤ density K →
      ∀ G : Hypergraph (Fin n) (r + 1), G ⊆ K →
      ((K \ G).card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * K.card →
      ∃ σ : Option (Fin L × ↥(newEdges P₀.val H)) → Equiv.Perm (Fin n),
        ∀ P : Block (Fin n) q, ∃ f : W ↪ Fin n, mapBlock f P₀ = P ∧
          IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
            (mapGraph f H \ cliqueEdges (r + 1) P) := by
  let _ := Fintype.ofFinite W
  have hE : (newEdges P₀.val H).card ≤ h := (card_filter_le _ _).trans hH
  obtain ⟨L, hL⟩ := eventually_sparse_host_rainbow_extensions P₀.val (newEdges P₀.val H)
    (fun e he => ((mem_newEdges _ _).mp he).2) h hh hE hα hαh
  refine ⟨L, ?_⟩
  filter_upwards [hL] with n hn
  intro K hT hd G hGK hloss
  obtain ⟨σ, hσ⟩ := hn K hT hd G hGK hloss
  refine ⟨σ, rainbow_clique_root_of_extensions H P₀ σ G (fun φ => ?_)⟩
  have hG0 := density_nonneg G
  have hpos : (0 : ℝ) < (rainbowExtensions φ (newEdges P₀.val H) σ G).card :=
    (by positivity : (0 : ℝ) ≤ (3 / 8) * density G ^ (newEdges P₀.val H).card *
      (n : ℝ) ^ (Fintype.card W - P₀.val.card)).trans_lt (hσ φ)
  exact card_pos.mp (by exact_mod_cast hpos)

omit [Fintype V] [DecidableEq V] in
theorem eventually_sparse_host_rainbow_pair_roots {S : ExchangeSystem W q (r + 1)}
    {N : Block W q} {e : Block W (r + 1)} (hpair : IsEliminationPair S N e)
    (h : ℕ) (hh : 1 ≤ h) (hH : S.graph.card ≤ h)
    {α : ℝ} (hα : 0 < α) (hαh : α * h ≤ 1 / 4) :
    ∃ L : ℕ, ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h →
      (1 / 2 : ℝ) * (n : ℝ) ^ (-α) ≤ density K →
      ∀ G : Hypergraph (Fin n) (r + 1), G ⊆ K →
      ((K \ G).card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * K.card →
      ∃ σ : Option (Fin L × ↥(newEdges (S.base.val ∪ N.val) S.graph)) → Equiv.Perm (Fin n),
        ∀ P Q : Block (Fin n) q, ∀ d : Block (Fin n) (r + 1), P.val ∩ Q.val = d.val →
          ∃ f : W ↪ Fin n, mapBlock f S.base = P ∧ mapBlock f N = Q ∧
            IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
              (mapGraph f S.graph \ (cliqueEdges (r + 1) P ∪ cliqueEdges (r + 1) Q)) := by
  have hE : (newEdges (S.base.val ∪ N.val) S.graph).card ≤ h :=
    (card_filter_le _ _).trans hH
  obtain ⟨L, hL⟩ := eventually_sparse_host_rainbow_extensions (S.base.val ∪ N.val)
    (newEdges (S.base.val ∪ N.val) S.graph) (fun e he => ((mem_newEdges _ _).mp he).2)
      h hh hE hα hαh
  refine ⟨L, ?_⟩
  filter_upwards [hL] with n hn
  intro K hT hd G hGK hloss
  obtain ⟨σ, hσ⟩ := hn K hT hd G hGK hloss
  refine ⟨σ, rainbow_pair_roots_of_extensions hpair σ G (fun φ => ?_)⟩
  have hG0 := density_nonneg G
  have hpos : (0 : ℝ) <
      (rainbowExtensions φ (newEdges (S.base.val ∪ N.val) S.graph) σ G).card :=
    (by positivity : (0 : ℝ) ≤ (3 / 8) * density G ^
      (newEdges (S.base.val ∪ N.val) S.graph).card *
        (n : ℝ) ^ (Fintype.card W - (S.base.val ∪ N.val).card)).trans_lt (hσ φ)
  exact card_pos.mp (by exact_mod_cast hpos)

end Arxiv2411_18291
