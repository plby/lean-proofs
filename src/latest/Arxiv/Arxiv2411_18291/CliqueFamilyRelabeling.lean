import Arxiv.Arxiv2411_18291.CliqueFamilyBoundedness
import Arxiv.Arxiv2411_18291.CoefficientRelabeling
import Arxiv.Arxiv2411_18291.RootedCliqueExtensions

/-!
# Relabeling and unions of bounded clique families

Vertex permutations preserve clique counts and boundary degrees. A finite
nonempty union of relabeled families has the sum of their bounds, regardless
of overlap between the families.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V W I : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {q r : ℕ}

omit [Fintype V] [Fintype W] in
theorem mapGraph_filter_containing (f : V ↪ W) (D : Finset (Block V q)) (S : Block V r) :
    (mapGraph f D).filter (fun Q => (mapBlock f S).val ⊆ Q.val) =
      mapGraph f (D.filter fun Q => S.val ⊆ Q.val) := by
  simp only [mapGraph, filter_map, blockEmbedding, Function.Embedding.coeFn_mk, Function.comp_def,
    mapBlock_subset_mapBlock]

omit [Fintype V] [Fintype W] in
theorem card_mapGraph_containing (f : V ↪ W) (D : Finset (Block V q)) (S : Block V r) :
    ((mapGraph f D).filter fun Q => (mapBlock f S).val ⊆ Q.val).card =
      (D.filter fun Q => S.val ⊆ Q.val).card := by
  rw [mapGraph_filter_containing, card_mapGraph]

theorem boundary_indicator_mapGraph (f : V ↪ W) (D : Finset (Block V q)) (e : Block V r) :
    boundary r (indicator (mapGraph f D)) (mapBlock f e) = boundary r (indicator D) e := by
  simp only [boundary_indicator, card_mapGraph_containing]

theorem degree_boundary_indicator_mapGraph (f : V ≃ W) (D : Finset (Block V q))
    (S : Block V r) :
    degree (boundary (r + 1) (indicator (mapGraph f.toEmbedding D)))
        (mapBlock f.toEmbedding S).val = degree (boundary (r + 1) (indicator D)) S.val := by
  rw [show (mapBlock f.toEmbedding S).val = S.val.map f.toEmbedding from rfl,
    ← degree_relabel]
  simp only [boundary_indicator_mapGraph]

theorem IsCliqueFamilyBounded.map {D : Finset (Block V q)} {θ : ℝ}
    (hD : IsCliqueFamilyBounded r D θ) (f : V ≃ W) :
    IsCliqueFamilyBounded r (mapGraph f.toEmbedding D) θ := by
  intro S
  obtain ⟨S, rfl⟩ := (blockEquiv (r := r) f).surjective S
  change ((degree (boundary (r + 1) (indicator (mapGraph f.toEmbedding D)))
    (mapBlock f.toEmbedding S).val : ℤ) : ℝ) < θ * Fintype.card W
  rw [degree_boundary_indicator_mapGraph, ← Fintype.card_congr f]
  exact hD S

theorem cliqueFamily_mapGraph (f : V ≃ W) (K : Hypergraph V r) (q : ℕ) :
    cliqueFamily (mapGraph f.toEmbedding K) q = mapGraph f.toEmbedding (cliqueFamily K q) := by
  ext Q
  obtain ⟨Q, rfl⟩ := (blockEquiv (r := q) f).surjective Q
  change mapBlock f.toEmbedding Q ∈ cliqueFamily (mapGraph f.toEmbedding K) q ↔
    mapBlock f.toEmbedding Q ∈ mapGraph f.toEmbedding (cliqueFamily K q)
  have hmem : mapBlock f.toEmbedding Q ∈ mapGraph f.toEmbedding (cliqueFamily K q) ↔
      Q ∈ cliqueFamily K q := by
    simp only [mapGraph, mem_map, blockEmbedding, Function.Embedding.coeFn_mk,
      (mapBlock_injective f.toEmbedding).eq_iff, exists_eq_right]
  rw [hmem]
  simp only [cliqueFamily, mem_filter, mem_univ, true_and]
  rw [← map_cliqueEdges]
  exact map_subset_map

theorem IsCliqueFamilyBounded.biUnion (s : Finset I)
    (hs : s.Nonempty) (D : I → Finset (Block V q)) (θ : ℝ)
    (hD : ∀ i ∈ s, IsCliqueFamilyBounded r (D i) θ) :
    IsCliqueFamilyBounded r (s.biUnion D) (s.card * θ) := by
  classical
  revert hs hD
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro _ hD
    have hiD := hD i (mem_insert_self _ _)
    by_cases hs : s.Nonempty
    · have hsD := ih hs (fun j hj => hD j (mem_insert_of_mem hj))
      rw [biUnion_insert, card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      convert hiD.union hsD using 1
      ring
    · have hempty : s = ∅ := not_nonempty_iff_eq_empty.mp hs
      subst s
      simpa only [insert_empty_eq, singleton_biUnion, card_singleton,
        Nat.cast_one, one_mul] using hiD

end Arxiv2411_18291
