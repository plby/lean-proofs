import Arxiv.Arxiv2411_18291.ExchangeSystem
import Arxiv.Arxiv2411_18291.GreedyEmbeddingExistence

/-!
# Replacing a base clique by the exchange configuration

The negative decomposition minus the positive decomposition with its base
removed has boundary exactly the base clique. Its coefficients lie in
`{-1,0,1}`, and every supporting clique contains an edge outside the base.
All statements persist under injective relabeling.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291
namespace ExchangeSystem

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ}

def map (S : ExchangeSystem W q r) (f : W ↪ V) : ExchangeSystem V q r where
  graph := mapGraph f S.graph
  positive := mapGraph f S.positive
  negative := mapGraph f S.negative
  positive_decomposition := S.positive_decomposition.map f
  negative_decomposition := S.negative_decomposition.map f
  disjoint := (disjoint_map _).mpr S.disjoint
  base := mapBlock f S.base
  base_mem := (mem_mapGraph f S.positive _).mpr ⟨S.base, S.base_mem, rfl⟩

def replacementCliques (S : ExchangeSystem W q r) : Finset (Block W q) :=
  S.negative ∪ S.positive.erase S.base

def replacementVector (S : ExchangeSystem W q r) : Block W q → ℤ :=
  indicator S.negative - indicator (S.positive.erase S.base)

theorem replacementCliques_map (S : ExchangeSystem W q r) (f : W ↪ V) :
    (S.map f).replacementCliques = mapGraph f S.replacementCliques := by
  change mapGraph f S.negative ∪ (mapGraph f S.positive).erase (mapBlock f S.base) =
    mapGraph f (S.negative ∪ S.positive.erase S.base)
  rw [mapGraph_union, mapGraph_erase]

theorem replacement_ne_base (S : ExchangeSystem W q r) {P : Block W q}
    (hP : P ∈ S.replacementCliques) : P ≠ S.base := by
  rcases mem_union.mp hP with hN | hP
  · intro heq
    exact disjoint_left.mp S.disjoint (heq ▸ S.base_mem) hN
  · exact (mem_erase.mp hP).1

theorem replacement_clique_subset (S : ExchangeSystem W q r) {P : Block W q}
    (hP : P ∈ S.replacementCliques) : cliqueEdges r P ⊆ S.graph := by
  rcases mem_union.mp hP with hN | hP
  · exact S.negative_decomposition.clique_subset hN
  · exact S.positive_decomposition.clique_subset (mem_erase.mp hP).2

theorem replacement_new_edge (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 ≤ q)
    {P : Block W q} (hP : P ∈ S.replacementCliques) :
    ∃ e ∈ cliqueEdges (r + 1) P, e ∈ newEdges S.base.val S.graph := by
  have hnot : ¬cliqueEdges (r + 1) P ⊆ cliqueEdges (r + 1) S.base := by
    intro h
    apply S.replacement_ne_base hP
    exact Subtype.ext (eq_of_subset_of_card_le
      (clique_vertices_subset (Nat.succ_pos r) hqr P S.base h)
      (by rw [P.property, S.base.property]))
  obtain ⟨e, heP, heB⟩ := not_subset.mp hnot
  exact ⟨e, heP, (mem_newEdges S.graph e).mpr
    ⟨S.replacement_clique_subset hP heP, fun h => heB ((mem_cliqueEdges _ _).mpr h)⟩⟩

theorem boundary_replacement (S : ExchangeSystem W q r) :
    boundary r S.replacementVector = indicator (cliqueEdges r S.base) := by
  have hp : indicator (S.positive.erase S.base) = indicator S.positive - indicator {S.base} := by
    rw [← sdiff_singleton_eq_erase, indicator_sdiff (singleton_subset_iff.mpr S.base_mem)]
  rw [replacementVector, hp, boundary_sub, boundary_sub,
    S.negative_decomposition, S.positive_decomposition, boundary_indicator_singleton]
  funext e
  simp only [Pi.sub_apply]
  ring

theorem replacementVector_abs_le (S : ExchangeSystem W q r) (P : Block W q) :
    |S.replacementVector P| ≤ 1 := by
  simp only [replacementVector, Pi.sub_apply, indicator]
  split_ifs <;> norm_num

theorem replacementVector_support (S : ExchangeSystem W q r) (P : Block W q)
    (hP : P ∉ S.replacementCliques) : S.replacementVector P = 0 := by
  have hN : P ∉ S.negative := fun h => hP (mem_union_left _ h)
  have hpos : P ∉ S.positive.erase S.base := fun h => hP (mem_union_right _ h)
  simp only [replacementVector, Pi.sub_apply, indicator_apply_of_notMem hN,
    indicator_apply_of_notMem hpos, sub_self]

end ExchangeSystem
end Arxiv2411_18291
