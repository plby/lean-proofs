import Arxiv.Arxiv2411_18291.ExchangeNearFar
import Arxiv.Arxiv2411_18291.SplittingSigns

/-!
# Intersections of the placed exchange copies

Different copies can share edges only in the original graph. A clique
inside a copy meets that graph in precisely its edges in the copy's root.
Consequently near cliques meet the original graph in one edge and far
cliques avoid it. These conclusions concern actual placed copies.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r C : ℕ} {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {θ : ℝ}

theorem SplittingFamily.root_edges_subset (F : SplittingFamily S D B C θ)
    (s : SignedCliqueSlots D C) : cliqueEdges (r + 1) (mapBlock (F.embedding s) S.base) ⊆ B := by
  rw [F.base s]
  intro e he
  exact F.source_support (mem_biUnion.mpr ⟨s.1.val, s.1.property, he⟩)

theorem SplittingFamily.copy_new_of_notMem (F : SplittingFamily S D B C θ)
    (s : SignedCliqueSlots D C) (e : Block V (r + 1))
    (he : e ∈ mapGraph (F.embedding s) S.graph) (heB : e ∉ B) :
    e ∈ mapGraph (F.embedding s) (newEdges S.base.val S.graph) := by
  obtain ⟨e₀, he₀, heq⟩ := (mem_mapGraph _ _ _).mp he
  have hnot : ¬e₀.val ⊆ S.base.val := by
    intro h
    exact heB (heq ▸ F.root_edges_subset s ((mem_cliqueEdges _ _).mpr (map_subset_map.mpr h)))
  exact (mem_mapGraph _ _ _).mpr ⟨e₀, (mem_newEdges S.graph e₀).mpr ⟨he₀, hnot⟩, heq⟩

theorem SplittingFamily.copy_inter_subset (F : SplittingFamily S D B C θ)
    {s t : SignedCliqueSlots D C} (hst : s ≠ t) :
    mapGraph (F.embedding s) S.graph ∩ mapGraph (F.embedding t) S.graph ⊆ B := by
  intro e he
  by_contra heB
  exact disjoint_left.mp (F.disjoint hst)
    (F.copy_new_of_notMem s e (mem_inter.mp he).1 heB)
    (F.copy_new_of_notMem t e (mem_inter.mp he).2 heB)

theorem SplittingFamily.copy_clique_inter (F : SplittingFamily S D B C θ)
    (s : SignedCliqueSlots D C) (P : Block W q) (hP : cliqueEdges (r + 1) P ⊆ S.graph) :
    cliqueEdges (r + 1) (mapBlock (F.embedding s) P) ∩ B =
      cliqueEdges (r + 1) (mapBlock (F.embedding s) P) ∩
        cliqueEdges (r + 1) (mapBlock (F.embedding s) S.base) := by
  ext e
  constructor
  · intro he
    obtain ⟨heP, heB⟩ := mem_inter.mp he
    have heMap : e ∈ mapGraph (F.embedding s) (cliqueEdges (r + 1) P) := by
      rwa [map_cliqueEdges]
    obtain ⟨e₀, he₀, heq⟩ := (mem_mapGraph _ _ _).mp heMap
    have heRoot : e₀.val ⊆ S.base.val := by
      by_contra hnot
      have hnew : e ∈ mapGraph (F.embedding s) (newEdges S.base.val S.graph) :=
        (mem_mapGraph _ _ _).mpr ⟨e₀, (mem_newEdges S.graph e₀).mpr ⟨hP he₀, hnot⟩, heq⟩
      exact disjoint_left.mp (F.avoids s) hnew heB
    refine mem_inter.mpr ⟨heP, ?_⟩
    exact heq ▸ (mem_cliqueEdges _ _).mpr (map_subset_map.mpr heRoot)
  · intro he
    exact mem_inter.mpr ⟨(mem_inter.mp he).1, F.root_edges_subset s (mem_inter.mp he).2⟩

theorem SplittingFamily.near_copy_inter (F : SplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (s : SignedCliqueSlots D C) (P : S.nearCliques) :
    cliqueEdges (r + 1) (mapBlock (F.embedding s) P.val) ∩ B =
      {mapBlock (F.embedding s) (hA.nearRoot (Nat.succ_pos r) P)} := by
  rw [F.copy_clique_inter s P.val (S.replacement_clique_subset (mem_filter.mp P.property).1)]
  rw [← map_cliqueEdges, ← map_cliqueEdges, ← mapGraph_inter,
    hA.nearRoot_inter (Nat.succ_pos r) P]
  simp only [mapGraph, map_singleton]
  rfl

theorem SplittingFamily.far_copy_disjoint (F : SplittingFamily S D B C θ)
    (s : SignedCliqueSlots D C) {P : Block W q} (hP : P ∈ S.farCliques) :
    Disjoint (cliqueEdges (r + 1) (mapBlock (F.embedding s) P)) B := by
  apply disjoint_iff_inter_eq_empty.mpr
  rw [F.copy_clique_inter s P (S.replacement_clique_subset (mem_sdiff.mp hP).1)]
  rw [← map_cliqueEdges, ← map_cliqueEdges, ← mapGraph_inter,
    disjoint_iff_inter_eq_empty.mp (S.far_disjoint_base hP)]
  exact map_empty _

theorem SplittingFamily.near_of_copy_inter (F : SplittingFamily S D B C θ)
    (s : SignedCliqueSlots D C) {P : Block W q} (hP : P ∈ S.replacementCliques)
    (hne : (cliqueEdges (r + 1) (mapBlock (F.embedding s) P) ∩ B).Nonempty) :
    P ∈ S.nearCliques := by
  apply mem_filter.mpr
  refine ⟨hP, ?_⟩
  rw [F.copy_clique_inter s P (S.replacement_clique_subset hP),
    ← map_cliqueEdges, ← map_cliqueEdges, ← mapGraph_inter] at hne
  simpa only [mapGraph, map_nonempty] using hne

omit [Fintype V] [DecidableEq V] in
theorem mem_free_image_of_not_root (f : W ↪ V) (P : Finset W) (R : Finset W) {v : V}
    (hv : v ∈ P.map f) (hnot : v ∉ R.map f) : v ∈ (univ \ R).map f := by
  classical
  rw [map_sdiff]
  exact mem_sdiff.mpr ⟨(map_subset_map.mpr (subset_univ P)) hv, hnot⟩

end Arxiv2411_18291
