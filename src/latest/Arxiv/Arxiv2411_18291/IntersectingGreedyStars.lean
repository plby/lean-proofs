import Arxiv.Arxiv2411_18291.GreedyEmbeddingExistence
import Mathlib.Data.Fintype.Option

/-! # Intersecting roots force distinct centres in greedy star extensions -/

open Finset

noncomputable section

namespace Arxiv2411_18291

def greedyStarRoots (A : Type*) [Fintype A] : Finset (Option A) :=
  univ.map ⟨some, Option.some_injective A⟩

theorem mem_greedyStarRoots {A : Type*} [Fintype A] (x : Option A) :
    x ∈ greedyStarRoots A ↔ ∃ a, some a = x := by
  simp only [greedyStarRoots, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]

theorem none_not_mem_greedyStarRoots (A : Type*) [Fintype A] :
    none ∉ greedyStarRoots A := by
  rw [mem_greedyStarRoots]
  simp only [Option.some_ne_none, exists_false, not_false_eq_true]

def greedyStarRootEquiv (A : Type*) [Fintype A] : A ≃ greedyStarRoots A where
  toFun a := ⟨some a, (mem_greedyStarRoots _).mpr ⟨a, rfl⟩⟩
  invFun x := Classical.choose ((mem_greedyStarRoots _).mp x.property)
  left_inv a := Option.some.inj (Classical.choose_spec
    ((mem_greedyStarRoots _).mp (show some a ∈ greedyStarRoots A from
      (mem_greedyStarRoots _).mpr ⟨a, rfl⟩)))
  right_inv x := Subtype.ext (Classical.choose_spec ((mem_greedyStarRoots _).mp x.property))

def greedyStarSpoke {A : Type*} [DecidableEq A] (a : A) : Block (Option A) 2 :=
  ⟨{none, some a}, by simp⟩

theorem greedyStarSpoke_new {A : Type*} [Fintype A] [DecidableEq A]
    (H : Hypergraph (Option A) 2) (a : A) (ha : greedyStarSpoke a ∈ H) :
    greedyStarSpoke a ∈ newEdges (greedyStarRoots A) H := by
  refine (mem_newEdges H _).mpr ⟨ha, ?_⟩
  intro h
  exact none_not_mem_greedyStarRoots A (h (mem_insert_self _ _))

theorem intersecting_greedy_stars_centres_injective
    {A V : Type*} [Fintype A] [Fintype V] [DecidableEq A] [DecidableEq V] {t : ℕ}
    (H : Hypergraph (Option A) 2) (hH : ∀ a : A, greedyStarSpoke a ∈ H)
    (Φ : Fin t → greedyStarRoots A ↪ V)
    (hmeet : ∀ i j, (usedVertices (Φ i) ∩ usedVertices (Φ j)).Nonempty)
    (B : Hypergraph V 2) {L : ℝ}
    (Ψ : (i : Fin t) → EmbeddingExtension (Φ i)) (hΨ : IsGreedyFamily Φ H B Ψ L) :
    Function.Injective (fun i : Fin t => (Ψ i).val none) := by
  intro i j hcentre
  by_contra hij
  obtain ⟨v, hv⟩ := hmeet i j
  obtain ⟨hvi, hvj⟩ := mem_inter.mp hv
  obtain ⟨x, hx⟩ := (mem_usedVertices (Φ i) v).mp hvi
  obtain ⟨y, hy⟩ := (mem_usedVertices (Φ j) v).mp hvj
  obtain ⟨a, ha⟩ := (mem_greedyStarRoots _).mp x.property
  obtain ⟨b, hb⟩ := (mem_greedyStarRoots _).mp y.property
  have hax : (Ψ i).val (some a) = v := by rw [ha, (Ψ i).property x, hx]
  have hby : (Ψ j).val (some b) = v := by rw [hb, (Ψ j).property y, hy]
  have heq : mapBlock (Ψ i).val (greedyStarSpoke a) =
      mapBlock (Ψ j).val (greedyStarSpoke b) := by
    apply Subtype.ext
    simp only [mapBlock, greedyStarSpoke, map_insert, map_singleton, hcentre, hax, hby]
  have hi : mapBlock (Ψ i).val (greedyStarSpoke a) ∈
      mapGraph (Ψ i).val (newEdges (greedyStarRoots A) H) :=
    (mem_mapGraph _ _ _).mpr ⟨greedyStarSpoke a, greedyStarSpoke_new H a (hH a), rfl⟩
  have hj : mapBlock (Ψ j).val (greedyStarSpoke b) ∈
      mapGraph (Ψ j).val (newEdges (greedyStarRoots A) H) :=
    (mem_mapGraph _ _ _).mpr ⟨greedyStarSpoke b, greedyStarSpoke_new H b (hH b), rfl⟩
  exact disjoint_left.mp (hΨ.disjoint hij) hi (heq.symm ▸ hj)

theorem intersecting_greedy_stars_length_le
    {A V : Type*} [Fintype A] [Fintype V] [DecidableEq A] [DecidableEq V] {t : ℕ}
    (H : Hypergraph (Option A) 2) (hH : ∀ a : A, greedyStarSpoke a ∈ H)
    (Φ : Fin t → greedyStarRoots A ↪ V)
    (hmeet : ∀ i j, (usedVertices (Φ i) ∩ usedVertices (Φ j)).Nonempty)
    (B : Hypergraph V 2) {L : ℝ}
    (Ψ : (i : Fin t) → EmbeddingExtension (Φ i)) (hΨ : IsGreedyFamily Φ H B Ψ L) :
    t ≤ Fintype.card V := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
    (fun i : Fin t => (Ψ i).val none)
    (intersecting_greedy_stars_centres_injective H hH Φ hmeet B Ψ hΨ)

end Arxiv2411_18291
