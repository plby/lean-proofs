import Arxiv.Arxiv2411_18291.Decomposition
import Mathlib.Data.Fintype.Prod

/-! # Complete partite hypergraphs and cliques given by functions -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {F : Type*} {q r : ℕ}

/-- One vertex in each of the `q` parts, specified by a function. -/
def graphClique (v : Fin q → F) : Block (Fin q × F) q :=
  ⟨univ.map ⟨fun i => (i, v i), fun _ _ h => congrArg Prod.fst h⟩, by simp⟩

@[simp] theorem mem_graphClique (v : Fin q → F) (i : Fin q) (x : F) :
    (i, x) ∈ (graphClique v).val ↔ x = v i := by
  simp only [graphClique, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨j, h⟩
    have hj : j = i := congrArg Prod.fst h
    subst j
    exact (congrArg Prod.snd h).symm
  · intro h
    refine ⟨i, ?_⟩
    change (i, v i) = (i, x)
    rw [h]

theorem graphClique_injective :
    Function.Injective (graphClique : (Fin q → F) → Block (Fin q × F) q) := by
  intro v w h
  funext i
  have hm : (i, v i) ∈ (graphClique v).val := by simp
  rw [h] at hm
  exact (mem_graphClique w i (v i)).mp hm

/-- The complete `q`-partite `r`-graph with every part a copy of `F`. -/
def partiteGraph (F : Type*) [Fintype F] [DecidableEq F] (q r : ℕ) :
    Hypergraph (Fin q × F) r := by
  classical
  exact univ.filter fun e => Set.InjOn Prod.fst (e.val : Set (Fin q × F))

@[simp] theorem mem_partiteGraph [Fintype F] [DecidableEq F] (e : Block (Fin q × F) r) :
    e ∈ partiteGraph F q r ↔ Set.InjOn Prod.fst (e.val : Set (Fin q × F)) := by
  classical
  simp [partiteGraph]

theorem graphClique_edges_subset [Fintype F] [DecidableEq F] (v : Fin q → F) :
    cliqueEdges r (graphClique v) ⊆ partiteGraph F q r := by
  intro e he
  rw [mem_partiteGraph]
  have heQ := (mem_cliqueEdges e (graphClique v)).mp he
  intro a ha b hb hab
  have ha' : a.2 = v a.1 := (mem_graphClique v a.1 a.2).mp (heQ ha)
  have hb' : b.2 = v b.1 := (mem_graphClique v b.1 b.2).mp (heQ hb)
  exact Prod.ext hab (by rw [ha', hb', hab])

/-- A family with exactly one clique through each host edge and no edges
outside the host is a decomposition in the incidence-vector definition. -/
theorem isDecomposition_of_unique {V : Type*} [Fintype V] [DecidableEq V]
    (G : Hypergraph V r) (D : Finset (Block V q))
    (hsub : ∀ Q ∈ D, cliqueEdges r Q ⊆ G)
    (hunique : ∀ e ∈ G, ∃! Q, Q ∈ D ∧ e.val ⊆ Q.val) : IsDecomposition G D := by
  apply (isDecomposition_iff G D).mpr
  intro e
  by_cases he : e ∈ G
  · rw [if_pos he]
    apply card_eq_one_iff_existsUnique.mpr
    simpa only [mem_filter] using hunique e he
  · rw [if_neg he, card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro Q hQ
    obtain ⟨hQD, heQ⟩ := mem_filter.mp hQ
    exact he (hsub Q hQD ((mem_cliqueEdges e Q).mpr heQ))

/-- Two cliques whose vertex sets intersect in one `r`-set share exactly
the corresponding single edge. -/
theorem cliqueEdges_inter_eq_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Block V q) (e : Block V r) (h : P.val ∩ Q.val = e.val) :
    cliqueEdges r P ∩ cliqueEdges r Q = {e} := by
  ext f
  simp only [mem_inter, mem_cliqueEdges, mem_singleton]
  constructor
  · rintro ⟨hfP, hfQ⟩
    apply Subtype.ext
    apply eq_of_subset_of_card_le _ (by rw [e.property, f.property])
    rw [← h]
    exact subset_inter hfP hfQ
  · rintro rfl
    rw [← h]
    exact ⟨inter_subset_left, inter_subset_right⟩

end Arxiv2411_18291
