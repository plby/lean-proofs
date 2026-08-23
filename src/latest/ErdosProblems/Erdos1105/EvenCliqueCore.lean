import ErdosProblems.Erdos1105.EvenCoreArithmetic
import ErdosProblems.Erdos1105.ConnectedPathStability

namespace Erdos1105

open SimpleGraph Finset

/-- The clique low-core branch has only the pendant endpoint or the
sharp three-clique-join equality case left above the anti-Ramsey bound. -/
theorem even_clique_core_high_cases {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hn : 2 * d + 2 ≤ Fintype.card V) (hconn : G.Preconnected)
    (hfree : ¬pathGraph (2 * d + 2) ⊑ G)
    (hmax : ∀ J : SimpleGraph (Option V), graphCone G ≤ J → NoLongCycle J (2 * d + 3) →
      J = graphCone G)
    (hclique : (graphCone G).IsClique (vertexCore (graphCone G) d : Set (Option V)))
    (hhigh : pathFormula (Fintype.card V) (2 * d + 2) < G.edgeFinset.card) :
    PendantCliqueShape G (2 * d + 2) ∨
      ((vertexCore (graphCone G) d).card = d + 3 ∧
        G.edgeFinset.card = pathExtremalEdges (Fintype.card V) (2 * d + 1) (d - 1)) := by
  classical
  have hG : NoLongCycle (graphCone G) (2 * d + 3) :=
    no_long_cycle_cone_of_path_free G (by omega) hfree
  have hu := graphCone_universal G
  have hconn' := graphCone_delete_preconnected G hconn
  have hne : (vertexCore (graphCone G) d).Nonempty := by
    by_contra h
    have hempty : vertexCore (graphCone G) d = ∅ := not_nonempty_iff_eq_empty.mp h
    have he := edges_le_of_core_empty (graphCone G) d hempty
    rw [graphCone_card_edges G, Fintype.card_option] at he
    exact (not_lt_of_ge (even_empty_core_count_le_formula _ _ _ hd hn he)) hhigh
  let r := (vertexCore (graphCone G) d).card
  have hrlo : d + 2 ≤ r := vertexCore_card_lower (graphCone G) d hne
  have hNone := universal_mem_vertexCore (graphCone G) d hne hu
  have hrhi : r ≤ 2 * d + 1 := by
    have h := cone_clique_card_le (graphCone G) hG (by omega)
      (by simpa only [Fintype.card_option] using Nat.add_le_add_right hn 1)
      hu hconn' hclique (by omega) hNone
    dsimp only [r]
    omega
  have hrlo' : d + 3 ≤ r := by
    by_contra h
    have hr : r = d + 2 := by omega
    have he := edges_le_core_bound (graphCone G) d
    change (graphCone G).edgeFinset.card ≤ r.choose 2 + d * (Fintype.card (Option V) - r) at he
    rw [graphCone_card_edges G, Fintype.card_option, hr] at he
    exact (not_lt_of_ge (even_small_core_count_le_formula _ _ _ hd hn he)) hhigh
  have hstable := saturated_cone_core_stable (graphCone G) hG (by omega) hu hconn'
    hmax hclique hne (show r ≤ 2 * d + 3 by omega) (show 2 * d + 3 - r ≤ d by omega)
  have he := edges_le_core_bound (graphCone G) (2 * d + 3 - r)
  rw [hstable] at he
  change (graphCone G).edgeFinset.card ≤ r.choose 2 + (2 * d + 3 - r) *
    (Fintype.card (Option V) - r) at he
  rw [graphCone_card_edges G, Fintype.card_option] at he
  have hc := cone_nonempty_count (Fintype.card V) (2 * d + 2) r (by omega) (by omega) hn
  have hE : G.edgeFinset.card ≤ pathExtremalEdges (Fintype.card V) (2 * d + 1) (2 * d + 2 - r) := by
    have hk : 2 * d + 2 - 1 = 2 * d + 1 := by omega
    rw [hk, show 2 * d + 2 + 1 = 2 * d + 3 by omega] at hc
    omega
  by_cases ha1 : 2 * d + 2 - r = 1
  · obtain ⟨S, hS, hScard⟩ := cone_clique_remove_none (graphCone G) hclique hNone
    change G.IsClique (S : Set V) at hS
    have hSk : S.card + 2 = 2 * d + 2 := by dsimp only [r] at *; omega
    obtain ⟨v, hvS, hpend⟩ := large_clique_pendant_structure G hconn hS
      (by omega) (by omega) (by rw [hSk]; exact hfree)
    exact Or.inl ⟨S, by omega, v, hvS, hpend⟩
  · have ha₂ : 2 ≤ 2 * d + 2 - r := by omega
    have haLast : 2 * d + 2 - r = d - 1 := by
      by_contra h
      have haUpper : 2 * d + 2 - r ≤ d - 2 := by omega
      have hb := even_extremal_interior_le_formula (Fintype.card V) d (2 * d + 2 - r) ha₂ haUpper hn
      exact (not_lt_of_ge (hE.trans hb)) hhigh
    rw [haLast] at hE
    have hline := even_path_linear_term (Fintype.card V) d (by omega) (by omega)
    have hlow := le_max_right ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * (Fintype.card V - d + 1) + 2)
    rw [← pathFormula_even] at hlow
    exact Or.inr ⟨by dsimp only [r] at *; omega, by omega⟩

end Erdos1105

#print axioms Erdos1105.even_clique_core_high_cases
