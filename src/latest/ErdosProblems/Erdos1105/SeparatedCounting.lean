import ErdosProblems.Erdos1105.BridgeBudget
import ErdosProblems.Erdos1105.ComponentCounts
import ErdosProblems.Erdos1105.ComponentSumBound

namespace Erdos1105

open SimpleGraph Finset

theorem component_edges_le_capped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : G.ConnectedComponent)
    {j : ℕ} (hj : 2 ≤ j) (hfree : ¬pathGraph j ⊑ componentGraph G D) :
    (E767EGApi.edgesInside G (componentVertices G D)).card ≤
      cappedEdgeBound (componentVertices G D).card (j - 2) := by
  classical
  rw [E767EGApi.card_edgesInside]
  have h := path_free_edges_le_capped (G.induce (componentVertices G D : Set V)) hj hfree
  have hc : Fintype.card (componentVertices G D : Set V) = (componentVertices G D).card :=
    Fintype.card_of_finset' _ (fun _ ↦ Iff.rfl)
  simpa only [componentGraph, hc] using h

lemma capped_path_half_le_formula {n k : ℕ} (hk : 5 ≤ k) (hn : k ≤ n) :
    cappedEdgeBound n ((k - 1) / 2 - 1) ≤ pathFormula n k := by
  have hl : 1 ≤ (k - 1) / 2 := by omega
  rw [cappedEdgeBound_eq_linear (by omega), pathFormula]
  have hsub : n - ((k - 1) / 2 - 1) = n - (k - 1) / 2 + 1 := by omega
  rw [hsub]
  exact (Nat.le_add_right _ _).trans (le_max_right _ _)

/-- If every remaining component has short paths, even the elementary
degeneracy bound already gives the desired anti-Ramsey bound. -/
theorem SeparatedRepresentative.small_components_bound {V C : Type*}
    [Fintype V] [DecidableEq V] {G R H : SimpleGraph V} {c : Sym2 V → C}
    (hsep : SeparatedRepresentative G c R H) {k : ℕ} (hk : 5 ≤ k)
    (hn : k ≤ Fintype.card V)
    (hsmall : ∀ D : H.ConnectedComponent, ¬pathGraph ((k - 1) / 2 + 1) ⊑ componentGraph H D) :
    Nat.card R.edgeSet ≤ pathFormula (Fintype.card V) k := by
  classical
  let l := (k - 1) / 2
  have hl : 2 ≤ l := by dsimp [l]; omega
  have hE : (∑ D : H.ConnectedComponent, (E767EGApi.edgesInside H (componentVertices H D)).card) ≤
      ∑ D : H.ConnectedComponent, cappedEdgeBound (componentVertices H D).card (l - 1) := by
    apply sum_le_sum
    intro D _
    have h := component_edges_le_capped H D (by omega) (hsmall D)
    simpa only [show (k - 1) / 2 + 1 - 2 = l - 1 by dsimp [l]; omega] using h
  have hs := cappedEdgeBound_sum (univ : Finset H.ConnectedComponent)
    (fun D ↦ (componentVertices H D).card) (show 0 < l - 1 by omega)
    (fun D _ ↦ (graphComponent_supp H D).nonempty.card_pos)
  rw [sum_component_orders, card_univ] at hs
  rw [sum_component_edgesInside] at hE
  have hb := bridge_deletion_budget R H hsep.le hsep.removed_bridge
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let := hV
  have hc : 1 ≤ Nat.card R.ConnectedComponent := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  have heq : Nat.card H.edgeSet = H.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, edgeFinset_card]
  have hcc : Nat.card H.ConnectedComponent = Fintype.card H.ConnectedComponent :=
    Nat.card_eq_fintype_card
  have hbound := capped_path_half_le_formula hk hn
  dsimp only [l] at *
  omega

end Erdos1105

#print axioms Erdos1105.SeparatedRepresentative.small_components_bound
