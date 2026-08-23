import ErdosProblems.Erdos1105.SeparatedCounting

namespace Erdos1105

open SimpleGraph Finset

theorem two_le_components_of_not_preconnected {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hnot : ¬G.Preconnected) : 2 ≤ Nat.card G.ConnectedComponent := by
  classical
  have hex : ∃ a b, ¬G.Reachable a b := by simpa only [Preconnected, not_forall] using hnot
  obtain ⟨a, b, hab⟩ := hex
  have hne : G.connectedComponentMk a ≠ G.connectedComponentMk b :=
    fun h ↦ hab (ConnectedComponent.exact h)
  have h := ({G.connectedComponentMk a, G.connectedComponentMk b} :
    Finset G.ConnectedComponent).card_le_univ
  rw [card_pair hne] at h
  simpa only [Nat.card_eq_fintype_card] using h

theorem component_order_lt_of_not_preconnected {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hnot : ¬G.Preconnected) (D : G.ConnectedComponent) :
    (componentVertices G D).card < Fintype.card V := by
  classical
  have hne : componentVertices G D ≠ univ := by
    intro h
    apply hnot
    intro a b
    exact (graphComponent_supp G D).reachable (by simp [h]) (by simp [h])
  have h := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, hne⟩)
  simpa only [card_univ] using h

theorem component_edges_le_connected_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : G.ConnectedComponent)
    {j : ℕ} (hj : 3 ≤ j) (hfree : ¬pathGraph j ⊑ componentGraph G D) :
    (E767EGApi.edgesInside G (componentVertices G D)).card ≤
      connectedPathCount (componentVertices G D).card j := by
  classical
  rw [E767EGApi.card_edgesInside]
  have h := connected_path_count_bound (G.induce (componentVertices G D : Set V)) hj
    (componentGraph_connected G D).preconnected hfree
  have hc : Fintype.card (componentVertices G D : Set V) = (componentVertices G D).card :=
    Fintype.card_of_finset' _ (fun _ ↦ Iff.rfl)
  simpa only [componentGraph, hc] using h

/-- The component-counting lemma applied to the bridge decomposition.
One component has a longer path threshold; all others have the shorter
threshold forced by the fresh joining edges. -/
theorem SeparatedRepresentative.middle_component_bound {V C : Type*}
    [Fintype V] [DecidableEq V] {G R H : SimpleGraph V} {c : Sym2 V → C}
    (hsep : SeparatedRepresentative G c R H) (hnot : ¬R.Preconnected)
    (D : H.ConnectedComponent) {k₁ k₂ : ℕ} (hk₂ : 3 ≤ k₂) (hkk : k₂ ≤ k₁)
    (hn₀ : k₁ - 1 ≤ (componentVertices H D).card)
    (hn : k₁ + k₂ - 1 ≤ Fintype.card V)
    (hprimary : ¬pathGraph k₁ ⊑ componentGraph H D)
    (hsecondary : ∀ E : H.ConnectedComponent, E ≠ D → ¬pathGraph k₂ ⊑ componentGraph H E) :
    Nat.card R.edgeSet ≤ pathFormula (Fintype.card V) (k₁ + k₂ - 1) := by
  classical
  let U := (univ : Finset H.ConnectedComponent).erase D
  let n₀ := (componentVertices H D).card
  have hnotH : ¬H.Preconnected := fun h ↦ hnot (h.mono hsep.le)
  have hn₀lt := component_order_lt_of_not_preconnected H hnotH D
  have hp := component_edges_le_connected_count H D (by omega) hprimary
  have hs : (∑ E ∈ U, (E767EGApi.edgesInside H (componentVertices H E)).card) ≤
      ∑ E ∈ U, cappedEdgeBound (componentVertices H E).card (k₂ - 2) := by
    apply sum_le_sum
    intro E hE
    exact component_edges_le_capped H E (by omega) (hsecondary E (mem_erase.mp hE).1)
  have hcap := cappedEdgeBound_sum U (fun E ↦ (componentVertices H E).card)
    (show 0 < k₂ - 2 by omega) (fun E _ ↦ (graphComponent_supp H E).nonempty.card_pos)
  have hV := sum_component_orders H
  have hE := sum_component_edgesInside H
  have hVsplit := sum_erase_add (univ : Finset H.ConnectedComponent)
    (fun E ↦ (componentVertices H E).card) (mem_univ D)
  have hEsplit := sum_erase_add (univ : Finset H.ConnectedComponent)
    (fun E ↦ (E767EGApi.edgesInside H (componentVertices H E)).card) (mem_univ D)
  have hCsplit := card_erase_add_one (mem_univ D)
  have hb := bridge_deletion_budget R H hsep.le hsep.removed_bridge
  have hcR := two_le_components_of_not_preconnected R hnot
  have heq : Nat.card H.edgeSet = H.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, edgeFinset_card]
  have hcc : Nat.card H.ConnectedComponent = Fintype.card H.ConnectedComponent :=
    Nat.card_eq_fintype_card
  have hnrest : Fintype.card V - n₀ = ∑ E ∈ U, (componentVertices H E).card := by
    dsimp only [U, n₀]
    omega
  have hnum := connected_count_add_capped_le_formula hk₂ hkk hn₀ hn₀lt hn
  change connectedPathCount n₀ k₁ + cappedEdgeBound (Fintype.card V - n₀) (k₂ - 2) ≤ _ at hnum
  rw [hnrest] at hnum
  simp only [card_univ] at hCsplit
  dsimp only [U, n₀] at *
  omega

end Erdos1105

#print axioms Erdos1105.SeparatedRepresentative.middle_component_bound
