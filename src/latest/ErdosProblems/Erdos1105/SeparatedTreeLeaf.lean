import ErdosProblems.Erdos1105.SeparatedLongestPath

namespace Erdos1105

open SimpleGraph

theorem path_two_contained_of_adj {V : Type*} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) : pathGraph 2 ⊑ G := by
  simpa using (Walk.IsPath.of_adj hab).isContained_pathGraph

theorem SeparatedRepresentative.no_remaining_edge_outside {V C : Type*}
    [Fintype V] {G R H : SimpleGraph V} {c : Sym2 V → C}
    (hsep : SeparatedRepresentative G c R H) {b x y : V}
    (hsmall : ∀ E : H.ConnectedComponent, E ≠ H.connectedComponentMk b →
      ¬pathGraph 2 ⊑ componentGraph H E)
    (hxb : ¬R.Reachable x b) : ¬H.Adj x y := by
  classical
  intro hxy
  let E := H.connectedComponentMk x
  have hne : E ≠ H.connectedComponentMk b :=
    fun h ↦ hxb ((ConnectedComponent.exact h).mono hsep.le)
  have hx : x ∈ componentVertices H E := by simp [E]
  have hy : y ∈ componentVertices H E :=
    (graphComponent_supp H E).closed x hx y hxy
  exact hsmall E hne (path_two_contained_of_adj
    (show (componentGraph H E).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy))

/-- Away from the long remaining path, every original component is a
tree, so it has an isolated vertex or a leaf. -/
theorem SeparatedRepresentative.exists_outside_leaf {V C : Type*}
    [Fintype V] [DecidableEq V] {G R H : SimpleGraph V} {c : Sym2 V → C}
    (hsep : SeparatedRepresentative G c R H) (b : V) (hnot : ¬R.Preconnected)
    (hsmall : ∀ E : H.ConnectedComponent, E ≠ H.connectedComponentMk b →
      ¬pathGraph 2 ⊑ componentGraph H E) :
    ∃ x, ¬R.Reachable x b ∧ ∀ y z, R.Adj x y → R.Adj x z → y = z := by
  classical
  have hex : ∃ v, ¬R.Reachable v b := by
    by_contra h
    push Not at h
    exact hnot (fun x y ↦ (h x).trans (h y).symm)
  obtain ⟨v, hv⟩ := hex
  let E := R.connectedComponentMk v
  let S := componentVertices R E
  let A := R.induce (S : Set V)
  have hS := graphComponent_supp R E
  have hmemv : v ∈ S := by simp [S, E]
  have hout : ∀ x ∈ S, ¬R.Reachable x b := by
    intro x hx hxb
    exact hv ((hS.reachable hmemv hx).trans hxb)
  have hacyclic : A.IsAcyclic := by
    apply isAcyclic_iff_forall_isBridge.mpr
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy : R.Adj x.val y.val := he
      have hgone : s(x.val, y.val) ∉ H.edgeSet :=
        hsep.no_remaining_edge_outside hsmall (hout x.val x.property)
      exact isBridge_induce_of_isBridge R (S : Set V) s(x, y)
        (hsep.removed_bridge s(x.val, y.val) hxy hgone)
  have hconn : A.Connected := componentGraph_connected R E
  have htree : A.IsTree := ⟨hconn, hacyclic⟩
  have hleaf : ∃ x : (S : Set V), ∀ y z, A.Adj x y → A.Adj x z → y = z := by
    cases subsingleton_or_nontrivial (S : Set V) with
    | inl hsub =>
      exact ⟨⟨v, hmemv⟩, fun _ _ _ _ ↦ Subsingleton.elim _ _⟩
    | inr hnon =>
      obtain ⟨x, hx⟩ := htree.exists_vert_degree_one_of_nontrivial
      obtain ⟨y, _, hy⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
      exact ⟨x, fun z w hz hw ↦ (hy z hz).trans (hy w hw).symm⟩
  obtain ⟨x, hx⟩ := hleaf
  refine ⟨x.val, hout x.val x.property, ?_⟩
  intro y z hxy hxz
  have hy := hS.closed x.val x.property y hxy
  have hz := hS.closed x.val x.property z hxz
  exact congrArg Subtype.val (hx ⟨y, hy⟩ ⟨z, hz⟩ hxy hxz)

end Erdos1105

#print axioms Erdos1105.SeparatedRepresentative.exists_outside_leaf
