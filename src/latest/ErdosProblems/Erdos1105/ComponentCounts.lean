import ErdosProblems.Erdos1105.RepresentativeComponents

namespace Erdos1105

open SimpleGraph Finset

def componentGraph {V : Type*} [Fintype V] (G : SimpleGraph V) (D : G.ConnectedComponent) :=
  G.induce (componentVertices G D : Set V)

theorem component_vertices_disjoint {V : Type*} [Fintype V] (G : SimpleGraph V)
    {D E : G.ConnectedComponent} (hne : D ≠ E) :
    Disjoint (componentVertices G D) (componentVertices G E) := by
  rw [Finset.disjoint_left]
  intro v hvD hvE
  exact hne (ConnectedComponent.eq_of_common_vertex
    ((mem_componentVertices G D v).mp hvD) ((mem_componentVertices G E v).mp hvE))

theorem component_edges_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {D E : G.ConnectedComponent} (hne : D ≠ E) :
    Disjoint (E767EGApi.edgesInside G (componentVertices G D))
      (E767EGApi.edgesInside G (componentVertices G E)) := by
  rw [Finset.disjoint_left]
  intro e heD heE
  have hD := (mem_filter.mp heD).2
  have hE := (mem_filter.mp heE).2
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr e.toFinset_ne_empty
  exact Finset.disjoint_left.mp (component_vertices_disjoint G hne) (hD hv) (hE hv)

theorem sum_component_orders {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ D : G.ConnectedComponent, (componentVertices G D).card = Fintype.card V := by
  classical
  have hdisj : (↑(univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent).PairwiseDisjoint
      (componentVertices G) :=
    fun _ _ _ _ hne ↦ component_vertices_disjoint G hne
  have hunion : univ.biUnion (componentVertices G) = (univ : Finset V) := by
    ext v
    simp only [mem_biUnion, mem_univ, true_and, iff_true]
    exact ⟨G.connectedComponentMk v, by simp⟩
  rw [← card_biUnion hdisj, hunion, card_univ]

theorem sum_component_edgesInside {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ D : G.ConnectedComponent, (E767EGApi.edgesInside G (componentVertices G D)).card =
      G.edgeFinset.card := by
  classical
  have hdisj : (↑(univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent).PairwiseDisjoint
      (fun D ↦ E767EGApi.edgesInside G (componentVertices G D)) :=
    fun _ _ _ _ hne ↦ component_edges_disjoint G hne
  have hunion : univ.biUnion (fun D ↦ E767EGApi.edgesInside G (componentVertices G D)) =
      G.edgeFinset := by
    ext e
    constructor
    · intro he
      obtain ⟨D, _, hD⟩ := mem_biUnion.mp he
      exact (mem_filter.mp hD).1
    · intro he
      induction e using Sym2.inductionOn with
      | _ a b =>
        have hab : G.Adj a b := mem_edgeFinset.mp he
        refine mem_biUnion.mpr ⟨G.connectedComponentMk a, mem_univ _, mem_filter.mpr ⟨he, ?_⟩⟩
        intro v hv
        have hv : v = a ∨ v = b := by simpa using hv
        rcases hv with h | h
        · subst v
          simp
        · subst v
          apply (mem_componentVertices G _ b).mpr
          exact ConnectedComponent.sound hab.reachable.symm
  rw [← card_biUnion hdisj, hunion]

theorem componentGraph_connected {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : G.ConnectedComponent) : (componentGraph G D).Connected := by
  refine { preconnected := (graphComponent_supp G D).connected, nonempty := ?_ }
  obtain ⟨v, hv⟩ := (graphComponent_supp G D).nonempty
  exact ⟨v, hv⟩

end Erdos1105

#print axioms Erdos1105.sum_component_edgesInside
