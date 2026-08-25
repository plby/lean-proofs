import Wikipedia.SchoenfliesTheorem.FaceCyclesLand

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G B : Graph α β} {u v a b : α} {e : β} {D : List β}

theorem IsPath.ncard_walkVertices (h : G.IsPath u D v) :
    (G.walkVertices u D).ncard = D.length + 1 := by
  induction h with
  | nil => simp
  | @cons u w v e D he hD hfresh ih =>
      rw [walkVertices_cons he]
      rw [Set.ncard_insert_of_notMem hfresh hD.isWalk.finite_walkVertices]
      simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem IsPath.ncard_edgeSet_pathGraphOf (h : G.IsPath u D v) :
    E(G.pathGraphOf u D).ncard = D.length := by
  classical
  rw [pathGraphOf_edgeSet h.isWalk]
  rw [Set.ncard_eq_toFinset_card _ D.finite_toSet]
  change (show Multiset β from ⟦D⟧).finite_toSet.toFinset.card = D.length
  rw [Multiset.finite_toSet_toFinset]
  exact Multiset.toFinset_card_of_nodup h.nodup

theorem IsCycleThrough.ncard_vertexSet_cycleGraph
    (h : G.IsCycleThrough e u v D) :
    V(G.cycleGraph u e D).ncard = (e :: D).length := by
  rw [h.cycleGraph_vertexSet, h.isPath.ncard_walkVertices]
  simp

theorem IsCycleThrough.ncard_edgeSet_cycleGraph
    (h : G.IsCycleThrough e u v D) :
    E(G.cycleGraph u e D).ncard = (e :: D).length := by
  classical
  rw [h.cycleGraph_edgeSet]
  have hn : (D ++ [e]).Nodup :=
    List.nodup_append.2 ⟨h.isPath.nodup, by simp, by
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      apply h.notMem
      exact (hab.trans hb) ▸ ha⟩
  rw [Set.ncard_eq_toFinset_card _ (D ++ [e]).finite_toSet]
  change (show Multiset β from ⟦D ++ [e]⟧).finite_toSet.toFinset.card = (e :: D).length
  rw [Multiset.finite_toSet_toFinset,
    Multiset.toFinset_card_of_nodup (show (show Multiset β from ⟦D ++ [e]⟧).Nodup from hn)]
  simp

/-- A relative ear of length `l` contributes its `l-1` internal vertices to the current
subgraph. -/
theorem IsPath.ncard_vertexSet_union_pathGraphOf [B.Finite]
    (h : G.IsPath a D b) (hab : a ≠ b) (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) :
    V(B.union (G.pathGraphOf a D)).ncard = V(B).ncard + (D.length - 1) := by
  have hinter : V(B) ∩ G.walkVertices a D = {a, b} := by
    ext x
    constructor
    · rintro ⟨hxB, hxW⟩
      by_contra hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
      exact hint x hxW hx.1 hx.2 hxB
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨ha, mem_walkVertices_self⟩
      · exact ⟨hb, h.target_mem_walkVertices⟩
  have hlen : 1 ≤ D.length := Nat.one_le_iff_ne_zero.mpr fun hzero =>
    h.ne_nil hab (List.length_eq_zero_iff.mp hzero)
  have hunion := Set.ncard_union_add_ncard_inter (V(B)) (G.walkVertices a D)
    (finite_vertexSet B) h.isWalk.finite_walkVertices
  rw [vertexSet_union_pathGraphOf]
  rw [hinter, Set.ncard_pair hab, h.ncard_walkVertices] at hunion
  omega

/-- Every edge of a relative ear is new, so the enlarged graph has exactly `length` more
edges. -/
theorem IsPath.ncard_edgeSet_union_pathGraphOf [B.Finite]
    (h : G.IsPath a D b) (hnew : ∀ g ∈ D, g ∉ E(B)) :
    E(B.union (G.pathGraphOf a D)).ncard = E(B).ncard + D.length := by
  have hdis : Disjoint (E(B)) {g | g ∈ D} := by
    rw [Set.disjoint_left]
    intro g hgB hgD
    exact hnew g hgD hgB
  have hDcard := h.ncard_edgeSet_pathGraphOf
  rw [pathGraphOf_edgeSet h.isWalk] at hDcard
  rw [edgeSet_union_pathGraphOf h.isWalk,
    Set.ncard_union_eq hdis (finite_edgeSet B) D.finite_toSet, hDcard]

#print axioms Graph.IsPath.ncard_walkVertices
#print axioms Graph.IsPath.ncard_edgeSet_pathGraphOf
#print axioms Graph.IsCycleThrough.ncard_vertexSet_cycleGraph
#print axioms Graph.IsCycleThrough.ncard_edgeSet_cycleGraph
#print axioms Graph.IsPath.ncard_vertexSet_union_pathGraphOf
#print axioms Graph.IsPath.ncard_edgeSet_union_pathGraphOf

end Graph
