import ErdosProblems.Erdos1105.MaxComponentPalette

namespace Erdos1105

open SimpleGraph Finset

theorem MaxRepresentativeComponent.cross_deleted_disconnect {V C : Type*}
    [Fintype V] [DecidableEq V] {G R Q : SimpleGraph V} {c : Sym2 V → C} {S : Finset V}
    (hmax : MaxRepresentativeComponent G c R S) (hQ : ColorRepresentative G c Q)
    (hS : GraphComponent Q S) {a b : V} (ha : a ∈ S) (hb : b ∉ S) (hab : G.Adj a b)
    (e : Q.edgeSet) (hcol : c e.val = c s(a, b)) :
    ¬∀ x ∈ S, (Q.deleteEdges {e.val}).Reachable a x := by
  classical
  intro hdel
  let d : G.edgeSet := ⟨s(a, b), hab⟩
  let d' : (⊤ : SimpleGraph V).edgeSet := ⟨s(a, b), edgeSet_mono le_top hab⟩
  let K := swapRepresentative Q e.val d.val
  have hK := hQ.swap e d hcol.symm
  have hreach : ∀ x ∈ insert b S, K.Reachable a x := by
    intro x hx
    rcases mem_insert.mp hx with heq | hx
    · subst x
      exact (show K.Adj a b from
        (mem_swapRepresentative Q e.val d' _).mpr (Or.inr rfl)).reachable
    · exact (hdel x hx).mono (deleteEdges_le_swapRepresentative Q e.val d')
  have hcard := hmax.card_le hK (mem_insert_of_mem ha) hreach
  rw [card_insert_of_notMem hb] at hcard
  omega

theorem MaxRepresentativeComponent.cross_internal {V C : Type*}
    [Fintype V] [DecidableEq V] {G R Q : SimpleGraph V} {c : Sym2 V → C} {S : Finset V}
    (hmax : MaxRepresentativeComponent G c R S) (hQ : ColorRepresentative G c Q)
    (hS : GraphComponent Q S) {a b : V} (ha : a ∈ S) (hb : b ∉ S) (hab : G.Adj a b)
    (e : Q.edgeSet) (hcol : c e.val = c s(a, b)) : e.val.toFinset ⊆ S := by
  classical
  by_contra hout
  apply hmax.cross_deleted_disconnect hQ hS ha hb hab e hcol
  let φ : Q.induce (S : Set V) →g Q.deleteEdges {e.val} :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        apply deleteEdges_adj.mpr
        refine ⟨hxy, ?_⟩
        intro heq
        apply hout
        rw [← heq]
        exact pair_toFinset_subset.mpr ⟨x.property, y.property⟩ }
  intro x hx
  exact (hS.connected ⟨a, ha⟩ ⟨x, hx⟩).map φ

theorem MaxRepresentativeComponent.cross_bridge {V C : Type*}
    [Fintype V] [DecidableEq V] {G R Q : SimpleGraph V} {c : Sym2 V → C} {S : Finset V}
    (hmax : MaxRepresentativeComponent G c R S) (hQ : ColorRepresentative G c Q)
    (hS : GraphComponent Q S) {a b : V} (ha : a ∈ S) (hb : b ∉ S) (hab : G.Adj a b)
    (e : Q.edgeSet) (hcol : c e.val = c s(a, b)) : Q.IsBridge e.val := by
  by_contra hnb
  apply hmax.cross_deleted_disconnect hQ hS ha hb hab e hcol
  exact fun x hx ↦ reachable_delete_of_not_isBridge Q hnb (hS.reachable ha hx)

/-- A bridge remains a bridge in an induced subgraph containing its ends. -/
theorem isBridge_induce_of_isBridge {V : Type*} (G : SimpleGraph V) (S : Set V)
    (e : Sym2 S) (he : G.IsBridge (Sym2.map Subtype.val e)) : (G.induce S).IsBridge e := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    change G.IsBridge s(a.val, b.val) at he
    rw [isBridge_iff] at he ⊢
    intro hreach
    apply he
    let φ : ((G.induce S).deleteEdges {s(a, b)}) →g G.deleteEdges {s(a.val, b.val)} :=
      { toFun := Subtype.val
        map_rel' := by
          intro x y hxy
          rw [deleteEdges_adj, Set.mem_singleton_iff] at hxy ⊢
          refine ⟨hxy.1, fun h ↦ hxy.2 ?_⟩
          exact Sym2.map.injective Subtype.val_injective h }
    exact hreach.map φ

end Erdos1105

#print axioms Erdos1105.MaxRepresentativeComponent.cross_bridge
