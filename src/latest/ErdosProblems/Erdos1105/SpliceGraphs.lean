import ErdosProblems.Erdos1105.ReplaceComponent

namespace Erdos1105

open SimpleGraph Finset

def spliceGraphs {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V)
    (A : SimpleGraph (S : Set V)) (B : SimpleGraph (↑(Sᶜ) : Set V)) : SimpleGraph V where
  Adj a b := (∃ ha : a ∈ S, ∃ hb : b ∈ S, A.Adj ⟨a, ha⟩ ⟨b, hb⟩) ∨
    (∃ ha : a ∈ Sᶜ, ∃ hb : b ∈ Sᶜ, B.Adj ⟨a, ha⟩ ⟨b, hb⟩)
  symm := ⟨by
    intro a b h
    rcases h with ⟨ha, hb, h⟩ | ⟨ha, hb, h⟩
    · exact Or.inl ⟨hb, ha, h.symm⟩
    · exact Or.inr ⟨hb, ha, h.symm⟩⟩
  loopless := ⟨by
    intro a h
    rcases h with ⟨ha, _, h⟩ | ⟨ha, _, h⟩
    · exact A.loopless.irrefl ⟨a, ha⟩ h
    · exact B.loopless.irrefl ⟨a, ha⟩ h⟩

lemma spliceGraphs_left_closed {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V)
    (A : SimpleGraph (S : Set V)) (B : SimpleGraph (↑(Sᶜ) : Set V)) :
    ∀ a ∈ S, ∀ b, (spliceGraphs S A B).Adj a b → b ∈ S := by
  intro a ha b hab
  rcases hab with ⟨_, hb, _⟩ | ⟨hna, _, _⟩
  · exact hb
  · exact (mem_compl.mp hna ha).elim

lemma spliceGraphs_right_closed {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V)
    (A : SimpleGraph (S : Set V)) (B : SimpleGraph (↑(Sᶜ) : Set V)) :
    ∀ a ∈ Sᶜ, ∀ b, (spliceGraphs S A B).Adj a b → b ∈ Sᶜ := by
  intro a ha b hab
  rcases hab with ⟨hna, _, _⟩ | ⟨_, hb, _⟩
  · exact (mem_compl.mp ha hna).elim
  · exact hb

@[simp] theorem spliceGraphs_induce_left {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (A : SimpleGraph (S : Set V)) (B : SimpleGraph (↑(Sᶜ) : Set V)) :
    (spliceGraphs S A B).induce (S : Set V) = A := by
  ext a b
  constructor
  · rintro (⟨_, _, h⟩ | ⟨ha, _, _⟩)
    · exact h
    · exact (mem_compl.mp ha a.property).elim
  · intro h
    exact Or.inl ⟨a.property, b.property, h⟩

@[simp] theorem spliceGraphs_induce_right {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (A : SimpleGraph (S : Set V)) (B : SimpleGraph (↑(Sᶜ) : Set V)) :
    (spliceGraphs S A B).induce (↑(Sᶜ) : Set V) = B := by
  ext a b
  constructor
  · rintro (⟨ha, _, _⟩ | ⟨_, _, h⟩)
    · exact (mem_compl.mp a.property ha).elim
    · exact h
  · intro h
    exact Or.inr ⟨a.property, b.property, h⟩

theorem mem_of_reachable_closed {V : Type*} {G : SimpleGraph V} {S : Set V}
    (hclosed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S)
    {a b : V} (ha : a ∈ S) (hab : G.Reachable a b) : b ∈ S := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => exact ha
  | @cons u v w huv p ih => exact ih (hclosed u ha v huv)

theorem reachable_induce_of_closed {V : Type*} {G : SimpleGraph V} {S : Set V}
    (hclosed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S)
    (a b : S) (hab : G.Reachable a.val b.val) : (G.induce S).Reachable a b := by
  classical
  obtain ⟨p⟩ := hab
  have hs : ∀ x ∈ p.support, x ∈ S := by
    intro x hx
    exact mem_of_reachable_closed hclosed a.property ⟨p.takeUntil x hx⟩
  exact ⟨p.induce S hs⟩

theorem spliceGraphs_reachable_left {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (A : SimpleGraph (S : Set V)) (B : SimpleGraph (↑(Sᶜ) : Set V))
    (a b : (S : Set V)) : (spliceGraphs S A B).Reachable a.val b.val ↔ A.Reachable a b := by
  constructor
  · intro h
    have h' := reachable_induce_of_closed (spliceGraphs_left_closed S A B) a b h
    simpa only [spliceGraphs_induce_left] using h'
  · intro h
    exact h.map (show A →g spliceGraphs S A B from
      ⟨Subtype.val, fun {x y} h ↦ Or.inl ⟨x.property, y.property, h⟩⟩)

theorem spliceGraphs_reachable_right {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (A : SimpleGraph (S : Set V)) (B : SimpleGraph (↑(Sᶜ) : Set V))
    (a b : (↑(Sᶜ) : Set V)) : (spliceGraphs S A B).Reachable a.val b.val ↔ B.Reachable a b := by
  constructor
  · intro h
    have h' := reachable_induce_of_closed (spliceGraphs_right_closed S A B) a b h
    simpa only [spliceGraphs_induce_right] using h'
  · intro h
    exact h.map (show B →g spliceGraphs S A B from
      ⟨Subtype.val, fun {x y} h ↦ Or.inr ⟨x.property, y.property, h⟩⟩)

/-- A bridge in a closed induced subgraph is a bridge of the ambient graph. -/
theorem isBridge_of_induce_closed {V : Type*} {G : SimpleGraph V} {S : Set V}
    (hclosed : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S) (e : Sym2 S)
    (he : (G.induce S).IsBridge e) : G.IsBridge (Sym2.map Subtype.val e) := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    change G.IsBridge s(a.val, b.val)
    rw [isBridge_iff] at he ⊢
    intro hab
    have hc : ∀ x ∈ S, ∀ y, (G.deleteEdges {s(a.val, b.val)}).Adj x y → y ∈ S :=
      fun x hx y hxy ↦ hclosed x hx y (deleteEdges_adj.mp hxy).1
    have hreach := reachable_induce_of_closed hc a b hab
    let φ : ((G.deleteEdges {s(a.val, b.val)}).induce S) →g
        (G.induce S).deleteEdges {s(a, b)} :=
      { toFun := id
        map_rel' := by
          intro x y hxy
          have hxy' := deleteEdges_adj.mp
            (show (G.deleteEdges {s(a.val, b.val)}).Adj x.val y.val from hxy)
          apply deleteEdges_adj.mpr
          refine ⟨hxy'.1, fun h ↦ hxy'.2 ?_⟩
          exact congrArg (Sym2.map Subtype.val) h }
    exact he (hreach.map φ)

theorem spliceGraphs_bridge_left {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (A : SimpleGraph (S : Set V)) (B : SimpleGraph (↑(Sᶜ) : Set V))
    (e : Sym2 (S : Set V)) (he : A.IsBridge e) :
    (spliceGraphs S A B).IsBridge (Sym2.map Subtype.val e) := by
  apply isBridge_of_induce_closed (spliceGraphs_left_closed S A B) e
  simpa only [spliceGraphs_induce_left] using he

theorem spliceGraphs_bridge_right {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (A : SimpleGraph (S : Set V)) (B : SimpleGraph (↑(Sᶜ) : Set V))
    (e : Sym2 (↑(Sᶜ) : Set V)) (he : B.IsBridge e) :
    (spliceGraphs S A B).IsBridge (Sym2.map Subtype.val e) := by
  apply isBridge_of_induce_closed (spliceGraphs_right_closed S A B) e
  simpa only [spliceGraphs_induce_right] using he

end Erdos1105

#print axioms Erdos1105.spliceGraphs_bridge_left
