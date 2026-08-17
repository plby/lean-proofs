import ErdosProblems.Erdos223.SphericalEuler.PlaneDrawing

open scoped SimpleGraph

namespace SimpleGraph

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def forgetSide : V ⊕ V → V
  | .inl v => v
  | .inr v => v

def bipartiteDoubleCoverNeighborEquiv (v : V ⊕ V) :
    G.bipartiteDoubleCover.neighborSet v ≃ G.neighborSet (forgetSide v) :=
  match v with
  | .inl x =>
      { toFun := fun w => match w with
          | ⟨.inl y, hy⟩ => False.elim (by simp at hy)
          | ⟨.inr y, hy⟩ => ⟨y, by
              change G.Adj x y at hy ⊢
              exact hy⟩
        invFun := fun y => ⟨.inr y.1, by
          have hy := y.2
          change G.Adj x y.1 at hy ⊢
          exact hy⟩
        left_inv := fun w => by
          rcases w with ⟨y, hy⟩
          cases y with
          | inl y => simp at hy
          | inr y => rfl
        right_inv := by rintro ⟨y, hy⟩; rfl }
  | .inr x =>
      { toFun := fun w => match w with
          | ⟨.inl y, hy⟩ => ⟨y, by
              change G.Adj x y at hy ⊢
              exact hy⟩
          | ⟨.inr y, hy⟩ => False.elim (by simp at hy)
        invFun := fun y => ⟨.inl y.1, by
          have hy := y.2
          change G.Adj x y.1 at hy ⊢
          exact hy⟩
        left_inv := fun w => by
          rcases w with ⟨y, hy⟩
          cases y with
          | inl y => rfl
          | inr y => simp at hy
        right_inv := by rintro ⟨y, hy⟩; rfl }

lemma degree_bipartiteDoubleCover (v : V ⊕ V) :
    G.bipartiteDoubleCover.degree v = G.degree (forgetSide v) := by
  rw [← G.bipartiteDoubleCover.card_neighborSet_eq_degree,
    ← G.card_neighborSet_eq_degree]
  exact Fintype.card_congr (G.bipartiteDoubleCoverNeighborEquiv v)

lemma minDegree_bipartiteDoubleCover (hmin : ∀ v, 2 ≤ G.degree v) :
    ∀ w, 2 ≤ G.bipartiteDoubleCover.degree w := by
  intro w
  rw [G.degree_bipartiteDoubleCover w]
  exact hmin (forgetSide w)

end SimpleGraph
