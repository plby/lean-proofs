/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1006

def HasTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c a

def HasFourCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c d,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

def GirthGreaterThanFour {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬HasTriangle G ∧ ¬HasFourCycle G

abbrev Digraph (V : Type*) := V → V → Prop

def ExactlyOne (p q : Prop) : Prop :=
  (p ∧ ¬q) ∨ (q ∧ ¬p)

def IsOrientation {V : Type*} (G : SimpleGraph V) (D : Digraph V) : Prop :=
  (∀ ⦃u v⦄, D u v → G.Adj u v) ∧
    ∀ ⦃u v⦄, G.Adj u v → ExactlyOne (D u v) (D v u)

def DirectedAcyclic {V : Type*} (D : Digraph V) : Prop :=
  ∀ v, ¬ Relation.TransGen D v v

def eraseArc {V : Type*} (D : Digraph V) (a b : V) : Digraph V :=
  fun x y ↦ D x y ∧ ¬(x = a ∧ y = b)

def reverseArc {V : Type*} (D : Digraph V) (a b : V) : Digraph V :=
  fun x y ↦ eraseArc D a b x y ∨ (x = b ∧ y = a)

def GoodOrientation {V : Type*} (G : SimpleGraph V) (D : Digraph V) : Prop :=
  IsOrientation G D ∧ DirectedAcyclic D ∧
    ∀ ⦃a b⦄, D a b → DirectedAcyclic (reverseArc D a b)

def HasGoodOrientation {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ D : Digraph V, GoodOrientation G D

theorem not_erdos_1006 :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      GirthGreaterThanFour G ∧ ¬HasGoodOrientation G := by
  sorry

end Erdos1006
