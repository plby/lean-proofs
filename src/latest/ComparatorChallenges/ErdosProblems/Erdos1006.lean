/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

noncomputable section


namespace Erdos1006

open scoped Classical in
def HasTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c a

end Erdos1006

namespace Erdos1006

open scoped Classical in
def HasFourCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c d,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

end Erdos1006

namespace Erdos1006

open scoped Classical in
def GirthGreaterThanFour {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬HasTriangle G ∧ ¬HasFourCycle G

end Erdos1006

namespace Erdos1006

open scoped Classical in
abbrev Digraph (V : Type*) := V → V → Prop

end Erdos1006

namespace Erdos1006

open scoped Classical in
def ExactlyOne (p q : Prop) : Prop :=
  (p ∧ ¬q) ∨ (q ∧ ¬p)

end Erdos1006

namespace Erdos1006

open scoped Classical in
def IsOrientation {V : Type*} (G : SimpleGraph V) (D : Digraph V) : Prop :=
  (∀ ⦃u v⦄, D u v → G.Adj u v) ∧
    ∀ ⦃u v⦄, G.Adj u v → ExactlyOne (D u v) (D v u)

end Erdos1006

namespace Erdos1006

open scoped Classical in
def DirectedAcyclic {V : Type*} (D : Digraph V) : Prop :=
  ∀ v, ¬ Relation.TransGen D v v

end Erdos1006

namespace Erdos1006

open scoped Classical in
def eraseArc {V : Type*} (D : Digraph V) (a b : V) : Digraph V :=
  fun x y ↦ D x y ∧ ¬(x = a ∧ y = b)

end Erdos1006

namespace Erdos1006

open scoped Classical in
def reverseArc {V : Type*} (D : Digraph V) (a b : V) : Digraph V :=
  fun x y ↦ eraseArc D a b x y ∨ (x = b ∧ y = a)

end Erdos1006

namespace Erdos1006

open scoped Classical in
def GoodOrientation {V : Type*} (G : SimpleGraph V) (D : Digraph V) : Prop :=
  IsOrientation G D ∧ DirectedAcyclic D ∧
    ∀ ⦃a b⦄, D a b → DirectedAcyclic (reverseArc D a b)

end Erdos1006

namespace Erdos1006

open scoped Classical in
def HasGoodOrientation {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ D : Digraph V, GoodOrientation G D

end Erdos1006

namespace Erdos1006

open scoped Classical in
theorem erdos1006 :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      GirthGreaterThanFour G ∧ ¬HasGoodOrientation G := by
  sorry

end Erdos1006

end
