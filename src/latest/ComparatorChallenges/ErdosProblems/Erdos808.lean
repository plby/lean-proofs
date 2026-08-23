/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Classical Filter
open scoped BigOperators Real

noncomputable section


namespace Erdos808

open scoped Classical in
def edgeValues {V R : Type*} [Fintype V] [DecidableEq R]
    (op : V → V → R) (hop : ∀ u v, op u v = op v u)
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset R :=
  G.edgeFinset.image (Sym2.lift ⟨op, hop⟩)

end Erdos808

namespace Erdos808

open scoped Classical in
def edgeSums {V R : Type*} [Fintype V] [DecidableEq R] [AddCommMagma R]
    (a : V → R) (G : SimpleGraph V) [DecidableRel G.Adj] : Finset R :=
  edgeValues (fun u v ↦ a u + a v) (fun u v ↦ add_comm (a u) (a v)) G

end Erdos808

namespace Erdos808

open scoped Classical in
def edgeProducts {V R : Type*} [Fintype V] [DecidableEq R] [CommMagma R]
    (a : V → R) (G : SimpleGraph V) [DecidableRel G.Adj] : Finset R :=
  edgeValues (fun u v ↦ a u * a v) (fun u v ↦ mul_comm (a u) (a v)) G

end Erdos808

namespace Erdos808

open scoped Classical in
def StrongErdos808 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (a : V ↪ ℕ)
      (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
      (Fintype.card V : ℝ) ^ (1 + c) ≤ (G.edgeFinset.card : ℝ) →
      (Fintype.card V : ℝ) ^ (1 + c - ε) ≤
        max ((edgeSums a G).card : ℝ) ((edgeProducts a G).card : ℝ)

/-! ## The complementary Alon--Ruzsa--Solymosi lower bound -/

end Erdos808

namespace Erdos808

open scoped Classical in
theorem erdos_808 : ¬ StrongErdos808 := by
  sorry

end Erdos808

end
