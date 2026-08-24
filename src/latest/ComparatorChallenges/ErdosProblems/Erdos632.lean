/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

universe u v

variable {V : Type u} {Color : Type v}

namespace Erdos632

def IsSetColoring (G : SimpleGraph V) (phi : V → Finset Color) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → Disjoint (phi u) (phi v)

def IsLMulticoloring (G : SimpleGraph V) (L phi : V → Finset Color) (b : ℕ) : Prop :=
  IsSetColoring G phi ∧ ∀ v, phi v ⊆ L v ∧ (phi v).card = b

def IsABChoosable (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ (Color : Type v) [DecidableEq Color] (L : V → Finset Color),
    (∀ v, (L v).card = a) → ∃ phi, IsLMulticoloring G L phi b

theorem not_erdos_632 :
    ¬ (∀ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (a b m : ℕ),
      1 ≤ b → b ≤ a → 1 ≤ m →
        IsABChoosable.{0, 0} G a b →
          IsABChoosable.{0, 0} G (a * m) (b * m)) := by
  sorry

end Erdos632
