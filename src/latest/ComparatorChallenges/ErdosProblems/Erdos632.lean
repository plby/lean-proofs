import Mathlib

universe u v

variable {V : Type u} {Color : Type v}

noncomputable section


namespace Erdos632

open scoped Classical in
def IsSetColoring (G : SimpleGraph V) (phi : V → Finset Color) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → Disjoint (phi u) (phi v)

end Erdos632

namespace Erdos632

open scoped Classical in
def IsLMulticoloring (G : SimpleGraph V) (L phi : V → Finset Color) (b : ℕ) : Prop :=
  IsSetColoring G phi ∧ ∀ v, phi v ⊆ L v ∧ (phi v).card = b

end Erdos632

namespace Erdos632

open scoped Classical in
def IsABChoosable (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ (Color : Type v) [DecidableEq Color] (L : V → Finset Color),
    (∀ v, (L v).card = a) → ∃ phi, IsLMulticoloring G L phi b

end Erdos632

namespace Erdos632

open scoped Classical in
def Erdos632Conjecture : Prop :=
  ∀ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (a b m : ℕ),
    1 ≤ b → b ≤ a → 1 ≤ m →
      IsABChoosable.{0, 0} G a b →
        IsABChoosable.{0, 0} G (a * m) (b * m)

end Erdos632

namespace Erdos632

open scoped Classical in
theorem erdos_632 : ¬ Erdos632Conjecture := by
  sorry

end Erdos632

end
