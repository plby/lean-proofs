/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1067

def independent_paths {V : Type*} {G : SimpleGraph V} {u v : V} (S : Set (G.Walk u v)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → {x | x ∈ p.support} ∩ {x | x ∈ q.support} ⊆ {u, v}
def uncountably_chromatic {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ Nonempty (G.Coloring ℕ)
def finite_independent_paths {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  ∀ (S : Set (G.Walk u v)), independent_paths S → S.Finite

theorem not_erdos_1067 : ¬ (∀ {V : Type 1} (G : SimpleGraph V),
    (Nonempty (G.Coloring (Set.Iio (Ordinal.omega.{0} 1))) ∧ uncountably_chromatic G) →
      ∃ (S : Set V),
        (Nonempty ((G.induce S).Coloring (Set.Iio (Ordinal.omega.{0} 1))) ∧
            uncountably_chromatic (G.induce S)) ∧
        ∀ u v : S, u ≠ v → ¬ finite_independent_paths (G.induce S) u v) := by
  sorry

end Erdos1067
