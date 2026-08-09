import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Erdos1067

open Set Ordinal Function Cardinal

def independent_paths {V : Type*} {G : SimpleGraph V} {u v : V} (S : Set (G.Walk u v)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → {x | x ∈ p.support} ∩ {x | x ∈ q.support} ⊆ {u, v}
universe u
def uncountably_chromatic {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ Nonempty (G.Coloring ℕ)
def finite_independent_paths {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  ∀ (S : Set (G.Walk u v)), independent_paths S → S.Finite
open Set Ordinal Function Cardinal

def erdos_1067 : Prop :=
  ∀ {V : Type*} (G : SimpleGraph V),
    (Nonempty (G.Coloring (Set.Iio (Ordinal.omega.{0} 1))) ∧ uncountably_chromatic G) →
      ∃ (S : Set V),
        (Nonempty ((G.induce S).Coloring (Set.Iio (Ordinal.omega.{0} 1))) ∧
            uncountably_chromatic (G.induce S)) ∧
        ∀ u v : S, u ≠ v → ¬ finite_independent_paths (G.induce S) u v
end Erdos1067

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos1067.not_erdos_1067 :
    Not Erdos1067.erdos_1067.{1}
  := by
  sorry
