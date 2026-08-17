import Mathlib

open Fintype
open scoped Classical SimpleGraph
open SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos1031

noncomputable def homNum {V : Type*} (G : SimpleGraph V) : ℕ :=
  max G.cliqueNum G.indepNum

end Erdos1031

namespace Erdos1031

def HasLargeInducedNontrivialRegular {V : Type*} [Fintype V]
    (G : SimpleGraph V) (L : ℝ) : Prop :=
  ∃ (S : Set V) (d : ℕ),
    L ≤ (Fintype.card S : ℝ) ∧
    0 < d ∧ d + 1 < Fintype.card S ∧
    (G.induce S).IsRegularOfDegree d

end Erdos1031

namespace Erdos1031

theorem erdos_1031 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
        Fintype.card V = n →
        (homNum G : ℝ) < 10 * Real.log n →
        HasLargeInducedNontrivialRegular G (c * Real.log n) := by
  sorry

end Erdos1031

end
