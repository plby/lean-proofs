/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Fintype
open scoped Classical SimpleGraph
open SimpleGraph

noncomputable section


namespace Erdos1031

open scoped Classical in
noncomputable def homNum {V : Type*} (G : SimpleGraph V) : ℕ :=
  max G.cliqueNum G.indepNum

end Erdos1031

namespace Erdos1031

open scoped Classical in
def HasLargeInducedNontrivialRegular {V : Type*} [Fintype V]
    (G : SimpleGraph V) (L : ℝ) : Prop :=
  ∃ (S : Set V) (d : ℕ),
    L ≤ (Fintype.card S : ℝ) ∧
    0 < d ∧ d + 1 < Fintype.card S ∧
    (G.induce S).IsRegularOfDegree d

end Erdos1031

namespace Erdos1031

open scoped Classical in
theorem erdos_1031 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
        Fintype.card V = n →
        (homNum G : ℝ) < 10 * Real.log n →
        HasLargeInducedNontrivialRegular G (c * Real.log n) := by
  sorry

end Erdos1031

end
