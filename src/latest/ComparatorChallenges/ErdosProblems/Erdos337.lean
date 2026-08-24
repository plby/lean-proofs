/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Set.Card
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open scoped Pointwise

namespace Erdos337

def iterated_sumset (A : Set ℕ) : ℕ → Set ℕ
| 0 => {0}
| (k + 1) => A + iterated_sumset A k

noncomputable def count_in_range (A : Set ℕ) (x : ℝ) : ℕ :=
  (A ∩ Set.Icc 1 ⌊x⌋₊).ncard

def is_basis_of_order (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N₀, Set.Ici N₀ ⊆ iterated_sumset A h

end Erdos337

theorem Erdos337.not_erdos_337 :
    Not (∀ A : Set ℕ,
      (∃ k : ℕ, Erdos337.is_basis_of_order A k) →
      Asymptotics.IsLittleO Filter.atTop
        (fun x => (Erdos337.count_in_range A x : ℝ))
        (fun x => x) →
      Filter.Tendsto
        (fun x =>
          (Erdos337.count_in_range (A + A) x : ℝ) /
          (Erdos337.count_in_range A x : ℝ))
        Filter.atTop
        Filter.atTop) := by
  sorry
