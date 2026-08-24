/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

namespace Erdos867

def ConsecutiveSumFree (S : Finset ℕ) : Prop :=
  ∀ (start len : ℕ), 2 ≤ len → start + len ≤ S.card →
    (((S.sort (· ≤ ·)).drop start).take len).sum ∉ S

theorem construction_19_36 :
    ∃ C : ℕ, ∀ n : ℕ, 144 ≤ n → ∃ S : Finset ℕ,
    S ⊆ Icc 1 n ∧ ConsecutiveSumFree S ∧ 36 * S.card + C ≥ 19 * n := by
  sorry

theorem not_erdos_867 :
    ¬∃ C : ℕ, ∀ n : ℕ, ∀ S : Finset ℕ, S ⊆ Icc 1 n → ConsecutiveSumFree S → 2 * S.card ≤ n + C := by
  sorry

end Erdos867
