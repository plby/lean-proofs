/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos867

open Finset

set_option linter.style.setOption false
set_option linter.flexible false

def ConsecutiveSumFree (S : Finset ℕ) : Prop :=
  ∀ (start len : ℕ), 2 ≤ len → start + len ≤ S.card →
    (((S.sort (· ≤ ·)).drop start).take len).sum ∉ S
end Erdos867

open Erdos867


open Finset

namespace Erdos867

open scoped Classical in
theorem construction_19_36 :
    ∃ C : ℕ, ∀ n : ℕ, 144 ≤ n → ∃ S : Finset ℕ,
    S ⊆ Icc 1 n ∧ ConsecutiveSumFree S ∧ 36 * S.card + C ≥ 19 * n := by
  sorry


open scoped Classical in
theorem csf_exceeds_half_plus_constant :
    ¬∃ C : ℕ, ∀ n : ℕ, ∀ S : Finset ℕ, S ⊆ Icc 1 n → ConsecutiveSumFree S → 2 * S.card ≤ n + C := by
  sorry

end Erdos867
