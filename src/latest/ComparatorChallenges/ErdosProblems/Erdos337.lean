/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Set.Card
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option aesop.warn.nonterminal false

namespace Erdos337

open scoped Pointwise


open scoped Classical in
def iterated_sumset (A : Set ℕ) : ℕ → Set ℕ
| 0 => {0}
| (k + 1) => A + iterated_sumset A k

open scoped Classical in
noncomputable def count_in_range (A : Set ℕ) (x : ℝ) : ℕ :=
  (A ∩ Set.Icc 1 ⌊x⌋₊).ncard

open scoped Classical in
def is_basis_of_order (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N₀, Set.Ici N₀ ⊆ iterated_sumset A h
open Filter

open scoped Classical in
def erdos_337 : Prop :=
  ∀ A : Set ℕ,
    (∃ k : ℕ, is_basis_of_order A k) →
    Asymptotics.IsLittleO Filter.atTop
      (fun x => (count_in_range A x : ℝ))
      (fun x => x) →
    Filter.Tendsto
      (fun x =>
        (count_in_range (A + A) x : ℝ) /
        (count_in_range A x : ℝ))
      Filter.atTop
      Filter.atTop
end Erdos337


open scoped Classical in
theorem Erdos337.not_erdos_337 :
    Not Erdos337.erdos_337
  := by
  sorry
