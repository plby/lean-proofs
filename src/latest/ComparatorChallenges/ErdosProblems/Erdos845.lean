import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos845

set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise


variable {β : Type*} [Preorder β]

variable (S : Set β) (a b : β)

open scoped Classical in
abbrev Set.interIio (S : Set β) (b : β) : Set β :=
  S ∩ Set.Iio b

open scoped Classical in
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  (Set.interIio (S ∩ A) b).ncard / (Set.interIio A b).ncard

open scoped Topology

open scoped Classical in
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Filter.Tendsto (fun (b : β) => partialDensity S A b) Filter.atTop (𝓝 α)

open scoped BigOperators

open Filter

open Filter

open scoped Classical in
theorem erdos_845 : (false) ↔ ∀ᵉ (C : ℝ) (hC : 0 < C),
    let f : ℕ × ℕ → ℕ := fun x ↦ 2 ^ x.1 * 3 ^ x.2
    HasDensity {∑ x ∈ B, f x | (B : Finset (ℕ × ℕ)) (h : B.Nonempty)
      (hB : B.sup f ≤ C * B.inf' h f)} 0 := by
  sorry

open scoped Classical in
theorem van_doorn_everts_asymptotic_inexact :
    let f : ℕ × ℕ → ℕ := fun x ↦ 2 ^ x.1 * 3 ^ x.2
    ∃ C, ∀ n, ∃ (B : Finset (ℕ × ℕ)), ¬ (∃ b ∈ B, ∃ b' ∈ B,
      f b' > C * f b) ∧ n = ∑ x ∈ B, f x := by
  sorry

end Erdos845
