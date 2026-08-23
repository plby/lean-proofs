/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos26


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

open Filter

open scoped Classical in
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Filter.Tendsto (fun (b : β) => partialDensity S A b) Filter.atTop (𝓝 α)

open scoped Classical in
def IsThick {ι : Type*} (A : ι → ℕ) : Prop := ¬Summable (fun i ↦ (1 : ℝ) / A i)

open scoped Classical in
def MultiplesOf {ι : Type*} (A : ι → ℕ) : Set ℕ := Set.range fun (n, i) ↦ n * A i

open scoped Classical in
def IsBehrend {ι : Type*} (A : ι → ℕ) : Prop := HasDensity (MultiplesOf A) 1
end Erdos26



open scoped Topology
open Filter

namespace Erdos26.erdos_26.variants

open scoped Classical in
theorem rusza : ∃ A : ℕ → ℕ,
    StrictMono A ∧ ¬IsThick A ∧ ∀ k, ¬IsBehrend (A · + k) := by
  sorry

end Erdos26.erdos_26.variants
