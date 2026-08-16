import Mathlib

set_option linter.style.setOption false
set_option aesop.warn.nonterminal false

namespace Erdos31

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 50000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

section

variable {β : Type*} [Preorder β]

variable (S : Set β) (a b : β)

abbrev Set.interIio (S : Set β) (b : β) : Set β :=
  S ∩ Set.Iio b
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  (Set.interIio (S ∩ A) b).ncard / (Set.interIio A b).ncard
open scoped Topology

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Filter.Tendsto (fun (b : β) => partialDensity S A b) Filter.atTop (𝓝 α)
end

end Erdos31

open scoped Pointwise

attribute [local instance] Classical.propDecidable


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped Topology

namespace Erdos31

theorem erdos_31 (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set ℕ, HasDensity B 0 ∧
      ∃ n0 : ℕ, ∀ n ≥ n0, n ∈ A + B := by
  sorry

end Erdos31
