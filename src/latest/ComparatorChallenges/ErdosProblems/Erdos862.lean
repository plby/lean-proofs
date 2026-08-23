/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos862

set_option maxHeartbeats 1000000
open scoped BigOperators

noncomputable section

open Real Filter Asymptotics

def Sidon {α : Type} [AddCommMonoid α] (S : Set α) : Prop :=
  ∀ a b c d, a ∈ S → b ∈ S → c ∈ S → d ∈ S → a + b = c + d → ({a, b} : Set α) = {c, d}
section ErdosTuran

end ErdosTuran

section BoseChowla

variable {Fq Fqh : Type*} [Field Fq] [Fintype Fq]

variable [Field Fqh] [Fintype Fqh]

variable [Algebra Fq Fqh]

end BoseChowla

section Construction

end Construction

def MaximalSidonSubset (U : Finset ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ U ∧ Sidon (S : Set ℕ) ∧ ∀ S' : Finset ℕ, S' ⊆ U → Sidon (S' : Set ℕ) → S ⊆ S' → S = S'

open scoped Classical in
noncomputable def A1 (N : ℕ) : ℕ :=
  ((Finset.range N).powerset.filter (fun S => MaximalSidonSubset (Finset.range N) S)).card
open scoped Classical in
noncomputable def eta : ℝ := 1 / 2 * Real.log (5 / 4)
end

end Erdos862


open scoped BigOperators
open Real Filter Asymptotics

namespace Erdos862

open scoped Classical in
theorem erdos_862 :
    ∀ c < eta, ∀ᶠ N : ℕ in Filter.atTop, Real.log (A1 N : ℝ) / Real.sqrt N ≥ c := by
  sorry

end Erdos862
