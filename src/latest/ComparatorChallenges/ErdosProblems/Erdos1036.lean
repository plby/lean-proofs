/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace Harmonic.GeneralizeProofs
open Lean Meta Elab Parser.Tactic Elab.Tactic Batteries.Tactic.GeneralizeProofs
end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Batteries.Tactic.GeneralizeProofs
end Harmonic

namespace Erdos1036

set_option linter.style.setOption false
set_option linter.style.cases false
set_option linter.flexible false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise


set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Classical in
def hom_num {V : Type*} (G : SimpleGraph V) : ℕ := max G.cliqueNum G.indepNum
open scoped Classical in
def induced_iso_rel {V : Type*} (G : SimpleGraph V) (s t : Set V) : Prop :=
  Nonempty (G.induce s ≃g G.induce t)
open scoped Classical in
def I_num {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  Fintype.card (Quotient (Setoid.mk (induced_iso_rel G) (by
  constructor;
  · intro x
    use Equiv.refl x
    simp
  · rintro x y ⟨ f, hf ⟩;
    refine ⟨ f.symm, ?_ ⟩;
    grind;
  · rintro x y z ⟨ f, hf ⟩ ⟨ g, hg ⟩;
    exact ⟨ f.trans g, by aesop ⟩)))
end

end Erdos1036



open Lean Meta Elab Parser.Tactic Elab.Tactic Batteries.Tactic.GeneralizeProofs
open Lean Elab Parser.Tactic Elab.Tactic Batteries.Tactic.GeneralizeProofs
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos1036

open scoped Classical in
theorem erdos_1036 (c : ℝ) (hc : c > 0) :
  ∃ (ε : ℝ), ε > 0 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj],
  Fintype.card V = n →
  (hom_num G : ℝ) ≤ c * Real.logb 2 n →
  (I_num G : ℝ) ≥ (2 : ℝ) ^ (ε * n) := by
  sorry

end Erdos1036
