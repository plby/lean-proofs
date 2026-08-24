/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1025

abbrev Pair (α : Type*) := {e : Sym2 α // ¬ e.IsDiag}

namespace Pair

variable {α β : Type*}

def vertices [DecidableEq α] (e : Pair α) : Finset α := e.1.toFinset

end Pair

def AvoidsEndpoints {α : Type*} [DecidableEq α] (f : Pair α → α) : Prop :=
  ∀ e, f e ∉ e.vertices

def Independent {α : Type*} [DecidableEq α] (f : Pair α → α) (X : Finset α) : Prop :=
  ∀ e, e.vertices ⊆ X → f e ∉ X

def Guaranteed (n k : ℕ) : Prop :=
  k ≤ n ∧ ∀ f : Pair (Fin n) → Fin n, AvoidsEndpoints f →
    ∃ X : Finset (Fin n), Independent f X ∧ k ≤ X.card

noncomputable def g (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Guaranteed n) n

theorem erdos_1025 :
    (fun n : ℕ ↦ (g n : ℝ)) =Θ[Filter.atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
  sorry

end Erdos1025
