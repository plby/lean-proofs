/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators
open Filter Finset Function
open Asymptotics

noncomputable section

namespace Erdos1025

open scoped Classical in
abbrev Pair (α : Type*) := {e : Sym2 α // ¬ e.IsDiag}

end Erdos1025

namespace Erdos1025.Pair

variable {α β : Type*}

open scoped Classical in
def vertices [DecidableEq α] (e : Pair α) : Finset α := e.1.toFinset

end Erdos1025.Pair

namespace Erdos1025

open scoped Classical in
def AvoidsEndpoints {α : Type*} [DecidableEq α] (f : Pair α → α) : Prop :=
  ∀ e, f e ∉ e.vertices

end Erdos1025

namespace Erdos1025

open scoped Classical in
def Independent {α : Type*} [DecidableEq α] (f : Pair α → α) (X : Finset α) : Prop :=
  ∀ e, e.vertices ⊆ X → f e ∉ X

end Erdos1025

namespace Erdos1025

open scoped Classical in
def Guaranteed (n k : ℕ) : Prop :=
  k ≤ n ∧ ∀ f : Pair (Fin n) → Fin n, AvoidsEndpoints f →
    ∃ X : Finset (Fin n), Independent f X ∧ k ≤ X.card

end Erdos1025

namespace Erdos1025

open scoped Classical in
noncomputable def g (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Guaranteed n) n

end Erdos1025

namespace Erdos1025

open scoped Classical in
theorem erdos_1025 :
    (fun n : ℕ ↦ (g n : ℝ)) =Θ[Filter.atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
  sorry

end Erdos1025

end
