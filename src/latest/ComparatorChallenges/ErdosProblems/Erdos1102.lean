import Mathlib

set_option linter.style.setOption false
set_option linter.style.cases false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.cdot false
set_option linter.flexible false
set_option linter.style.longLine false

set_option maxHeartbeats 50000000

namespace Erdos1102

open Squarefree Set Order Filter Topology

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

noncomputable section

def HasPropertyP (A : Set ℕ) : Prop :=
  ∀ n ≥ 1, {a ∈ A | Squarefree (n + a)}.Finite
end

end Erdos1102

namespace Erdos1102b

open Squarefree Set Order Filter Topology

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

noncomputable section

def SF : Set ℕ := {n | Squarefree n}
def PropertyQ (A : Set ℕ) : Prop := ({n | ∀ a ∈ A, a < n → Squarefree (n + a)}).Infinite
def HasNaturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun n => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop (nhds d)
def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun (n : ℕ) => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop
def HasPropertyQ (A : Set ℕ) : Prop :=
  {n : ℕ | ∀ a ∈ A, a < n → Squarefree (n + a)}.Infinite
end
end Erdos1102b

namespace Erdos1102c

open Squarefree Set Order Filter Topology

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

noncomputable section

def PropertyP_bar (A : Set ℕ) : Prop := ({n | ∀ a ∈ A, Squarefree (n + a)}).Infinite
def PropertyP_bar_infty (A : Set ℕ) : Prop := ({n | ({a ∈ A | ¬Squarefree (n + a)}).Finite}).Infinite
def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun (n : ℕ) => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop
open Finset Filter Asymptotics

def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun (n : ℕ) => ((A ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop
end
end Erdos1102c

namespace Erdos1102d

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

noncomputable section

def PropertyQ (A : Set ℕ) : Prop := ({n | ∀ a ∈ A, a < n → Squarefree (n + a)}).Infinite
def Admissible (A : Set ℕ) : Prop :=
  ∀ p, Nat.Prime p → ∃ b, b < p^2 ∧ ∀ a ∈ A, a % p^2 ≠ b
def A1 : Set ℕ := {n | ∃ j : ℕ, j ≥ 1 ∧ n = 2^j + 1}
def A2 : Set ℕ := {n | ∃ j : ℕ, j ≥ 1 ∧ n = 2^j - 1}
def A3 : Set ℕ := {n | ∃ j : ℕ, j ≥ 1 ∧ n = Nat.factorial j + 1}
def A4 : Set ℕ := {n | ∃ j : ℕ, j > 1 ∧ n = Nat.factorial j - 1}
def GrowthCondition (A : Set ℕ) (C : ℝ) : Prop :=
  ∃ᶠ j in Filter.atTop, (Nat.nth (· ∈ A) (j - 1) : ℝ) ≥ Real.exp (C * j / Real.log j)
end
end Erdos1102d

attribute [local instance] Classical.propDecidable

open Squarefree Set Order Filter Topology
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Finset Filter Asymptotics

namespace Erdos1102.erdos_1102

theorem exists_sequence_with_P
    (f : ℕ → ℕ) (h_inf : Tendsto f atTop atTop)
    (h_pos : ∀ n, f n ≠ 0) :
    ∃ A : ℕ → ℕ, StrictMono A ∧
    HasPropertyP (range A) ∧
    ∀ j : ℕ, (A j : ℝ) / j ≤ f j := by
  sorry

end Erdos1102.erdos_1102
namespace Erdos1102b

theorem TheoremQ_upper (A : Set ℕ) (h : PropertyQ A) : upperDensity A ≤ 6 / Real.pi^2 := by
  sorry


theorem TheoremQ_lower : ∃ A : Set ℕ, A ⊆ SF ∧ PropertyQ A ∧ HasNaturalDensity A (6 / Real.pi^2) := by
  sorry

end Erdos1102b
namespace Erdos1102b.erdos_1102

theorem upper_density_Q
    (A : ℕ → ℕ) (h_inc : StrictMono A)
    (hQ : HasPropertyQ (range A)) :
    limsup (fun j : ℕ  ↦ (j / A j : ℝ)) atTop ≤ 6 / Real.pi^2 := by
  sorry


theorem lower_density_Q_exists :
    ∃ A : ℕ → ℕ, StrictMono A ∧
    (∀ j, Squarefree (A j)) ∧
    HasPropertyQ (range A) ∧
    Tendsto (fun j : ℕ  ↦ (j / A j : ℝ)) atTop (𝓝 (6 / Real.pi^2)) := by
  sorry

end Erdos1102b.erdos_1102
namespace Erdos1102c

theorem theorem_overp_i (A : Set ℕ) (h : PropertyP_bar_infty A) :
    upperDensity A < 6 / Real.pi^2 := by
  sorry


theorem theorem_overp_ii :
    ∀ ε > 0, ∃ A : Set ℕ, PropertyP_bar A ∧ lowerDensity A ≥ 6 / Real.pi^2 - ε := by
  sorry

end Erdos1102c
namespace Erdos1102d

theorem Theorem_suff :
  ∃ C > 0, ∀ A : Set ℕ, Admissible A → A.Infinite → GrowthCondition A C → PropertyQ A := by
  sorry

end Erdos1102d
theorem Erdos1102d.All_Sequences_PropertyQ :
    And (Erdos1102d.PropertyQ Erdos1102d.A1)
      (And (Erdos1102d.PropertyQ Erdos1102d.A2)
        (And (Erdos1102d.PropertyQ Erdos1102d.A3) (Erdos1102d.PropertyQ Erdos1102d.A4)))
  := by
  sorry
