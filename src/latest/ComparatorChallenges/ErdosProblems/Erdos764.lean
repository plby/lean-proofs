import Mathlib

open scoped BigOperators Classical
open Finset Nat Asymptotics Filter
open scoped Topology BigOperators
open Filter Set Finset
open Complex MeasureTheory Set Polynomial
open scoped Real Polynomial
open Complex MeasureTheory Set Filter
open scoped Real Topology Polynomial
open Complex Filter MeasureTheory Polynomial Real Set
open scoped Polynomial
open scoped BigOperators Classical Real Polynomial
open Finset Complex MeasureTheory Set Filter

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos764

def addConv (f g : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p.1 * g p.2

end Erdos764

namespace Erdos764

noncomputable def indicator (A : Set ℕ) (n : ℕ) : ℕ :=
  if n ∈ A then 1 else 0

end Erdos764

namespace Erdos764

noncomputable def tripleConv (A : Set ℕ) (n : ℕ) : ℕ :=
  addConv (addConv (indicator A) (indicator A)) (indicator A) n

end Erdos764

namespace Erdos764

noncomputable def summatory (A : Set ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ range (N + 1), tripleConv A n

end Erdos764

namespace Erdos764

noncomputable def remainder (A : Set ℕ) (c : ℝ) (N : ℕ) : ℝ :=
  (summatory A N : ℝ) - c * N

end Erdos764

namespace Erdos764

theorem erdos_764 :
    ¬ ∃ A : Set ℕ, ∃ c : ℝ, 0 < c ∧
      remainder A c =O[Filter.atTop] (fun _ : ℕ ↦ (1 : ℝ)) := by
  sorry

end Erdos764

end
