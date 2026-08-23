import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos487

open scoped Nat
open Filter


open scoped Classical in
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun N => ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ)) Filter.atTop
end Erdos487


open scoped Nat
open Asymptotics Filter

namespace Erdos487

open scoped Classical in
theorem erdos_487 (A : Set ℕ) (hA : lowerDensity A > 0) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ Nat.lcm a b = c := by
  sorry

end Erdos487
