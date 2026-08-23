import Mathlib

namespace Erdos1000

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false


open scoped BigOperators

open Filter

open Topology

open scoped Classical in
def phiA (n : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 (n k)).filter (fun m =>
      ∀ j ∈ Finset.range k, n k / Nat.gcd m (n k) ≠ n j)).card

open scoped Classical in
noncomputable def cesaroPhi (n : ℕ → ℕ) (N : ℕ) : ℝ :=
  ((N : ℝ)⁻¹) *
    ∑ k ∈ Finset.range N, (phiA n k : ℝ) / (n k : ℝ)
end Erdos1000


open scoped BigOperators
open Filter
open Topology

namespace Erdos1000

open scoped Classical in
theorem erdos_1000_true :
  ∃ n : ℕ → ℕ,
    StrictMono n ∧
    (∀ k, 0 < n k) ∧
    Tendsto (cesaroPhi n) atTop (𝓝 (0 : ℝ)) := by
  sorry

end Erdos1000
