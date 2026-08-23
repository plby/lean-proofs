/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset BigOperators

namespace Erdos481

variable {r : ℕ}
variable (a b : Fin r → ℕ+)

noncomputable def C : ℝ := ∑ i : Fin r, (1 : ℝ) / (a i : ℝ)

def T (L : List ℕ+) : List ℕ+ :=
  L.flatMap fun x : ℕ+ => (List.finRange r).map fun i =>
    ⟨a i * x + b i, Nat.add_pos_right _ (b i).2⟩

def A : ℕ → List ℕ+
  | 0 => []
  | 1 => [1]
  | n + 2 => T a b (A (n + 1))
end Erdos481

open Finset BigOperators

namespace Erdos481

open scoped Classical in
theorem erdos_481 {r : ℕ} (a b : Fin r → ℕ+)
    (hr : 0 < r) (hC : 1 < C a) :
    ∃ k, 1 ≤ k ∧ ¬(A a b k).Nodup := by
  sorry

end Erdos481
