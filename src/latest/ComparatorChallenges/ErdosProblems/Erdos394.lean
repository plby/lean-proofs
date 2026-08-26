/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Nat Filter Finset
open scoped Asymptotics Topology Nat

namespace Erdos394

/-- The product `m (m+1) ... (m+k-1)`. -/
def consecutiveProduct (k m : ℕ) : ℕ :=
  ∏ i ∈ range k, (m + i)

/--
The least *positive* `m` for which `n ∣ m(m+1)...(m+k-1)`.
For positive `k,n`, the defining set is nonempty because `m=n` works.
-/
noncomputable def t (k n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ n ∣ consecutiveProduct k m}

/-- Partial sums occurring in the problem, indexed by a real cutoff. -/
noncomputable def Tsum (k : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (t k n : ℝ)

/-- Both average-order questions have affirmative answers. -/
theorem erdos_394 :
    (∃ c : ℝ, c > 0 ∧
      (fun x : ℝ ↦ Tsum 2 x) =O[atTop]
        (fun x : ℝ ↦ x ^ 2 / (Real.log x) ^ c)) ∧
    ∀ k : ℕ, k ≥ 2 →
      (fun x : ℝ ↦ Tsum (k + 1) x) =o[atTop]
        (fun x : ℝ ↦ Tsum k x) := by
  sorry

end Erdos394
