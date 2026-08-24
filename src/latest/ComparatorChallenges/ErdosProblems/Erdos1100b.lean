/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Nat

namespace Erdos1100b

noncomputable def tau_perp (n : ℕ) : ℕ :=
  let l := (divisors n).sort (· ≤ ·)
  (l.zip l.tail).countP (fun (a, b) => Nat.gcd a b = 1)
noncomputable def n_val_Ioc (x : ℝ) : ℕ :=
  ((Finset.Ioc (Nat.floor x) (Nat.floor (2 * x))).filter Nat.Prime).prod (fun p => p)

noncomputable def bound (n : ℕ) (ε : ℝ) : ℝ :=
  Real.exp ( (1 / 2 - ε) * (Real.log (Real.log n))^2 / Real.log (Real.log (Real.log n)) )

theorem erdos_1100
    (hPNT : Filter.Tendsto (fun x => Real.log (Erdos1100b.n_val_Ioc x) / x)
      Filter.atTop (nhds 1)) :
    ∀ ε ∈ Set.Ioo 0 (1 / 2), ∀ N, ∃ n ≥ N, (tau_perp n : ℝ) > bound n ε := by
  sorry

end Erdos1100b
