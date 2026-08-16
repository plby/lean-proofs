import Mathlib

namespace Erdos1100b

set_option linter.style.longLine false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

open Nat

noncomputable def tau_perp (n : ℕ) : ℕ :=
  let l := (divisors n).sort (· ≤ ·)
  (l.zip l.tail).countP (fun (a, b) => Nat.gcd a b = 1)
noncomputable def n_val_Ioc (x : ℝ) : ℕ :=
  ((Finset.Ioc (Nat.floor x) (Nat.floor (2 * x))).filter Nat.Prime).prod (fun p => p)
def PNT_statement : Prop :=
  Filter.Tendsto (fun x => Real.log (n_val_Ioc x) / x) Filter.atTop (nhds 1)
noncomputable def bound (n : ℕ) (ε : ℝ) : ℝ :=
  Real.exp ( (1 / 2 - ε) * (Real.log (Real.log n))^2 / Real.log (Real.log (Real.log n)) )
end Erdos1100b

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Nat

namespace Erdos1100b

theorem main_theorem (hPNT : PNT_statement) :
    ∀ ε ∈ Set.Ioo 0 (1 / 2), ∀ N, ∃ n ≥ N, (tau_perp n : ℝ) > bound n ε := by
  sorry

end Erdos1100b
