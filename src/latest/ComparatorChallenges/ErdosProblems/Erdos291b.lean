/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos291b

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise


set_option maxHeartbeats 300000

open scoped Classical in
def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id
open scoped Classical in
def X (r : ℕ → ℤ) (n : ℕ) : ℚ := (L n : ℚ) * ∑ i ∈ Finset.Icc 1 n, (r i : ℚ) / i
open scoped Classical in
def z (m : ℕ) : ℕ := ((Finset.range m).filter Nat.Prime).card
open scoped Classical in
structure ProblemParameters where
  r : ℕ → ℤ
  m : ℕ
  tilde_m : ℕ
  q0 : ℕ
  hm4 : 4 ≤ m
  h_r_nz : ∀ i, r i ≠ 0
  h_r_bdd : ∀ i, |r i| < m
  htilde_m : 20 * m^(2 * z m) < tilde_m
  hq0_prime : q0.Prime
  hq0_dvd : q0 ∣ tilde_m
  hq0_large : m^(2 * z m - 1) < q0
  h_priemteller : (m : ℝ)^(2 * z m) < Real.exp (2.52 * m)
  h_bla0 : ∀ w ∈ Finset.Ico (tilde_m - m^(2 * z m - 1)) tilde_m, ∀ k, L (w + k) > 2^(w + k)
open scoped Classical in
def J1' (p : ProblemParameters) : Finset ℕ := Finset.Ico (p.tilde_m - p.m^(2 * z p.m - 1)) p.tilde_m
open scoped Classical in
def J2' (p : ProblemParameters) : Finset ℕ := Finset.Ico p.tilde_m (p.tilde_m + p.m^(2 * z p.m - 1))
open scoped Classical in
def X_int (r : ℕ → ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, r i * ((L n) / i : ℕ)
open scoped Classical in
noncomputable def I0 (p : ProblemParameters) : Finset ℕ :=
  if ∀ n ∈ J1' p, |X p.r n| > (n : ℚ)^(z p.m) then J1' p else J2' p
end Erdos291b


namespace Erdos291b

end Erdos291b

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos291b

open scoped Classical in
theorem ohyeah1 (p : ProblemParameters) :
    ∃ n ∈ I0 p, ∃ q, q.Prime ∧ q ≥ p.m ∧ q ∣ Int.natAbs (X_int p.r n) := by
  sorry


open scoped Classical in
theorem generalErdos291 (r : ℕ → ℤ) (t : ℕ) (ht : t > 0) (h_per : Function.Periodic r t)
    (h_r_nz : ∀ i, r i ≠ 0)
    (h_priemteller : ∀ m : ℕ, m ≥ 4 → (m : ℝ)^(2 * z m) < Real.exp (2.52 * m))
    (h_bla0 : ∀ n : ℕ, n ≥ 100 → L n > 2^n) :
    ∀ N, ∃ b, Nat.gcd (Int.natAbs (X_int r b)) (L b) > N := by
  sorry

end Erdos291b
