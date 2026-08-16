import Mathlib

namespace Erdos291b

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 300000

def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id
def X (r : ℕ → ℤ) (n : ℕ) : ℚ := (L n : ℚ) * ∑ i ∈ Finset.Icc 1 n, (r i : ℚ) / i
def z (m : ℕ) : ℕ := ((Finset.range m).filter Nat.Prime).card
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
def J1' (p : ProblemParameters) : Finset ℕ := Finset.Ico (p.tilde_m - p.m^(2 * z p.m - 1)) p.tilde_m
def J2' (p : ProblemParameters) : Finset ℕ := Finset.Ico p.tilde_m (p.tilde_m + p.m^(2 * z p.m - 1))
def X_int (r : ℕ → ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, r i * ((L n) / i : ℕ)
noncomputable def I0 (p : ProblemParameters) : Finset ℕ :=
  if ∀ n ∈ J1' p, |X p.r n| > (n : ℚ)^(z p.m) then J1' p else J2' p
end Erdos291b

attribute [local instance] Classical.propDecidable

namespace Erdos291b

end Erdos291b

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos291b

theorem ohyeah1 (p : ProblemParameters) :
    ∃ n ∈ I0 p, ∃ q, q.Prime ∧ q ≥ p.m ∧ q ∣ Int.natAbs (X_int p.r n) := by
  sorry


theorem generalErdos291 (r : ℕ → ℤ) (t : ℕ) (ht : t > 0) (h_per : Function.Periodic r t)
    (h_r_nz : ∀ i, r i ≠ 0)
    (h_priemteller : ∀ m : ℕ, m ≥ 4 → (m : ℝ)^(2 * z m) < Real.exp (2.52 * m))
    (h_bla0 : ∀ n : ℕ, n ≥ 100 → L n > 2^n) :
    ∀ N, ∃ b, Nat.gcd (Int.natAbs (X_int r b)) (L b) > N := by
  sorry

end Erdos291b
