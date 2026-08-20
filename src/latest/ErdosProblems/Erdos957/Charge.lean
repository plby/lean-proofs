import ErdosProblems.Erdos957.Hull

/-!
# The charging calculation in the proof of Erdős problem 957

This file isolates the finite double-counting argument from the geometric part
of Dumitrescu's proof.  Charges and transfers are integer valued.  This avoids
all uses of truncated subtraction: an outgoing transfer is literally
subtracted in `ℤ`.
-/

namespace Erdos957

open scoped BigOperators

section Conservation

variable {V : Type*} [Fintype V]

/-- Twice the usual initial charge of a vertex. -/
def doubledInitialToken (degree : V → ℕ) (v : V) : ℤ :=
  2 * (degree v : ℤ)

/--
The final doubled charge after moving `transfer u v` tokens from `u` to `v`.
The use of `ℤ` makes the conservation identity unconditional: no hypothesis
about a vertex having enough tokens is needed merely to state the accounting.
-/
def doubledFinalToken (degree : V → ℕ) (transfer : V → V → ℕ) (v : V) : ℤ :=
  doubledInitialToken degree v
    + ∑ u, (transfer u v : ℤ)
    - ∑ w, (transfer v w : ℤ)

/-- Every finite family of directed transfers preserves the total charge. -/
theorem sum_doubledFinalToken_eq_sum_doubledInitialToken
    (degree : V → ℕ) (transfer : V → V → ℕ) :
    ∑ v, doubledFinalToken degree transfer v =
      ∑ v, doubledInitialToken degree v := by
  simp only [doubledFinalToken, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  omega

end Conservation

section Capacity

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
The doubled capacity used after the transfers.  A general vertex has capacity
`12`, a hull vertex loses `6`, and a distinguished flat diameter endpoint
loses a further `2`.  In the geometric application `Q ⊆ H`, so these are
respectively the doubled forms of the capacities `6`, `3`, and `2`.
-/
def doubledCapacity (H Q : Finset V) (v : V) : ℤ :=
  12 - (if v ∈ H then 6 else 0) - (if v ∈ Q then 2 else 0)

/-- The total doubled capacity, expressed only through cardinalities. -/
theorem sum_doubledCapacity (H Q : Finset V) :
    ∑ v, doubledCapacity H Q v =
      12 * (Fintype.card V : ℤ) - 6 * (H.card : ℤ) - 2 * (Q.card : ℤ) := by
  simp [doubledCapacity, Finset.sum_sub_distrib]
  ring

/--
Abstract form of Dumitrescu's doubled-token calculation.

`H` is the hull-vertex set, `Q` is the set of flat diameter endpoints, and
`d` is the number of diameter endpoints.  The hypotheses `hdH` and `hdQ`
encode `d ≤ |H|` and `d ≤ |Q| + 2520`; the latter is the exceptional-angle
estimate.  The handshake identity says that `s` is the number of shortest
edges.  All geometric work is confined to proving `hcap`, the pointwise final
capacity bound.
-/
theorem doubledToken_bound
    (degree : V → ℕ) (transfer : V → V → ℕ) (H Q : Finset V) (s d : ℕ)
    (handshake : ∑ v, degree v = 2 * s)
    (hcap : ∀ v, doubledFinalToken degree transfer v ≤ doubledCapacity H Q v)
    (hdH : d ≤ H.card) (hdQ : d ≤ Q.card + 2520) :
    (4 * s : ℤ) ≤
      12 * (Fintype.card V : ℤ) - 8 * (d : ℤ) + 5040 := by
  have hsum :
      ∑ v, doubledFinalToken degree transfer v ≤
        ∑ v, doubledCapacity H Q v :=
    Finset.sum_le_sum fun v _ ↦ hcap v
  rw [sum_doubledFinalToken_eq_sum_doubledInitialToken,
    sum_doubledCapacity] at hsum
  have hinitial :
      ∑ v, doubledInitialToken degree v = (4 * s : ℤ) := by
    simp only [doubledInitialToken, ← Finset.mul_sum]
    have handshake' : ∑ v, (degree v : ℤ) = 2 * (s : ℤ) := by
      exact_mod_cast handshake
    rw [handshake']
    ring
  rw [hinitial] at hsum
  have hdH' : (d : ℤ) ≤ H.card := by exact_mod_cast hdH
  have hdQ' : (d : ℤ) ≤ (Q.card : ℤ) + 2520 := by exact_mod_cast hdQ
  nlinarith

end Capacity

section Product

/--
The purely algebraic last step of the proof, in an integer-cleared form.
Here `sMin` and `sMax` are the two edge counts and `d` is the number of
diameter endpoints.  The coefficient `10080 = 8 * 1260` is the linear error
term after clearing the denominator in `9 / 8`.
-/
theorem product_bound_int (n d sMin sMax : ℕ)
    (hcharge : (4 * sMin : ℤ) ≤ 12 * (n : ℤ) - 8 * (d : ℤ) + 5040)
    (hmax : sMax ≤ d) (hdn : d ≤ n) :
    8 * (sMin : ℤ) * (sMax : ℤ) ≤
      9 * (n : ℤ) ^ 2 + 10080 * (n : ℤ) := by
  have hmax' : (sMax : ℤ) ≤ d := by exact_mod_cast hmax
  have hdn' : (d : ℤ) ≤ n := by exact_mod_cast hdn
  have hsMin : (0 : ℤ) ≤ sMin := by positivity
  have hd : (0 : ℤ) ≤ d := by positivity
  have hprod := Int.mul_le_mul_of_nonneg_left hmax' hsMin
  have hchargeMul := Int.mul_le_mul_of_nonneg_right hcharge (show (0 : ℤ) ≤ 2 * d by positivity)
  nlinarith [sq_nonneg (4 * (d : ℤ) - 3 * (n : ℤ))]

/-- The same product estimate in the real-number form used in the theorem. -/
theorem product_bound_real (n d sMin sMax : ℕ)
    (hcharge : (4 * sMin : ℤ) ≤ 12 * (n : ℤ) - 8 * (d : ℤ) + 5040)
    (hmax : sMax ≤ d) (hdn : d ≤ n) :
    (sMin : ℝ) * (sMax : ℝ) ≤
      (9 / 8 : ℝ) * (n : ℝ) ^ 2 + 1260 * (n : ℝ) := by
  have h := product_bound_int n d sMin sMax hcharge hmax hdn
  have h' :
    (8 : ℝ) * (sMin : ℝ) * (sMax : ℝ) ≤
      9 * (n : ℝ) ^ 2 + 10080 * (n : ℝ) := by
    exact_mod_cast h
  nlinarith

end Product

end Erdos957

