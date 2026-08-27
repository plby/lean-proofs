/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact local factors of the common coefficient transform

An optional coordinate records absence of a prime or its unique assigned
coordinate. Incompatible coordinate requirements have zero density.
The same calculation gives the total and pinned local factors by taking
the local parameter to be `p` and `p - 1`, respectively.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

def localDivisorCoeff (v : ℝ) (d r : Option ι) : ℝ :=
  match d with
  | none => 1
  | some i => if r = some i then -v else 0

def localCrtDensity (v : ℝ) (d e : Option ι) : ℝ :=
  match d, e with
  | none, none => 1
  | some _, none => 1 / v
  | none, some _ => 1 / v
  | some i, some j => if i = j then 1 / v else 0

def localQuadraticKernel (v : ℝ) (r s : Option ι) : ℝ :=
  match r, s with
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some i, some j => if i = j then v - 1 else -1

def localRowWeight [Fintype ι] (v : ℝ) (r : Option ι) : ℝ :=
  match r with
  | none => 1
  | some _ => v - Fintype.card ι

theorem sum_localDivisorCoeff_mul [Fintype ι] (v : ℝ) (r : Option ι)
    (f : Option ι → ℝ) :
    (∑ d, localDivisorCoeff v d r * f d) =
      match r with
      | none => f none
      | some i => f none - v * f (some i) := by
  cases r <;> simp [Fintype.sum_option, localDivisorCoeff, ite_mul, sub_eq_add_neg]

theorem localQuadraticKernel_eq_contraction [Fintype ι] {v : ℝ} (hv : v ≠ 0)
    (r s : Option ι) :
    localQuadraticKernel v r s =
      ∑ d, localDivisorCoeff v d r *
        ∑ e, localDivisorCoeff v e s * localCrtDensity v d e := by
  simp_rw [sum_localDivisorCoeff_mul]
  cases r with
  | none =>
    cases s <;> simp [localCrtDensity, localQuadraticKernel, hv]
  | some i =>
    cases s with
    | none => simp [localCrtDensity, localQuadraticKernel, hv]
    | some j =>
      by_cases hij : i = j
      · subst j
        simp [localCrtDensity, localQuadraticKernel, hv]
        field_simp [hv]
        ring
      · simp [localCrtDensity, localQuadraticKernel, hij, hv]

theorem sum_localQuadraticKernel [Fintype ι] (v : ℝ) (r : Option ι) :
    (∑ s, localQuadraticKernel v r s) = localRowWeight v r := by
  cases r with
  | none => simp [Fintype.sum_option, localQuadraticKernel, localRowWeight]
  | some i =>
    have hentry (j : ι) : (if i = j then v - 1 else -1) =
        (if j = i then v else 0) - 1 := by
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji, Ne.symm hji]
    rw [Fintype.sum_option]
    simp only [localQuadraticKernel, zero_add]
    simp_rw [hentry]
    rw [Finset.sum_sub_distrib]
    simp [localRowWeight]

theorem localRowWeight_eq_of_kernel_ne_zero [Fintype ι] (v : ℝ) {r s : Option ι}
    (h : localQuadraticKernel v r s ≠ 0) : localRowWeight v r = localRowWeight v s := by
  cases r <;> cases s <;> simp_all [localQuadraticKernel, localRowWeight]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.localQuadraticKernel_eq_contraction
#print axioms Erdos4b.FGKMT.sum_localQuadraticKernel
