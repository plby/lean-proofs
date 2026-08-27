/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTLocalQuadratic

/-! # The exact inverse of the local divisor transform -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

def localInverseCoeff (v : ℝ) (r d : Option ι) : ℝ :=
  match r, d with
  | none, none => 1
  | none, some _ => 1 / v
  | some _, none => 0
  | some i, some j => if i = j then -(1 / v) else 0

theorem sum_localInverseCoeff_mul [Fintype ι] (v : ℝ) (r : Option ι)
    (f : Option ι → ℝ) :
    (∑ d, localInverseCoeff v r d * f d) =
      match r with
      | none => f none + (∑ i, f (some i)) / v
      | some i => -f (some i) / v := by
  cases r <;>
    simp [Fintype.sum_option, localInverseCoeff, ite_mul, div_eq_mul_inv,
      Finset.mul_sum, mul_comm]

theorem localDivisor_inverse_contraction [Fintype ι] {v : ℝ} (hv : v ≠ 0)
    (d e : Option ι) :
    (∑ r, localDivisorCoeff v d r * localInverseCoeff v r e) =
      if d = e then 1 else 0 := by
  cases d with
  | none =>
    cases e <;> simp [Fintype.sum_option, localDivisorCoeff, localInverseCoeff]
  | some i =>
    cases e with
    | none => simp [localDivisorCoeff, localInverseCoeff]
    | some j =>
      by_cases hij : i = j
      · subst j
        simp [localDivisorCoeff, localInverseCoeff, ite_mul, hv]
      · simp [localDivisorCoeff, localInverseCoeff, ite_mul, hij]

theorem localInverse_divisor_contraction [Fintype ι] {v : ℝ} (hv : v ≠ 0)
    (r s : Option ι) :
    (∑ d, localInverseCoeff v r d * localDivisorCoeff v d s) =
      if r = s then 1 else 0 := by
  rw [sum_localInverseCoeff_mul]
  cases r with
  | none =>
    cases s <;> simp [localDivisorCoeff, hv]
  | some i =>
    cases s with
    | none => simp [localDivisorCoeff]
    | some j =>
      by_cases hij : i = j
      · subst j
        simp [localDivisorCoeff, hv]
      · simp [localDivisorCoeff, hij, Ne.symm hij]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.localDivisor_inverse_contraction
#print axioms Erdos4b.FGKMT.localInverse_divisor_contraction
