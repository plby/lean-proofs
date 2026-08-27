/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTInverseTransform
import ErdosProblems.Erdos4b.FGKMTAssignmentArithmetic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Field

/-! # The pinned inverse kernel is the literal Möbius--totient quotient -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [Fintype α] [DecidableEq ι]

omit [DecidableEq ι] in
theorem assignmentPrimeProduct_totient {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (r : α → Option ι) :
    ((assignmentPrimeProduct p r).totient : ℝ) =
      ∏ q, if r q = none then 1 else (p q : ℝ) - 1 := by
  classical
  have hnat : (assignmentPrimeProduct p r).totient =
      ∏ l ∈ (assignmentPrimeProduct p r).primeFactors, (l - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul,
      Nat.prod_primeFactors_of_squarefree (assignmentPrimeProduct_squarefree hp hinj r),
      Nat.div_self (assignmentPrimeProduct_pos (fun q => (hp q).pos) r), one_mul]
  rw [hnat, Nat.cast_prod, assignmentPrimeProduct_primeFactors hp r]
  unfold assignmentUsedPrimes
  rw [Finset.prod_image (fun q _hq s _hs hqs => hinj hqs), Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro q _hq
  by_cases hq : r q = none
  · simp [hq]
  · simp [hq, Nat.cast_sub (hp q).one_le]

open scoped Classical in
theorem assignmentInverseKernel_eq_moebius_totient {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (r d : α → Option ι) :
    assignmentInverseKernel (fun q => (p q : ℝ) - 1) r d =
      if AssignmentExtends r d then
        (ArithmeticFunction.moebius (assignmentPrimeProduct p r) : ℝ) /
          (assignmentPrimeProduct p d).totient
      else 0 := by
  classical
  by_cases h : AssignmentExtends r d
  · rw [if_pos h, assignmentPrimeProduct_moebius hp hinj r,
      assignmentPrimeProduct_totient hp hinj d, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro q _hq
    cases hr : r q with
    | none => cases d q <;> simp [localInverseCoeff]
    | some i => simp [localInverseCoeff, h q i hr, div_eq_mul_inv]
  · rw [if_neg h]
    unfold AssignmentExtends at h
    push Not at h
    obtain ⟨q, i, hr, hd⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    cases hdi : d q with
    | none => simp [localInverseCoeff, hr]
    | some j =>
      have hij : i ≠ j := fun heq => hd (by simpa only [heq] using hdi)
      simp [localInverseCoeff, hr, hij]

open scoped Classical in
theorem finiteInverseCoefficientTransform_eq_moebius_totient [DecidableEq α] [Fintype ι]
    {p : α → ℕ} (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (l : (α → Option ι) → ℝ) (r : α → Option ι) :
    finiteInverseCoefficientTransform (fun q => (p q : ℝ) - 1) l r =
      (ArithmeticFunction.moebius (assignmentPrimeProduct p r) : ℝ) *
        ∑ d, if ∀ i, assignmentPrimeTuple p r i ∣ assignmentPrimeTuple p d i then
          l d / (assignmentPrimeProduct p d).totient else 0 := by
  classical
  unfold finiteInverseCoefficientTransform
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [assignmentInverseKernel_eq_moebius_totient hp hinj r d,
    assignmentExtends_iff_coordinate_dvd hp hinj]
  split_ifs <;> ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.assignmentPrimeProduct_totient
#print axioms Erdos4b.FGKMT.finiteInverseCoefficientTransform_eq_moebius_totient
