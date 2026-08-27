/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentRecovery
import ErdosProblems.Erdos4b.FGKMTNormalizedTransform
import ErdosProblems.Erdos4b.FGKMTMovedFactorVariation

/-!
# The common finite sieve coefficients for the actual smooth profile

The finite transform is identified with the literal Möbius-divisor sum
with denominator `prod (p - k)`. The simplex cutoff forces both the
profile and every nonzero coefficient into the required product range.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

def primeAssignmentProfile (k R : ℕ) (p : α → ℕ) (r : α → Option (Fin k)) : ℝ :=
  sieveProfile k k (sieveLogTuple R (assignmentPrimeTuple p r))

def commonSieveCoefficient (k R : ℕ) (p : α → ℕ) : (α → Option (Fin k)) → ℝ :=
  normalizedCoefficientTransform (fun q => (p q : ℝ)) (primeAssignmentProfile k R p)

theorem commonSieveCoefficient_eq_moebius (k R : ℕ) {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (d : α → Option (Fin k)) :
    commonSieveCoefficient k R p d =
      (ArithmeticFunction.moebius (assignmentPrimeProduct p d) : ℝ) * assignmentPrimeProduct p d *
        ∑ r : α → Option (Fin k),
          if ∀ i, assignmentPrimeTuple p d i ∣ assignmentPrimeTuple p r i then
            primeAssignmentProfile k R p r /
              ∏ l ∈ (assignmentPrimeProduct p r).primeFactors, ((l : ℝ) - k)
          else 0 := by
  classical
  unfold commonSieveCoefficient normalizedCoefficientTransform finiteCoefficientTransform
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  dsimp only
  rw [assignmentCoeffKernel_eq_moebius hp hinj d r,
    assignmentRowWeight_eq_primeFactors hp hinj r]
  simp only [Fintype.card_fin]
  by_cases h : AssignmentExtends d r
  · rw [if_pos h, if_pos ((assignmentExtends_iff_coordinate_dvd hp hinj d r).mp h)]
  · rw [if_neg h, if_neg (fun hh => h
      ((assignmentExtends_iff_coordinate_dvd hp hinj d r).mpr hh))]
    simp

theorem sieveProfile_logTuple_zero_of_product_ge {k R : ℕ} (hR : 1 < R)
    (r : Fin k → ℕ) (hr : ∀ i, 0 < r i) (hprod : R ≤ ∏ i, r i) :
    sieveProfile k k (sieveLogTuple R r) = 0 := by
  apply sieveProfile_zero_of_sum_ge_one
  rw [sum_sieveLogTuple R r hr]
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  apply (le_div_iff₀ hlogR).mpr
  rw [one_mul]
  exact Real.log_le_log (by exact_mod_cast (Nat.zero_lt_one.trans hR)) (by exact_mod_cast hprod)

omit [DecidableEq α] in
theorem primeAssignmentProfile_zero_of_product_ge {k R : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hR : 1 < R) (r : α → Option (Fin k))
    (hr : R ≤ assignmentPrimeProduct p r) : primeAssignmentProfile k R p r = 0 := by
  apply sieveProfile_logTuple_zero_of_product_ge hR (assignmentPrimeTuple p r)
    (assignmentPrimeTuple_pos (fun q => (hp q).pos) r)
  rwa [prod_assignmentPrimeTuple]

theorem commonSieveCoefficient_zero_of_product_ge {k R : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hR : 1 < R)
    (d : α → Option (Fin k)) (hd : R ≤ assignmentPrimeProduct p d) :
    commonSieveCoefficient k R p d = 0 := by
  classical
  unfold commonSieveCoefficient normalizedCoefficientTransform finiteCoefficientTransform
  apply Finset.sum_eq_zero
  intro r _hr
  dsimp only
  by_cases hext : AssignmentExtends d r
  · have hcoord := (assignmentExtends_iff_coordinate_dvd hp hinj d r).mp hext
    have hdiv : assignmentPrimeProduct p d ∣ assignmentPrimeProduct p r := by
      rw [← prod_assignmentPrimeTuple p d, ← prod_assignmentPrimeTuple p r]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _hi => hcoord i)
    have hle := Nat.le_of_dvd (assignmentPrimeProduct_pos (fun q => (hp q).pos) r) hdiv
    rw [primeAssignmentProfile_zero_of_product_ge hp hR r (hd.trans hle)]
    simp
  · rw [assignmentCoeffKernel_eq_moebius hp hinj d r, if_neg hext, zero_mul]

omit [DecidableEq α] in
theorem primeAssignmentRowWeight_pos {k : ℕ} {p : α → ℕ}
    (hp : ∀ q, k < p q) (r : α → Option (Fin k)) :
    0 < assignmentRowWeight (fun q => (p q : ℝ)) r := by
  apply Finset.prod_pos
  intro q _hq
  cases r q with
  | none => exact zero_lt_one
  | some i =>
    change 0 < (p q : ℝ) - Fintype.card (Fin k)
    simp only [Fintype.card_fin]
    exact sub_pos.mpr (by exact_mod_cast hp q)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonSieveCoefficient_eq_moebius
#print axioms Erdos4b.FGKMT.commonSieveCoefficient_zero_of_product_ge
