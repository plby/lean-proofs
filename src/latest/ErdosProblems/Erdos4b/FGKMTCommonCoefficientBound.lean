/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCoefficientColumn
import ErdosProblems.Erdos4b.FGKMTCoefficientSupportCount

/-!
# A uniform squared l1 bound for the actual common coefficients

The literal profile is bounded by one. Its support, the absolute
column calculation, and Cauchy--Schwarz give the explicit envelope
`R^3 * (1 + log R)^(2*k)`, uniformly in the finite prime universe.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] in
theorem primeAssignmentProfile_le_one (k R : ℕ) (p : α → ℕ)
    (r : α → Option (Fin k)) : primeAssignmentProfile k R p r ≤ 1 := by
  have hT : 0 ≤ sieveProfileScale k :=
    mul_nonneg (Nat.cast_nonneg k) (Real.log_natCast_nonneg k)
  have hprod : (∏ i, dimensionProfileFactor k
      (sieveLogTuple R (assignmentPrimeTuple p r) i)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i _hi
      exact dimensionProfileFactor_nonneg k _
    · intro i _hi
      exact sieveFactor_le_one hT (sieveLogTuple_nonneg R _ i) _
  exact (mul_le_of_le_one_left
    (Finset.prod_nonneg fun i _ => dimensionProfileFactor_nonneg k _)
    (sieveCutoff_le_one _)).trans hprod

theorem commonSieveCoefficient_l1_le_two_weights {k R : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hlarge : ∀ q, 2 * k + 1 ≤ p q) (hR : 1 < R) :
    (∑ d, |commonSieveCoefficient k R p d|) ≤
      ∑ r ∈ assignmentProductSupport k R p, assignmentScalarWeight (fun _ => 2) r := by
  have hpos (r : α → Option (Fin k)) :
      0 < assignmentRowWeight (fun q => (p q : ℝ)) r :=
    primeAssignmentRowWeight_pos (fun q => by have := hlarge q; omega) r
  have hF (r : α → Option (Fin k)) : 0 ≤ primeAssignmentProfile k R p r :=
    sieveProfile_nonneg k k _
  calc
    _ ≤ ∑ r : α → Option (Fin k),
        |primeAssignmentProfile k R p r / assignmentRowWeight (fun q => (p q : ℝ)) r| *
          assignmentScalarWeight (fun q => 1 + (p q : ℝ)) r :=
      finiteCoefficientTransform_l1_le (fun q => Nat.cast_nonneg _) _
    _ = ∑ r : α → Option (Fin k), primeAssignmentProfile k R p r *
        (assignmentScalarWeight (fun q => 1 + (p q : ℝ)) r /
          assignmentRowWeight (fun q => (p q : ℝ)) r) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [abs_of_nonneg (div_nonneg (hF r) (hpos r).le)]
      ring
    _ ≤ _ := by
      rw [assignmentProductSupport, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro r _hr
      by_cases hs : assignmentPrimeProduct p r < R
      · rw [if_pos hs]
        refine (mul_le_of_le_one_left ?_ (primeAssignmentProfile_le_one k R p r)).trans
          (assignmentColumn_div_row_le_two hlarge r)
        exact div_nonneg
          (assignmentScalarWeight_nonneg (fun q => by positivity) r) (hpos r).le
      · rw [if_neg hs, primeAssignmentProfile_zero_of_product_ge hp hR r (Nat.le_of_not_gt hs)]
        simp only [zero_mul, le_refl]

theorem commonSieveCoefficient_l1_sq_le {k R : ℕ} {p : α → ℕ}
    (hk : 2 ≤ k) (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (hlarge : ∀ q, 2 * k ^ 2 < p q) (hR : 1 < R) :
    (∑ d, |commonSieveCoefficient k R p d|) ^ 2 ≤
      (R : ℝ) ^ 3 * (1 + Real.log R) ^ (2 * k) := by
  have hcolumn (q : α) : 2 * k + 1 ≤ p q := by
    have := hlarge q
    nlinarith
  have hfour (q : α) : 4 ≤ p q := by
    have := hcolumn q
    omega
  have hcard := card_assignmentProductSupport_le (k := k) (R := R) hp hinj
  calc
    _ ≤ (∑ r ∈ assignmentProductSupport k R p,
        assignmentScalarWeight (fun _ => 2) r) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun d _ => abs_nonneg _)
        (commonSieveCoefficient_l1_le_two_weights hp hcolumn hR) 2
    _ ≤ (R : ℝ) * ((assignmentProductSupport k R p).card : ℝ) ^ 2 :=
      sum_two_weights_sq_le_radius_card hfour
    _ ≤ (R : ℝ) * ((R : ℝ) * (1 + Real.log R) ^ k) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2)
        (Nat.cast_nonneg R)
    _ = _ := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm k 2]
      ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonSieveCoefficient_l1_sq_le
