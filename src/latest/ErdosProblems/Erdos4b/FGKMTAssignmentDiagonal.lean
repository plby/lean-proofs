/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCommonCoefficients
import ErdosProblems.Erdos4b.FGKMTCoordinateRecurrence

/-!
# The actual arithmetic diagonal of the common sieve coefficients

Squarefreeness and coprimality identify the reciprocal row product with
the already estimated rough sieve weight. The error is still an exact
finite profile-variation sum.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] in
theorem assignmentRowWeight_inv_eq_rough {k M : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (hM : ∀ q, ¬p q ∣ M) (r : α → Option (Fin k)) :
    1 / assignmentRowWeight (fun q => (p q : ℝ)) r =
      roughSieveWeight M (fun l => (l : ℝ) - k) (assignmentPrimeProduct p r) := by
  rw [roughSieveWeight_apply_of_squarefree_coprime
    (assignmentPrimeProduct_squarefree hp hinj r) (assignmentPrimeProduct_coprime hp hM r).symm,
    assignmentRowWeight_eq_primeFactors hp hinj r]
  simp

theorem commonSieveCoefficient_quadratic_decomposition (k M R : ℕ) {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hM : ∀ q, ¬p q ∣ M) :
    finiteSieveQuadratic (fun q => (p q : ℝ)) (commonSieveCoefficient k R p) =
      (∑ r : α → Option (Fin k), primeAssignmentProfile k R p r ^ 2 *
        roughSieveWeight M (fun l => (l : ℝ) - k) (assignmentPrimeProduct p r)) +
      ∑ r : α → Option (Fin k), ∑ s : α → Option (Fin k),
        primeAssignmentProfile k R p r *
          (primeAssignmentProfile k R p s - primeAssignmentProfile k R p r) *
            assignmentQuadraticKernel (fun q => (p q : ℝ)) r s /
              (assignmentRowWeight (fun q => (p q : ℝ)) r *
                assignmentRowWeight (fun q => (p q : ℝ)) s) := by
  rw [commonSieveCoefficient, normalizedCoefficientTransform_diagonal_error
    (fun q => by exact_mod_cast (hp q).ne_zero)]
  congr 1
  apply Finset.sum_congr rfl
  intro r _hr
  rw [div_eq_mul_one_div, assignmentRowWeight_inv_eq_rough hp hinj hM r]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.assignmentRowWeight_inv_eq_rough
#print axioms Erdos4b.FGKMT.commonSieveCoefficient_quadratic_decomposition
