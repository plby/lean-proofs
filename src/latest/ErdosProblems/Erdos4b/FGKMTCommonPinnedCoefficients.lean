/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedAssignment
import ErdosProblems.Erdos4b.FGKMTInverseArithmetic
import ErdosProblems.Erdos4b.FGKMTCommonCoefficients

/-!
# The actual common coefficients with one prime coordinate pinned

There are `m+1` original coordinates and `m` unpinned coordinates.
The pin may be any original coordinate. No coefficient or profile is
replaced: the pinned amplitude is the inverse of the restricted vector.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

def commonPinnedCoefficient (m R : ℕ) (p : α → ℕ) (j : Fin (m + 1))
    (d : α → Option (Fin m)) : ℝ :=
  commonSieveCoefficient (m + 1) R p (mapPrimeAssignment j.succAboveEmb d)

def commonPinnedProfile (m R : ℕ) (p : α → ℕ) (j : Fin (m + 1))
    (r : α → Option (Fin m)) : ℝ :=
  pinnedProfileTransform (fun q => (p q : ℝ)) j.succAboveEmb
    (primeAssignmentProfile (m + 1) R p) r

omit [DecidableEq α] in
theorem commonPinnedRowWeight_pos {m : ℕ} {p : α → ℕ}
    (hp : ∀ q, m + 1 < p q) (r : α → Option (Fin m)) :
    0 < assignmentRowWeight (fun q => (p q : ℝ) - 1) r := by
  apply Finset.prod_pos
  intro q _hq
  cases r q with
  | none => exact zero_lt_one
  | some i =>
    change 0 < (p q : ℝ) - 1 - Fintype.card (Fin m)
    simp only [Fintype.card_fin]
    have hq : (m : ℝ) + 1 < p q := by exact_mod_cast hp q
    linarith

theorem commonPinnedCoefficient_eq_normalized {m R : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hlarge : ∀ q, m + 1 < p q) (j : Fin (m + 1)) :
    commonPinnedCoefficient m R p j =
      normalizedCoefficientTransform (fun q => (p q : ℝ) - 1)
        (commonPinnedProfile m R p j) := by
  have hv : ∀ q, (p q : ℝ) - 1 ≠ 0 := fun q =>
    (sub_pos.mpr (by exact_mod_cast (hp q).one_lt)).ne'
  exact (normalizedCoefficient_pinned_recovery hv
    (fun r => (commonPinnedRowWeight_pos hlarge r).ne') j.succAboveEmb
      (primeAssignmentProfile (m + 1) R p)).symm

theorem commonPinnedProfile_eq_product {m R : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (j : Fin (m + 1)) (r : α → Option (Fin m)) :
    commonPinnedProfile m R p j r =
      ∑ s, (∏ q, localPinnedProfileKernel (p q) j.succAboveEmb (r q) (s q)) *
        primeAssignmentProfile (m + 1) R p s := by
  apply pinnedProfileTransform_eq_product
  intro q
  exact (sub_pos.mpr (by exact_mod_cast (hp q).one_lt)).ne'

open scoped Classical in
theorem commonPinnedProfile_eq_moebius_totient {m R : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (j : Fin (m + 1)) (r : α → Option (Fin m)) :
    commonPinnedProfile m R p j r =
      (ArithmeticFunction.moebius (assignmentPrimeProduct p r) : ℝ) *
        assignmentRowWeight (fun q => (p q : ℝ) - 1) r *
        ∑ d, if ∀ i, assignmentPrimeTuple p r i ∣ assignmentPrimeTuple p d i then
          commonPinnedCoefficient m R p j d / (assignmentPrimeProduct p d).totient else 0 := by
  unfold commonPinnedProfile pinnedProfileTransform
  rw [finiteInverseCoefficientTransform_eq_moebius_totient hp hinj]
  dsimp only [commonPinnedCoefficient, commonSieveCoefficient]
  ring

theorem commonPinnedCoefficient_quadratic_decomposition {m R : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hlarge : ∀ q, m + 1 < p q) (j : Fin (m + 1)) :
    finiteSieveQuadratic (fun q => (p q : ℝ) - 1) (commonPinnedCoefficient m R p j) =
      (∑ r, (commonPinnedProfile m R p j r) ^ 2 /
        assignmentRowWeight (fun q => (p q : ℝ) - 1) r) +
      ∑ r, ∑ s, commonPinnedProfile m R p j r *
        (commonPinnedProfile m R p j s - commonPinnedProfile m R p j r) *
          assignmentQuadraticKernel (fun q => (p q : ℝ) - 1) r s /
            (assignmentRowWeight (fun q => (p q : ℝ) - 1) r *
              assignmentRowWeight (fun q => (p q : ℝ) - 1) s) := by
  rw [commonPinnedCoefficient_eq_normalized hp hlarge]
  apply normalizedCoefficientTransform_diagonal_error
  intro q
  exact (sub_pos.mpr (by exact_mod_cast (hp q).one_lt)).ne'

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPinnedProfile_eq_moebius_totient
#print axioms Erdos4b.FGKMT.commonPinnedProfile_eq_product
#print axioms Erdos4b.FGKMT.commonPinnedCoefficient_quadratic_decomposition
