/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTLocalQuadratic

/-!
# The exact finite common-coefficient quadratic transform

All assignments range over a genuine finite function space. Expanding
the coefficients and distributing products gives the product of the
checked local kernels, including all cross-coordinate zero factors.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [DecidableEq α] [Fintype α] [DecidableEq ι] [Fintype ι]

def assignmentCoeffKernel (v : α → ℝ) (d r : α → Option ι) : ℝ :=
  ∏ p, localDivisorCoeff (v p) (d p) (r p)

def assignmentCrtKernel (v : α → ℝ) (d e : α → Option ι) : ℝ :=
  ∏ p, localCrtDensity (v p) (d p) (e p)

def assignmentQuadraticKernel (v : α → ℝ) (r s : α → Option ι) : ℝ :=
  ∏ p, localQuadraticKernel (v p) (r p) (s p)

def assignmentRowWeight (v : α → ℝ) (r : α → Option ι) : ℝ :=
  ∏ p, localRowWeight (v p) (r p)

def finiteCoefficientTransform (v : α → ℝ) (Y : (α → Option ι) → ℝ)
    (d : α → Option ι) : ℝ :=
  ∑ r, assignmentCoeffKernel v d r * Y r

def finiteSieveQuadratic (v : α → ℝ) (l : (α → Option ι) → ℝ) : ℝ :=
  ∑ d, ∑ e, l d * l e * assignmentCrtKernel v d e

theorem assignmentQuadraticKernel_eq_contraction {v : α → ℝ} (hv : ∀ p, v p ≠ 0)
    (r s : α → Option ι) :
    (∑ d : α → Option ι, ∑ e : α → Option ι,
      assignmentCoeffKernel v d r * assignmentCoeffKernel v e s * assignmentCrtKernel v d e) =
        assignmentQuadraticKernel v r s := by
  calc
    _ = ∑ d : α → Option ι, ∑ e : α → Option ι,
        ∏ p, localDivisorCoeff (v p) (d p) (r p) *
          localDivisorCoeff (v p) (e p) (s p) * localCrtDensity (v p) (d p) (e p) := by
      simp only [assignmentCoeffKernel, assignmentCrtKernel, Finset.prod_mul_distrib]
    _ = ∑ d : α → Option ι, ∏ p, ∑ e : Option ι,
        localDivisorCoeff (v p) (d p) (r p) *
          localDivisorCoeff (v p) e (s p) * localCrtDensity (v p) (d p) e := by
      apply Finset.sum_congr rfl
      intro d _hd
      exact (Fintype.prod_sum (fun p e => localDivisorCoeff (v p) (d p) (r p) *
        localDivisorCoeff (v p) e (s p) * localCrtDensity (v p) (d p) e)).symm
    _ = ∏ p, ∑ d : Option ι, ∑ e : Option ι,
        localDivisorCoeff (v p) d (r p) *
          localDivisorCoeff (v p) e (s p) * localCrtDensity (v p) d e :=
      (Fintype.prod_sum (fun p d => ∑ e : Option ι,
        localDivisorCoeff (v p) d (r p) *
          localDivisorCoeff (v p) e (s p) * localCrtDensity (v p) d e)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p _hp
      rw [localQuadraticKernel_eq_contraction (hv p)]
      simp only [Finset.mul_sum, mul_assoc]

theorem finiteSieveQuadratic_transform {v : α → ℝ} (hv : ∀ p, v p ≠ 0)
    (Y : (α → Option ι) → ℝ) :
    finiteSieveQuadratic v (finiteCoefficientTransform v Y) =
      ∑ r, ∑ s, Y r * Y s * assignmentQuadraticKernel v r s := by
  let T := fun (d e r s : α → Option ι) =>
    (assignmentCoeffKernel v d r * Y r) *
      (assignmentCoeffKernel v e s * Y s) * assignmentCrtKernel v d e
  calc
    _ = ∑ d, ∑ e, ∑ r, ∑ s, T d e r s := by
      simp only [finiteSieveQuadratic, finiteCoefficientTransform, T,
        Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      rw [Finset.sum_comm]
    _ = ∑ d, ∑ r, ∑ e, ∑ s, T d e r s := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_comm]
    _ = ∑ r, ∑ d, ∑ e, ∑ s, T d e r s := by rw [Finset.sum_comm]
    _ = ∑ r, ∑ d, ∑ s, ∑ e, T d e r s := by
      apply Finset.sum_congr rfl
      intro r _hr
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_comm]
    _ = ∑ r, ∑ s, ∑ d, ∑ e, T d e r s := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Finset.sum_comm]
    _ = ∑ r, ∑ s, (Y r * Y s) *
        ∑ d, ∑ e, assignmentCoeffKernel v d r * assignmentCoeffKernel v e s *
          assignmentCrtKernel v d e := by
      apply Finset.sum_congr rfl
      intro r _hr
      apply Finset.sum_congr rfl
      intro s _hs
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      dsimp only [T]
      ring
    _ = _ := by simp only [assignmentQuadraticKernel_eq_contraction hv]

theorem sum_assignmentQuadraticKernel (v : α → ℝ) (r : α → Option ι) :
    (∑ s, assignmentQuadraticKernel v r s) = assignmentRowWeight v r := by
  unfold assignmentQuadraticKernel assignmentRowWeight
  rw [← Fintype.prod_sum]
  simp only [sum_localQuadraticKernel]

omit [DecidableEq α] in
theorem assignmentRowWeight_eq_of_kernel_ne_zero (v : α → ℝ) {r s : α → Option ι}
    (h : assignmentQuadraticKernel v r s ≠ 0) :
    assignmentRowWeight v r = assignmentRowWeight v s := by
  apply Finset.prod_congr rfl
  intro p hp
  exact localRowWeight_eq_of_kernel_ne_zero (v p) ((Finset.prod_ne_zero_iff.mp h) p hp)

theorem finiteSieveQuadratic_diagonal_error {v : α → ℝ} (hv : ∀ p, v p ≠ 0)
    (Y : (α → Option ι) → ℝ) :
    finiteSieveQuadratic v (finiteCoefficientTransform v Y) =
      (∑ r, Y r ^ 2 * assignmentRowWeight v r) +
        ∑ r, ∑ s, Y r * (Y s - Y r) * assignmentQuadraticKernel v r s := by
  rw [finiteSieveQuadratic_transform hv]
  calc
    _ = ∑ r, (Y r ^ 2 * assignmentRowWeight v r +
        ∑ s, Y r * (Y s - Y r) * assignmentQuadraticKernel v r s) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [← sum_assignmentQuadraticKernel v r, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _hs
      ring
    _ = _ := Finset.sum_add_distrib

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.assignmentQuadraticKernel_eq_contraction
#print axioms Erdos4b.FGKMT.finiteSieveQuadratic_diagonal_error
