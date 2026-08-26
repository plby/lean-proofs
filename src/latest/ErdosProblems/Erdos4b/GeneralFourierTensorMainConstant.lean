/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTensorSquareAsymptotic
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# The tensor-square constant as a variational integral

Finite-dimensional Fubini identifies the sum of pairwise derivative
integrals with the integral of the squared mixed derivative of the
finite tensor combination on the positive orthant.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory
open scoped BigOperators ContDiff

theorem integrable_deriv_mul_deriv_Ioi
    (F G : ℝ → ℂ) (hF : HasCompactSupport F)
    (hFs : ContDiff ℝ ∞ F) (hGs : ContDiff ℝ ∞ G) :
    Integrable (fun t ↦ deriv F t * deriv G t) (volume.restrict (Set.Ioi 0)) := by
  have hcont : Continuous (fun t ↦ deriv F t * deriv G t) :=
    (hFs.continuous_deriv (by simp)).mul (hGs.continuous_deriv (by simp))
  have hcompact : HasCompactSupport (fun t ↦ deriv F t * deriv G t) := hF.deriv.mul_right
  exact (hcont.integrable_of_hasCompactSupport hcompact).integrableOn

theorem integrable_derivative_pair_tensor {ι : Type*} [Fintype ι]
    (F G : ι → ℝ → ℂ) (hF : ∀ i, HasCompactSupport (F i))
    (hFs : ∀ i, ContDiff ℝ ∞ (F i)) (hGs : ∀ i, ContDiff ℝ ∞ (G i)) :
    Integrable (fun t : ι → ℝ ↦ ∏ i, deriv (F i) (t i) * deriv (G i) (t i))
      (Measure.pi (fun _ : ι ↦ volume.restrict (Set.Ioi 0 : Set ℝ))) := by
  exact Integrable.fintype_prod fun i ↦
    integrable_deriv_mul_deriv_Ioi (F i) (G i) (hF i) (hFs i) (hGs i)

theorem integral_derivative_pair_tensor {ι : Type*} [Fintype ι]
    (F G : ι → ℝ → ℂ) :
    (∫ t : ι → ℝ, (∏ i, deriv (F i) (t i) * deriv (G i) (t i))
      ∂(Measure.pi (fun _ : ι ↦ volume.restrict (Set.Ioi 0 : Set ℝ)))) =
      ∏ i, ∫ t : ℝ in Set.Ioi 0, deriv (F i) t * deriv (G i) t :=
  integral_fintype_prod_eq_prod (fun i t ↦ deriv (F i) t * deriv (G i) t)

theorem integral_tensor_sum_square_eq_pair_sum
    {ι J : Type*} [Fintype ι] (S : Finset J) (F : J → ι → ℝ → ℂ)
    (hcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (hsmooth : ∀ j ∈ S, ∀ i, ContDiff ℝ ∞ (F j i)) :
    (∫ t : ι → ℝ, (∑ j ∈ S, ∏ i, deriv (F j i) (t i)) ^ 2
      ∂(Measure.pi (fun _ : ι ↦ volume.restrict (Set.Ioi 0 : Set ℝ)))) =
      ∑ j ∈ S, ∑ k ∈ S, ∏ i,
        ∫ t : ℝ in Set.Ioi 0, deriv (F j i) t * deriv (F k i) t := by
  have hint (j : J) (hj : j ∈ S) (k : J) (hk : k ∈ S) :=
    integrable_derivative_pair_tensor (F j) (F k) (hcompact j hj) (hsmooth j hj) (hsmooth k hk)
  have hid (t : ι → ℝ) :
      (∑ j ∈ S, ∏ i, deriv (F j i) (t i)) ^ 2 =
        ∑ j ∈ S, ∑ k ∈ S, ∏ i, deriv (F j i) (t i) * deriv (F k i) (t i) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact (Finset.prod_mul_distrib).symm
  simp_rw [hid]
  rw [integral_finsetSum S (fun j hj ↦ integrable_finsetSum S fun k hk ↦ hint j hj k hk)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finsetSum S (fun k hk ↦ hint j hj k hk)]
  apply Finset.sum_congr rfl
  intro k hk
  exact integral_derivative_pair_tensor (F j) (F k)

theorem selbergTensorSquareMainConstant_eq_integral
    {ι J : Type*} [Fintype ι]
    (S : Finset J) (F : J → (ι ⊕ ι) → ℝ → ℂ)
    (hcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (hsmooth : ∀ j ∈ S, ∀ i, ContDiff ℝ ∞ (F j i)) :
    selbergTensorSquareMainConstant S F =
      ∫ t : (ι ⊕ ι) → ℝ in Set.univ.pi (fun _ ↦ Set.Ioi 0),
        (∑ j ∈ S, ∏ i, deriv (F j i) (t i)) ^ 2 := by
  change _ = ∫ t : (ι ⊕ ι) → ℝ, _
    ∂((Measure.pi fun _ : ι ⊕ ι ↦ (volume : Measure ℝ)).restrict
      (Set.univ.pi (fun _ ↦ Set.Ioi 0)))
  rw [Measure.restrict_pi_pi]
  exact (integral_tensor_sum_square_eq_pair_sum S F hcompact hsmooth).symm

end

end Erdos4b
