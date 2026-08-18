/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterKernelParameters

/-!
# The localized Fourier polynomial

Subtracting half of the zero coefficient makes the cosine kernel
nonpositive outside the target torus ball while retaining a positive mean.
-/

open Set Function MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate

namespace Erdos984

noncomputable section

def kernelZeroTuple {D : Type*} (k : ℕ) : D → HunterKernelDigit k :=
  fun _ ↦ kernelZeroDigit k

@[simp] lemma kernelFrequency_zeroTuple {D : Type*} (k : ℕ) :
    kernelFrequency k (kernelZeroTuple (D := D) k) = 0 := by
  funext j
  simp [kernelFrequency, kernelZeroTuple]

lemma decodeKernelDigit_injective (k : ℕ) :
    Function.Injective (decodeKernelDigit k) := by
  intro q q' h
  apply Fin.ext
  simp only [decodeKernelDigit] at h
  omega

lemma kernelFrequency_injective {D : Type*} (k : ℕ) :
    Function.Injective (kernelFrequency (D := D) k) := by
  intro q q' h
  funext j
  apply decodeKernelDigit_injective k
  exact congrFun h j

@[simp] lemma kernelCoeff_zeroTuple {D : Type*} [Fintype D] (k : ℕ) :
    kernelCoeff k (kernelZeroTuple (D := D) k) = kernelMean1 k ^ Fintype.card D := by
  simp [kernelCoeff, kernelZeroTuple, Finset.prod_const]

lemma kernelCoeff_le_mean {D : Type*} [Fintype D] (k : ℕ)
    (q : D → HunterKernelDigit k) :
    kernelCoeff k q ≤ kernelMean1 k ^ Fintype.card D := by
  have h := Finset.prod_le_prod (s := (Finset.univ : Finset D))
    (fun j _hj ↦ kernelDigitCoeff_nonneg k (q j))
    (fun j _hj ↦ kernelDigitCoeff_le_mean k (q j))
  simpa [kernelCoeff] using h

/-- Complex-valued localized kernel.  It is real-valued, but the complex
form makes character orthogonality immediate. -/
def hunterLocalizedKernel (D : ℕ) (x : UnitAddTorus (Fin D)) : ℂ :=
  torusCosineKernel (hunterKernelPower D) x - hunterKernelCutoff D

/-- Fourier coefficient of the localized kernel. -/
def hunterLocalizedCoeff (D : ℕ)
    (q : Fin D → HunterKernelDigit (hunterKernelPower D)) : ℝ :=
  kernelCoeff (hunterKernelPower D) q -
    if q = kernelZeroTuple (hunterKernelPower D) then hunterKernelCutoff D else 0

@[simp] lemma hunterLocalizedCoeff_zero (D : ℕ) :
    hunterLocalizedCoeff D (kernelZeroTuple (D := Fin D) (hunterKernelPower D)) =
      hunterKernelMean D / 2 := by
  rw [hunterLocalizedCoeff, if_pos rfl, kernelCoeff_zeroTuple]
  simp only [hunterKernelMean, Fintype.card_fin, hunterKernelCutoff]
  ring

lemma hunterLocalizedCoeff_of_ne_zero (D : ℕ)
    {q : Fin D → HunterKernelDigit (hunterKernelPower D)}
    (hq : q ≠ kernelZeroTuple (hunterKernelPower D)) :
    hunterLocalizedCoeff D q = kernelCoeff (hunterKernelPower D) q := by
  simp [hunterLocalizedCoeff, hq]

lemma hunterLocalizedCoeff_nonneg (D : ℕ)
    (q : Fin D → HunterKernelDigit (hunterKernelPower D)) :
    0 ≤ hunterLocalizedCoeff D q := by
  by_cases hq : q = kernelZeroTuple (hunterKernelPower D)
  · subst q
    rw [hunterLocalizedCoeff_zero]
    exact div_nonneg (hunterKernelMean_pos D).le (by norm_num)
  · rw [hunterLocalizedCoeff_of_ne_zero D hq]
    exact kernelCoeff_nonneg _ _

lemma hunterLocalizedCoeff_le_mean (D : ℕ)
    (q : Fin D → HunterKernelDigit (hunterKernelPower D)) :
    hunterLocalizedCoeff D q ≤ hunterKernelMean D := by
  by_cases hq : q = kernelZeroTuple (hunterKernelPower D)
  · subst q
    rw [hunterLocalizedCoeff_zero]
    exact div_le_self (hunterKernelMean_pos D).le (by norm_num : (1 : ℝ) ≤ 2)
  · rw [hunterLocalizedCoeff_of_ne_zero D hq]
    simpa only [hunterKernelMean, Fintype.card_fin] using
      kernelCoeff_le_mean (D := Fin D) (hunterKernelPower D) q

/-- Exact Fourier expansion after subtracting the cutoff. -/
lemma sum_hunterLocalizedCoeff_torusFourier (D : ℕ)
    (x : UnitAddTorus (Fin D)) :
    ∑ q : Fin D → HunterKernelDigit (hunterKernelPower D),
      (hunterLocalizedCoeff D q : ℂ) *
        torusFourier (kernelFrequency (hunterKernelPower D) q) x =
      hunterLocalizedKernel D x := by
  classical
  rw [hunterLocalizedKernel, ← sum_kernelCoeff_torusFourier]
  simp only [hunterLocalizedCoeff]
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_eq_single
    (kernelZeroTuple (D := Fin D) (hunterKernelPower D))]
  · simp only [kernelFrequency_zeroTuple, if_true]
    change (hunterKernelCutoff D : ℂ) *
      torusFourier (fun _ : Fin D ↦ (0 : ℤ)) x = _
    rw [torusFourier_zero]
    ring
  · intro q _hq hq
    simp [hq]
  · simp

lemma sum_hunterLocalizedCoeff (D : ℕ) :
    ∑ q : Fin D → HunterKernelDigit (hunterKernelPower D),
      hunterLocalizedCoeff D q = 1 - hunterKernelCutoff D := by
  have h := sum_hunterLocalizedCoeff_torusFourier D
    (0 : UnitAddTorus (Fin D))
  have hcircle : circleCosSq (0 : UnitAddCircle) = 1 := by
    simpa using circleCosSq_coe 0
  have hkernel : torusCosineKernel (hunterKernelPower D)
      (0 : UnitAddTorus (Fin D)) = 1 := by
    simp [torusCosineKernel, hcircle]
  have hfourier (xi : Fin D → ℤ) :
      torusFourier xi (0 : UnitAddTorus (Fin D)) = 1 := by
    simp [torusFourier]
  rw [hunterLocalizedKernel] at h
  simp_rw [hfourier] at h
  rw [hkernel] at h
  have hre := congrArg Complex.re h
  simpa using hre

lemma sum_hunterLocalizedCoeff_le_one (D : ℕ) :
    ∑ q : Fin D → HunterKernelDigit (hunterKernelPower D),
      hunterLocalizedCoeff D q ≤ 1 := by
  rw [sum_hunterLocalizedCoeff]
  exact sub_le_self _ (hunterKernelCutoff_pos D).le

lemma sum_sq_hunterLocalizedCoeff_le_mean (D : ℕ) :
    ∑ q : Fin D → HunterKernelDigit (hunterKernelPower D),
      hunterLocalizedCoeff D q ^ 2 ≤ hunterKernelMean D := by
  calc
    ∑ q : Fin D → HunterKernelDigit (hunterKernelPower D),
        hunterLocalizedCoeff D q ^ 2 ≤
        ∑ q : Fin D → HunterKernelDigit (hunterKernelPower D),
          hunterKernelMean D * hunterLocalizedCoeff D q := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hunterLocalizedCoeff_le_mean D q)
        (hunterLocalizedCoeff_nonneg D q)
    _ = hunterKernelMean D *
        (∑ q : Fin D → HunterKernelDigit (hunterKernelPower D),
          hunterLocalizedCoeff D q) := by rw [Finset.mul_sum]
    _ ≤ hunterKernelMean D * 1 := by
      exact mul_le_mul_of_nonneg_left (sum_hunterLocalizedCoeff_le_one D)
        (hunterKernelMean_pos D).le
    _ = hunterKernelMean D := mul_one _

lemma hunterLocalizedKernel_im (D : ℕ) (x : UnitAddTorus (Fin D)) :
    (hunterLocalizedKernel D x).im = 0 := by
  rw [hunterLocalizedKernel, Complex.sub_im, torusCosineKernel_real]
  simp

lemma hunterLocalizedKernel_re (D : ℕ) (x : UnitAddTorus (Fin D)) :
    (hunterLocalizedKernel D x).re =
      (torusCosineKernel (hunterKernelPower D) x).re - hunterKernelCutoff D := by
  simp [hunterLocalizedKernel]

lemma hunterLocalizedKernel_re_nonpos_of_lt_norm
    (D : ℕ) (hD : 4 ≤ D) (x : UnitAddTorus (Fin D))
    (hx : hunterRho D < ‖x‖) :
    (hunterLocalizedKernel D x).re ≤ 0 := by
  rw [hunterLocalizedKernel_re]
  linarith [torusCosineKernel_re_le_cutoff_of_lt_norm D hD x hx]

lemma hunterLocalizedKernel_re_nonpos_of_rho_sq_le_squaredNorm
    (D : ℕ) (hD : 4 ≤ D) (x : UnitAddTorus (Fin D))
    (hx : hunterRho D ^ 2 ≤ squaredNorm (centeredTorusLift x)) :
    (hunterLocalizedKernel D x).re ≤ 0 := by
  rw [hunterLocalizedKernel_re]
  linarith [torusCosineKernel_re_le_cutoff_of_rho_sq_le_squaredNorm D hD x hx]

end

end Erdos984
