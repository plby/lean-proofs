/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import DedekindResidue.ExplicitFormula.GRHZeros

/-!
# The continued Dedekind zeta function

AINTLIB constructs the completed Dedekind zeta function and, more usefully at its two
poles, the entire function extending `s * (s - 1) * Λₖ(s)`.  This file divides that
entire function by the elementary factors and by the completion prefactor.  The reciprocal
Gamma factors are entire, including at their zeros, so this gives a genuine analytic
continuation of mathlib's raw `NumberField.dedekindZeta` away from `0` and `1`.

At `1` the total function representing the meromorphic continuation necessarily contains
a junk value.  `continuedDedekindZetaOneRegularized` is the analytic extension of
`(s - 1) * continuedDedekindZeta K s` across that pole.
-/

namespace Erdos980.NaturalChebotarev.ContinuedZeta

open Complex NumberField NumberField.InfinitePlace

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The reciprocal of the completion prefactor, written with reciprocal Gamma factors.
This expression, unlike a proof through differentiability of `Gamma`, is visibly entire
at the nonpositive integers. -/
def completedZetaPrefactorInv (s : ℂ) : ℂ :=
  (((|discr K| : ℝ) : ℂ) ^ (s / 2))⁻¹
    * ((Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K)

/-- The explicit reciprocal prefactor agrees everywhere with field inversion of AINTLIB's
completion prefactor. -/
theorem completedZetaPrefactorInv_eq_inv (s : ℂ) :
    completedZetaPrefactorInv K s =
      (DedekindResidue.completedZetaPrefactor K s)⁻¹ := by
  rw [completedZetaPrefactorInv, DedekindResidue.completedZetaPrefactor,
    DedekindResidue.gammaFactor, mul_inv, mul_inv, inv_pow, inv_pow]

/-- The reciprocal completion prefactor is entire.  This is the key point that makes the
quotient usable at the trivial zeros. -/
theorem differentiable_completedZetaPrefactorInv :
    Differentiable ℂ (completedZetaPrefactorInv K) := by
  have hdiscr : (((|discr K| : ℝ) : ℂ)) ≠ 0 := by
    simp only [ne_eq, ofReal_eq_zero]
    have := discr_ne_zero K
    positivity
  have hcpow : Differentiable ℂ
      (fun s : ℂ ↦ ((|discr K| : ℝ) : ℂ) ^ (s / 2)) :=
    (differentiable_id.div_const 2).const_cpow (Or.inl hdiscr)
  have hcpow_ne : ∀ s : ℂ, ((|discr K| : ℝ) : ℂ) ^ (s / 2) ≠ 0 := by
    intro s
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl hdiscr
  exact (hcpow.inv hcpow_ne).mul
    (differentiable_Gammaℝ_inv.pow _ |>.mul (differentiable_Gammaℂ_inv.pow _))

/-- The completion prefactor is nonzero in the open right half-plane. -/
theorem completedZetaPrefactor_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DedekindResidue.completedZetaPrefactor K s ≠ 0 := by
  rw [DedekindResidue.completedZetaPrefactor]
  refine mul_ne_zero ?_ (DedekindResidue.gammaFactor_ne_zero_of_re_pos K hs)
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  left
  simp only [ofReal_eq_zero]
  have := discr_ne_zero K
  positivity

/-- The meromorphic continuation of the raw Dedekind zeta function.  The numerator is
AINTLIB's entire extension of `s * (s - 1) * Λₖ(s)`; reciprocal Gamma factors perform
the cancellations at the trivial zeros. -/
def continuedDedekindZeta (s : ℂ) : ℂ :=
  DedekindResidue.completedDedekindZetaEntire K s / (s * (s - 1))
    * completedZetaPrefactorInv K s

/-- Away from the two poles, the continuation is exactly completed zeta divided by its
completion prefactor. -/
theorem continuedDedekindZeta_eq_completed_div_prefactor {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    continuedDedekindZeta K s =
      DedekindResidue.completedDedekindZeta K s /
        DedekindResidue.completedZetaPrefactor K s := by
  rw [continuedDedekindZeta, completedZetaPrefactorInv_eq_inv,
    DedekindResidue.completedDedekindZetaEntire_eq K hs0 hs1]
  rw [mul_div_cancel_left₀ _ (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)), div_eq_mul_inv]

/-- On the half-plane of absolute convergence, the continuation is mathlib's raw
Dedekind zeta function. -/
theorem continuedDedekindZeta_eq_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    continuedDedekindZeta K s = NumberField.dedekindZeta K s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at hs
  rw [continuedDedekindZeta_eq_completed_div_prefactor K hs0 hs1,
    DedekindResidue.completedDedekindZeta_eq_of_one_lt_re K hs]
  exact mul_div_cancel_left₀ _
    (completedZetaPrefactor_ne_zero_of_re_pos K (zero_lt_one.trans hs))

/-- The continued Dedekind zeta function is complex differentiable away from its two
possible simple poles. -/
theorem differentiableAt_continuedDedekindZeta {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (continuedDedekindZeta K) s := by
  change DifferentiableAt ℂ (fun z : ℂ ↦
    DedekindResidue.completedDedekindZetaEntire K z / (z * (z - 1))
      * completedZetaPrefactorInv K z) s
  exact (((DedekindResidue.differentiable_completedDedekindZetaEntire K) s).div
    (differentiableAt_id.mul (differentiableAt_id.sub_const 1))
    (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))).mul
      (differentiable_completedZetaPrefactorInv K s)

/-- The continued Dedekind zeta function is analytic at every point other than `0` and
`1`. -/
theorem analyticAt_continuedDedekindZeta {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (continuedDedekindZeta K) s := by
  change AnalyticAt ℂ (fun z : ℂ ↦
    DedekindResidue.completedDedekindZetaEntire K z / (z * (z - 1))
      * completedZetaPrefactorInv K z) s
  exact (((DedekindResidue.differentiable_completedDedekindZetaEntire K).analyticAt s).div
    (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
    (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))).mul
      ((differentiable_completedZetaPrefactorInv K).analyticAt s)

/-- Set-level form of analyticity away from `0` and `1`. -/
theorem analyticOnNhd_continuedDedekindZeta :
    AnalyticOnNhd ℂ (continuedDedekindZeta K) {s : ℂ | s ≠ 0 ∧ s ≠ 1} := by
  intro s hs
  exact analyticAt_continuedDedekindZeta K hs.1 hs.2

/-- The analytic extension across `1` of `(s - 1) * continuedDedekindZeta K s`. -/
def continuedDedekindZetaOneRegularized (s : ℂ) : ℂ :=
  DedekindResidue.completedDedekindZetaEntire K s / s * completedZetaPrefactorInv K s

/-- The one-pole regularization is differentiable away from `0`, in particular at `1`. -/
theorem differentiableAt_continuedDedekindZetaOneRegularized {s : ℂ} (hs0 : s ≠ 0) :
    DifferentiableAt ℂ (continuedDedekindZetaOneRegularized K) s := by
  change DifferentiableAt ℂ (fun z : ℂ ↦
    DedekindResidue.completedDedekindZetaEntire K z / z
      * completedZetaPrefactorInv K z) s
  exact (((DedekindResidue.differentiable_completedDedekindZetaEntire K) s).div
    differentiableAt_id hs0).mul (differentiable_completedZetaPrefactorInv K s)

/-- The regularized function is analytic at `1`. -/
theorem analyticAt_continuedDedekindZetaOneRegularized_one :
    AnalyticAt ℂ (continuedDedekindZetaOneRegularized K) 1 := by
  change AnalyticAt ℂ (fun z : ℂ ↦
    DedekindResidue.completedDedekindZetaEntire K z / z
      * completedZetaPrefactorInv K z) 1
  exact (((DedekindResidue.differentiable_completedDedekindZetaEntire K).analyticAt 1).div
    analyticAt_id one_ne_zero).mul
      ((differentiable_completedZetaPrefactorInv K).analyticAt 1)

/-- Off the pole (and the reflected pole at `0`), the regularized function has its
expected value. -/
theorem continuedDedekindZetaOneRegularized_eq {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    continuedDedekindZetaOneRegularized K s =
      (s - 1) * continuedDedekindZeta K s := by
  rw [continuedDedekindZetaOneRegularized, continuedDedekindZeta]
  field_simp [hs0, sub_ne_zero.mpr hs1]

/-- The analytic regularization is nonzero at `1`; hence the continuation has a genuine
simple pole there. -/
theorem continuedDedekindZetaOneRegularized_one_ne_zero :
    continuedDedekindZetaOneRegularized K 1 ≠ 0 := by
  rw [continuedDedekindZetaOneRegularized, div_one]
  refine mul_ne_zero
    (DedekindResidue.completedDedekindZetaEntire_one_ne_zero K) ?_
  rw [completedZetaPrefactorInv_eq_inv]
  exact inv_ne_zero (completedZetaPrefactor_ne_zero_of_re_pos K (by norm_num))

end

end Erdos980.NaturalChebotarev.ContinuedZeta
