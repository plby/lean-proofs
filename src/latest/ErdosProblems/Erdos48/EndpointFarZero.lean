/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.EndpointZeroKernelMean
import BoundedGaps.BombieriVinogradov.Analytic.DirichletZeroReciprocalSum

/-!
# The far-left endpoint zero-kernel remainder

Zeros with real part at most a fixed `alpha`, where `alpha >= 1/2`, have an
explicit-formula kernel bounded by `12 x^alpha / (1+|gamma|)`.  The standard
reciprocal-height multiplicity estimate then controls the complete far-left
remainder uniformly over primitive conductors.
-/

namespace Erdos48

open Complex
open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

/-- A source-shaped kernel bound at an arbitrary real-part cutoff at least
one half. -/
theorem norm_dirichletExplicitFormulaKernel_le_of_re_le
    {x alpha : ℝ} {rho : ℂ}
    (hx : 4 ≤ x) (halpha : 1 / 2 ≤ alpha)
    (hzeroRe : 0 < rho.re) (hre : rho.re ≤ alpha) :
    ‖dirichletExplicitFormulaKernel x rho‖ ≤
      12 * x ^ alpha / (1 + |rho.im|) := by
  let g : ℝ := |rho.im|
  have hxone : (1 : ℝ) ≤ x := by linarith
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hbeta0 : 0 ≤ rho.re := hzeroRe.le
  have hpow : x ^ rho.re ≤ x ^ alpha :=
    Real.rpow_le_rpow_of_exponent_le hxone hre
  have hpowOne : (1 : ℝ) ≤ x ^ rho.re := by
    calc
      (1 : ℝ) = x ^ (0 : ℝ) := (Real.rpow_zero x).symm
      _ ≤ x ^ rho.re :=
        Real.rpow_le_rpow_of_exponent_le hxone hbeta0
  have hrhoNe : rho ≠ 0 := by
    intro hrho
    subst rho
    norm_num at hzeroRe
  have hnormrho : 0 < ‖rho‖ := norm_pos_iff.mpr hrhoNe
  have hquot :
      ‖dirichletExplicitFormulaKernel x rho‖ ≤
        (x ^ rho.re + 1) / ‖rho‖ := by
    rw [dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hxpos hrhoNe,
      norm_div]
    apply div_le_div_of_nonneg_right _ hnormrho.le
    calc
      ‖(x : ℂ) ^ rho - 1‖ ≤ ‖(x : ℂ) ^ rho‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = x ^ rho.re + 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, norm_one]
  have hg0 : 0 ≤ g := abs_nonneg rho.im
  have hgden : 0 < 1 + g := by linarith
  apply (le_div_iff₀ hgden).2
  by_cases hbeta : rho.re ≤ 1 / 3
  · by_cases hgamma : g ≤ 1
    · have hkernel :=
        norm_dirichletExplicitFormulaKernel_le_rpow_mul_log hxone hbeta0
      have hlog6 : Real.log x ≤ 6 * x ^ (1 / 6 : ℝ) := by
        have h := Real.log_le_rpow_div hxpos.le
          (show (0 : ℝ) < 1 / 6 by norm_num)
        convert h using 1
        ring
      have hsum : rho.re + 1 / 6 ≤ alpha := by linarith
      have hpowsum : x ^ (rho.re + 1 / 6) ≤ x ^ alpha :=
        Real.rpow_le_rpow_of_exponent_le hxone hsum
      calc
        ‖dirichletExplicitFormulaKernel x rho‖ * (1 + g) ≤
            (x ^ rho.re * Real.log x) * (1 + g) :=
          mul_le_mul_of_nonneg_right hkernel (by linarith)
        _ ≤ (x ^ rho.re * (6 * x ^ (1 / 6 : ℝ))) * 2 := by
          gcongr
          linarith
        _ = 12 * x ^ (rho.re + 1 / 6) := by
          rw [show x ^ rho.re * (6 * x ^ (1 / 6 : ℝ)) * 2 =
            12 * (x ^ rho.re * x ^ (1 / 6 : ℝ)) by ring,
            ← Real.rpow_add hxpos]
        _ ≤ 12 * x ^ alpha :=
          mul_le_mul_of_nonneg_left hpowsum (by norm_num)
    · have hgOne : 1 < g := lt_of_not_ge hgamma
      have hgNorm : g ≤ ‖rho‖ := by
        simpa [g] using Complex.abs_im_le_norm rho
      have hdenLe : 1 + g ≤ 2 * ‖rho‖ := by nlinarith
      calc
        ‖dirichletExplicitFormulaKernel x rho‖ * (1 + g) ≤
            ((x ^ rho.re + 1) / ‖rho‖) * (1 + g) :=
          mul_le_mul_of_nonneg_right hquot (by linarith)
        _ ≤ ((x ^ rho.re + 1) / ‖rho‖) * (2 * ‖rho‖) := by gcongr
        _ = 2 * (x ^ rho.re + 1) := by field_simp [hnormrho.ne']
        _ ≤ 4 * x ^ rho.re := by nlinarith
        _ ≤ 12 * x ^ alpha := by nlinarith
  · have hbetaThird : 1 / 3 < rho.re := lt_of_not_ge hbeta
    have hreNorm : rho.re ≤ ‖rho‖ := by
      simpa [abs_of_pos hzeroRe] using Complex.abs_re_le_norm rho
    have himNorm : g ≤ ‖rho‖ := by
      simpa [g] using Complex.abs_im_le_norm rho
    have hdenLe : 1 + g ≤ 4 * ‖rho‖ := by nlinarith
    calc
      ‖dirichletExplicitFormulaKernel x rho‖ * (1 + g) ≤
          ((x ^ rho.re + 1) / ‖rho‖) * (1 + g) :=
        mul_le_mul_of_nonneg_right hquot (by linarith)
      _ ≤ ((x ^ rho.re + 1) / ‖rho‖) * (4 * ‖rho‖) := by gcongr
      _ = 4 * (x ^ rho.re + 1) := by field_simp [hnormrho.ne']
      _ ≤ 8 * x ^ rho.re := by nlinarith
      _ ≤ 12 * x ^ alpha := by nlinarith

/-- The far-left kernel for one primitive character is bounded by its full
reciprocal-height zero multiplicity. -/
theorem norm_primitiveFarZeroKernelSumAt_le_reciprocalMultiplicity
    {q : ℕ} [NeZero q] (hq : 1 < q) (psi : primitiveCharacters q)
    {x eta T : ℝ} {J : ℕ} (hx : 4 ≤ x)
    (halpha : 1 / 2 ≤ 1 - (((J + 1 : ℕ) : ℝ) * eta)) :
    ‖primitiveFarZeroKernelSumAt q psi x eta J T‖ ≤
      12 * x ^ (1 - (((J + 1 : ℕ) : ℝ) * eta)) *
        dirichletNontrivialZeroReciprocalMultiplicitySum psi.1 T := by
  rw [primitiveFarZeroKernelSumAt_eq hq,
    dirichletNontrivialZeroFarKernelSum]
  let S := (dirichletNontrivialLFunctionZerosFinset psi.1 T).filter
    (fun rho ↦ rho.re < 1 - (((J + 1 : ℕ) : ℝ) * eta))
  let C : ℝ := 12 * x ^ (1 - (((J + 1 : ℕ) : ℝ) * eta))
  let w : ℂ → ℝ := fun rho ↦
    (analyticOrderNatAt (DirichletCharacter.LFunction psi.1) rho : ℝ) /
      (1 + |rho.im|)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hterm : ∀ rho ∈ S,
      ‖(analyticOrderNatAt
          (DirichletCharacter.LFunction psi.1) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho‖ ≤ C * w rho := by
    intro rho hrho
    have hrhoData := Finset.mem_filter.mp hrho
    have hzero :=
      (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrhoData.1).1
    have hkernel := norm_dirichletExplicitFormulaKernel_le_of_re_le
      hx halpha hzero.2.1 hrhoData.2.le
    rw [norm_mul, Complex.norm_natCast]
    calc
      (analyticOrderNatAt
          (DirichletCharacter.LFunction psi.1) rho : ℝ) *
          ‖dirichletExplicitFormulaKernel x rho‖ ≤
        (analyticOrderNatAt
          (DirichletCharacter.LFunction psi.1) rho : ℝ) *
          (12 * x ^ (1 - (((J + 1 : ℕ) : ℝ) * eta)) /
            (1 + |rho.im|)) :=
        mul_le_mul_of_nonneg_left hkernel (by positivity)
      _ = C * w rho := by dsimp [C, w]; ring
  have hsubset : S ⊆ dirichletNontrivialLFunctionZerosFinset psi.1 T :=
    Finset.filter_subset _ _
  calc
    ‖∑ rho ∈ S,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction psi.1) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho‖ ≤
      ∑ rho ∈ S,
        ‖(analyticOrderNatAt
          (DirichletCharacter.LFunction psi.1) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho‖ := norm_sum_le _ _
    _ ≤ ∑ rho ∈ S, C * w rho := Finset.sum_le_sum hterm
    _ = C * ∑ rho ∈ S, w rho := by rw [Finset.mul_sum]
    _ ≤ C * ∑ rho ∈ dirichletNontrivialLFunctionZerosFinset psi.1 T,
        w rho := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun rho _ _ ↦ by dsimp [w]; positivity)) hC
    _ = 12 * x ^ (1 - (((J + 1 : ℕ) : ℝ) * eta)) *
        dirichletNontrivialZeroReciprocalMultiplicitySum psi.1 T := by
      rw [dirichletNontrivialZeroReciprocalMultiplicitySum]

/-- There is one absolute constant bounding the complete aggregate far-left
remainder through conductor `Q`. -/
theorem exists_nat_primitiveFarZeroKernelMass_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (Q : ℕ), 2 ≤ Q →
        ∀ (T : ℝ), 2 ≤ T →
          ∀ (x eta : ℝ) (J : ℕ), 4 ≤ x →
            1 / 2 ≤ 1 - (((J + 1 : ℕ) : ℝ) * eta) →
            primitiveFarZeroKernelMass Q x eta J T ≤
              (Q : ℝ) ^ 2 *
                (96 * (A : ℝ) *
                  x ^ (1 - (((J + 1 : ℕ) : ℝ) * eta)) *
                    Real.log ((Q : ℝ) * (T + 2)) ^ 2) := by
  obtain ⟨A, hA, hreciprocal⟩ :=
    exists_nat_dirichletNontrivialZeroReciprocalMultiplicitySum_le
  refine ⟨A, hA, ?_⟩
  intro Q hQ T hT x eta J hx halpha
  let C : ℝ := 96 * (A : ℝ) *
    x ^ (1 - (((J + 1 : ℕ) : ℝ) * eta)) *
      Real.log ((Q : ℝ) * (T + 2)) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint : ∀ q ∈ Finset.Ioc 1 Q,
      ∀ psi : primitiveCharacters q,
        ‖primitiveFarZeroKernelSumAt q psi x eta J T‖ ≤ C := by
    intro q hqMem psi
    have hq : 1 < q := (Finset.mem_Ioc.mp hqMem).1
    letI : NeZero q := ⟨by omega⟩
    have hkernel :=
      norm_primitiveFarZeroKernelSumAt_le_reciprocalMultiplicity
        (T := T) hq psi hx halpha
    have hrec := hreciprocal q psi.1 T hT
    have hqQ : (q : ℝ) ≤ Q := by
      exact_mod_cast (Finset.mem_Ioc.mp hqMem).2
    have hscalePos : 0 < (q : ℝ) * (T + 2) := by positivity
    have hscale : (q : ℝ) * (T + 2) ≤ (Q : ℝ) * (T + 2) := by
      gcongr
    have hlog := Real.log_le_log hscalePos hscale
    have hlog0 : 0 ≤ Real.log ((q : ℝ) * (T + 2)) := by
      apply Real.log_nonneg
      have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
    have hlogSq : Real.log ((q : ℝ) * (T + 2)) ^ 2 ≤
        Real.log ((Q : ℝ) * (T + 2)) ^ 2 := by
      nlinarith [sq_nonneg (Real.log ((Q : ℝ) * (T + 2)) -
        Real.log ((q : ℝ) * (T + 2)))]
    calc
      ‖primitiveFarZeroKernelSumAt q psi x eta J T‖ ≤
          12 * x ^ (1 - (((J + 1 : ℕ) : ℝ) * eta)) *
            dirichletNontrivialZeroReciprocalMultiplicitySum psi.1 T :=
        hkernel
      _ ≤ 12 * x ^ (1 - (((J + 1 : ℕ) : ℝ) * eta)) *
          (8 * (A : ℝ) *
            Real.log ((q : ℝ) * (T + 2)) ^ 2) :=
        mul_le_mul_of_nonneg_left hrec (by positivity)
      _ = 96 * (A : ℝ) *
            x ^ (1 - (((J + 1 : ℕ) : ℝ) * eta)) *
              Real.log ((q : ℝ) * (T + 2)) ^ 2 := by ring
      _ ≤ 96 * (A : ℝ) *
            x ^ (1 - (((J + 1 : ℕ) : ℝ) * eta)) *
              Real.log ((Q : ℝ) * (T + 2)) ^ 2 := by gcongr
      _ = C := by rfl
  unfold primitiveFarZeroKernelMass
  calc
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ‖primitiveFarZeroKernelSumAt q psi x eta J T‖) ≤
      ∑ q ∈ Finset.Ioc 1 Q,
        (Fintype.card (primitiveCharacters q) : ℝ) * C := by
      apply Finset.sum_le_sum
      intro q hqMem
      calc
        (∑ psi : primitiveCharacters q,
            ‖primitiveFarZeroKernelSumAt q psi x eta J T‖) ≤
          ∑ _psi : primitiveCharacters q, C :=
            Finset.sum_le_sum fun psi _ ↦ hpoint q hqMem psi
        _ = (Fintype.card (primitiveCharacters q) : ℝ) * C := by simp
    _ ≤ ∑ _q ∈ Finset.Ioc 1 Q, (Q : ℝ) * C := by
      apply Finset.sum_le_sum
      intro q hqMem
      apply mul_le_mul_of_nonneg_right _ hC
      have hqpos : 0 < q := by
        have := (Finset.mem_Ioc.mp hqMem).1
        omega
      have hcard := card_primitiveCharacters_le_totient
        hqpos
      have htot := Nat.totient_le q
      exact_mod_cast hcard.trans (htot.trans (Finset.mem_Ioc.mp hqMem).2)
    _ ≤ (Q : ℝ) ^ 2 * C := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.Ioc 1 Q).card ≤ Q := by
        rw [Nat.card_Ioc]
        omega
      have hQC : 0 ≤ (Q : ℝ) * C := mul_nonneg (by positivity) hC
      calc
        ((Finset.Ioc 1 Q).card : ℝ) * ((Q : ℝ) * C) ≤
            (Q : ℝ) * ((Q : ℝ) * C) := by gcongr
        _ = (Q : ℝ) ^ 2 * C := by ring
    _ = _ := rfl

end

end Erdos48
