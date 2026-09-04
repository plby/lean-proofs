/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.ZeroBandPartition

/-!
# Sharp endpoint bounds for middle zero bands

The line-segment estimate for the explicit-formula kernel loses a factor
`log x`.  On the endpoint bands used below every zero has real part at least
one half, so the quotient formula and `|rho| >= Re rho` instead give the
source-shaped estimate `|((x^rho)-1)/rho| <= 4 x^(Re rho)`.
-/

namespace Erdos48

open Complex
open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

/-- In the half strip `Re rho >= 1/2`, the modified explicit-formula kernel
is bounded without a logarithmic loss. -/
theorem norm_dirichletExplicitFormulaKernel_le_four_rpow
    {x : ℝ} (hx : 1 ≤ x) {rho : ℂ} (hre : 1 / 2 ≤ rho.re) :
    ‖dirichletExplicitFormulaKernel x rho‖ ≤ 4 * x ^ rho.re := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hre0 : 0 ≤ rho.re := by linarith
  have hrhoNe : rho ≠ 0 := by
    intro hrho
    subst rho
    norm_num at hre
  have hnormrho : 0 < ‖rho‖ := norm_pos_iff.mpr hrhoNe
  have hreNorm : rho.re ≤ ‖rho‖ := by
    simpa [abs_of_nonneg hre0] using Complex.abs_re_le_norm rho
  have hhalfNorm : 1 / 2 ≤ ‖rho‖ := hre.trans hreNorm
  have hpowOne : (1 : ℝ) ≤ x ^ rho.re := by
    calc
      (1 : ℝ) = x ^ (0 : ℝ) := (Real.rpow_zero x).symm
      _ ≤ x ^ rho.re :=
        Real.rpow_le_rpow_of_exponent_le hx hre0
  rw [dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hxpos hrhoNe,
    norm_div]
  apply (div_le_iff₀ hnormrho).2
  calc
    ‖(x : ℂ) ^ rho - 1‖ ≤ ‖(x : ℂ) ^ rho‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ = x ^ rho.re + 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, norm_one]
    _ ≤ 2 * x ^ rho.re := by linarith
    _ ≤ (4 * x ^ rho.re) * ‖rho‖ := by
      have h := mul_le_mul_of_nonneg_left hhalfNorm
        (show 0 ≤ 4 * x ^ rho.re by positivity)
      nlinarith

/-- Termwise middle-band estimate in one upper-half zero rectangle. -/
theorem sum_norm_highZeroRealBand_terms_le_four
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {x etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hetaHi : etaHi ≤ 1 / 2) (hT : 0 ≤ T) :
    (∑ rho ∈ highZeroRealBand hq chi hchi etaLo etaHi T,
        ‖(analyticOrderNatAt
            (DirichletCharacter.LFunction chi) rho : ℂ) *
          dirichletExplicitFormulaKernel x rho‖) ≤
      (highZeroRectangleMass hq chi hchi etaHi T : ℝ) *
        (4 * x ^ (1 - etaLo)) := by
  classical
  let S := highZeroRealBand hq chi hchi etaLo etaHi T
  let Z := highZeroRectangle hq chi hchi etaHi T
  let C : ℝ := 4 * x ^ (1 - etaLo)
  have hterm : ∀ rho ∈ S,
      ‖(analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho‖ ≤
        (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℝ) * C := by
    intro rho hrho
    have hrhoData := Finset.mem_filter.mp
      (show rho ∈
          (highZeroRectangle hq chi hchi etaHi T).filter
            (fun z ↦ z.re < 1 - etaLo) by
        simpa only [S, highZeroRealBand] using hrho)
    have hhigh := (mem_highZeroRectangle_iff hq chi hchi
      (hetaHi.trans (by norm_num)) hT rho).mp hrhoData.1
    have hreHalf : 1 / 2 ≤ rho.re := by linarith [hhigh.2.1]
    have hkernel := norm_dirichletExplicitFormulaKernel_le_four_rpow
      hx hreHalf
    have hpow : x ^ rho.re ≤ x ^ (1 - etaLo) :=
      Real.rpow_le_rpow_of_exponent_le hx hrhoData.2.le
    have hkernelC : ‖dirichletExplicitFormulaKernel x rho‖ ≤ C := by
      exact hkernel.trans <|
        mul_le_mul_of_nonneg_left hpow (by norm_num)
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hkernelC (by positivity)
  change (∑ rho ∈ S,
      ‖(analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℂ) *
        dirichletExplicitFormulaKernel x rho‖) ≤ _
  calc
    (∑ rho ∈ S,
        ‖(analyticOrderNatAt
            (DirichletCharacter.LFunction chi) rho : ℂ) *
          dirichletExplicitFormulaKernel x rho‖) ≤
        ∑ rho ∈ S,
          (analyticOrderNatAt
            (DirichletCharacter.LFunction chi) rho : ℝ) * C :=
      Finset.sum_le_sum hterm
    _ ≤ ∑ rho ∈ Z,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℝ) * C := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simpa only [S, Z] using
          highZeroRealBand_subset hq chi hchi etaLo etaHi T
      · intro rho hrhoZ hrhoS
        positivity
    _ = (highZeroRectangleMass hq chi hchi etaHi T : ℝ) * C := by
      unfold highZeroRectangleMass
      push_cast
      rw [Finset.sum_mul]
    _ = _ := rfl

/-- The full upper-half middle band has the same sharp bound. -/
theorem norm_highZeroRealBandKernelSum_le_four
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {x etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hetaHi : etaHi ≤ 1 / 2) (hT : 0 ≤ T) :
    ‖highZeroRealBandKernelSum hq chi hchi x etaLo etaHi T‖ ≤
      (highZeroRectangleMass hq chi hchi etaHi T : ℝ) *
        (4 * x ^ (1 - etaLo)) := by
  unfold highZeroRealBandKernelSum
  exact (norm_sum_le _ _).trans
    (sum_norm_highZeroRealBand_terms_le_four
      hq chi hchi hx hetaHi hT)

/-- Restricting to positive ordinates preserves the sharp middle-band
estimate. -/
theorem norm_highZeroPositiveRealBandKernelSum_le_four
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {x etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hetaHi : etaHi ≤ 1 / 2) (hT : 0 ≤ T) :
    ‖highZeroPositiveRealBandKernelSum hq chi hchi
        x etaLo etaHi T‖ ≤
      (highZeroRectangleMass hq chi hchi etaHi T : ℝ) *
        (4 * x ^ (1 - etaLo)) := by
  classical
  unfold highZeroPositiveRealBandKernelSum
  calc
    ‖∑ rho ∈ highZeroPositiveRealBand hq chi hchi etaLo etaHi T,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho‖ ≤
      ∑ rho ∈ highZeroPositiveRealBand hq chi hchi etaLo etaHi T,
        ‖(analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho‖ := norm_sum_le _ _
    _ ≤ ∑ rho ∈ highZeroRealBand hq chi hchi etaLo etaHi T,
        ‖(analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro rho hrho hnot
        positivity
    _ ≤ _ := sum_norm_highZeroRealBand_terms_le_four
      hq chi hchi hx hetaHi hT

/-- Aggregate sharp bound for all upper-half middle bands. -/
theorem sum_norm_highZeroRealBandKernelSum_le_four
    {Q : ℕ} {x etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hetaHi : etaHi ≤ 1 / 2) (hT : 0 ≤ T) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ‖primitiveHighZeroRealBandKernelSumAt q psi
          x etaLo etaHi T‖) ≤
      (primitiveHighZeroMass Q etaHi T : ℝ) *
        (4 * x ^ (1 - etaLo)) := by
  classical
  let C : ℝ := 4 * x ^ (1 - etaLo)
  calc
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ‖primitiveHighZeroRealBandKernelSumAt q psi
          x etaLo etaHi T‖) ≤
        ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          (primitiveHighZeroMassAt q psi etaHi T : ℝ) * C := by
      apply Finset.sum_le_sum
      intro q hqMem
      apply Finset.sum_le_sum
      intro psi hpsi
      have hq : 1 < q := (Finset.mem_Ioc.mp hqMem).1
      let : NeZero q := ⟨by omega⟩
      rw [primitiveHighZeroRealBandKernelSumAt_eq hq]
      simpa only [primitiveHighZeroMassAt_eq hq, C] using
        norm_highZeroRealBandKernelSum_le_four hq psi.1 psi.2
          hx hetaHi hT
    _ = (primitiveHighZeroMass Q etaHi T : ℝ) * C := by
      unfold primitiveHighZeroMass
      push_cast
      simp_rw [Finset.sum_mul]
    _ = _ := rfl

/-- Aggregate sharp bound for the strict-positive-ordinate part. -/
theorem sum_norm_highZeroPositiveRealBandKernelSum_le_four
    {Q : ℕ} {x etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hetaHi : etaHi ≤ 1 / 2) (hT : 0 ≤ T) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ‖primitiveHighZeroPositiveRealBandKernelSumAt q psi
          x etaLo etaHi T‖) ≤
      (primitiveHighZeroMass Q etaHi T : ℝ) *
        (4 * x ^ (1 - etaLo)) := by
  classical
  let C : ℝ := 4 * x ^ (1 - etaLo)
  calc
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ‖primitiveHighZeroPositiveRealBandKernelSumAt q psi
          x etaLo etaHi T‖) ≤
        ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          (primitiveHighZeroMassAt q psi etaHi T : ℝ) * C := by
      apply Finset.sum_le_sum
      intro q hqMem
      apply Finset.sum_le_sum
      intro psi hpsi
      have hq : 1 < q := (Finset.mem_Ioc.mp hqMem).1
      let : NeZero q := ⟨by omega⟩
      rw [primitiveHighZeroPositiveRealBandKernelSumAt_eq hq]
      simpa only [primitiveHighZeroMassAt_eq hq, C] using
        norm_highZeroPositiveRealBandKernelSum_le_four hq psi.1 psi.2
          hx hetaHi hT
    _ = (primitiveHighZeroMass Q etaHi T : ℝ) * C := by
      unfold primitiveHighZeroMass
      push_cast
      simp_rw [Finset.sum_mul]
    _ = _ := rfl

/-- Both signs of a middle zero band cost at most eight times the high-zero
mass, with no `log x` loss. -/
theorem sum_norm_primitiveTwoSidedZeroRealBandKernelSumAt_le_eight
    {Q : ℕ} {x etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hetaHi : etaHi ≤ 1 / 2) (hT : 0 ≤ T) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ‖primitiveTwoSidedZeroRealBandKernelSumAt q psi
          x etaLo etaHi T‖) ≤
      8 * ((primitiveHighZeroMass Q etaHi T : ℝ) *
        x ^ (1 - etaLo)) := by
  have hhigh := sum_norm_highZeroRealBandKernelSum_le_four
    (Q := Q) (x := x) (etaLo := etaLo) (etaHi := etaHi) (T := T)
      hx hetaHi hT
  have hlow :
      (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          ‖primitiveLowZeroRealBandKernelSumAt q psi
            x etaLo etaHi T‖) ≤
        (primitiveHighZeroMass Q etaHi T : ℝ) *
          (4 * x ^ (1 - etaLo)) := by
    rw [sum_norm_primitiveLowZeroRealBandKernelSumAt_eq]
    exact sum_norm_highZeroPositiveRealBandKernelSum_le_four
      (Q := Q) (x := x) (etaLo := etaLo) (etaHi := etaHi) (T := T)
        hx hetaHi hT
  have hsplit :
      (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          ‖primitiveTwoSidedZeroRealBandKernelSumAt q psi
            x etaLo etaHi T‖) ≤
        ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          (‖primitiveHighZeroRealBandKernelSumAt q psi
              x etaLo etaHi T‖ +
            ‖primitiveLowZeroRealBandKernelSumAt q psi
              x etaLo etaHi T‖) := by
    apply Finset.sum_le_sum
    intro q hqMem
    apply Finset.sum_le_sum
    intro psi hpsi
    have hq : 1 < q := (Finset.mem_Ioc.mp hqMem).1
    rw [primitiveTwoSidedZeroRealBandKernelSumAt_eq_high_add_low
      hq psi (zero_lt_one.trans_le hx) (hetaHi.trans_lt (by norm_num)) hT]
    exact norm_add_le _ _
  calc
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ‖primitiveTwoSidedZeroRealBandKernelSumAt q psi
          x etaLo etaHi T‖) ≤
        ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          (‖primitiveHighZeroRealBandKernelSumAt q psi
              x etaLo etaHi T‖ +
            ‖primitiveLowZeroRealBandKernelSumAt q psi
              x etaLo etaHi T‖) := hsplit
    _ = (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          ‖primitiveHighZeroRealBandKernelSumAt q psi
            x etaLo etaHi T‖) +
        ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          ‖primitiveLowZeroRealBandKernelSumAt q psi
            x etaLo etaHi T‖ := by
      simp_rw [Finset.sum_add_distrib]
    _ ≤ 2 * ((primitiveHighZeroMass Q etaHi T : ℝ) *
          (4 * x ^ (1 - etaLo))) := by
      nlinarith [hhigh, hlow]
    _ = 8 * ((primitiveHighZeroMass Q etaHi T : ℝ) *
          x ^ (1 - etaLo)) := by ring

end

end Erdos48
