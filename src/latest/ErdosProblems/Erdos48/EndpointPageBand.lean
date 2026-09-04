/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.EndpointZeroBands
import ErdosProblems.Erdos48.PageExcludedConductor
import BoundedGaps.BombieriVinogradov.Analytic.LocalLogarithmicResidue

/-!
# Removing the Page band from the endpoint zero kernel

Vanishing analytic multiplicity in a high-zero rectangle makes the rectangle
empty.  Page uniqueness then removes the complete two-sided innermost band
at every conductor except the one excluded conductor.
-/

namespace Erdos48

open Complex
open BoundedGaps.Maynard

noncomputable section

/-- A primitive high-zero rectangle of total analytic multiplicity zero is
empty. -/
theorem highZeroRectangle_eq_empty_of_mass_eq_zero
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (psi : primitiveCharacters q) {eta T : ℝ}
    (heta : eta ≤ 1) (hT : 0 ≤ T)
    (hmass : highZeroRectangleMass hq psi.1 psi.2 eta T = 0) :
    highZeroRectangle hq psi.1 psi.2 eta T = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro rho hrho
  have hzero :=
    (mem_highZeroRectangle_iff hq psi.1 psi.2 heta hT rho).mp hrho |>.1
  have hpos :
      0 < analyticOrderNatAt (DirichletCharacter.LFunction psi.1) rho :=
    (LFunction_zero_local_logDeriv_expansion
      (primitiveCharacter_ne_one_of_one_lt hq psi) hzero).1
  have hle :
      analyticOrderNatAt (DirichletCharacter.LFunction psi.1) rho ≤
        highZeroRectangleMass hq psi.1 psi.2 eta T := by
    unfold highZeroRectangleMass
    exact Finset.single_le_sum
      (fun z _ ↦ Nat.zero_le
        (analyticOrderNatAt (DirichletCharacter.LFunction psi.1) z)) hrho
  omega

/-- Vanishing primitive rectangle mass kills every upper-half real sub-band.
-/
theorem primitiveHighZeroRealBandKernelSumAt_eq_zero_of_mass_eq_zero
    {q : ℕ} (hq : 1 < q) (psi : primitiveCharacters q)
    {x etaLo etaHi T : ℝ} (hetaHi : etaHi ≤ 1) (hT : 0 ≤ T)
    (hmass : primitiveHighZeroMassAt q psi etaHi T = 0) :
    primitiveHighZeroRealBandKernelSumAt q psi
        x etaLo etaHi T = 0 := by
  let : NeZero q := ⟨by omega⟩
  rw [primitiveHighZeroRealBandKernelSumAt_eq hq,
    highZeroRealBandKernelSum]
  have hrect : highZeroRectangle hq psi.1 psi.2 etaHi T = ∅ := by
    apply highZeroRectangle_eq_empty_of_mass_eq_zero hq psi hetaHi hT
    simpa only [primitiveHighZeroMassAt_eq hq] using hmass
  have hband : highZeroRealBand hq psi.1 psi.2 etaLo etaHi T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro rho hrho
    have := highZeroRealBand_subset hq psi.1 psi.2 etaLo etaHi T hrho
    simpa [hrect] using this
  rw [hband]
  simp

/-- The same vanishing statement for the strict positive-ordinate sub-band.
-/
theorem primitiveHighZeroPositiveRealBandKernelSumAt_eq_zero_of_mass_eq_zero
    {q : ℕ} (hq : 1 < q) (psi : primitiveCharacters q)
    {x etaLo etaHi T : ℝ} (hetaHi : etaHi ≤ 1) (hT : 0 ≤ T)
    (hmass : primitiveHighZeroMassAt q psi etaHi T = 0) :
    primitiveHighZeroPositiveRealBandKernelSumAt q psi
        x etaLo etaHi T = 0 := by
  let : NeZero q := ⟨by omega⟩
  rw [primitiveHighZeroPositiveRealBandKernelSumAt_eq hq,
    highZeroPositiveRealBandKernelSum]
  have hrect : highZeroRectangle hq psi.1 psi.2 etaHi T = ∅ := by
    apply highZeroRectangle_eq_empty_of_mass_eq_zero hq psi hetaHi hT
    simpa only [primitiveHighZeroMassAt_eq hq] using hmass
  have hband : highZeroPositiveRealBand hq psi.1 psi.2 etaLo etaHi T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro rho hrho
    have hreal := (Finset.mem_filter.mp hrho).1
    have hrectMem := highZeroRealBand_subset
      hq psi.1 psi.2 etaLo etaHi T hreal
    simpa [hrect] using hrectMem
  rw [hband]
  simp

/-- If the Page rectangle vanishes for both a primitive character and its
inverse, then its complete two-sided Page-band kernel vanishes. -/
theorem primitiveTwoSidedZeroPageBandKernelSumAt_eq_zero
    {q : ℕ} (hq : 1 < q) (psi : primitiveCharacters q)
    {x eta T : ℝ} (hx : 0 < x) (heta : eta < 1) (hT : 0 ≤ T)
    (hmass : primitiveHighZeroMassAt q psi eta T = 0)
    (hmassInv : primitiveHighZeroMassAt q
      (primitiveCharacterInvEquiv q psi) eta T = 0) :
    primitiveTwoSidedZeroRealBandKernelSumAt q psi x 0 eta T = 0 := by
  rw [primitiveTwoSidedZeroRealBandKernelSumAt_eq_high_add_low
    hq psi hx heta hT,
    primitiveHighZeroRealBandKernelSumAt_eq_zero_of_mass_eq_zero
      hq psi heta.le hT hmass,
    primitiveLowZeroRealBandKernelSumAt,
    primitiveHighZeroPositiveRealBandKernelSumAt_eq_zero_of_mass_eq_zero
      hq (primitiveCharacterInvEquiv q psi) heta.le hT hmassInv]
  simp

/-- Page uniqueness removes the innermost two-sided band at every conductor
other than the excluded conductor. -/
theorem pageBandKernel_eq_zero_of_ne_excluded
    {Q T : ℕ} {eta : ℝ} {m₀ q : ℕ}
    (hpage : ∀ d ∈ Finset.Ioc 1 Q, d ≠ m₀ →
      ∀ psi : primitiveCharacters d,
        primitiveHighZeroMassAt d psi eta T = 0)
    (hq : q ∈ Finset.Ioc 1 Q) (hqm₀ : q ≠ m₀)
    (psi : primitiveCharacters q) {x : ℝ}
    (hx : 0 < x) (heta : eta < 1) :
    primitiveTwoSidedZeroRealBandKernelSumAt q psi
        x 0 eta T = 0 := by
  have hqOne : 1 < q := (Finset.mem_Ioc.mp hq).1
  apply primitiveTwoSidedZeroPageBandKernelSumAt_eq_zero
    hqOne psi hx heta (by positivity)
  · exact hpage q hq hqm₀ psi
  · exact hpage q hq hqm₀ (primitiveCharacterInvEquiv q psi)

/-- Totalized complete zero kernel for a primitive character. -/
noncomputable def primitiveZeroKernelSumAt
    (q : ℕ) (psi : primitiveCharacters q) (x T : ℝ) : ℂ :=
  if hq : 1 < q then
    @dirichletNontrivialZeroKernelSum q ⟨by omega⟩ psi.1 x T
  else 0

theorem primitiveZeroKernelSumAt_eq
    {q : ℕ} (hq : 1 < q) (psi : primitiveCharacters q) (x T : ℝ) :
    primitiveZeroKernelSumAt q psi x T =
      @dirichletNontrivialZeroKernelSum q ⟨by omega⟩ psi.1 x T := by
  simp only [primitiveZeroKernelSumAt, dif_pos hq]

/-- Totalized far-left zero-kernel remainder for a primitive character. -/
noncomputable def primitiveFarZeroKernelSumAt
    (q : ℕ) (psi : primitiveCharacters q)
    (x eta : ℝ) (J : ℕ) (T : ℝ) : ℂ :=
  if hq : 1 < q then
    @dirichletNontrivialZeroFarKernelSum q ⟨by omega⟩
      psi.1 x eta J T
  else 0

theorem primitiveFarZeroKernelSumAt_eq
    {q : ℕ} (hq : 1 < q) (psi : primitiveCharacters q)
    (x eta : ℝ) (J : ℕ) (T : ℝ) :
    primitiveFarZeroKernelSumAt q psi x eta J T =
      @dirichletNontrivialZeroFarKernelSum q ⟨by omega⟩
        psi.1 x eta J T := by
  simp only [primitiveFarZeroKernelSumAt, dif_pos hq]

/-- After the Page band vanishes, the complete zero kernel is bounded by the
norms of the next `J` linear bands and one far-left remainder. -/
theorem norm_dirichletNontrivialZeroKernelSum_le_linearBands_add_far_of_page
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (psi : primitiveCharacters q) {x eta T : ℝ} (J : ℕ)
    (heta : 0 ≤ eta)
    (hpage : primitiveTwoSidedZeroRealBandKernelSumAt q psi
      x 0 eta T = 0) :
    ‖dirichletNontrivialZeroKernelSum psi.1 x T‖ ≤
      (∑ j ∈ Finset.range J,
        ‖primitiveTwoSidedZeroRealBandKernelSumAt q psi x
          (((j + 1 : ℕ) : ℝ) * eta)
          (((j + 2 : ℕ) : ℝ) * eta) T‖) +
        ‖primitiveFarZeroKernelSumAt q psi x eta J T‖ := by
  have hdecomp :=
    dirichletNontrivialZeroKernelSum_eq_sum_linearBands_add_far
      psi.1 x eta T J heta
  rw [hdecomp]
  calc
    ‖(∑ j ∈ Finset.range (J + 1),
          dirichletNontrivialZeroRealBandKernelSum psi.1 x
            ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T) +
        dirichletNontrivialZeroFarKernelSum psi.1 x eta J T‖ ≤
      ‖∑ j ∈ Finset.range (J + 1),
          dirichletNontrivialZeroRealBandKernelSum psi.1 x
            ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T‖ +
        ‖dirichletNontrivialZeroFarKernelSum psi.1 x eta J T‖ :=
      norm_add_le _ _
    _ ≤ (∑ j ∈ Finset.range (J + 1),
          ‖dirichletNontrivialZeroRealBandKernelSum psi.1 x
            ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T‖) +
        ‖dirichletNontrivialZeroFarKernelSum psi.1 x eta J T‖ := by
      gcongr
      exact norm_sum_le _ _
    _ = (∑ j ∈ Finset.range J,
          ‖primitiveTwoSidedZeroRealBandKernelSumAt q psi x
            (((j + 1 : ℕ) : ℝ) * eta)
            (((j + 2 : ℕ) : ℝ) * eta) T‖) +
        ‖primitiveFarZeroKernelSumAt q psi x eta J T‖ := by
      rw [Finset.sum_range_succ']
      rw [primitiveFarZeroKernelSumAt_eq hq]
      have hband (j : ℕ) :
          primitiveTwoSidedZeroRealBandKernelSumAt q psi x
              ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T =
            dirichletNontrivialZeroRealBandKernelSum psi.1 x
              ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T := by
        exact primitiveTwoSidedZeroRealBandKernelSumAt_eq hq psi
          x ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T
      simp_rw [← hband]
      simp only [Nat.cast_zero, zero_mul, Nat.zero_add, Nat.cast_one,
        one_mul, hpage, norm_zero, add_zero]

/-- The preceding pointwise bound with the Page hypothesis discharged by
the excluded-conductor theorem. -/
theorem norm_zeroKernel_le_linearBands_add_far_of_ne_excluded
    {Q T : ℕ} {eta : ℝ} {m₀ q : ℕ}
    (hpage : ∀ d ∈ Finset.Ioc 1 Q, d ≠ m₀ →
      ∀ psi : primitiveCharacters d,
        primitiveHighZeroMassAt d psi eta T = 0)
    (hq : q ∈ Finset.Ioc 1 Q) (hqm₀ : q ≠ m₀)
    (psi : primitiveCharacters q) {x : ℝ}
    (hx : 0 < x) (heta : 0 < eta) (heta1 : eta < 1) (J : ℕ) :
    ‖primitiveZeroKernelSumAt q psi x T‖ ≤
      (∑ j ∈ Finset.range J,
        ‖primitiveTwoSidedZeroRealBandKernelSumAt q psi x
          (((j + 1 : ℕ) : ℝ) * eta)
          (((j + 2 : ℕ) : ℝ) * eta) T‖) +
        ‖primitiveFarZeroKernelSumAt q psi x eta J T‖ := by
  have hqOne : 1 < q := (Finset.mem_Ioc.mp hq).1
  let : NeZero q := ⟨by omega⟩
  rw [primitiveZeroKernelSumAt_eq hqOne]
  apply norm_dirichletNontrivialZeroKernelSum_le_linearBands_add_far_of_page
    hqOne psi J heta.le
  exact pageBandKernel_eq_zero_of_ne_excluded hpage hq hqm₀ psi hx heta1

end

end Erdos48
