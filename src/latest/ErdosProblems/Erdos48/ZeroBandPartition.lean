/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.ZeroConjugation
import BoundedGaps.BombieriVinogradov.Analytic.DirichletNontrivialZeroTransport

/-!
# Partitioning a two-sided Dirichlet-zero band

The density estimate is naturally proved in the upper half-plane, whereas
the primitive explicit formula sums over both signs of the ordinate.  This
file identifies the nonnegative part of a two-sided real band with the
upper rectangle and identifies its negative part, by conjugation, with the
strictly positive band for the inverse character.
-/

namespace Erdos48

open Complex
open scoped BigOperators ComplexConjugate
open BoundedGaps.Maynard

noncomputable section

/-- Nontrivial zeros in the two-sided real band
`1-etaHi ≤ re rho < 1-etaLo`, truncated at height `T`. -/
noncomputable def dirichletNontrivialZeroRealBand
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (etaLo etaHi T : ℝ) : Finset ℂ :=
  (dirichletNontrivialLFunctionZerosFinset chi T).filter fun rho ↦
    1 - etaHi ≤ rho.re ∧ rho.re < 1 - etaLo

@[simp] theorem mem_dirichletNontrivialZeroRealBand_iff
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    {etaLo etaHi T : ℝ} {rho : ℂ} :
    rho ∈ dirichletNontrivialZeroRealBand chi etaLo etaHi T ↔
      IsDirichletNontrivialLFunctionZero chi rho ∧
        |rho.im| ≤ |T| ∧
          1 - etaHi ≤ rho.re ∧ rho.re < 1 - etaLo := by
  classical
  rw [dirichletNontrivialZeroRealBand, Finset.mem_filter,
    mem_dirichletNontrivialLFunctionZerosFinset_iff]
  tauto

/-- The nonnegative-ordinate portion of a two-sided real band. -/
noncomputable def dirichletNonnegativeZeroRealBand
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (etaLo etaHi T : ℝ) : Finset ℂ :=
  (dirichletNontrivialZeroRealBand chi etaLo etaHi T).filter fun rho ↦
    0 ≤ rho.im

/-- The negative-ordinate portion of a two-sided real band. -/
noncomputable def dirichletNegativeZeroRealBand
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (etaLo etaHi T : ℝ) : Finset ℂ :=
  (dirichletNontrivialZeroRealBand chi etaLo etaHi T).filter fun rho ↦
    rho.im < 0

/-- Modified explicit-formula kernel over a two-sided real band. -/
noncomputable def dirichletNontrivialZeroRealBandKernelSum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x etaLo etaHi T : ℝ) : ℂ :=
  ∑ rho ∈ dirichletNontrivialZeroRealBand chi etaLo etaHi T,
    (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : ℂ) *
      dirichletExplicitFormulaKernel x rho

private theorem dirichletNontrivialZeroRealBand_eq_union
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (etaLo etaHi T : ℝ) :
    dirichletNontrivialZeroRealBand chi etaLo etaHi T =
      dirichletNonnegativeZeroRealBand chi etaLo etaHi T ∪
        dirichletNegativeZeroRealBand chi etaLo etaHi T := by
  classical
  ext rho
  simp only [dirichletNonnegativeZeroRealBand,
    dirichletNegativeZeroRealBand, Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hrho
    by_cases him : 0 ≤ rho.im
    · exact Or.inl ⟨hrho, him⟩
    · exact Or.inr ⟨hrho, lt_of_not_ge him⟩
  · rintro (⟨hrho, _⟩ | ⟨hrho, _⟩) <;> exact hrho

private theorem disjoint_nonnegative_negative_zeroRealBand
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (etaLo etaHi T : ℝ) :
    Disjoint (dirichletNonnegativeZeroRealBand chi etaLo etaHi T)
      (dirichletNegativeZeroRealBand chi etaLo etaHi T) := by
  classical
  rw [Finset.disjoint_left]
  intro rho hnonneg hnegative
  have h0 := (Finset.mem_filter.mp hnonneg).2
  have hlt := (Finset.mem_filter.mp hnegative).2
  linarith

/-- The two sign bands partition the complete two-sided band exactly. -/
theorem dirichletNontrivialZeroRealBandKernelSum_eq_signs
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x etaLo etaHi T : ℝ) :
    dirichletNontrivialZeroRealBandKernelSum chi x etaLo etaHi T =
      (∑ rho ∈ dirichletNonnegativeZeroRealBand chi etaLo etaHi T,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho) +
      ∑ rho ∈ dirichletNegativeZeroRealBand chi etaLo etaHi T,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho := by
  classical
  rw [dirichletNontrivialZeroRealBandKernelSum,
    dirichletNontrivialZeroRealBand_eq_union chi etaLo etaHi T,
    Finset.sum_union (disjoint_nonnegative_negative_zeroRealBand
      chi etaLo etaHi T)]

/-- In the open strip `etaHi < 1`, the nonnegative part of the natural
two-sided band is exactly the upper-half band used by the density theorem. -/
theorem dirichletNonnegativeZeroRealBand_eq_highZeroRealBand
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {etaLo etaHi T : ℝ} (hetaHi : etaHi < 1) (hT : 0 ≤ T) :
    dirichletNonnegativeZeroRealBand chi etaLo etaHi T =
      highZeroRealBand hq chi hchi etaLo etaHi T := by
  classical
  ext rho
  rw [dirichletNonnegativeZeroRealBand, Finset.mem_filter,
    mem_dirichletNontrivialZeroRealBand_iff,
    highZeroRealBand, Finset.mem_filter,
    mem_highZeroRectangle_iff hq chi hchi hetaHi.le hT]
  constructor
  · rintro ⟨⟨⟨hzero, hre0, hre1⟩, hheight, hrelo, hrehi⟩, him0⟩
    have himT : rho.im ≤ T := by
      rw [abs_of_nonneg him0, abs_of_nonneg hT] at hheight
      exact hheight
    exact ⟨⟨hzero, hrelo, hre1.le, him0, himT⟩, hrehi⟩
  · rintro ⟨⟨hzero, hrelo, hre1, him0, himT⟩, hrehi⟩
    have hre0 : 0 < rho.re := by linarith
    have hreLt : rho.re < 1 :=
      LFunction_zero_re_lt_one_of_isPrimitive hq chi hchi hzero
    have hheight : |rho.im| ≤ |T| := by
      rw [abs_of_nonneg him0, abs_of_nonneg hT]
      exact himT
    exact ⟨⟨⟨hzero, hre0, hreLt⟩, hheight, hrelo, hrehi⟩, him0⟩

private theorem inv_isPrimitive
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi.IsPrimitive) : chi⁻¹.IsPrimitive := by
  simpa [DirichletCharacter.IsPrimitive,
    DirichletCharacter.conductor_inv] using hchi

private theorem conj_mem_positive_inv_band_of_mem_negative_band
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {etaLo etaHi T : ℝ} (hetaHi : etaHi < 1) (hT : 0 ≤ T)
    {rho : ℂ} (hrho : rho ∈
      dirichletNegativeZeroRealBand chi etaLo etaHi T) :
    conj rho ∈ highZeroPositiveRealBand hq chi⁻¹
      (inv_isPrimitive chi hchi)
      etaLo etaHi T := by
  have hrhoData := Finset.mem_filter.mp hrho
  have hband := mem_dirichletNontrivialZeroRealBand_iff.mp hrhoData.1
  have hchiNe : chi ≠ 1 := character_ne_one_of_isPrimitive hq chi hchi
  have hzeroInv : DirichletCharacter.LFunction chi⁻¹ (conj rho) = 0 := by
    rw [LFunction_inv_conj chi hchiNe rho, hband.1.1, map_zero]
  rw [highZeroPositiveRealBand, Finset.mem_filter,
    highZeroRealBand, Finset.mem_filter,
    mem_highZeroRectangle_iff hq chi⁻¹
      (inv_isPrimitive chi hchi)
      hetaHi.le hT]
  have himNeg : rho.im < 0 := hrhoData.2
  have himConj : 0 < (conj rho).im := by simp; linarith
  have himT : (conj rho).im ≤ T := by
    have hheight := hband.2.1
    rw [abs_of_nonpos himNeg.le, abs_of_nonneg hT] at hheight
    simpa using hheight
  exact ⟨⟨⟨hzeroInv, hband.2.2.1, hband.1.2.2.le,
    himConj.le, himT⟩, hband.2.2.2⟩, himConj⟩

private theorem conj_mem_negative_band_of_mem_positive_inv_band
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {etaLo etaHi T : ℝ} (hetaHi : etaHi < 1) (hT : 0 ≤ T)
    {rho : ℂ} (hrho : rho ∈ highZeroPositiveRealBand hq chi⁻¹
      (inv_isPrimitive chi hchi)
      etaLo etaHi T) :
    conj rho ∈ dirichletNegativeZeroRealBand chi etaLo etaHi T := by
  let hinvPrimitive : chi⁻¹.IsPrimitive := inv_isPrimitive chi hchi
  have hrhoData := Finset.mem_filter.mp hrho
  have hrealData := Finset.mem_filter.mp hrhoData.1
  have hhigh := (mem_highZeroRectangle_iff hq chi⁻¹
    hinvPrimitive hetaHi.le hT rho).mp hrealData.1
  have hchiInvNe : chi⁻¹ ≠ 1 := character_ne_one_of_isPrimitive
    hq chi⁻¹ hinvPrimitive
  have hzero : DirichletCharacter.LFunction chi (conj rho) = 0 := by
    have hconj := LFunction_inv_conj chi⁻¹ hchiInvNe rho
    simpa [hhigh.1] using hconj
  rw [dirichletNegativeZeroRealBand, Finset.mem_filter,
    mem_dirichletNontrivialZeroRealBand_iff]
  have himPos : 0 < rho.im := hrhoData.2
  have himNeg : (conj rho).im < 0 := by simp; linarith
  have hheight : |(conj rho).im| ≤ |T| := by
    rw [abs_of_nonpos himNeg.le, abs_of_nonneg hT]
    simpa using hhigh.2.2.2.2
  have hrePos : 0 < (conj rho).re := by simp; linarith
  have hreLt : (conj rho).re < 1 := by
    simpa using LFunction_zero_re_lt_one_of_isPrimitive
      hq chi hchi hzero
  exact ⟨⟨⟨hzero, hrePos, hreLt⟩, hheight,
    by simpa using hhigh.2.1, by simpa using hrealData.2⟩, himNeg⟩

/-- Conjugation identifies the negative band for `chi` with the strict
positive band for `chi⁻¹`, including multiplicity and the modified kernel. -/
theorem negativeZeroRealBandKernelSum_eq_conj_positive_inv
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {x etaLo etaHi T : ℝ} (hx : 0 < x)
    (hetaHi : etaHi < 1) (hT : 0 ≤ T) :
    (∑ rho ∈ dirichletNegativeZeroRealBand chi etaLo etaHi T,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho) =
      conj (highZeroPositiveRealBandKernelSum hq chi⁻¹
        (inv_isPrimitive chi hchi)
        x etaLo etaHi T) := by
  classical
  let hprimInv : chi⁻¹.IsPrimitive := inv_isPrimitive chi hchi
  let S := dirichletNegativeZeroRealBand chi etaLo etaHi T
  let U := highZeroPositiveRealBand hq chi⁻¹ hprimInv etaLo etaHi T
  rw [highZeroPositiveRealBandKernelSum, map_sum]
  symm
  apply Finset.sum_bij (fun rho _ ↦ conj rho)
  · intro rho hrho
    simpa only [S, hprimInv] using
      conj_mem_negative_band_of_mem_positive_inv_band
        hq chi hchi hetaHi hT hrho
  · intro a ha b hb hab
    simpa using congrArg conj hab
  · intro rho hrho
    refine ⟨conj rho, ?_, by simp⟩
    simpa only [U, hprimInv] using
      conj_mem_positive_inv_band_of_mem_negative_band
        hq chi hchi hetaHi hT hrho
  · intro rho hrho
    rw [map_mul, map_natCast,
      conj_dirichletExplicitFormulaKernel hx rho]
    have horder := analyticOrderNatAt_LFunction_inv_conj
      chi (character_ne_one_of_isPrimitive hq chi hchi) (conj rho)
    have horderCast :
        (analyticOrderNatAt
            (DirichletCharacter.LFunction chi⁻¹) rho : ℂ) =
          (analyticOrderNatAt
            (DirichletCharacter.LFunction chi) (conj rho) : ℂ) := by
      simpa using congrArg (fun n : ℕ ↦ (n : ℂ)) horder
    rw [horderCast]

/-- Exact two-sided band decomposition in the form consumed by the aggregate
kernel estimate. -/
theorem dirichletNontrivialZeroRealBandKernelSum_eq_high_add_low
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {x etaLo etaHi T : ℝ} (hx : 0 < x)
    (hetaHi : etaHi < 1) (hT : 0 ≤ T) :
    dirichletNontrivialZeroRealBandKernelSum chi x etaLo etaHi T =
      highZeroRealBandKernelSum hq chi hchi x etaLo etaHi T +
        conj (highZeroPositiveRealBandKernelSum hq chi⁻¹
          (inv_isPrimitive chi hchi)
          x etaLo etaHi T) := by
  rw [dirichletNontrivialZeroRealBandKernelSum_eq_signs,
    dirichletNonnegativeZeroRealBand_eq_highZeroRealBand
      hq chi hchi hetaHi hT,
    negativeZeroRealBandKernelSum_eq_conj_positive_inv
      hq chi hchi hx hetaHi hT]
  rfl

/-- Totalized natural two-sided band kernel for a primitive character. -/
noncomputable def primitiveTwoSidedZeroRealBandKernelSumAt
    (q : ℕ) (psi : primitiveCharacters q)
    (x etaLo etaHi T : ℝ) : ℂ :=
  if hq : 1 < q then
    @dirichletNontrivialZeroRealBandKernelSum q ⟨by omega⟩ psi.1
      x etaLo etaHi T
  else 0

theorem primitiveTwoSidedZeroRealBandKernelSumAt_eq
    {q : ℕ} (hq : 1 < q) (psi : primitiveCharacters q)
    (x etaLo etaHi T : ℝ) :
    primitiveTwoSidedZeroRealBandKernelSumAt q psi
        x etaLo etaHi T =
      @dirichletNontrivialZeroRealBandKernelSum q ⟨by omega⟩ psi.1
        x etaLo etaHi T := by
  simp only [primitiveTwoSidedZeroRealBandKernelSumAt, dif_pos hq]

/-- The totalized natural two-sided band is exactly the previously defined
upper contribution plus the conjugated positive contribution for the inverse
primitive character. -/
theorem primitiveTwoSidedZeroRealBandKernelSumAt_eq_high_add_low
    {q : ℕ} (hq : 1 < q) (psi : primitiveCharacters q)
    {x etaLo etaHi T : ℝ} (hx : 0 < x)
    (hetaHi : etaHi < 1) (hT : 0 ≤ T) :
    primitiveTwoSidedZeroRealBandKernelSumAt q psi
        x etaLo etaHi T =
      primitiveHighZeroRealBandKernelSumAt q psi
          x etaLo etaHi T +
        primitiveLowZeroRealBandKernelSumAt q psi
          x etaLo etaHi T := by
  letI : NeZero q := ⟨by omega⟩
  rw [primitiveTwoSidedZeroRealBandKernelSumAt_eq hq,
    primitiveHighZeroRealBandKernelSumAt_eq hq,
    primitiveLowZeroRealBandKernelSumAt,
    primitiveHighZeroPositiveRealBandKernelSumAt_eq hq]
  exact dirichletNontrivialZeroRealBandKernelSum_eq_high_add_low
    hq psi.1 psi.2 hx hetaHi hT

/-- Aggregate norm bound for the natural two-sided real band.  This is the
form used after decomposing the complete explicit-formula zero sum into
horizontal bands. -/
theorem sum_norm_primitiveTwoSidedZeroRealBandKernelSumAt_le
    {Q : ℕ} {x etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hetaHi : etaHi < 1) (hT : 0 ≤ T) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ‖primitiveTwoSidedZeroRealBandKernelSumAt q psi
          x etaLo etaHi T‖) ≤
      2 * ((primitiveHighZeroMass Q etaHi T : ℝ) *
        (x ^ (1 - etaLo) * Real.log x)) := by
  calc
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
      intro psi _
      have hq : 1 < q := (Finset.mem_Ioc.mp hqMem).1
      rw [primitiveTwoSidedZeroRealBandKernelSumAt_eq_high_add_low
        hq psi (zero_lt_one.trans_le hx) hetaHi hT]
      exact norm_add_le _ _
    _ ≤ _ := sum_norm_twoSidedZeroRealBandKernel_le
      hx hetaHi.le hT

end

end Erdos48
