/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.LogFreeDensityEnvelope
import BoundedGaps.BombieriVinogradov.Analytic.DirichletNonexceptionalZeroKernel

/-!
# Explicit-formula kernels in high-zero rectangles

This file is the first bridge from zero density to the explicit formula.
It bounds the kernel contribution of a real-part band by the analytic
multiplicity of the enclosing high-zero rectangle.
-/

namespace Erdos48

open Complex
open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

/-- The upper-half zeros in the `etaHi` rectangle which lie strictly to the
left of the line `re = 1 - etaLo`. -/
noncomputable def highZeroRealBand
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (etaLo etaHi T : ℝ) : Finset ℂ :=
  (highZeroRectangle hq chi hchi etaHi T).filter fun rho ↦
    rho.re < 1 - etaLo

theorem highZeroRealBand_subset
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (etaLo etaHi T : ℝ) :
    highZeroRealBand hq chi hchi etaLo etaHi T ⊆
      highZeroRectangle hq chi hchi etaHi T := by
  exact Finset.filter_subset _ _

/-- The modified explicit-formula kernel over one upper-half real-part
band. -/
noncomputable def highZeroRealBandKernelSum
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (x etaLo etaHi T : ℝ) : ℂ :=
  ∑ rho ∈ highZeroRealBand hq chi hchi etaLo etaHi T,
    (analyticOrderNatAt
      (DirichletCharacter.LFunction chi) rho : ℂ) *
        dirichletExplicitFormulaKernel x rho

/-- A real-part band contributes at most its enclosing multiplicity times
the largest kernel on that band. -/
theorem norm_highZeroRealBandKernelSum_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {x etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hetaHi : etaHi ≤ 1) (hT : 0 ≤ T) :
    ‖highZeroRealBandKernelSum hq chi hchi x etaLo etaHi T‖ ≤
      (highZeroRectangleMass hq chi hchi etaHi T : ℝ) *
        (x ^ (1 - etaLo) * Real.log x) := by
  classical
  let S := highZeroRealBand hq chi hchi etaLo etaHi T
  let Z := highZeroRectangle hq chi hchi etaHi T
  let C : ℝ := x ^ (1 - etaLo) * Real.log x
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
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
      hetaHi hT rho).mp hrhoData.1
    have hre0 : 0 ≤ rho.re := by linarith
    have hkernel := norm_dirichletExplicitFormulaKernel_le_rpow_mul_log
      hx hre0
    have hpow : x ^ rho.re ≤ x ^ (1 - etaLo) :=
      Real.rpow_le_rpow_of_exponent_le hx hrhoData.2.le
    have hkernelC : ‖dirichletExplicitFormulaKernel x rho‖ ≤ C := by
      exact hkernel.trans <|
        mul_le_mul_of_nonneg_right hpow hlog
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hkernelC (by positivity)
  unfold highZeroRealBandKernelSum
  change ‖∑ rho ∈ S,
      (analyticOrderNatAt
        (DirichletCharacter.LFunction chi) rho : ℂ) *
          dirichletExplicitFormulaKernel x rho‖ ≤ _
  calc
    ‖∑ rho ∈ S,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho‖ ≤
        ∑ rho ∈ S,
          ‖(analyticOrderNatAt
            (DirichletCharacter.LFunction chi) rho : ℂ) *
              dirichletExplicitFormulaKernel x rho‖ := norm_sum_le _ _
    _ ≤ ∑ rho ∈ S,
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
    _ = (highZeroRectangleMass hq chi hchi etaHi T : ℝ) *
        (x ^ (1 - etaLo) * Real.log x) := rfl

/-- Termwise form of the preceding estimate.  It is useful for taking a
strict sub-band (in particular, positive ordinates) without relying on
cancellation in the larger band. -/
theorem sum_norm_highZeroRealBand_terms_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {x etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hetaHi : etaHi ≤ 1) (hT : 0 ≤ T) :
    (∑ rho ∈ highZeroRealBand hq chi hchi etaLo etaHi T,
        ‖(analyticOrderNatAt
            (DirichletCharacter.LFunction chi) rho : ℂ) *
          dirichletExplicitFormulaKernel x rho‖) ≤
      (highZeroRectangleMass hq chi hchi etaHi T : ℝ) *
        (x ^ (1 - etaLo) * Real.log x) := by
  classical
  let S := highZeroRealBand hq chi hchi etaLo etaHi T
  let Z := highZeroRectangle hq chi hchi etaHi T
  let C : ℝ := x ^ (1 - etaLo) * Real.log x
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
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
      hetaHi hT rho).mp hrhoData.1
    have hre0 : 0 ≤ rho.re := by linarith
    have hkernel := norm_dirichletExplicitFormulaKernel_le_rpow_mul_log
      hx hre0
    have hpow : x ^ rho.re ≤ x ^ (1 - etaLo) :=
      Real.rpow_le_rpow_of_exponent_le hx hrhoData.2.le
    have hkernelC : ‖dirichletExplicitFormulaKernel x rho‖ ≤ C := by
      exact hkernel.trans <|
        mul_le_mul_of_nonneg_right hpow hlog
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

/-- The positive-ordinate portion of an upper-half real band. -/
noncomputable def highZeroPositiveRealBand
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (etaLo etaHi T : ℝ) : Finset ℂ :=
  (highZeroRealBand hq chi hchi etaLo etaHi T).filter
    fun rho ↦ 0 < rho.im

/-- Modified kernel over the strict positive-ordinate part of a band. -/
noncomputable def highZeroPositiveRealBandKernelSum
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (x etaLo etaHi T : ℝ) : ℂ :=
  ∑ rho ∈ highZeroPositiveRealBand hq chi hchi etaLo etaHi T,
    (analyticOrderNatAt
      (DirichletCharacter.LFunction chi) rho : ℂ) *
        dirichletExplicitFormulaKernel x rho

theorem norm_highZeroPositiveRealBandKernelSum_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {x etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hetaHi : etaHi ≤ 1) (hT : 0 ≤ T) :
    ‖highZeroPositiveRealBandKernelSum hq chi hchi
        x etaLo etaHi T‖ ≤
      (highZeroRectangleMass hq chi hchi etaHi T : ℝ) *
        (x ^ (1 - etaLo) * Real.log x) := by
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
    _ ≤ _ := sum_norm_highZeroRealBand_terms_le
      hq chi hchi hx hetaHi hT

/-- Totalized band kernel for a primitive character.  Conductors occurring
in the aggregate theorem are all greater than one, but totalization keeps
the finite sum free of proof-valued arguments. -/
noncomputable def primitiveHighZeroRealBandKernelSumAt
    (q : ℕ) (psi : primitiveCharacters q)
    (x etaLo etaHi T : ℝ) : ℂ :=
  if hq : 1 < q then
    @highZeroRealBandKernelSum q ⟨by omega⟩ hq psi.1 psi.2
      x etaLo etaHi T
  else 0

/-- Totalized strict-positive-ordinate band kernel. -/
noncomputable def primitiveHighZeroPositiveRealBandKernelSumAt
    (q : ℕ) (psi : primitiveCharacters q)
    (x etaLo etaHi T : ℝ) : ℂ :=
  if hq : 1 < q then
    @highZeroPositiveRealBandKernelSum q ⟨by omega⟩ hq psi.1 psi.2
      x etaLo etaHi T
  else 0

theorem primitiveHighZeroPositiveRealBandKernelSumAt_eq
    {q : ℕ} (hq : 1 < q) (psi : primitiveCharacters q)
    (x etaLo etaHi T : ℝ) :
    primitiveHighZeroPositiveRealBandKernelSumAt q psi
        x etaLo etaHi T =
      @highZeroPositiveRealBandKernelSum q ⟨by omega⟩ hq psi.1 psi.2
        x etaLo etaHi T := by
  simp only [primitiveHighZeroPositiveRealBandKernelSumAt, dif_pos hq]

theorem sum_norm_highZeroPositiveRealBandKernelSum_le
    {Q : ℕ} {x etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hetaHi : etaHi ≤ 1) (hT : 0 ≤ T) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ‖primitiveHighZeroPositiveRealBandKernelSumAt q psi
          x etaLo etaHi T‖) ≤
      (primitiveHighZeroMass Q etaHi T : ℝ) *
        (x ^ (1 - etaLo) * Real.log x) := by
  classical
  let C : ℝ := x ^ (1 - etaLo) * Real.log x
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.log_nonneg hx)
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
      letI : NeZero q := ⟨by omega⟩
      rw [primitiveHighZeroPositiveRealBandKernelSumAt_eq hq]
      simpa only [primitiveHighZeroMassAt_eq hq, C] using
        norm_highZeroPositiveRealBandKernelSum_le hq psi.1 psi.2
          hx hetaHi hT
    _ = (primitiveHighZeroMass Q etaHi T : ℝ) * C := by
      unfold primitiveHighZeroMass
      push_cast
      simp_rw [Finset.sum_mul]
    _ = _ := rfl

theorem primitiveHighZeroRealBandKernelSumAt_eq
    {q : ℕ} (hq : 1 < q) (psi : primitiveCharacters q)
    (x etaLo etaHi T : ℝ) :
    primitiveHighZeroRealBandKernelSumAt q psi x etaLo etaHi T =
      @highZeroRealBandKernelSum q ⟨by omega⟩ hq psi.1 psi.2
        x etaLo etaHi T := by
  simp only [primitiveHighZeroRealBandKernelSumAt, dif_pos hq]

/-- Summing the preceding band bound over all primitive characters and
conductors replaces the individual rectangle masses by the aggregate mass
used in the density theorem. -/
theorem sum_norm_highZeroRealBandKernelSum_le
    {Q : ℕ} {x etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hetaHi : etaHi ≤ 1) (hT : 0 ≤ T) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ‖primitiveHighZeroRealBandKernelSumAt q psi
          x etaLo etaHi T‖) ≤
      (primitiveHighZeroMass Q etaHi T : ℝ) *
        (x ^ (1 - etaLo) * Real.log x) := by
  classical
  let C : ℝ := x ^ (1 - etaLo) * Real.log x
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.log_nonneg hx)
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
      letI : NeZero q := ⟨by omega⟩
      rw [primitiveHighZeroRealBandKernelSumAt_eq hq]
      simpa only [primitiveHighZeroMassAt_eq hq, C] using
        norm_highZeroRealBandKernelSum_le hq psi.1 psi.2
          hx hetaHi hT
    _ = (primitiveHighZeroMass Q etaHi T : ℝ) * C := by
      unfold primitiveHighZeroMass
      push_cast
      simp_rw [Finset.sum_mul]
    _ = (primitiveHighZeroMass Q etaHi T : ℝ) *
        (x ^ (1 - etaLo) * Real.log x) := rfl

end

end Erdos48
