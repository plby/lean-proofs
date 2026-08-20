/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.EndpointExplicitFormula

/-!
# Linear real-part bands for the endpoint explicit formula

The Page band has width `eta`.  Successive bands of the same width exhaust a
finite right-hand portion of the critical strip.  This file proves the exact
finite decomposition, leaving a single far-left remainder.
-/

namespace Erdos48

open Complex
open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

/-- The contribution of zeros strictly to the left of the first `J+1`
linear bands of width `eta`. -/
noncomputable def dirichletNontrivialZeroFarKernelSum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x eta : ℝ) (J : ℕ) (T : ℝ) : ℂ :=
  ∑ rho ∈ (dirichletNontrivialLFunctionZerosFinset chi T).filter
      (fun rho ↦ rho.re < 1 - ((J + 1 : ℕ) : ℝ) * eta),
    (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : ℂ) *
      dirichletExplicitFormulaKernel x rho

/-- The first band and the far-left part partition the complete nontrivial
zero kernel. -/
theorem dirichletNontrivialZeroKernelSum_eq_firstBand_add_far
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x eta T : ℝ) :
    dirichletNontrivialZeroKernelSum chi x T =
      dirichletNontrivialZeroRealBandKernelSum chi x 0 eta T +
        dirichletNontrivialZeroFarKernelSum chi x eta 0 T := by
  classical
  let S := dirichletNontrivialLFunctionZerosFinset chi T
  let f : ℂ → ℂ := fun rho ↦
    (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : ℂ) *
      dirichletExplicitFormulaKernel x rho
  let p : ℂ → Prop := fun rho ↦ rho.re < 1 - eta
  have hsplit := Finset.sum_filter_add_sum_filter_not S p f
  have hband :
      dirichletNontrivialZeroRealBand chi 0 eta T =
        S.filter (fun rho ↦ ¬p rho) := by
    ext rho
    simp only [dirichletNontrivialZeroRealBand, S, p,
      Finset.mem_filter, mem_dirichletNontrivialLFunctionZerosFinset_iff]
    constructor
    · rintro ⟨hS, hlo, hhi⟩
      exact ⟨hS, by linarith⟩
    · rintro ⟨hS, hnlt⟩
      exact ⟨hS, by linarith, by simpa using hS.1.2.2⟩
  rw [dirichletNontrivialZeroKernelSum,
    dirichletNontrivialZeroRealBandKernelSum,
    dirichletNontrivialZeroFarKernelSum, hband]
  simp only [Nat.zero_add, Nat.cast_one, one_mul]
  change (∑ rho ∈ S, f rho) =
    (∑ rho ∈ S.filter (fun rho ↦ ¬p rho), f rho) +
      ∑ rho ∈ S.filter p, f rho
  simpa [add_comm] using hsplit.symm

/-- One far-left remainder splits into the next adjacent band and the next
far-left remainder. -/
theorem dirichletNontrivialZeroFarKernelSum_eq_nextBand_add_far
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x eta T : ℝ) (J : ℕ) (heta : 0 ≤ eta) :
    dirichletNontrivialZeroFarKernelSum chi x eta J T =
      dirichletNontrivialZeroRealBandKernelSum chi x
          (((J + 1 : ℕ) : ℝ) * eta)
          (((J + 2 : ℕ) : ℝ) * eta) T +
        dirichletNontrivialZeroFarKernelSum chi x eta (J + 1) T := by
  classical
  let S := dirichletNontrivialLFunctionZerosFinset chi T
  let f : ℂ → ℂ := fun rho ↦
    (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : ℂ) *
      dirichletExplicitFormulaKernel x rho
  let upper : ℝ := 1 - ((J + 1 : ℕ) : ℝ) * eta
  let lower : ℝ := 1 - ((J + 2 : ℕ) : ℝ) * eta
  let A := S.filter (fun rho ↦ rho.re < upper)
  let p : ℂ → Prop := fun rho ↦ rho.re < lower
  have hsplit := Finset.sum_filter_add_sum_filter_not A p f
  have hnext :
      A.filter (fun rho ↦ ¬p rho) =
        dirichletNontrivialZeroRealBand chi
          (((J + 1 : ℕ) : ℝ) * eta)
          (((J + 2 : ℕ) : ℝ) * eta) T := by
    ext rho
    simp only [A, p, upper, lower,
      dirichletNontrivialZeroRealBand, S, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hrho, hupp⟩, hnotLow⟩
      exact ⟨hrho, by linarith, hupp⟩
    · rintro ⟨hrho, hlow, hupp⟩
      exact ⟨⟨hrho, hupp⟩, by linarith⟩
  have hfar :
      A.filter p =
        S.filter
          (fun rho ↦ rho.re < 1 - (((J + 1) + 1 : ℕ) : ℝ) * eta) := by
    ext rho
    simp only [A, p, upper, lower, S, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hrho, _⟩, hlow⟩
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ⟨hrho, hlow⟩
    · rintro ⟨hrho, hlow⟩
      have hupp : rho.re < upper := by
        dsimp [upper, lower] at hlow ⊢
        push_cast at hlow ⊢
        nlinarith
      exact ⟨⟨hrho, hupp⟩, by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlow⟩
  rw [dirichletNontrivialZeroFarKernelSum,
    dirichletNontrivialZeroRealBandKernelSum,
    dirichletNontrivialZeroFarKernelSum, ← hnext, ← hfar]
  change (∑ rho ∈ A, f rho) =
    (∑ rho ∈ A.filter (fun rho ↦ ¬p rho), f rho) +
      ∑ rho ∈ A.filter p, f rho
  simpa [add_comm] using hsplit.symm

/-- Exact decomposition into `J+1` adjacent bands followed by one far-left
remainder. -/
theorem dirichletNontrivialZeroKernelSum_eq_sum_linearBands_add_far
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x eta T : ℝ) (J : ℕ) (heta : 0 ≤ eta) :
    dirichletNontrivialZeroKernelSum chi x T =
      (∑ j ∈ Finset.range (J + 1),
        dirichletNontrivialZeroRealBandKernelSum chi x
          ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T) +
        dirichletNontrivialZeroFarKernelSum chi x eta J T := by
  induction J with
  | zero =>
      simpa using
        dirichletNontrivialZeroKernelSum_eq_firstBand_add_far chi x eta T
  | succ J ih =>
      calc
        dirichletNontrivialZeroKernelSum chi x T =
            (∑ j ∈ Finset.range (J + 1),
              dirichletNontrivialZeroRealBandKernelSum chi x
                ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T) +
              dirichletNontrivialZeroFarKernelSum chi x eta J T := ih
        _ = (∑ j ∈ Finset.range (J + 1),
              dirichletNontrivialZeroRealBandKernelSum chi x
                ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T) +
            (dirichletNontrivialZeroRealBandKernelSum chi x
                (((J + 1 : ℕ) : ℝ) * eta)
                (((J + 2 : ℕ) : ℝ) * eta) T +
              dirichletNontrivialZeroFarKernelSum chi x eta (J + 1) T) := by
          rw [dirichletNontrivialZeroFarKernelSum_eq_nextBand_add_far
            chi x eta T J heta]
        _ = (∑ j ∈ Finset.range ((J + 1) + 1),
              dirichletNontrivialZeroRealBandKernelSum chi x
                ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T) +
              dirichletNontrivialZeroFarKernelSum chi x eta (J + 1) T := by
          conv_rhs =>
            lhs
            rw [Finset.sum_range_succ]
          ring

end

end Erdos48
