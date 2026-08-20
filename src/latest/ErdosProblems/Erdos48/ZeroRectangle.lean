/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.DetectorPropagation
import ErdosProblems.Erdos48.SeparatedSelection
import ErdosProblems.Erdos48.LocalZeroMultiplicity

/-!
# Finite rectangles of primitive Dirichlet zeros

The zero-density argument counts zeros in the half rectangle
`1 - eta ≤ re rho ≤ 1`, `0 ≤ im rho ≤ T`.  Entirety and compactness make
this a genuine `Finset`; its weight is the exact natural analytic order.
-/

namespace Erdos48

open Complex Metric Set
open BoundedGaps.Maynard

noncomputable section

/-- Zeros of a primitive Dirichlet `L`-function in the upper half of the
standard log-free-density rectangle. -/
noncomputable def highZeroRectangle
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (eta T : ℝ) : Finset ℂ :=
  let U : Set ℂ := closedBall 0 (T + 2)
  let D := MeromorphicOn.divisor (DirichletCharacter.LFunction chi) U
  (divisor_LFunction_closedBall_support_finite
      (character_ne_one_of_isPrimitive hq chi hchi) 0 (T + 2)).toFinset.filter
    fun rho ↦
      1 - eta ≤ rho.re ∧ rho.re ≤ 1 ∧ 0 ≤ rho.im ∧ rho.im ≤ T

private theorem mem_zeroRectangle_closedBall
    {rho : ℂ} {eta T : ℝ} (heta1 : eta ≤ 1) (hT : 0 ≤ T)
    (hrelo : 1 - eta ≤ rho.re) (hrehi : rho.re ≤ 1)
    (himlo : 0 ≤ rho.im) (himhi : rho.im ≤ T) :
    rho ∈ closedBall (0 : ℂ) (T + 2) := by
  have hre0 : 0 ≤ rho.re := by linarith
  rw [mem_closedBall, dist_zero_right]
  calc
    ‖rho‖ ≤ |rho.re| + |rho.im| := Complex.norm_le_abs_re_add_abs_im rho
    _ = rho.re + rho.im := by rw [abs_of_nonneg hre0, abs_of_nonneg himlo]
    _ ≤ T + 2 := by linarith

theorem mem_highZeroRectangle_iff
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {eta T : ℝ} (heta1 : eta ≤ 1) (hT : 0 ≤ T) (rho : ℂ) :
    rho ∈ highZeroRectangle hq chi hchi eta T ↔
      DirichletCharacter.LFunction chi rho = 0 ∧
        1 - eta ≤ rho.re ∧ rho.re ≤ 1 ∧
          0 ≤ rho.im ∧ rho.im ≤ T := by
  let U : Set ℂ := closedBall 0 (T + 2)
  let D := MeromorphicOn.divisor (DirichletCharacter.LFunction chi) U
  have hnontrivial := character_ne_one_of_isPrimitive hq chi hchi
  change rho ∈
      (divisor_LFunction_closedBall_support_finite hnontrivial 0 (T + 2)).toFinset.filter
        (fun z ↦ 1 - eta ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ T) ↔ _
  rw [Finset.mem_filter,
    (divisor_LFunction_closedBall_support_finite
      hnontrivial 0 (T + 2)).mem_toFinset]
  constructor
  · rintro ⟨hsupport, hrelo, hrehi, himlo, himhi⟩
    have hrhoU : rho ∈ U := by
      simpa only [U] using
        mem_zeroRectangle_closedBall heta1 hT hrelo hrehi himlo himhi
    exact ⟨(mem_support_divisor_LFunction_iff hnontrivial hrhoU).mp
      (by simpa only [D, U] using hsupport), hrelo, hrehi, himlo, himhi⟩
  · rintro ⟨hzero, hrelo, hrehi, himlo, himhi⟩
    have hrhoU : rho ∈ U := by
      simpa only [U] using
        mem_zeroRectangle_closedBall heta1 hT hrelo hrehi himlo himhi
    refine ⟨?_, hrelo, hrehi, himlo, himhi⟩
    have hs := (mem_support_divisor_LFunction_iff hnontrivial hrhoU).mpr hzero
    simpa only [D, U] using hs

/-- The ordinates occurring in a finite zero rectangle. -/
noncomputable def highZeroOrdinates
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (eta T : ℝ) : Finset ℝ :=
  (highZeroRectangle hq chi hchi eta T).image Complex.im

theorem mem_highZeroOrdinates_iff
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {eta T : ℝ} (heta1 : eta ≤ 1) (hT : 0 ≤ T) (t : ℝ) :
    t ∈ highZeroOrdinates hq chi hchi eta T ↔
      ∃ rho : ℂ,
        DirichletCharacter.LFunction chi rho = 0 ∧
          1 - eta ≤ rho.re ∧ rho.re ≤ 1 ∧
            rho.im = t ∧ 0 ≤ t ∧ t ≤ T := by
  rw [highZeroOrdinates, Finset.mem_image]
  constructor
  · rintro ⟨rho, hrho, rfl⟩
    have hmem := (mem_highZeroRectangle_iff hq chi hchi heta1 hT rho).mp hrho
    exact ⟨rho, hmem.1, hmem.2.1, hmem.2.2.1, rfl,
      hmem.2.2.2.1, hmem.2.2.2.2⟩
  · rintro ⟨rho, hzero, hrelo, hrehi, hrhoim, ht0, htT⟩
    refine ⟨rho, ?_, hrhoim⟩
    exact (mem_highZeroRectangle_iff hq chi hchi heta1 hT rho).mpr
      ⟨hzero, hrelo, hrehi, by simpa [hrhoim] using ht0,
        by simpa [hrhoim] using htT⟩

/-- Exact total analytic multiplicity in the high-zero rectangle. -/
noncomputable def highZeroRectangleMass
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (eta T : ℝ) : ℕ :=
  ∑ rho ∈ highZeroRectangle hq chi hchi eta T,
    analyticOrderNatAt (DirichletCharacter.LFunction chi) rho

end

end Erdos48
