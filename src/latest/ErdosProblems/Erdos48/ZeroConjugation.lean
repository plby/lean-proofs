/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.ZeroKernelHighRectangle
import BoundedGaps.BombieriVinogradov.Analytic.DirichletLFunctionConjugation

/-!
# Conjugation of primitive Dirichlet zeros

Complex conjugation exchanges a character with its inverse.  Besides the
zero location, the explicit-formula argument needs preservation of analytic
multiplicity; that order statement is proved here from the iterated-
derivative characterization of analytic order.
-/

namespace Erdos48

open Complex
open scoped ComplexConjugate
open BoundedGaps.Maynard

noncomputable section

/-- Iterated derivatives commute with the holomorphic operation
`f(z) ↦ conj (f (conj z))`. -/
theorem iteratedDeriv_conj_comp_conj (n : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv n (conj ∘ f ∘ conj) =
      conj ∘ iteratedDeriv n f ∘ conj := by
  induction n generalizing f with
  | zero =>
      ext z
      simp
  | succ n ih =>
      simp only [iteratedDeriv_succ', deriv_conj_conj, ih]

/-- Conjugating a zero and inverting the character preserves its analytic
multiplicity. -/
theorem analyticOrderNatAt_LFunction_inv_conj
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (rho : ℂ) :
    analyticOrderNatAt (DirichletCharacter.LFunction chi⁻¹) (conj rho) =
      analyticOrderNatAt (DirichletCharacter.LFunction chi) rho := by
  let f : ℂ → ℂ := DirichletCharacter.LFunction chi
  let g : ℂ → ℂ := DirichletCharacter.LFunction chi⁻¹
  let h : ℂ → ℂ := conj ∘ f ∘ conj
  have hchiInv : chi⁻¹ ≠ 1 := inv_ne_one.mpr hchi
  have hgf : g = h := by
    funext z
    dsimp [g, h, f]
    simpa using LFunction_inv_conj chi hchi (conj z)
  have hf : AnalyticAt ℂ f rho :=
    (DirichletCharacter.differentiable_LFunction hchi).analyticAt rho
  have hg : AnalyticAt ℂ g (conj rho) :=
    (DirichletCharacter.differentiable_LFunction hchiInv).analyticAt (conj rho)
  have horder : analyticOrderAt g (conj rho) = analyticOrderAt f rho := by
    apply ENat.eq_of_forall_natCast_le_iff
    intro n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg,
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
    constructor
    · intro H i hi
      have hiZero := H i hi
      rw [hgf, iteratedDeriv_conj_comp_conj] at hiZero
      simpa [h, f, Function.comp_def] using congrArg conj hiZero
    · intro H i hi
      rw [hgf, iteratedDeriv_conj_comp_conj]
      simp only [Function.comp_apply, map_eq_zero]
      simpa [f] using H i hi
  simpa only [analyticOrderNatAt, g, f, horder]

/-- The integrated kernel in the Dirichlet explicit formula is compatible
with complex conjugation when its real scale is positive. -/
theorem conj_dirichletExplicitFormulaKernel
    {x : ℝ} (hx : 0 < x) (rho : ℂ) :
    conj (dirichletExplicitFormulaKernel x rho) =
      dirichletExplicitFormulaKernel x (conj rho) := by
  by_cases hrho : rho = 0
  · subst rho
    simp
  · rw [dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hx hrho,
      dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hx
        (by
          intro h
          apply hrho
          simpa using congrArg conj h)]
    rw [map_div₀, map_sub, map_one]
    congr 1
    have harg : (x : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hx.le]
      exact Real.pi_ne_zero.symm
    simpa using (Complex.conj_cpow (x : ℂ) (conj rho) harg).symm

/-- Consequently, the norm of the explicit-formula kernel is invariant
under conjugation. -/
theorem norm_dirichletExplicitFormulaKernel_conj
    {x : ℝ} (hx : 0 < x) (rho : ℂ) :
    ‖dirichletExplicitFormulaKernel x (conj rho)‖ =
      ‖dirichletExplicitFormulaKernel x rho‖ := by
  rw [← conj_dirichletExplicitFormulaKernel hx rho, norm_conj]

/-- Inversion permutes primitive characters of a fixed modulus. -/
noncomputable def primitiveCharacterInvEquiv (q : ℕ) :
    primitiveCharacters q ≃ primitiveCharacters q where
  toFun psi := ⟨psi.1⁻¹, by
    rw [DirichletCharacter.IsPrimitive,
      DirichletCharacter.conductor_inv]
    exact psi.2⟩
  invFun psi := ⟨psi.1⁻¹, by
    rw [DirichletCharacter.IsPrimitive,
      DirichletCharacter.conductor_inv]
    exact psi.2⟩
  left_inv psi := by
    apply Subtype.ext
    simp
  right_inv psi := by
    apply Subtype.ext
    simp

@[simp] theorem primitiveCharacterInvEquiv_apply_coe
    (q : ℕ) (psi : primitiveCharacters q) :
    (primitiveCharacterInvEquiv q psi).1 = psi.1⁻¹ := rfl

/-- The lower-half band contribution attached to `psi`, defined by
conjugating the upper-half contribution for the inverse character.  This
definition builds the zero-pairing into the finite sum and avoids any choice
of representatives for conjugate zero locations. -/
noncomputable def primitiveLowZeroRealBandKernelSumAt
  (q : ℕ) (psi : primitiveCharacters q)
    (x etaLo etaHi T : ℝ) : ℂ :=
  conj (primitiveHighZeroPositiveRealBandKernelSumAt q
    (primitiveCharacterInvEquiv q psi) x etaLo etaHi T)

theorem norm_primitiveLowZeroRealBandKernelSumAt
    (q : ℕ) (psi : primitiveCharacters q)
    (x etaLo etaHi T : ℝ) :
    ‖primitiveLowZeroRealBandKernelSumAt q psi x etaLo etaHi T‖ =
      ‖primitiveHighZeroPositiveRealBandKernelSumAt q
        (primitiveCharacterInvEquiv q psi) x etaLo etaHi T‖ := by
  simp [primitiveLowZeroRealBandKernelSumAt]

/-- Inversion merely permutes the primitive characters, so the aggregate
norm of all lower-half bands is exactly the aggregate upper-half norm. -/
theorem sum_norm_primitiveLowZeroRealBandKernelSumAt_eq
    (Q : ℕ) (x etaLo etaHi T : ℝ) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ‖primitiveLowZeroRealBandKernelSumAt q psi
          x etaLo etaHi T‖) =
      ∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        ‖primitiveHighZeroPositiveRealBandKernelSumAt q psi
          x etaLo etaHi T‖ := by
  apply Finset.sum_congr rfl
  intro q hq
  simp_rw [norm_primitiveLowZeroRealBandKernelSumAt]
  exact (primitiveCharacterInvEquiv q).sum_comp
    (fun psi : primitiveCharacters q ↦
      ‖primitiveHighZeroPositiveRealBandKernelSumAt q psi
        x etaLo etaHi T‖)

/-- The two conjugate half-bands together cost at most twice the aggregate
high-zero rectangle mass. -/
theorem sum_norm_twoSidedZeroRealBandKernel_le
    {Q : ℕ} {x etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hetaHi : etaHi ≤ 1) (hT : 0 ≤ T) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
        (‖primitiveHighZeroRealBandKernelSumAt q psi
            x etaLo etaHi T‖ +
          ‖primitiveLowZeroRealBandKernelSumAt q psi
            x etaLo etaHi T‖)) ≤
      2 * ((primitiveHighZeroMass Q etaHi T : ℝ) *
        (x ^ (1 - etaLo) * Real.log x)) := by
  have hhigh := sum_norm_highZeroRealBandKernelSum_le
    (Q := Q) (x := x) (etaLo := etaLo) (etaHi := etaHi) (T := T)
      hx hetaHi hT
  have hlow :
      (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
          ‖primitiveLowZeroRealBandKernelSumAt q psi
            x etaLo etaHi T‖) ≤
        (primitiveHighZeroMass Q etaHi T : ℝ) *
          (x ^ (1 - etaLo) * Real.log x) := by
    rw [sum_norm_primitiveLowZeroRealBandKernelSumAt_eq]
    exact sum_norm_highZeroPositiveRealBandKernelSum_le
      (Q := Q) (x := x) (etaLo := etaLo) (etaHi := etaHi) (T := T)
        hx hetaHi hT
  have hsum := add_le_add hhigh hlow
  simpa only [Finset.sum_add_distrib, two_mul]
    using hsum

end

end Erdos48
