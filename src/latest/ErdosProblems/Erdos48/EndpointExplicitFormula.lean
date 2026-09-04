/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.EndpointMass
import ErdosProblems.Erdos48.ZeroBandPartition
import BoundedGaps.BombieriVinogradov.Analytic.DirichletPrimitiveExplicitFormula

/-!
# The primitive explicit formula at the FLP endpoint

This file isolates the direct bridge from the primitive character sum used by
Ford--Luca--Pomerance to the complete, multiplicity-weighted nontrivial-zero
kernel.  Conductors in the application are greater than one, so the principal
main term vanishes.
-/

namespace Erdos48

open Complex
open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

/-- The aggregate norm of the complete explicit-formula zero kernel at one
primitive conductor. -/
noncomputable def primitiveZeroKernelMass (x q : ℕ) (T : ℝ) : ℝ :=
  if hq : 0 < q then
    letI : NeZero q := ⟨by omega⟩
    ∑ psi : primitiveCharacters q,
      ‖dirichletNontrivialZeroKernelSum psi.1 (x : ℝ) T‖
  else 0

theorem primitiveZeroKernelMass_eq
    (x : ℕ) {q : ℕ} (hq : 0 < q) (T : ℝ) :
    primitiveZeroKernelMass x q T =
      letI : NeZero q := ⟨by omega⟩
      ∑ psi : primitiveCharacters q,
        ‖dirichletNontrivialZeroKernelSum psi.1 (x : ℝ) T‖ := by
  simp only [primitiveZeroKernelMass, dif_pos hq]

/-- For a primitive character of conductor greater than one, the source
main/zero expression is the negative of the complete nontrivial-zero kernel.
-/
theorem dirichletExplicitFormulaMainZeroTerms_eq_neg_kernel
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (psi : primitiveCharacters q) (x T : ℝ) :
    dirichletExplicitFormulaMainZeroTerms psi.1 x T =
      -dirichletNontrivialZeroKernelSum psi.1 x T := by
  rw [dirichletExplicitFormulaMainZeroTerms]
  simp [primitiveCharacter_ne_one_of_one_lt hq psi]

/-- The natural endpoint of one primitive twist is bounded by the exact
explicit-formula error and the norm of its complete zero kernel. -/
theorem norm_twistedChebyshevSum_le_error_add_zeroKernel
    {K q x : ℕ} [NeZero q] (hq : 1 < q)
    (psi : primitiveCharacters q) {T : ℝ}
    (hformula :
      ‖twistedChebyshevSum x q psi.1 -
          dirichletExplicitFormulaMainZeroTerms psi.1 (x : ℝ) T‖ ≤
        (K : ℝ) * dirichletExplicitFormulaErrorScale (x : ℝ) q T) :
    ‖twistedChebyshevSum x q psi.1‖ ≤
      (K : ℝ) * dirichletExplicitFormulaErrorScale (x : ℝ) q T +
        ‖dirichletNontrivialZeroKernelSum psi.1 (x : ℝ) T‖ := by
  rw [dirichletExplicitFormulaMainZeroTerms_eq_neg_kernel hq] at hformula
  calc
    ‖twistedChebyshevSum x q psi.1‖ =
        ‖(twistedChebyshevSum x q psi.1 +
            dirichletNontrivialZeroKernelSum psi.1 (x : ℝ) T) -
          dirichletNontrivialZeroKernelSum psi.1 (x : ℝ) T‖ := by
      congr 1
      ring
    _ ≤ ‖twistedChebyshevSum x q psi.1 +
            dirichletNontrivialZeroKernelSum psi.1 (x : ℝ) T‖ +
          ‖dirichletNontrivialZeroKernelSum psi.1 (x : ℝ) T‖ :=
      norm_sub_le _ _
    _ ≤ (K : ℝ) * dirichletExplicitFormulaErrorScale (x : ℝ) q T +
          ‖dirichletNontrivialZeroKernelSum psi.1 (x : ℝ) T‖ := by
      exact add_le_add (by simpa only [sub_neg_eq_add] using hformula) le_rfl

/-- Uniform primitive explicit-formula endpoint estimate, with the numerical
constant existentially supplied by the audited BoundedGaps development. -/
theorem exists_nat_norm_twistedChebyshevSum_le_error_add_zeroKernel :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (psi : primitiveCharacters q) (T : ℝ), 2 ≤ T →
          ∀ x : ℕ, 4 ≤ x → T ≤ (x : ℝ) →
            ‖twistedChebyshevSum x q psi.1‖ ≤
              (K : ℝ) *
                  dirichletExplicitFormulaErrorScale (x : ℝ) q T +
                ‖dirichletNontrivialZeroKernelSum
                  psi.1 (x : ℝ) T‖ := by
  obtain ⟨K, hK, hformula⟩ :=
    exists_nat_norm_twistedChebyshevSum_sub_dirichletExplicitFormulaMainZeroTerms_le_of_isPrimitive
  refine ⟨K, hK, ?_⟩
  intro q _ hq psi T hT x hx hTx
  exact norm_twistedChebyshevSum_le_error_add_zeroKernel hq psi
    (hformula q psi.1 psi.2 T hT x hx hTx)

/-- Summing the pointwise explicit formula over all primitive characters of
one conductor gives FLP's endpoint mass plus one constant error per
character. -/
theorem primitiveEndpointMass_le_card_mul_error_add_zeroKernelMass
    {K q x : ℕ} [NeZero q] (hq : 1 < q) {T : ℝ}
    (hpoint : ∀ psi : primitiveCharacters q,
      ‖twistedChebyshevSum x q psi.1‖ ≤
        (K : ℝ) * dirichletExplicitFormulaErrorScale (x : ℝ) q T +
          ‖dirichletNontrivialZeroKernelSum psi.1 (x : ℝ) T‖) :
    primitiveEndpointMass x q ≤
      (Fintype.card (primitiveCharacters q) : ℝ) *
          ((K : ℝ) * dirichletExplicitFormulaErrorScale (x : ℝ) q T) +
        primitiveZeroKernelMass x q T := by
  classical
  rw [primitiveZeroKernelMass_eq x (by omega) T]
  unfold primitiveEndpointMass
  calc
    (∑ psi : primitiveCharacters q,
        ‖twistedChebyshevSum x q psi.1‖) ≤
        ∑ psi : primitiveCharacters q,
          ((K : ℝ) * dirichletExplicitFormulaErrorScale (x : ℝ) q T +
            ‖dirichletNontrivialZeroKernelSum psi.1 (x : ℝ) T‖) :=
      Finset.sum_le_sum fun psi _ ↦ hpoint psi
    _ = (Fintype.card (primitiveCharacters q) : ℝ) *
          ((K : ℝ) * dirichletExplicitFormulaErrorScale (x : ℝ) q T) +
        ∑ psi : primitiveCharacters q,
          ‖dirichletNontrivialZeroKernelSum psi.1 (x : ℝ) T‖ := by
      rw [Finset.sum_add_distrib]
      simp

/-- The fully uniform one-conductor endpoint inequality. -/
theorem exists_nat_primitiveEndpointMass_le_card_mul_error_add_zeroKernelMass :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ (q : ℕ), 1 < q →
        ∀ (T : ℝ), 2 ≤ T →
          ∀ x : ℕ, 4 ≤ x → T ≤ (x : ℝ) →
            primitiveEndpointMass x q ≤
              (Fintype.card (primitiveCharacters q) : ℝ) *
                  ((K : ℝ) *
                    dirichletExplicitFormulaErrorScale (x : ℝ) q T) +
                primitiveZeroKernelMass x q T := by
  obtain ⟨K, hK, hpoint⟩ :=
    exists_nat_norm_twistedChebyshevSum_le_error_add_zeroKernel
  refine ⟨K, hK, ?_⟩
  intro q hq T hT x hx hTx
  let : NeZero q := ⟨by omega⟩
  apply primitiveEndpointMass_le_card_mul_error_add_zeroKernelMass hq
  intro psi
  exact hpoint q hq psi T hT x hx hTx

end

end Erdos48
