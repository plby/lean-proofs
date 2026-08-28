import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauNormalizationMatrices
import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauUniqueness

/-!
# Cyclic normalization of the actual integral modular pair

The finite integral matrix classification produces an actual power of
`A = TS` whose inverse conjugates the second modular transformation to
`S` projectively.  The normalizing matrix fixes the source's point `ρ`.
It simultaneously changes the cusp transformation to translation by
`-1`, and any fixed point of the second generator to `i`.

No global period map, desired covariance law, or desired representation
is assumed.  The hypotheses are exactly the two integer trace conditions
on the actual matrix to be normalized.
-/

noncomputable section

open Function Set Matrix ModularGroup UpperHalfPlane
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

theorem triangleModularA_smul_rhoPoint : triangleModularA • rhoPoint = rhoPoint := by
  rw [triangleModularA_eq_T_mul_S]
  exact TS_smul_rhoPoint

theorem triangleModularA_pow_smul_rhoPoint (n : ℕ) :
    triangleModularA ^ n • rhoPoint = rhoPoint := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_smul, triangleModularA_smul_rhoPoint, ih]

/-- Each of the possible normalizers fixes the already normalized
order-three elliptic value. -/
theorem modularCyclicNormalizer_smul_rhoPoint (k : Fin 3) :
    modularCyclicNormalizer k • rhoPoint = rhoPoint := by
  rw [modularCyclicNormalizer, inv_smul_eq_iff]
  exact (triangleModularA_pow_smul_rhoPoint k).symm

theorem modularCyclicNormalizer_intertwines_A (k : Fin 3) (z : ℍ) :
    modularCyclicNormalizer k • (triangleModularA • z) =
      triangleModularA • (modularCyclicNormalizer k • z) := by
  have he := congrArg (fun C : SL(2, ℤ) => C • (modularCyclicNormalizer k • z))
    (modularCyclicNormalizer_conjugate_A k)
  simpa only [mul_smul, inv_smul_smul] using he

private theorem normalized_B_action (k : Fin 3) (B : SL(2, ℤ))
    (hB : modularProjectivization
      (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
      modularProjectivization S) (z : ℍ) :
    modularCyclicNormalizer k • (B • z) = S • (modularCyclicNormalizer k • z) := by
  have he := congrArg (fun C : PSL(2, ℤ) =>
    modularPSLPermutation C (modularCyclicNormalizer k • z)) hB
  simpa only [modularPSLPermutation_projectivization, mul_smul, inv_smul_smul] using he

private theorem normalized_product_projective (k : Fin 3) (B : SL(2, ℤ))
    (hB : modularProjectivization
      (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
      modularProjectivization S) :
    modularProjectivization
      (modularCyclicNormalizer k * (triangleModularA * B) * (modularCyclicNormalizer k)⁻¹) =
      modularProjectivization T := by
  have he : modularCyclicNormalizer k * (triangleModularA * B) *
      (modularCyclicNormalizer k)⁻¹ =
      (modularCyclicNormalizer k * triangleModularA * (modularCyclicNormalizer k)⁻¹) *
        (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) := by group
  rw [he, map_mul, modularCyclicNormalizer_conjugate_A, hB]
  exact triangleModularGenerator₁_mul_generator₂

private theorem normalized_cusp_projective (k : Fin 3) (B : SL(2, ℤ))
    (hB : modularProjectivization
      (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
      modularProjectivization S) :
    modularProjectivization
      (modularCyclicNormalizer k * (triangleModularA * B)⁻¹ * (modularCyclicNormalizer k)⁻¹) =
      modularProjectivization T⁻¹ := by
  have he : modularCyclicNormalizer k * (triangleModularA * B)⁻¹ *
      (modularCyclicNormalizer k)⁻¹ =
      (modularCyclicNormalizer k * (triangleModularA * B) *
        (modularCyclicNormalizer k)⁻¹)⁻¹ := by group
  rw [he, map_inv, normalized_product_projective k B hB, ← map_inv]

private theorem normalized_cusp_action (k : Fin 3) (B : SL(2, ℤ))
    (hB : modularProjectivization
      (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
      modularProjectivization S) (z : ℍ) :
    modularCyclicNormalizer k • ((triangleModularA * B)⁻¹ • z) =
      T⁻¹ • (modularCyclicNormalizer k • z) := by
  have he := congrArg (fun C : PSL(2, ℤ) =>
    modularPSLPermutation C (modularCyclicNormalizer k • z))
      (normalized_cusp_projective k B hB)
  simpa only [modularPSLPermutation_projectivization, mul_smul, inv_smul_smul] using he

/-- One actual cyclic normalizer preserves the first elliptic value and
generator and changes the second generator and cusp to the standard
modular transformations.  All three choices are explicitly bounded. -/
theorem modular_pair_cyclic_normalization (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod : Matrix.trace (triangleModularA * B).val = 2 ∨
      Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3,
      modularCyclicNormalizer k • rhoPoint = rhoPoint ∧
      (∀ z : ℍ, modularCyclicNormalizer k • (triangleModularA • z) =
        triangleModularA • (modularCyclicNormalizer k • z)) ∧
      (∀ z : ℍ, modularCyclicNormalizer k • (B • z) =
        S • (modularCyclicNormalizer k • z)) ∧
      (∀ z : ℍ, modularCyclicNormalizer k • ((triangleModularA * B)⁻¹ • z) =
        T⁻¹ • (modularCyclicNormalizer k • z)) := by
  obtain ⟨k, hk⟩ := modular_pair_projective_conjugation_normalization B htr hprod
  exact ⟨k, modularCyclicNormalizer_smul_rhoPoint k,
    modularCyclicNormalizer_intertwines_A k, normalized_B_action k B hk,
    normalized_cusp_action k B hk⟩

/-- In the same simultaneous normalization the cusp action is literally
the negative unit translation in the upper-half-plane coordinate. -/
theorem modular_pair_cusp_translation_normalization (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod : Matrix.trace (triangleModularA * B).val = 2 ∨
      Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3,
      modularCyclicNormalizer k • rhoPoint = rhoPoint ∧
      (∀ z : ℍ, modularCyclicNormalizer k • (B • z) =
        S • (modularCyclicNormalizer k • z)) ∧
      (∀ z : ℍ, modularCyclicNormalizer k • ((triangleModularA * B)⁻¹ • z) =
        (-1 : ℝ) +ᵥ (modularCyclicNormalizer k • z)) := by
  obtain ⟨k, hρ, _, hB, hcusp⟩ := modular_pair_cyclic_normalization B htr hprod
  refine ⟨k, hρ, hB, fun z => ?_⟩
  rw [hcusp z]
  simpa using UpperHalfPlane.modular_T_zpow_smul (modularCyclicNormalizer k • z) (-1)

/-- Any fixed point of the second actual modular transformation is
simultaneously taken to `i`, while `ρ` and the first generator stay fixed. -/
theorem modular_pair_elliptic_value_normalization (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod : Matrix.trace (triangleModularA * B).val = 2 ∨
      Matrix.trace (triangleModularA * B).val = -2)
    (z : ℍ) (hz : B • z = z) :
    ∃ k : Fin 3,
      modularCyclicNormalizer k • rhoPoint = rhoPoint ∧
      modularCyclicNormalizer k • z = UpperHalfPlane.I ∧
      (∀ w : ℍ, modularCyclicNormalizer k • (triangleModularA • w) =
        triangleModularA • (modularCyclicNormalizer k • w)) ∧
      (∀ w : ℍ, modularCyclicNormalizer k • (B • w) =
        S • (modularCyclicNormalizer k • w)) ∧
      (∀ w : ℍ, modularCyclicNormalizer k • ((triangleModularA * B)⁻¹ • w) =
        T⁻¹ • (modularCyclicNormalizer k • w)) := by
  obtain ⟨k, hρ, hA, hB, hcusp⟩ := modular_pair_cyclic_normalization B htr hprod
  refine ⟨k, hρ, ?_, hA, hB, hcusp⟩
  apply (modularI_fixed_iff _).mp
  exact (hB z).symm.trans (congrArg (fun w : ℍ => modularCyclicNormalizer k • w) hz)

end Wikipedia.HopfProblem.SpecialPeriods
