import Wikipedia.HopfProblem.SpecialPeriodsTriangleModularRepresentation
import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauNormalizationArithmetic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Integral modular matrices compatible with the normalized order-three generator

For the actual matrix `A = TS`, an integral determinant-one matrix `B`
with trace zero and `trace (AB) = ±2` has only six possibilities.  They
are the three conjugates of `S` by `1,A,A²` and their central negatives.
This is an integer-matrix classification, not an assumed monodromy or
normalization of a desired period map.
-/

noncomputable section

open Function Set Matrix ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The three actual cyclic conjugates of the modular involution lift. -/
def modularSCyclicConjugate (k : Fin 3) : SL(2, ℤ) :=
  triangleModularA ^ (k : ℕ) * S * (triangleModularA ^ (k : ℕ))⁻¹

@[simp] theorem modularSCyclicConjugate_zero : modularSCyclicConjugate 0 = S := by
  simp [modularSCyclicConjugate]

theorem modularSCyclicConjugate_zero_matrix :
    (modularSCyclicConjugate 0 : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, 0] := by
  decide

theorem modularSCyclicConjugate_one_matrix :
    (modularSCyclicConjugate 1 : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -2; 1, -1] := by
  decide

theorem modularSCyclicConjugate_two_matrix :
    (modularSCyclicConjugate 2 : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; 2, -1] := by
  decide

theorem triangleModularA_product_trace (B : SL(2, ℤ)) :
    Matrix.trace (triangleModularA * B).val = B 0 0 + B 0 1 - B 1 0 := by
  change Matrix.trace ((triangleModularA : Matrix (Fin 2) (Fin 2) ℤ) * B.val) = _
  rw [Matrix.trace_fin_two]
  simp [triangleModularA, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem trace_zero_entry_one_one (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0) : B 1 1 = -(B 0 0) := by
  rw [Matrix.trace_fin_two] at htr
  omega

/-- The sign `trace (AB) = -2` picks out the three positive cyclic
conjugates, without any residual central sign. -/
theorem modular_trace_zero_trace_neg_two_classification (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod : Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3, B = modularSCyclicConjugate k := by
  have h11 := trace_zero_entry_one_one B htr
  have hdet : -(B 0 0) ^ 2 - B 0 1 * B 1 0 = 1 := by
    have hd : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 :=
      (Matrix.det_fin_two B.val).symm.trans B.property
    rw [h11] at hd
    nlinarith [hd]
  rw [triangleModularA_product_trace] at hprod
  rcases GlobalTauNormalization.trace_neg_two_triples (B 0 0) (B 0 1) (B 1 0)
    hdet hprod with ⟨hp, hq, hr⟩ | ⟨hp, hq, hr⟩ | ⟨hp, hq, hr⟩
  · refine ⟨0, Subtype.ext ?_⟩
    rw [modularSCyclicConjugate_zero_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, h11]
  · refine ⟨1, Subtype.ext ?_⟩
    rw [modularSCyclicConjugate_one_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, h11]
  · refine ⟨2, Subtype.ext ?_⟩
    rw [modularSCyclicConjugate_two_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, h11]

/-- The exact finite classification of integral order-two lifts whose
product with the fixed order-three lift is parabolic. -/
theorem modular_trace_zero_parabolic_pair_classification (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod : Matrix.trace (triangleModularA * B).val = 2 ∨
      Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3, B = modularSCyclicConjugate k ∨ B = -modularSCyclicConjugate k := by
  rcases hprod with hprod | hprod
  · have htr' : Matrix.trace (-B).val = 0 := by
      change Matrix.trace (-B.val) = 0
      rw [Matrix.trace_neg, htr, neg_zero]
    have hprod' : Matrix.trace (triangleModularA * (-B)).val = -2 := by
      rw [mul_neg]
      change Matrix.trace (-(triangleModularA * B).val) = -2
      rw [Matrix.trace_neg, hprod]
    obtain ⟨k, hk⟩ := modular_trace_zero_trace_neg_two_classification (-B) htr' hprod'
    refine ⟨k, Or.inr ?_⟩
    simpa only [neg_neg] using congrArg (fun C : SL(2, ℤ) => -C) hk
  · obtain ⟨k, hk⟩ := modular_trace_zero_trace_neg_two_classification B htr hprod
    exact ⟨k, Or.inl hk⟩

/-- These six matrices are exactly, not merely among, the integral
solutions to the two trace conditions. -/
theorem modular_trace_zero_parabolic_pair_iff (B : SL(2, ℤ)) :
    (Matrix.trace B.val = 0 ∧
      (Matrix.trace (triangleModularA * B).val = 2 ∨
        Matrix.trace (triangleModularA * B).val = -2)) ↔
      ∃ k : Fin 3, B = modularSCyclicConjugate k ∨ B = -modularSCyclicConjugate k := by
  constructor
  · rintro ⟨htr, hprod⟩
    exact modular_trace_zero_parabolic_pair_classification B htr hprod
  · rintro ⟨k, rfl | rfl⟩ <;> fin_cases k <;> decide

/-- The normalizing matrix is a power of `A`, hence fixes the first
elliptic point and leaves its modular generator unchanged. -/
def modularCyclicNormalizer (k : Fin 3) : SL(2, ℤ) := (triangleModularA ^ (k : ℕ))⁻¹

theorem modularCyclicNormalizer_conjugate_A (k : Fin 3) :
    modularCyclicNormalizer k * triangleModularA * (modularCyclicNormalizer k)⁻¹ =
      triangleModularA := by
  fin_cases k <;> decide

theorem modularCyclicNormalizer_conjugate_S (k : Fin 3) :
    modularCyclicNormalizer k * modularSCyclicConjugate k * (modularCyclicNormalizer k)⁻¹ =
      S := by
  simp [modularCyclicNormalizer, modularSCyclicConjugate, mul_assoc]

/-- Conjugation by one of the three actual cyclic normalizers changes
the second integral matrix to `S` or its central negative. -/
theorem modular_pair_signed_conjugation_normalization (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod : Matrix.trace (triangleModularA * B).val = 2 ∨
      Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3,
      modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹ = S ∨
      modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹ = -S := by
  obtain ⟨k, hk | hk⟩ := modular_trace_zero_parabolic_pair_classification B htr hprod
  · refine ⟨k, Or.inl ?_⟩
    rw [hk]
    exact modularCyclicNormalizer_conjugate_S k
  · refine ⟨k, Or.inr ?_⟩
    rw [hk, mul_neg, neg_mul, modularCyclicNormalizer_conjugate_S]

/-- The central sign disappears in the actual projective modular
group, giving an exact normalized second generator there. -/
theorem modular_pair_projective_conjugation_normalization (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod : Matrix.trace (triangleModularA * B).val = 2 ∨
      Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3,
      modularProjectivization
        (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
        modularProjectivization S := by
  obtain ⟨k, hk | hk⟩ := modular_pair_signed_conjugation_normalization B htr hprod
  · exact ⟨k, congrArg modularProjectivization hk⟩
  · exact ⟨k, (congrArg modularProjectivization hk).trans (modularProjectivization_neg S)⟩

end Wikipedia.HopfProblem.SpecialPeriods
