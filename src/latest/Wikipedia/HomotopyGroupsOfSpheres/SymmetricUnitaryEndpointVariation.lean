import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryExponential

/-!
# Endpoint-preserving variations inside the symmetric determinant-one space

The variation of `exp(t iA)` in the direction `C` is the actual matrix
`exp(t iA/2) exp(s sin(πt) iC) exp(t iA/2)`. Symmetry and determinant one
hold for every parameter, and both endpoints are fixed. No assertion
about the second variation of energy is made here.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

open ImaginarySymmetricMatrices RealSymmetricMixing

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem exponential_det (A : DirectionSpace N) : (exponential A).val.val.val.det = 1 :=
  congrArg (fun z : Circle ↦ (z : ℂ)) (exponential A).property

theorem exponential_add_smul (A : DirectionSpace N) (s t : ℝ) :
    (exponential (s • A)).val.val.val * (exponential (t • A)).val.val.val =
      (exponential ((s + t) • A)).val.val.val := by
  change NormedSpace.exp (imaginary (s • A.val)) * NormedSpace.exp (imaginary (t • A.val)) =
    NormedSpace.exp (imaginary ((s + t) • A.val))
  rw [map_smul, map_smul, map_smul, add_smul]
  exact (Matrix.exp_add_of_commute _ _
    (((Commute.refl (imaginary A.val)).smul_left s).smul_right t)).symm

def sandwich (A : DirectionSpace N) (B : SpecialSpace N) : SpecialSpace N :=
  congruenceSpecial (exponential ((1 / 2 : ℝ) • A)).val.val
    (by rw [exponential_det, one_pow]) B

theorem sandwich_matrix (A : DirectionSpace N) (B : SpecialSpace N) :
    (sandwich A B).val.val.val =
      (exponential ((1 / 2 : ℝ) • A)).val.val.val * B.val.val.val *
        (exponential ((1 / 2 : ℝ) • A)).val.val.val.transpose := rfl

theorem sandwich_identity (A : DirectionSpace N) :
    sandwich A specialIdentity = exponential A := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [sandwich_matrix]
  change (exponential ((1 / 2 : ℝ) • A)).val.val.val * 1 *
    (exponential ((1 / 2 : ℝ) • A)).val.val.val.transpose = (exponential A).val.val.val
  rw [mul_one, (exponential ((1 / 2 : ℝ) • A)).val.property, exponential_add_smul]
  norm_num

theorem sandwich_zero (B : SpecialSpace N) : sandwich (0 : DirectionSpace N) B = B := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [sandwich_matrix, smul_zero, exponential_zero]
  change (1 : Matrix N N ℂ) * B.val.val.val * (1 : Matrix N N ℂ).transpose = B.val.val.val
  rw [Matrix.transpose_one, one_mul, mul_one]

theorem continuous_sandwich :
    Continuous (fun z : DirectionSpace N × SpecialSpace N ↦ sandwich z.1 z.2) := by
  have hE : Continuous (fun z : DirectionSpace N × SpecialSpace N ↦
      exponential ((1 / 2 : ℝ) • z.1)) :=
    continuous_exponential.comp (continuous_fst.const_smul (1 / 2 : ℝ))
  have hF : Continuous (fun z : DirectionSpace N × SpecialSpace N ↦
      (exponential ((1 / 2 : ℝ) • z.1)).val.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp hE))
  have hB : Continuous (fun z : DirectionSpace N × SpecialSpace N ↦ z.2.val.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp continuous_snd))
  have hM := (hF.matrix_mul hB).matrix_mul hF.matrix_transpose
  exact ((hM.subtype_mk _).subtype_mk _).subtype_mk _

def endpointVariation (A C : DirectionSpace N) (s t : ℝ) : SpecialSpace N :=
  sandwich (t • A) (exponential ((s * Real.sin (Real.pi * t)) • C))

theorem endpointVariation_at_zero (A C : DirectionSpace N) (s : ℝ) :
    endpointVariation A C s 0 = specialIdentity := by
  simp only [endpointVariation, zero_smul, mul_zero, Real.sin_zero,
    exponential_zero, sandwich_zero]

theorem endpointVariation_at_one (A C : DirectionSpace N) (s : ℝ) :
    endpointVariation A C s 1 = exponential A := by
  simp only [endpointVariation, one_smul, mul_one, Real.sin_pi, mul_zero, zero_smul,
    exponential_zero, sandwich_identity]

theorem endpointVariation_base (A C : DirectionSpace N) (t : ℝ) :
    endpointVariation A C 0 t = exponentialCurve A t := by
  simp only [endpointVariation, zero_mul, zero_smul, exponential_zero,
    sandwich_identity, exponentialCurve]

theorem continuous_endpointVariation (A C : DirectionSpace N) :
    Continuous (fun z : ℝ × ℝ ↦ endpointVariation A C z.1 z.2) := by
  have hA : Continuous (fun z : ℝ × ℝ ↦ z.2 • A) := continuous_snd.smul continuous_const
  have hC : Continuous (fun z : ℝ × ℝ ↦ (z.1 * Real.sin (Real.pi * z.2)) • C) :=
    (continuous_fst.mul (Real.continuous_sin.comp (continuous_snd.const_mul Real.pi))).smul
      continuous_const
  let E : C(DirectionSpace N, SpecialSpace N) := ⟨exponential, continuous_exponential⟩
  let D : C(ℝ × ℝ, DirectionSpace N) :=
    ⟨fun z ↦ (z.1 * Real.sin (Real.pi * z.2)) • C, hC⟩
  let P : C(ℝ × ℝ, DirectionSpace N × SpecialSpace N) :=
    ⟨fun z ↦ (z.2 • A, (E.comp D) z), hA.prodMk (E.comp D).continuous⟩
  let S : C(DirectionSpace N × SpecialSpace N, SpecialSpace N) :=
    ⟨fun z ↦ sandwich z.1 z.2, continuous_sandwich⟩
  exact (S.comp P).continuous

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
