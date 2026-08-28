import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricUnitaryModel

/-!
# The explicit Bott matrix is the actual nested minimum rotation

The matrix formula is identified with the exponential and anticommuting
rotation used in the checked homotopy comparisons. This is an equality of
actual maps, before passing to homotopy classes.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicSymmetricMatrices QuaternionicColumns
open NoExoticSixSphere.GLOrthonormalization

variable {N : Type*} [Fintype N] [DecidableEq N]

def sphericalCoefficients (s t : ℝ) : Coefficients :=
  ⟨(Real.cos s, Real.sin s * Real.cos t, Real.sin s * Real.sin t), by
    have ht : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := by
      nlinarith only [Real.sin_sq_add_cos_sq t]
    change Real.cos s ^ 2 + (Real.sin s * Real.cos t) ^ 2 +
      (Real.sin s * Real.sin t) ^ 2 = 1
    calc
      _ = Real.cos s ^ 2 + Real.sin s ^ 2 * (Real.cos t ^ 2 + Real.sin t ^ 2) := by
        ring
      _ = 1 := by rw [ht, mul_one]; nlinarith only [Real.sin_sq_add_cos_sq s]⟩

def rotation (s t : ℝ) (B : Space N) : SpGroup N :=
  family (sphericalCoefficients s t, B)

theorem rotation_val (s t : ℝ) (B : Space N) :
    (rotation s t B).val =
      matrix (Real.cos s) (Real.sin s * Real.cos t) (Real.sin s * Real.sin t) B := rfl

theorem continuous_rotation :
    Continuous (fun z : (ℝ × ℝ) × Space N ↦ rotation z.1.1 z.1.2 z.2) := by
  have hcoeff : Continuous (fun z : ℝ × ℝ ↦ sphericalCoefficients z.1 z.2) := by
    apply Continuous.subtype_mk
    exact (Real.continuous_cos.comp continuous_fst).prodMk
      (((Real.continuous_sin.comp continuous_fst).mul
        (Real.continuous_cos.comp continuous_snd)).prodMk
      ((Real.continuous_sin.comp continuous_fst).mul
        (Real.continuous_sin.comp continuous_snd)))
  exact family.continuous.comp ((hcoeff.comp continuous_fst).prodMk continuous_snd)

theorem rotation_zero (t : ℝ) (B : Space N) : rotation 0 t B = 1 := by
  apply Subtype.ext
  rw [rotation_val, Real.cos_zero, Real.sin_zero, zero_mul, zero_mul, matrix_north]
  rfl

theorem rotation_boundary (s : ℝ) (B C : Space N) : rotation s 0 B = rotation s 0 C := by
  apply Subtype.ext
  simp only [rotation_val, Real.sin_zero, mul_zero, matrix_zero_coefficient]

theorem rotation_pi (t : ℝ) (B C : Space N) : rotation Real.pi t B = rotation Real.pi t C := by
  apply Subtype.ext
  simp only [rotation_val, Real.cos_pi, Real.sin_pi, zero_mul, matrix_south]

theorem rotation_boundary_pi (s : ℝ) (B C : Space N) :
    rotation s Real.pi B = rotation s Real.pi C := by
  apply Subtype.ext
  simp only [rotation_val, Real.sin_pi, mul_zero, matrix_zero_coefficient]

variable {n : ℕ}

theorem realAction_rotation (s t : ℝ) (B : Space (Fin (n + 1))) :
    realAction n (rotation s t B).val =
      (Exponential.exp
        (s • (AnticommutingStructures.rotation
          (AnticommutingStructures.ofSymmetricUnitary B) t).val)).val.val.val := by
  rw [ComplexStructures.exp_smul, rotation_val]
  change realRepresentation n
      (Real.cos s • 1 + ((Real.sin s * Real.cos t) • imaginaryAxis (Fin (n + 1)) +
        (Real.sin s * Real.sin t) • quaternionMatrix B.val.val)) =
    Real.cos s • 1 + Real.sin s •
      (Real.cos t • realRepresentation n (imaginaryAxis (Fin (n + 1))) +
        Real.sin t • realRepresentation n (quaternionMatrix B.val.val))
  simp only [map_add, map_smul, map_one]
  module

theorem symplecticHomeomorph_rotation (s t : ℝ) (B : Space (Fin (n + 1))) :
    symplecticHomeomorph n (rotation s t B) =
      Exponential.exp
        (s • (AnticommutingStructures.rotation
          (AnticommutingStructures.ofSymmetricUnitary B) t).val) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact realAction_rotation s t B

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
