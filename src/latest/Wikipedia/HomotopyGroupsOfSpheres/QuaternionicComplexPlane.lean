import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicScalars
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith

/-!
# Complex coordinates on the quaternionic anticommuting plane

The quaternions anticommuting with `i` are exactly `z j` for `z : ℂ`.
These explicit coordinates will identify the second Bott parameter space
with symmetric unitary matrices, including its original topology.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexPlane

open QuaternionicScalars

local notation "ℍ" => Quaternion ℝ

def embed (z : ℂ) : ℍ := (z : ℍ) * j

def coordinate (q : ℍ) : ℂ := ⟨q.imJ, q.imK⟩

theorem embed_eq_mk (z : ℂ) : embed z = ⟨0, 0, z.re, z.im⟩ := by
  have h : (QuaternionAlgebra.mk z.re z.im 0 0 : QuaternionAlgebra ℝ (-1) 0 (-1)) *
      QuaternionAlgebra.mk 0 0 1 0 = QuaternionAlgebra.mk 0 0 z.re z.im := by
    ext <;> norm_num
  exact h

theorem coeComplex_injective : Function.Injective (fun z : ℂ ↦ (z : ℍ)) := by
  intro z w h
  apply Complex.ext
  · exact congrArg QuaternionAlgebra.re h
  · exact congrArg QuaternionAlgebra.imI h

@[simp] theorem coordinate_embed (z : ℂ) : coordinate (embed z) = z := by
  rw [embed_eq_mk]
  rfl

theorem embed_injective : Function.Injective embed :=
  Function.LeftInverse.injective coordinate_embed

theorem embed_anticommutes (z : ℂ) : i * embed z = -(embed z * i) := by
  rw [embed_eq_mk]
  have h : (QuaternionAlgebra.mk 0 1 0 0 : QuaternionAlgebra ℝ (-1) 0 (-1)) *
      QuaternionAlgebra.mk 0 0 z.re z.im =
        -(QuaternionAlgebra.mk 0 0 z.re z.im * QuaternionAlgebra.mk 0 1 0 0) := by
    ext <;> norm_num
  exact h

theorem embed_coordinate {q : ℍ} (hq : i * q = -(q * i)) : embed (coordinate q) = q := by
  rcases q with ⟨a, b, c, d⟩
  have hq' : (QuaternionAlgebra.mk 0 1 0 0 : QuaternionAlgebra ℝ (-1) 0 (-1)) *
      QuaternionAlgebra.mk a b c d =
        -(QuaternionAlgebra.mk a b c d * QuaternionAlgebra.mk 0 1 0 0) := hq
  have hre := congrArg QuaternionAlgebra.re hq'
  have him := congrArg QuaternionAlgebra.imI hq'
  norm_num at hre him
  have ha : a = 0 := by linarith
  have hb : b = 0 := by linarith
  subst a b
  exact embed_eq_mk ⟨c, d⟩

@[simp] theorem embed_star (z : ℂ) : star (embed z) = -(embed z) := by
  rw [embed_eq_mk]
  change star (QuaternionAlgebra.mk 0 0 z.re z.im : QuaternionAlgebra ℝ (-1) 0 (-1)) =
    -QuaternionAlgebra.mk 0 0 z.re z.im
  ext <;> norm_num

theorem j_mul_coeComplex (z : ℂ) : j * (z : ℍ) = ((star z : ℂ) : ℍ) * j := by
  have h : (QuaternionAlgebra.mk 0 0 1 0 : QuaternionAlgebra ℝ (-1) 0 (-1)) *
      QuaternionAlgebra.mk z.re z.im 0 0 =
        QuaternionAlgebra.mk (star z).re (star z).im 0 0 * QuaternionAlgebra.mk 0 0 1 0 := by
    ext <;> norm_num
  exact h

theorem embed_mul_embed (z w : ℂ) :
    embed z * embed w = -((z * star w : ℂ) : ℍ) := by
  simp only [embed, mul_assoc]
  rw [← mul_assoc j, j_mul_coeComplex, mul_assoc _ j j, j_mul_j, mul_neg_one]
  rw [mul_neg, ← Quaternion.coeComplex_mul]

theorem continuous_coeComplex : Continuous (fun z : ℂ ↦ (z : ℍ)) :=
  Quaternion.ofComplex.toLinearMap.continuous_of_finiteDimensional

theorem continuous_embed : Continuous embed := continuous_coeComplex.mul continuous_const

theorem continuous_coordinate : Continuous coordinate := by
  have he : coordinate = fun q : ℍ ↦ (q.imJ : ℂ) + (q.imK : ℂ) * Complex.I := by
    funext q
    apply Complex.ext <;> simp [coordinate]
  rw [he]
  exact (Complex.continuous_ofReal.comp Quaternion.continuous_imJ).add
    ((Complex.continuous_ofReal.comp Quaternion.continuous_imK).mul continuous_const)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexPlane
