import Wikipedia.NoExoticSixSphere.QuaternionCommutatorRotation

/-!
# First-column formulas for the actual quaternion commutator lift

These are matrix identities for the constructed rotation and the literal
first-column projection. No homotopy class, degree, or parity is assigned
by the coordinate calculation.
-/

noncomputable section

open scoped Matrix commutatorElement

namespace NoExoticSixSphere.QuaternionCommutatorColumns

open Wikipedia.HopfProblem.UnitQuaternionSphere
open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
open QuaternionCommutatorRotation

local notation "ℍ" => Quaternion ℝ

def diagonalZero (c s : ℝ) (r : ℍ) : ℍ := (c ^ 2 : ℝ) + (s ^ 2 : ℝ) * r

def offDiagonal (c s : ℝ) (r : ℍ) : ℍ := (c * s : ℝ) * (1 - r)

def diagonalOne (c s : ℝ) (r : ℍ) : ℍ := (s ^ 2 : ℝ) + (c ^ 2 : ℝ) * r

theorem rotation_conjugate_matrix (c s : ℝ) (r : ℍ) :
    rotationMatrix c (s : ℍ) * fiberMatrix r * star (rotationMatrix c (s : ℍ)) =
      !![diagonalZero c s r, offDiagonal c s r; offDiagonal c s r, diagonalOne c s r] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, fiberMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      diagonalZero, offDiagonal, diagonalOne] <;>
    ext <;> simp [pow_two, Quaternion.re_one, Quaternion.imI_one,
      Quaternion.imJ_one, Quaternion.imK_one] <;> ring

theorem conjugatedFiber_matrix (θ : ℝ) (r : UnitQuaternions) :
    (conjugatedFiber θ r).val =
      !![diagonalZero (Real.cos θ) (Real.sin θ) r.val,
        offDiagonal (Real.cos θ) (Real.sin θ) r.val;
        offDiagonal (Real.cos θ) (Real.sin θ) r.val,
        diagonalOne (Real.cos θ) (Real.sin θ) r.val] :=
  rotation_conjugate_matrix (Real.cos θ) (Real.sin θ) r.val

theorem commutator_top (q : UnitQuaternions) (g : SpTwo) :
    (⁅fiberInclusion q, g⁆).val 0 0 =
      g.val 0 0 * star (g.val 0 0) + g.val 0 1 * star q.val * star (g.val 0 1) := by
  change (fiberMatrix q.val * g.val * star (fiberMatrix q.val) * star g.val) 0 0 = _
  simp [fiberMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Matrix.star_apply]

theorem commutator_bottom (q : UnitQuaternions) (g : SpTwo) :
    (⁅fiberInclusion q, g⁆).val 1 0 =
      q.val * (g.val 1 0 * star (g.val 0 0) +
        g.val 1 1 * star q.val * star (g.val 0 1)) := by
  change (fiberMatrix q.val * g.val * star (fiberMatrix q.val) * star g.val) 1 0 = _
  simp [fiberMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Matrix.star_apply, mul_add, mul_assoc]

theorem commutator_top_real (q : UnitQuaternions) (g : SpTwo) :
    ((⁅fiberInclusion q, g⁆).val 0 0).re =
      Quaternion.normSq (g.val 0 0) + Quaternion.normSq (g.val 0 1) * q.val.re := by
  rw [commutator_top, Quaternion.re_add, Quaternion.self_mul_star, Quaternion.re_coe]
  congr 1
  generalize g.val 0 1 = b
  generalize q.val = a
  simp [Quaternion.normSq_def', Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

theorem row_normSq (g : SpTwo) :
    Quaternion.normSq (g.val 0 0) + Quaternion.normSq (g.val 0 1) = 1 := by
  have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℍ ↦ B 0 0)
    (Unitary.coe_mul_star_self g)
  have hq : ((Quaternion.normSq (g.val 0 0) +
      Quaternion.normSq (g.val 0 1) : ℝ) : ℍ) = 1 := by
    simpa only [Unitary.coe_star, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Quaternion.self_mul_star, Matrix.one_apply_eq, Quaternion.coe_add] using h
  exact congrArg (fun q : ℍ ↦ q.re) hq

theorem commutator_top_real_reduced (q : UnitQuaternions) (g : SpTwo) :
    ((⁅fiberInclusion q, g⁆).val 0 0).re =
      1 - Quaternion.normSq (g.val 0 1) * (1 - q.val.re) := by
  rw [commutator_top_real]
  linarith [row_normSq g]

end NoExoticSixSphere.QuaternionCommutatorColumns
