import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSections
import Wikipedia.HomotopyGroupsOfSpheres.Samelson
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A rotation moving the quaternionic fiber to the other diagonal block

Conjugation by a real quarter-turn exchanges the two diagonal quaternion
subgroups of the actual group `SpTwo`. The resulting commutator family
contracts the included quaternion commutator, fixing the fat wedge.
This does not yet compute the degree of its first-column projection.
-/

noncomputable section

open scoped Matrix unitInterval commutatorElement

namespace NoExoticSixSphere.QuaternionCommutatorRotation

open Wikipedia.HopfProblem.UnitQuaternionSphere
open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

local notation "ℍ" => Quaternion ℝ

def realRotation (θ : ℝ) : SpTwo :=
  rotation (Real.cos θ) (Real.sin θ : ℍ) (by
    rw [Quaternion.normSq_coe]
    exact Real.cos_sq_add_sin_sq θ)

theorem continuous_realRotation : Continuous realRotation := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    dsimp [realRotation, rotation, rotationMatrix]
  · exact Quaternion.continuous_coe.comp Real.continuous_cos
  · exact (Quaternion.continuous_coe.comp Real.continuous_sin).star.neg
  · exact Quaternion.continuous_coe.comp Real.continuous_sin
  · exact Quaternion.continuous_coe.comp Real.continuous_cos

theorem realRotation_zero : realRotation 0 = 1 := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [realRotation, rotation, rotationMatrix]

theorem quarter_turn_conjugate (q : UnitQuaternions) :
    realRotation (Real.pi / 2) * fiberInclusion q *
      (realRotation (Real.pi / 2))⁻¹ = firstDiagonal q := by
  apply Subtype.ext
  change (realRotation (Real.pi / 2)).val * (fiberInclusion q).val *
    star (realRotation (Real.pi / 2)).val = (firstDiagonal q).val
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [realRotation, rotation, rotationMatrix, fiberInclusion, fiberMatrix,
      firstDiagonal, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

theorem diagonal_commute (q r : UnitQuaternions) :
    Commute (fiberInclusion q) (firstDiagonal r) := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fiberInclusion, fiberMatrix, firstDiagonal, Matrix.mul_apply, Fin.sum_univ_two]

def conjugatedFiber (θ : ℝ) (r : UnitQuaternions) : SpTwo :=
  realRotation θ * fiberInclusion r * (realRotation θ)⁻¹

theorem continuous_conjugatedFiber :
    Continuous (fun z : ℝ × UnitQuaternions ↦ conjugatedFiber z.1 z.2) :=
  ((continuous_realRotation.comp continuous_fst).mul
    (continuous_fiberInclusion.comp continuous_snd)).mul
      (continuous_realRotation.comp continuous_fst).inv

theorem conjugatedFiber_one (θ : ℝ) : conjugatedFiber θ 1 = 1 := by
  simp [conjugatedFiber]

attribute [local irreducible] realRotation conjugatedFiber

def contraction (t : I) (q r : UnitQuaternions) : SpTwo :=
  ⁅fiberInclusion q, conjugatedFiber (t.val * (Real.pi / 2)) r⁆

theorem continuous_contraction :
    Continuous (fun z : I × (UnitQuaternions × UnitQuaternions) ↦
      contraction z.1 z.2.1 z.2.2) := by
  have ha : Continuous (fun z : I × (UnitQuaternions × UnitQuaternions) ↦
      z.1.val * (Real.pi / 2)) :=
    (continuous_subtype_val.comp continuous_fst).mul_const _
  have hb : Continuous (fun z : I × (UnitQuaternions × UnitQuaternions) ↦ z.2.2) :=
    continuous_snd.snd
  have hc : Continuous (fun z : I × (UnitQuaternions × UnitQuaternions) ↦
      conjugatedFiber (z.1.val * (Real.pi / 2)) z.2.2) :=
    continuous_conjugatedFiber.comp (ha.prodMk hb)
  have hq : Continuous (fun z : I × (UnitQuaternions × UnitQuaternions) ↦
      fiberInclusion z.2.1) := continuous_fiberInclusion.comp continuous_snd.fst
  exact ((hq.mul hc).mul hq.inv).mul hc.inv

theorem contraction_zero (q r : UnitQuaternions) :
    contraction 0 q r = fiberInclusion ⁅q, r⁆ := by
  change ⁅fiberInclusion q, conjugatedFiber (0 * (Real.pi / 2)) r⁆ = _
  simp only [zero_mul, conjugatedFiber,
    realRotation_zero, one_mul, inv_one, mul_one]
  exact (map_commutatorElement fiberInclusion q r).symm

theorem contraction_one (q r : UnitQuaternions) : contraction 1 q r = 1 := by
  change ⁅fiberInclusion q, conjugatedFiber (1 * (Real.pi / 2)) r⁆ = 1
  simp only [one_mul, conjugatedFiber,
    quarter_turn_conjugate]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (diagonal_commute q r)

theorem contraction_fatWedge (t : I) (q r : UnitQuaternions) (h : q = 1 ∨ r = 1) :
    contraction t q r = 1 := by
  rcases h with rfl | rfl
  · simp [contraction]
  · simp [contraction, conjugatedFiber_one]

end NoExoticSixSphere.QuaternionCommutatorRotation
