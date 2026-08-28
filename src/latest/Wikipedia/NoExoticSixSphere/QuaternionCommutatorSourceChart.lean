import Wikipedia.NoExoticSixSphere.QuaternionCommutatorProjectedDifferential
import Wikipedia.NoExoticSixSphere.QuaternionCommutatorAntipodalFiber
import Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Actual sphere-chart inputs for the quaternionic commutator

Centered stereographic charts at minus one supply the pure quaternion
tangent directions. The projected map remains the original matrix map.
-/

noncomputable section

open scoped ContDiff commutatorElement

namespace NoExoticSixSphere.QuaternionCommutatorSourceChart

open Wikipedia.HopfProblem.UnitQuaternionSphere
open Wikipedia.HomotopyGroupsOfSpheres
open QuaternionicFibration SphereCenteredCoordinates
open QuaternionCommutatorRotation QuaternionCommutatorProjectedDifferential

local notation "ℍ" => Quaternion ℝ

def center : SphereCenteredCoordinates.UnitSphere ℍ := ⟨-1, by simp⟩

abbrev Imaginary := Tangent center

theorem imaginary_re (v : Imaginary) : v.val.re = 0 := by
  have h := Submodule.mem_orthogonal_singleton_iff_inner_left.mp v.property
  simpa [center, Quaternion.inner_def] using h

theorem imaginary_star (v : Imaginary) : star v.val = -v.val :=
  Quaternion.star_eq_neg.mpr (imaginary_re v)

def quaternionChart (v : Imaginary) : UnitQuaternions :=
  ⟨(inverse center v).val, (mem_unitary_iff_norm_eq_one _).mpr
    (mem_sphere_zero_iff_norm.mp (inverse center v).property)⟩

theorem quaternionChart_zero : (quaternionChart 0).val = -1 :=
  congrArg Subtype.val (inverse_zero center)

theorem hasFDerivAt_quaternionChart :
    HasFDerivAt (fun v : Imaginary ↦ (quaternionChart v).val) Imaginary.subtypeL 0 :=
  hasFDerivAt_inverse_val center

theorem contDiff_quaternionChart {n : ℕ∞ω} :
    ContDiff ℝ n (fun v : Imaginary ↦ (quaternionChart v).val) :=
  contDiff_inverse_val center

abbrev Parameters := ℝ × (Imaginary × Imaginary)

def angle : Parameters →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ _ _

def leftInput : Parameters →L[ℝ] Imaginary :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

def rightInput : Parameters →L[ℝ] Imaginary :=
  (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

def leftDerivative : Parameters →L[ℝ] ℍ := Imaginary.subtypeL.comp leftInput

def rightDerivative : Parameters →L[ℝ] ℍ := Imaginary.subtypeL.comp rightInput

def pairDerivative : Parameters →L[ℝ] (ℍ × ℍ) :=
  (-leftDerivative).prod (((4 : ℝ) • angle).smulRight (1 : ℍ) + rightDerivative)

def pairMap (z : Parameters) : ℍ × ℍ :=
  column (Real.pi / 4 + z.1) (quaternionChart z.2.1).val (quaternionChart z.2.2).val

theorem hasFDerivAt_pairMap : HasFDerivAt pairMap pairDerivative 0 := by
  have hθ : HasFDerivAt (fun z : Parameters ↦ Real.pi / 4 + z.1) angle 0 :=
    angle.hasFDerivAt.const_add _
  have hq : HasFDerivAt (fun z : Parameters ↦ (quaternionChart z.2.1).val)
      leftDerivative 0 := by
    have hc : HasFDerivAt (fun v : Imaginary ↦ (quaternionChart v).val)
        Imaginary.subtypeL (leftInput (0 : Parameters)) := by
      rw [map_zero]
      exact hasFDerivAt_quaternionChart
    exact hc.comp 0 leftInput.hasFDerivAt
  have hr : HasFDerivAt (fun z : Parameters ↦ (quaternionChart z.2.2).val)
      rightDerivative 0 := by
    have hc : HasFDerivAt (fun v : Imaginary ↦ (quaternionChart v).val)
        Imaginary.subtypeL (rightInput (0 : Parameters)) := by
      rw [map_zero]
      exact hasFDerivAt_quaternionChart
    exact hc.comp 0 rightInput.hasFDerivAt
  exact hasFDerivAt_column hθ hq hr (by simp) quaternionChart_zero quaternionChart_zero
    (fun v ↦ imaginary_star v.2.1) (fun v ↦ imaginary_star v.2.2)

theorem contDiff_pairMap {n : ℕ∞ω} : ContDiff ℝ n pairMap :=
  contDiff_column (contDiff_const.add angle.contDiff)
    (contDiff_quaternionChart.comp leftInput.contDiff)
    (contDiff_quaternionChart.comp rightInput.contDiff)

def projectionMap (z : Parameters) : BaseSphere :=
  projection ⁅fiberInclusion (quaternionChart z.2.1),
    conjugatedFiber (Real.pi / 4 + z.1) (quaternionChart z.2.2)⁆

def pairToPlane : (ℍ × ℍ) ≃L[ℝ] QuaternionPlane :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℍ ℍ).symm

theorem projectionMap_val (z : Parameters) : (projectionMap z).val = pairToPlane (pairMap z) := by
  apply (WithLp.equiv 2 (ℍ × ℍ)).injective
  exact column_actual _ _ _

def ambientDerivative : Parameters →L[ℝ] QuaternionPlane :=
  pairToPlane.toContinuousLinearMap.comp pairDerivative

theorem hasFDerivAt_projectionMap :
    HasFDerivAt (fun z : Parameters ↦ (projectionMap z).val) ambientDerivative 0 := by
  simp only [projectionMap_val]
  exact pairToPlane.hasFDerivAt.comp 0 hasFDerivAt_pairMap

theorem contDiff_projectionMap {n : ℕ∞ω} :
    ContDiff ℝ n (fun z : Parameters ↦ (projectionMap z).val) := by
  simp only [projectionMap_val]
  exact pairToPlane.contDiff.comp contDiff_pairMap

end NoExoticSixSphere.QuaternionCommutatorSourceChart
