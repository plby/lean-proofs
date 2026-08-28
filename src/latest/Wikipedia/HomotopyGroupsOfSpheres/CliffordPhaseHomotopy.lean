import Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveLatitude
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # The based homotopy from identity padding to the rank-six phase family -/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices

def polarAngle : C(ComplexCrossProductUnitary.UnitSphere, ℝ) where
  toFun z := Real.arccos (z.val 0).re
  continuous_toFun := by
    have hz : Continuous (fun z : ComplexCrossProductUnitary.UnitSphere ↦
        ((fun i ↦ z.val i) : Vector)) :=
      (PiLp.continuous_ofLp 2 (fun _ : Fin 3 ↦ ℂ)).comp continuous_subtype_val
    exact Real.continuous_arccos.comp
      (Complex.continuous_re.comp ((continuous_apply 0).comp hz))

theorem polarAngle_axis : polarAngle axis = 0 := by
  change Real.arccos (axis.val 0).re = 0
  rw [show axis.val 0 = 1 from congrFun axis_val 0]
  exact Real.arccos_one

theorem polarAngle_latitude (θ : ℝ) (v : UnitSphere) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    polarAngle (latitudePoint θ v) = θ := by
  change Real.arccos ((latitudePoint θ v).val 0).re = θ
  rw [latitudePoint_re, Real.arccos_cos h0 hπ]

def paddedSource : C(ComplexCrossProductUnitary.UnitSphere, Space (Fin 6 ⊕ Fin 6)) :=
  BalancedPhasePadding.identityPadding.comp ComplexCliffordFive.linearizedSymmetricMap

def paddedTarget : C(ComplexCrossProductUnitary.UnitSphere, Space (Fin 6 ⊕ Fin 6)) :=
  BalancedPhasePadding.phasedMap ComplexCliffordFive.linearizedSymmetricMap polarAngle

attribute [local irreducible] ComplexCliffordFive.linearizedSymmetricMap
  BalancedPhasePadding.paddingHomotopy

def phasePaddingHomotopy : paddedSource.HomotopyRel paddedTarget {axis} :=
  BalancedPhasePadding.paddingHomotopy ComplexCliffordFive.linearizedSymmetricMap
    polarAngle axis polarAngle_axis

theorem paddedTarget_latitude (θ : ℝ) (v : UnitSphere) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    paddedTarget (latitudePoint θ v) =
      (BalancedRealInvolutions.rotation (rawBalanced v) θ).val := by
  apply Subtype.ext
  apply Subtype.ext
  change (BalancedPhasePadding.padding
    (polarAngle (latitudePoint θ v),
      ComplexCliffordFive.linearizedSymmetricMap (latitudePoint θ v))).val.val = _
  rw [polarAngle_latitude θ v h0 hπ,
    BalancedPhasePadding.padding_rotation_val θ (matrix v.val) _ (linearized_latitude_val θ v)]
  rfl

theorem paddedTarget_axis : paddedTarget axis = identity := by
  rw [← latitudePoint_zero pole, paddedTarget_latitude 0 pole le_rfl Real.pi_pos.le,
    BalancedRealInvolutions.rotation_zero]
  rfl

theorem paddedSource_axis : paddedSource axis = identity := by
  have h := phasePaddingHomotopy.eq_fst 1 (Set.mem_singleton axis)
  rw [phasePaddingHomotopy.apply_one] at h
  exact h.symm.trans paddedTarget_axis

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
