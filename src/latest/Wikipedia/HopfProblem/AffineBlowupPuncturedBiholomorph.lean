import Wikipedia.HopfProblem.AffineBlowupTopology
import Wikipedia.HopfProblem.AffineBlowupManifold
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Blow-down is biholomorphic away from the exceptional curve

The existing punctured homeomorphism has an explicit analytic inverse on
each of the two sets where a base coordinate is nonzero.  All manifold
structures here are the inherited structures on the actual open subspaces.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.AffineBlowup

open ToricCharts

local notation "I₂" => modelWithCornersSelf ℂ (CoordinateSpace 2)

theorem puncturedProjection_holomorphic : ContMDiff I₂ I₂ ω puncturedProjection := by
  intro x
  have he : ContMDiffAt I₂ I₂ ω
      (fun y : puncturedSpace => (puncturedProjection y : CoordinateSpace 2)) x ↔
    ContMDiffAt I₂ I₂ ω puncturedProjection x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((projection_holomorphic.comp contMDiff_subtype_val) x)

theorem puncturedHomeomorph_holomorphic : ContMDiff I₂ I₂ ω puncturedHomeomorph :=
  puncturedProjection_holomorphic

theorem puncturedHomeomorph_symm_eq_of_projection (v : puncturedBase) (x : Space)
    (hx : projection x = (v : CoordinateSpace 2)) :
    (puncturedHomeomorph.symm v : Space) = x := by
  let x' : puncturedSpace := ⟨x, by change projection x ≠ 0; rw [hx]; exact v.2⟩
  have he : puncturedHomeomorph x' = v := Subtype.ext hx
  rw [← he, puncturedHomeomorph.symm_apply_apply]

/-- In the chart with nonzero second base coordinate, the inverse blow-down
is `(x,y) ↦ (x/y,y)`. -/
theorem puncturedHomeomorph_symm_eq_left (v : puncturedBase)
    (hv : (v : CoordinateSpace 2) 1 ≠ 0) :
    (puncturedHomeomorph.symm v : Space) =
      affineMap false ![(v : CoordinateSpace 2) 0 / (v : CoordinateSpace 2) 1,
        (v : CoordinateSpace 2) 1] := by
  apply puncturedHomeomorph_symm_eq_of_projection
  ext i
  fin_cases i
  · exact div_mul_cancel₀ _ hv
  · rfl

/-- In the chart with nonzero first base coordinate, the inverse blow-down
is `(x,y) ↦ (x,y/x)`. -/
theorem puncturedHomeomorph_symm_eq_right (v : puncturedBase)
    (hv : (v : CoordinateSpace 2) 0 ≠ 0) :
    (puncturedHomeomorph.symm v : Space) =
      affineMap true ![(v : CoordinateSpace 2) 0,
        (v : CoordinateSpace 2) 1 / (v : CoordinateSpace 2) 0] := by
  apply puncturedHomeomorph_symm_eq_of_projection
  ext i
  fin_cases i
  · rfl
  · exact mul_div_cancel₀ _ hv

theorem puncturedHomeomorph_symm_holomorphic :
    ContMDiff I₂ I₂ ω puncturedHomeomorph.symm := by
  intro v
  have he : ContMDiffAt I₂ I₂ ω
      (fun w : puncturedBase => (puncturedHomeomorph.symm w : Space)) v ↔
    ContMDiffAt I₂ I₂ ω puncturedHomeomorph.symm v :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply he.mp
  by_cases h1 : (v : CoordinateSpace 2) 1 ≠ 0
  · have hc : ContDiffAt ℂ ω (fun w : CoordinateSpace 2 => ![w 0 / w 1, w 1]) v.1 := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i
      · exact (contDiff_apply ℂ ℂ 0).contDiffAt.div (contDiff_apply ℂ ℂ 1).contDiffAt h1
      · exact (contDiff_apply ℂ ℂ 1).contDiffAt
    have hm : ContMDiffAt I₂ I₂ ω
        (fun w : puncturedBase => affineMap false ![w.1 0 / w.1 1, w.1 1]) v :=
      (affineMap_holomorphic false).contMDiffAt.comp v
        (hc.contMDiffAt.comp v contMDiff_subtype_val.contMDiffAt)
    apply hm.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne_fun
      ((continuous_apply 1).comp continuous_subtype_val) continuous_const).mem_nhds h1]
      with w hw
    exact puncturedHomeomorph_symm_eq_left w hw
  · have h0 : (v : CoordinateSpace 2) 0 ≠ 0 := by
      intro hv0
      apply v.2
      ext i
      fin_cases i
      · exact hv0
      · exact not_ne_iff.mp h1
    have hc : ContDiffAt ℂ ω (fun w : CoordinateSpace 2 => ![w 0, w 1 / w 0]) v.1 := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i
      · exact (contDiff_apply ℂ ℂ 0).contDiffAt
      · exact (contDiff_apply ℂ ℂ 1).contDiffAt.div (contDiff_apply ℂ ℂ 0).contDiffAt h0
    have hm : ContMDiffAt I₂ I₂ ω
        (fun w : puncturedBase => affineMap true ![w.1 0, w.1 1 / w.1 0]) v :=
      (affineMap_holomorphic true).contMDiffAt.comp v
        (hc.contMDiffAt.comp v contMDiff_subtype_val.contMDiffAt)
    apply hm.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne_fun
      ((continuous_apply 0).comp continuous_subtype_val) continuous_const).mem_nhds h0]
      with w hw
    exact puncturedHomeomorph_symm_eq_right w hw

/-- The actual punctured blow-down, with its existing underlying
homeomorphism, is an analytic diffeomorphism. -/
def puncturedBiholomorph : Diffeomorph I₂ I₂ puncturedSpace puncturedBase ω where
  toEquiv := puncturedHomeomorph.toEquiv
  contMDiff_toFun := puncturedHomeomorph_holomorphic
  contMDiff_invFun := puncturedHomeomorph_symm_holomorphic

@[simp] theorem puncturedBiholomorph_apply (x : puncturedSpace) :
    puncturedBiholomorph x = puncturedProjection x := rfl

@[simp] theorem puncturedBiholomorph_symm_apply (v : puncturedBase) :
    puncturedBiholomorph.symm v = puncturedHomeomorph.symm v := rfl

theorem puncturedProjection_isLocalDiffeomorph :
    IsLocalDiffeomorph I₂ I₂ ω puncturedProjection :=
  puncturedBiholomorph.isLocalDiffeomorph

end Wikipedia.HopfProblem.AffineBlowup
