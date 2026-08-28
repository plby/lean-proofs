import Wikipedia.SmoothSixDPoincare.PuncturedHandleCoordinates
import Wikipedia.SmoothSixDPoincare.PuncturedRadialHomotopy

/-!
# The punctured closed unit ball retracts onto its actual outer sphere

In the existing polar coordinates, interpolate the positive radius to one.
The homotopy stays in the punctured closed ball and fixes every outer
boundary point for its entire duration.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.PuncturedClosedBallRetraction

open Wikipedia.SmoothSixDPoincare.PuncturedHandle

def outerRadius : Radius := ⟨1, by norm_num⟩

def radiusHomotopy : C(unitInterval × Radius, Radius) where
  toFun p := ⟨(1 - (p.1 : ℝ)) * (p.2 : ℝ) + (p.1 : ℝ), by
    have hpos := (convex_Ioi (𝕜 := ℝ) (0 : ℝ)) p.2.property.1
      (show (1 : ℝ) ∈ Ioi 0 by norm_num)
      (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ))
    have hle := (convex_Iic (𝕜 := ℝ) (1 : ℝ)) p.2.property.2
      (show (1 : ℝ) ∈ Iic 1 by norm_num)
      (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ))
    exact ⟨by simpa only [smul_eq_mul, mul_one, mem_Ioi] using hpos,
      by simpa only [smul_eq_mul, mul_one, mem_Iic] using hle⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)).add
        (continuous_subtype_val.comp continuous_fst)

theorem radiusHomotopy_zero (r : Radius) : radiusHomotopy (0, r) = r := by
  apply Subtype.ext
  change (1 - (0 : ℝ)) * (r : ℝ) + 0 = r
  ring

theorem radiusHomotopy_one (r : Radius) : radiusHomotopy (1, r) = outerRadius := by
  apply Subtype.ext
  change (1 - (1 : ℝ)) * (r : ℝ) + 1 = 1
  ring

theorem radiusHomotopy_outer (t : unitInterval) :
    radiusHomotopy (t, outerRadius) = outerRadius := by
  apply Subtype.ext
  change (1 - (t : ℝ)) * 1 + (t : ℝ) = 1
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def direction : C(PuncturedBall F, UnitSphere F) :=
  ⟨fun x ↦ (polar F x).1, (polar F).continuous.fst⟩

def inclusion : C(UnitSphere F, PuncturedBall F) :=
  ⟨boundaryPoint, continuous_subtype_val.subtype_mk _⟩

theorem polar_boundary (u : UnitSphere F) :
    polar F (boundaryPoint u) = (u, outerRadius) := by
  apply Prod.ext
  · apply Subtype.ext
    change ‖u.val‖⁻¹ • u.val = u.val
    rw [mem_sphere_zero_iff_norm.mp u.property, inv_one, one_smul]
  · apply Subtype.ext
    exact mem_sphere_zero_iff_norm.mp u.property

theorem point_outer (u : UnitSphere F) : point u outerRadius = boundaryPoint u := by
  apply Subtype.ext
  change (1 : ℝ) • u.val = u.val
  exact one_smul ℝ u.val

theorem direction_inclusion (u : UnitSphere F) : direction (inclusion u) = u :=
  congrArg Prod.fst (polar_boundary u)

def deformationMap : C(unitInterval × PuncturedBall F, PuncturedBall F) where
  toFun p := (polar F).symm ((polar F p.2).1, radiusHomotopy (p.1, (polar F p.2).2))
  continuous_toFun := (polar F).symm.continuous.comp
    (((polar F).continuous.fst.comp continuous_snd).prodMk
      (radiusHomotopy.continuous.comp (continuous_fst.prodMk
        ((polar F).continuous.snd.comp continuous_snd))))

theorem deformationMap_zero (u : PuncturedBall F) : deformationMap (0, u) = u := by
  change (polar F).symm ((polar F u).1, radiusHomotopy (0, (polar F u).2)) = u
  rw [radiusHomotopy_zero]
  exact (polar F).symm_apply_apply u

theorem deformationMap_one (u : PuncturedBall F) :
    deformationMap (1, u) = inclusion (direction u) := by
  change point (polar F u).1 (radiusHomotopy (1, (polar F u).2)) = _
  rw [radiusHomotopy_one, point_outer]
  rfl

theorem deformationMap_boundary (t : unitInterval) (u : UnitSphere F) :
    deformationMap (t, inclusion u) = inclusion u := by
  change (polar F).symm ((polar F (boundaryPoint u)).1,
    radiusHomotopy (t, (polar F (boundaryPoint u)).2)) = boundaryPoint u
  rw [polar_boundary, radiusHomotopy_outer]
  exact point_outer u

def deformation : (ContinuousMap.id (PuncturedBall F)).Homotopy
    (inclusion.comp direction) where
  toContinuousMap := deformationMap
  map_zero_left := deformationMap_zero
  map_one_left := deformationMap_one

end Wikipedia.HopfProblem.DegreeCollapse.PuncturedClosedBallRetraction
