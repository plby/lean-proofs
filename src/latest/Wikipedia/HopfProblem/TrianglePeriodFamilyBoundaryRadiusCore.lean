import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupMeridians
import Mathlib.Topology.Homotopy.Basic

/-!
# Radial expansion in the actual punctured-plane boundary coordinates

Positive radii at most one half form a strip with an unrestricted real
angle.  Radial expansion to one half is an explicit continuous homotopy
fixing the outer edge.  Both puncture coordinates map the whole strip into
the actual twice-punctured plane.  Their full-turn endpoints and common
outer basepoint are literal equalities in that space.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryRadius

open SpecialPeriods.Triangle

/-- The positive radii that keep the two puncture disks disjoint. -/
abbrev SmallRadius := Set.Ioc (0 : ℝ) (1 / 2)

/-- The common outer radius of the two normalized meridians. -/
def outerRadius : SmallRadius := ⟨1 / 2, by norm_num⟩

@[simp] theorem outerRadius_coe : (outerRadius : ℝ) = 1 / 2 := rfl

/-- Radius together with an unwrapped real angle, measured in full turns. -/
abbrev RadiusStrip := SmallRadius × ℝ

/-- Linear radial expansion toward the outer radius, staying strictly away from zero. -/
def radiusBlend (s : unitInterval) (r : SmallRadius) : SmallRadius :=
  ⟨(1 - (s : ℝ)) * (r : ℝ) + (s : ℝ) / 2, by
    constructor
    · have hr := r.property.1
      have h := mul_nonneg s.property.1 (sub_nonneg.mpr r.property.2)
      nlinarith
    · have h := mul_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr r.property.2)
      nlinarith⟩

@[simp] theorem radiusBlend_coe (s : unitInterval) (r : SmallRadius) :
    (radiusBlend s r : ℝ) = (1 - (s : ℝ)) * (r : ℝ) + (s : ℝ) / 2 := rfl

@[simp] theorem radiusBlend_zero (r : SmallRadius) : radiusBlend 0 r = r := by
  apply Subtype.ext
  simp

@[simp] theorem radiusBlend_one (r : SmallRadius) : radiusBlend 1 r = outerRadius := by
  apply Subtype.ext
  simp

@[simp] theorem radiusBlend_outer (s : unitInterval) :
    radiusBlend s outerRadius = outerRadius := by
  apply Subtype.ext
  simp only [radiusBlend_coe, outerRadius_coe]
  ring

@[fun_prop] theorem continuous_radiusBlend :
    Continuous (fun x : unitInterval × SmallRadius => radiusBlend x.1 x.2) := by
  unfold radiusBlend
  fun_prop

/-- Replace the radius by one half while keeping the unwrapped angle unchanged. -/
def stripExpand : C(RadiusStrip, RadiusStrip) :=
  ⟨fun x => (outerRadius, x.2), continuous_const.prodMk continuous_snd⟩

@[simp] theorem stripExpand_apply (x : RadiusStrip) :
    stripExpand x = (outerRadius, x.2) := rfl

/-- The explicit radial deformation of the actual strip. -/
def stripRadialHomotopy : (ContinuousMap.id RadiusStrip).Homotopy stripExpand where
  toFun x := (radiusBlend x.1 x.2.1, x.2.2)
  continuous_toFun :=
    (continuous_radiusBlend.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      continuous_snd.snd
  map_zero_left x := by
    change (radiusBlend 0 x.1, x.2) = x
    simp
  map_one_left x := by
    change (radiusBlend 1 x.1, x.2) = (outerRadius, x.2)
    rw [radiusBlend_one]

@[simp] theorem stripRadialHomotopy_apply (s : unitInterval) (x : RadiusStrip) :
    stripRadialHomotopy (s, x) = (radiusBlend s x.1, x.2) := rfl

/-- The deformation fixes the outer edge pointwise at every time. -/
@[simp] theorem stripRadialHomotopy_fixed_outer (s : unitInterval) (θ : ℝ) :
    stripRadialHomotopy (s, (outerRadius, θ)) = (outerRadius, θ) := by
  rw [stripRadialHomotopy_apply, radiusBlend_outer]

private theorem small_circle_ne_one (r : SmallRadius) (θ : ℝ) :
    circleMap 0 (r : ℝ) θ ≠ 1 := by
  intro h
  have hn := norm_circleMap_zero (r : ℝ) θ
  rw [h, norm_one, abs_of_pos r.property.1] at hn
  have hr := r.property.2
  linarith

private theorem radialCoordinate_mem (b : Bool) (x : RadiusStrip) :
    (if b then 1 - circleMap 0 (x.1 : ℝ) (2 * Real.pi * x.2)
      else circleMap 0 (x.1 : ℝ) (2 * Real.pi * x.2)) ∈ twicePuncturedPlaneDomain := by
  have h₀ := circleMap_ne_center (ne_of_gt x.1.property.1)
    (c := (0 : ℂ)) (θ := 2 * Real.pi * x.2)
  have h₁ := small_circle_ne_one x.1 (2 * Real.pi * x.2)
  cases b
  · exact ⟨h₀, h₁⟩
  · constructor
    · exact sub_ne_zero.mpr h₁.symm
    · intro h
      exact h₀ (sub_eq_self.mp h)

/-- The actual radius-angle coordinate around zero or one in the twice-punctured plane. -/
def radialCoordinate (b : Bool) : C(RadiusStrip, TwicePuncturedPlane) :=
  ⟨fun x => ⟨if b then 1 - circleMap 0 (x.1 : ℝ) (2 * Real.pi * x.2)
      else circleMap 0 (x.1 : ℝ) (2 * Real.pi * x.2), radialCoordinate_mem b x⟩, by
    apply Continuous.subtype_mk
    cases b <;> dsimp [circleMap] <;> fun_prop⟩

@[simp] theorem radialCoordinate_coe (b : Bool) (r : SmallRadius) (θ : ℝ) :
    (radialCoordinate b (r, θ) : ℂ) =
      if b then 1 - circleMap 0 (r : ℝ) (2 * Real.pi * θ)
      else circleMap 0 (r : ℝ) (2 * Real.pi * θ) := rfl

/-- The positive-real radial basepoint of the selected puncture coordinate. -/
def radialBasepoint (b : Bool) (r : SmallRadius) : TwicePuncturedPlane :=
  radialCoordinate b (r, 0)

@[simp] theorem radialBasepoint_coe (b : Bool) (r : SmallRadius) :
    (radialBasepoint b r : ℂ) = if b then (1 : ℂ) - (r : ℝ) else (r : ℝ) := by
  rw [radialBasepoint, radialCoordinate_coe]
  simp [circleMap]

/-- One full turn returns to the actual radial basepoint. -/
@[simp] theorem radialCoordinate_one (b : Bool) (r : SmallRadius) :
    radialCoordinate b (r, 1) = radialBasepoint b r := by
  apply Subtype.ext
  rw [radialCoordinate_coe, radialBasepoint_coe]
  have h : circleMap 0 (r : ℝ) (2 * Real.pi) = circleMap 0 (r : ℝ) 0 := by
    simpa only [zero_add] using periodic_circleMap (0 : ℂ) (r : ℝ) 0
  rw [mul_one, h]
  simp [circleMap]

/-- Both outer radial basepoints are the common normalized meridian basepoint. -/
@[simp] theorem radialBasepoint_outer (b : Bool) :
    radialBasepoint b outerRadius = meridianBasepoint := by
  apply Subtype.ext
  rw [radialBasepoint_coe, outerRadius_coe, meridianBasepoint_coe]
  cases b <;> norm_num

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryRadius
