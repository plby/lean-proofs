import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryRadiusCore
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCover
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Literal small-radius circles with real tails

The radial strip keeps a real angular coordinate before taking its complex
exponential. Its three-piece path first moves radially from `1/2` to the
chosen radius, then turns once positively, then returns radially at angle
one. The projected path is exactly the real-tail conjugate of the literal
small circle. Both real tails remain in the middle slit-overlap strip.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryRadius

open SpecialPeriods.Triangle

/-- The affine real radial tail, starting at the outer radius. -/
def stripRadiusTail (r : SmallRadius) : Path outerRadius r where
  toFun t := radiusBlend (unitInterval.symm t) r
  continuous_toFun := by
    unfold radiusBlend
    fun_prop
  source' := by simp
  target' := by simp

@[simp] theorem stripRadiusTail_apply (r : SmallRadius) (t : unitInterval) :
    stripRadiusTail r t = radiusBlend (unitInterval.symm t) r := rfl

/-- The tail uses the ordinary affine parametrization of the real interval. -/
theorem stripRadiusTail_coe (r : SmallRadius) (t : unitInterval) :
    (stripRadiusTail r t : ℝ) = (1 - (t : ℝ)) / 2 + (t : ℝ) * (r : ℝ) := by
  rw [stripRadiusTail_apply, radiusBlend_coe]
  simp only [unitInterval.coe_symm_eq]
  ring

/-- A radial tail at any fixed real angle. -/
def stripTail (r : SmallRadius) (θ : ℝ) : Path (outerRadius, θ) (r, θ) :=
  (stripRadiusTail r).map (continuous_id.prodMk continuous_const)

@[simp] theorem stripTail_apply (r : SmallRadius) (θ : ℝ) (t : unitInterval) :
    stripTail r θ t = (stripRadiusTail r t, θ) := rfl

/-- One positive angular turn at the fixed small radius. -/
def stripCircle (r : SmallRadius) : Path (r, (0 : ℝ)) (r, 1) where
  toFun t := (r, (t : ℝ))
  continuous_toFun := continuous_const.prodMk continuous_subtype_val
  source' := rfl
  target' := rfl

@[simp] theorem stripCircle_apply (r : SmallRadius) (t : unitInterval) :
    stripCircle r t = (r, (t : ℝ)) := rfl

/-- The based radial-circle path in the actual radial strip. -/
def stripBasedPath (r : SmallRadius) :
    Path (outerRadius, (0 : ℝ)) (outerRadius, 1) :=
  (stripTail r 0).trans ((stripCircle r).trans (stripTail r 1).symm)

/-- Project a strip path with the fixed outer endpoints to a based planar loop. -/
def projectStripPath (b : Bool)
    (p : Path (outerRadius, (0 : ℝ)) (outerRadius, 1)) :
    Path meridianBasepoint meridianBasepoint :=
  (p.map (radialCoordinate b).continuous).cast
    (radialBasepoint_outer b).symm
    ((radialCoordinate_one b outerRadius).trans (radialBasepoint_outer b)).symm

@[simp] theorem projectStripPath_apply (b : Bool)
    (p : Path (outerRadius, (0 : ℝ)) (outerRadius, 1)) (t : unitInterval) :
    projectStripPath b p t = radialCoordinate b (p t) := rfl

/-- The actual real tail from the fixed middle basepoint to the small circle. -/
def radialTail (b : Bool) (r : SmallRadius) :
    Path meridianBasepoint (radialBasepoint b r) :=
  ((stripTail r 0).map (radialCoordinate b).continuous).cast
    (radialBasepoint_outer b).symm rfl

/-- The same real tail evaluated at the angular lift one. -/
def radialTailOne (b : Bool) (r : SmallRadius) :
    Path meridianBasepoint (radialBasepoint b r) :=
  ((stripTail r 1).map (radialCoordinate b).continuous).cast
    ((radialCoordinate_one b outerRadius).trans (radialBasepoint_outer b)).symm
    (radialCoordinate_one b r).symm

@[simp] theorem radialTail_apply (b : Bool) (r : SmallRadius) (t : unitInterval) :
    radialTail b r t = radialBasepoint b (stripRadiusTail r t) := rfl

theorem radialTailOne_eq (b : Bool) (r : SmallRadius) :
    radialTailOne b r = radialTail b r := by
  apply Path.ext
  funext t
  change radialCoordinate b (stripRadiusTail r t, 1) =
    radialBasepoint b (stripRadiusTail r t)
  exact radialCoordinate_one b _

/-- The tail is literally real and remains between the two deleted points. -/
theorem radialTail_coe (b : Bool) (r : SmallRadius) (t : unitInterval) :
    (radialTail b r t : ℂ) =
      if b then 1 - (((1 - (t : ℝ)) / 2 + (t : ℝ) * (r : ℝ) : ℝ) : ℂ)
      else (((1 - (t : ℝ)) / 2 + (t : ℝ) * (r : ℝ) : ℝ) : ℂ) := by
  rw [radialTail_apply, radialBasepoint_coe, stripRadiusTail_coe]

/-- The entire real tail lies in the actual middle overlap strip. -/
theorem radialTail_mem_middle (b : Bool) (r : SmallRadius) (t : unitInterval) :
    radialTail b r t ∈ slitOverlapStrip 1 := by
  rw [mem_slitOverlapStrip, radialTail_apply, radialBasepoint_coe]
  have h := (stripRadiusTail r t).property
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Complex.sub_re,
    Complex.one_re, Complex.ofReal_re, overlapStrip, Set.mem_ofPred_eq]
  · exact ⟨h.1, lt_of_le_of_lt h.2 (by norm_num)⟩
  · constructor <;> linarith [h.1, h.2]

/-- The literal positive small circle about the selected puncture. -/
def radialCircle (b : Bool) (r : SmallRadius) :
    Path (radialBasepoint b r) (radialBasepoint b r) :=
  ((stripCircle r).map (radialCoordinate b).continuous).cast rfl
    (radialCoordinate_one b r).symm

@[simp] theorem radialCircle_coe (b : Bool) (r : SmallRadius) (t : unitInterval) :
    (radialCircle b r t : ℂ) =
      if b then 1 - circleMap 0 (r : ℝ) (2 * Real.pi * (t : ℝ))
      else circleMap 0 (r : ℝ) (2 * Real.pi * (t : ℝ)) :=
  radialCoordinate_coe b r t

/-- The actual based small meridian with its real middle-strip tail. -/
def basedRadiusMeridian (b : Bool) (r : SmallRadius) :
    Path meridianBasepoint meridianBasepoint :=
  projectStripPath b (stripBasedPath r)

/-- The projected radial-strip path is exactly tail, circle, and reversed tail. -/
theorem basedRadiusMeridian_eq_tail_circle (b : Bool) (r : SmallRadius) :
    basedRadiusMeridian b r =
      (radialTail b r).trans ((radialCircle b r).trans (radialTail b r).symm) := by
  unfold basedRadiusMeridian projectStripPath stripBasedPath
  rw [Path.map_trans, Path.map_trans]
  change (radialTail b r).trans ((radialCircle b r).trans (radialTailOne b r).symm) = _
  rw [radialTailOne_eq]

/-- The expanded path has fixed outer radius and the same real angular parameter. -/
def stripExpandedPath (r : SmallRadius) :
    Path (outerRadius, (0 : ℝ)) (outerRadius, 1) :=
  (stripBasedPath r).map stripExpand.continuous

/-- The explicit radial deformation fixes both endpoints of the strip path. -/
def stripBasedPathRadialHomotopy (r : SmallRadius) :
    (stripBasedPath r).Homotopy (stripExpandedPath r) where
  toFun z := stripRadialHomotopy (z.1, stripBasedPath r z.2)
  continuous_toFun := stripRadialHomotopy.continuous.comp
    (continuous_fst.prodMk ((stripBasedPath r).continuous.comp continuous_snd))
  map_zero_left t := stripRadialHomotopy.map_zero_left (stripBasedPath r t)
  map_one_left t := stripRadialHomotopy.map_one_left (stripBasedPath r t)
  prop' s t ht := by
    rcases ht with ht | ht
    · subst t
      change stripRadialHomotopy (s, stripBasedPath r 0) = stripBasedPath r 0
      rw [(stripBasedPath r).source]
      exact stripRadialHomotopy_fixed_outer s 0
    · rw [Set.mem_singleton_iff] at ht
      subst t
      change stripRadialHomotopy (s, stripBasedPath r 1) = stripBasedPath r 1
      rw [(stripBasedPath r).target]
      exact stripRadialHomotopy_fixed_outer s 1

/-- The resulting explicit based radial homotopy of literal planar loops. -/
def basedRadiusRadialHomotopy (b : Bool) (r : SmallRadius) :
    (basedRadiusMeridian b r).Homotopy (projectStripPath b (stripExpandedPath r)) :=
  ((stripBasedPathRadialHomotopy r).map (radialCoordinate b)).pathCast
    (radialBasepoint_outer b).symm
    ((radialCoordinate_one b outerRadius).trans (radialBasepoint_outer b)).symm

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryRadius
