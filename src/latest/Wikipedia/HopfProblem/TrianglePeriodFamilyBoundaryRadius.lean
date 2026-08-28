import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryRadiusPaths
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupSemicircles

/-!
# Based radial comparison with the actual compatible meridians

For every real radius `0 < r ≤ 1/2`, the explicit radial homotopy expands
the literal circle while keeping its angular parameter and fixing the
based-loop endpoints. Its real middle-strip tails become constant. The
standard path-unit homotopies remove those constants. The resulting
outer circle is exactly the previously constructed positive meridian.

Reversing both loops when the normalization orientation requires it gives
an actual based homotopy to the compatible meridian, not just an equality
of winding numbers or an assigned generator label.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryRadius

open SpecialPeriods.Triangle RiemannMapping Meridians

/-- Radial expansion collapses each radial tail to its fixed outer endpoint. -/
theorem stripExpand_map_tail (r : SmallRadius) (θ : ℝ) :
    (stripTail r θ).map stripExpand.continuous = Path.refl (outerRadius, θ) := by
  apply Path.ext
  funext t
  rfl

/-- Radial expansion preserves the angular parametrization of the circle. -/
theorem stripExpand_map_circle (r : SmallRadius) :
    (stripCircle r).map stripExpand.continuous = stripCircle outerRadius := by
  apply Path.ext
  funext t
  rfl

/-- The expanded strip path is the outer circle with constant paths at its two ends. -/
theorem stripExpandedPath_eq (r : SmallRadius) :
    stripExpandedPath r = (Path.refl (outerRadius, (0 : ℝ))).trans
      ((stripCircle outerRadius).trans (Path.refl (outerRadius, (1 : ℝ)))) := by
  rw [stripExpandedPath, stripBasedPath, Path.map_trans, Path.map_trans,
    ← Path.map_symm, stripExpand_map_tail, stripExpand_map_circle, stripExpand_map_tail]
  rfl

/-- The literal outer circle, projected with its two equal planar endpoints. -/
def outerCircleLoop (b : Bool) : Path meridianBasepoint meridianBasepoint :=
  projectStripPath b (stripCircle outerRadius)

/-- The outer circle is exactly the existing positive planar meridian. -/
theorem outerCircleLoop_eq (b : Bool) :
    outerCircleLoop b = if b then positiveMeridianOne else positiveMeridianZero := by
  apply Path.ext
  funext t
  apply Subtype.ext
  cases b
  · change circleMap 0 (1 / 2) (2 * Real.pi * (t : ℝ)) = (positiveMeridianZero t : ℂ)
    exact (positiveMeridianZero_eq_circleMap t).symm
  · change 1 - circleMap 0 (1 / 2) (2 * Real.pi * (t : ℝ)) =
      (positiveMeridianOne t : ℂ)
    rw [positiveMeridianOne_apply, circleMap_zero]
    have he : (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
        (2 * Real.pi : ℂ) * Complex.I * (t : ℝ) := by
      push_cast
      ring
    rw [he]
    norm_num

/-- Projection of the radial expansion has exactly the two constant endpoint paths. -/
theorem projectStripExpandedPath_eq (b : Bool) (r : SmallRadius) :
    projectStripPath b (stripExpandedPath r) = (Path.refl meridianBasepoint).trans
      ((outerCircleLoop b).trans (Path.refl meridianBasepoint)) := by
  let h₀ := (radialBasepoint_outer b).symm
  let h₁ := ((radialCoordinate_one b outerRadius).trans (radialBasepoint_outer b)).symm
  let p₀ : Path meridianBasepoint meridianBasepoint :=
    ((Path.refl (outerRadius, (0 : ℝ))).map (radialCoordinate b).continuous).cast h₀ h₀
  let p₁ : Path meridianBasepoint meridianBasepoint :=
    ((Path.refl (outerRadius, (1 : ℝ))).map (radialCoordinate b).continuous).cast h₁ h₁
  have hp₀ : p₀ = Path.refl meridianBasepoint := by
    apply Path.ext
    funext t
    exact radialBasepoint_outer b
  have hp₁ : p₁ = Path.refl meridianBasepoint := by
    apply Path.ext
    funext t
    exact (radialCoordinate_one b outerRadius).trans (radialBasepoint_outer b)
  rw [stripExpandedPath_eq]
  unfold projectStripPath
  rw [Path.map_trans, Path.map_trans]
  change p₀.trans ((outerCircleLoop b).trans p₁) = _
  rw [hp₀, hp₁]

/-- The actual based radial homotopy followed by the two endpoint-unit homotopies. -/
def basedRadiusMeridianHomotopy (b : Bool) (r : SmallRadius) :
    (basedRadiusMeridian b r).Homotopy
      (if b then positiveMeridianOne else positiveMeridianZero) :=
  ((((basedRadiusRadialHomotopy b r).cast rfl (projectStripExpandedPath_eq b r)).trans
      (Path.Homotopy.reflTrans _)).trans
      (Path.Homotopy.transRefl _)).cast rfl (outerCircleLoop_eq b)

/-- Every literal positive small meridian, with its fixed-basepoint tail, is homotopic
to the existing positive radius-`1/2` meridian. -/
theorem basedRadiusMeridian_homotopic (b : Bool) (r : SmallRadius) :
    (basedRadiusMeridian b r).Homotopic
      (if b then positiveMeridianOne else positiveMeridianZero) :=
  ⟨basedRadiusMeridianHomotopy b r⟩

/-- The small meridian with the same actual normalization orientation as the marked lift. -/
def compatibleRadiusMeridian (b : Bool) (r : SmallRadius) :
    Path meridianBasepoint meridianBasepoint :=
  if 0 < normalizationOrientation then (basedRadiusMeridian b r).symm
  else basedRadiusMeridian b r

/-- The actual based radial homotopy respects the chosen compatible orientation. -/
def compatibleRadiusMeridianHomotopy (b : Bool) (r : SmallRadius) :
    (compatibleRadiusMeridian b r).Homotopy (compatiblePlanarMeridian b) := by
  unfold compatibleRadiusMeridian
  rw [compatiblePlanarMeridian_eq]
  by_cases ho : 0 < normalizationOrientation
  · simpa only [if_pos ho] using (basedRadiusMeridianHomotopy b r).symm₂
  · simpa only [if_neg ho] using basedRadiusMeridianHomotopy b r

/-- Small circles and the constructed compatible meridians are genuinely based homotopic. -/
theorem compatibleRadiusMeridian_homotopic (b : Bool) (r : SmallRadius) :
    (compatibleRadiusMeridian b r).Homotopic (compatiblePlanarMeridian b) :=
  ⟨compatibleRadiusMeridianHomotopy b r⟩

/-- Equality is in the actual based path-homotopy quotient. -/
theorem compatibleRadiusMeridian_class (b : Bool) (r : SmallRadius) :
    Path.Homotopic.Quotient.mk (compatibleRadiusMeridian b r) =
      Path.Homotopic.Quotient.mk (compatiblePlanarMeridian b) :=
  Path.Homotopic.Quotient.eq.mpr (compatibleRadiusMeridian_homotopic b r)

/-- The full actual fundamental-group class has the same compatible marking. -/
theorem compatibleRadiusMeridian_fundamentalGroup (b : Bool) (r : SmallRadius) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (compatibleRadiusMeridian b r)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (compatiblePlanarMeridian b)) :=
  congrArg FundamentalGroup.fromPath (compatibleRadiusMeridian_class b r)

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryRadius
