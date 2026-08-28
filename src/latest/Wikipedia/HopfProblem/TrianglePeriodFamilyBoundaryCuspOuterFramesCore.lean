import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspOuterCircle
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLiftedCurve
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyMeridianTransitions

/-!
# The actual normalized lift of the clockwise outer circle

The regular-base curve is the literal inverse coordinate image of the
radius-two clockwise circle. Its initial point is the normalized lower
slit section at the bottom point. The infinite real lift is obtained from
the actual covering, with no independently assigned endpoint or deck word.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods SpecialPeriods.Triangle Homology

/-- The actual regular-base curve with the unchanged real circle parameter. -/
def outerClockwiseRegularCurve : C(ℝ, TriangleRegularQuotient) :=
  (triangleRegularPlaneHomeomorph.symm : C(TwicePuncturedPlane, TriangleRegularQuotient)).comp
    outerClockwiseCurve

@[simp] theorem outerClockwiseRegularCurve_coordinate (t : ℝ) :
    triangleRegularPlaneHomeomorph (outerClockwiseRegularCurve t) =
      outerClockwiseCurve t :=
  triangleRegularPlaneHomeomorph.apply_symm_apply _

/-- The actual bottom point, with normalized complex coordinate `1/2 - 2i`. -/
def outerClockwiseRegularBasepoint : TriangleRegularQuotient :=
  triangleRegularPlaneHomeomorph.symm (outerCircleBasepoint 2 (by norm_num))

@[simp] theorem outerClockwiseRegularBasepoint_coordinate :
    triangleRegularPlaneHomeomorph outerClockwiseRegularBasepoint =
      outerCircleBasepoint 2 (by norm_num) :=
  triangleRegularPlaneHomeomorph.apply_symm_apply _

/-- The literal clockwise outer loop in the actual regular quotient. -/
def outerClockwiseRegularMeridian :
    Path outerClockwiseRegularBasepoint outerClockwiseRegularBasepoint :=
  outerClockwiseCircle.map triangleRegularPlaneHomeomorph.symm.continuous

@[simp] theorem outerClockwiseRegularCurve_unit (t : unitInterval) :
    outerClockwiseRegularCurve t = outerClockwiseRegularMeridian t := by
  change triangleRegularPlaneHomeomorph.symm (outerClockwiseCurve t) =
    triangleRegularPlaneHomeomorph.symm (outerClockwiseCircle t)
  rw [outerClockwiseCurve_unit]

@[simp] theorem outerClockwiseRegularCurve_zero :
    outerClockwiseRegularCurve 0 = outerClockwiseRegularBasepoint :=
  (outerClockwiseRegularCurve_unit 0).trans outerClockwiseRegularMeridian.source

@[simp] theorem outerClockwiseRegularCurve_one :
    outerClockwiseRegularCurve 1 = outerClockwiseRegularBasepoint :=
  (outerClockwiseRegularCurve_unit 1).trans outerClockwiseRegularMeridian.target

theorem outerClockwiseRegularCurve_periodic :
    Function.Periodic outerClockwiseRegularCurve 1 := by
  intro t
  change triangleRegularPlaneHomeomorph.symm (outerClockwiseCurve (t + 1)) =
    triangleRegularPlaneHomeomorph.symm (outerClockwiseCurve t)
  rw [outerClockwiseCurve_periodic t]

theorem outerClockwiseRegularBasepoint_mem_lower :
    outerClockwiseRegularBasepoint ∈ lowerBase := by
  rw [mem_regularOpen, outerClockwiseRegularBasepoint_coordinate]
  change ((1 / 2 : ℂ) - (2 : ℂ) * Complex.I) ∈ lowerSlitPlane
  apply Or.inr
  norm_num

/-- The bottom point as an actual point of the lower slit. -/
def outerClockwiseLowerBasepoint : lowerBase :=
  ⟨outerClockwiseRegularBasepoint, outerClockwiseRegularBasepoint_mem_lower⟩

/-- The chosen lift is the actual normalized lower section at the bottom point. -/
def outerClockwiseBaseLift : TriangleRegularPoint :=
  lowerLift normalizedSlitBaseLift outerClockwiseLowerBasepoint

@[simp] theorem outerClockwiseBaseLift_project :
    triangleRegularProject outerClockwiseBaseLift = outerClockwiseRegularBasepoint :=
  lowerLift_project normalizedSlitBaseLift outerClockwiseLowerBasepoint

/-- The genuine normalized lift on the whole real line. -/
def outerClockwiseLift : C(ℝ, TriangleRegularPoint) :=
  realCurveLift outerClockwiseRegularCurve outerClockwiseBaseLift
    (outerClockwiseBaseLift_project.trans outerClockwiseRegularCurve_zero.symm)

@[simp] theorem outerClockwiseLift_zero : outerClockwiseLift 0 = outerClockwiseBaseLift :=
  realCurveLift_zero _ _ _

@[simp] theorem outerClockwiseLift_projection (t : ℝ) :
    triangleRegularProject (outerClockwiseLift t) = outerClockwiseRegularCurve t :=
  realCurveLift_projection _ _ _ t

/-- The projection has the literal clockwise complex-coordinate value at every real time. -/
theorem outerClockwiseLift_coordinate (t : ℝ) :
    (triangleRegularPlaneHomeomorph (triangleRegularProject (outerClockwiseLift t)) : ℂ) =
      outerCircleValue 2 (-t) := by
  rw [outerClockwiseLift_projection, outerClockwiseRegularCurve_coordinate, outerClockwiseCurve_coe]

/-- Its unit restriction is the uniquely lifted literal outer meridian. -/
theorem outerClockwiseLift_eq_liftPath (t : unitInterval) :
    outerClockwiseLift t =
      triangleRegularProject_covering.isCoveringMap.liftPath
        outerClockwiseRegularMeridian outerClockwiseBaseLift
        (outerClockwiseRegularMeridian.source.trans outerClockwiseBaseLift_project.symm) t := by
  apply congrFun ((triangleRegularProject_covering.isCoveringMap.eq_liftPath_iff _).mpr
    ⟨outerClockwiseLift.continuous.comp continuous_subtype_val,
      by
        funext u
        exact (outerClockwiseLift_projection u).trans (outerClockwiseRegularCurve_unit u),
      outerClockwiseLift_zero⟩) t

/-- The shortened upper interval really maps into the actual upper slit. -/
theorem outerClockwiseRegularCurve_mem_upperBase (t : ℝ)
    (ht₀ : 1 / 8 < t) (ht₁ : t < 7 / 8) :
    outerClockwiseRegularCurve t ∈ upperBase := by
  rw [mem_regularOpen, outerClockwiseRegularCurve_coordinate]
  exact outerClockwiseCurve_mem_upperSlitPlane t ht₀ ht₁

/-- The shortened interval crossing zero really maps into the actual lower slit. -/
theorem outerClockwiseRegularCurve_mem_lowerBase (t : ℝ)
    (ht₀ : -(3 / 8) < t) (ht₁ : t < 3 / 8) :
    outerClockwiseRegularCurve t ∈ lowerBase := by
  rw [mem_regularOpen, outerClockwiseRegularCurve_coordinate]
  exact outerClockwiseCurve_mem_lowerSlitPlane t ht₀ ht₁

/-- The two closed outer path pieces lie in the lower slit. -/
theorem outerClockwiseRegularCurve_mem_lower_piece (t : ℝ)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (ht : t ≤ 1 / 4 ∨ 3 / 4 ≤ t) :
    outerClockwiseRegularCurve t ∈ lowerBase := by
  rw [mem_regularOpen, outerClockwiseRegularCurve_coordinate]
  change (outerClockwiseCurve t : ℂ) ∈ lowerSlitPlane
  have he := outerClockwiseCurve_unit (⟨t, ht₀, ht₁⟩ : unitInterval)
  rw [he]
  exact outerClockwiseCircle_mem_lowerSlitPlane _ ht

/-- The closed middle path piece lies in the upper slit. -/
theorem outerClockwiseRegularCurve_mem_upper_piece (t : ℝ)
    (ht₀ : 1 / 4 ≤ t) (ht₁ : t ≤ 3 / 4) :
    outerClockwiseRegularCurve t ∈ upperBase := by
  rw [mem_regularOpen, outerClockwiseRegularCurve_coordinate]
  change (outerClockwiseCurve t : ℂ) ∈ upperSlitPlane
  let u : unitInterval := ⟨t, by constructor <;> linarith⟩
  have he := outerClockwiseCurve_unit u
  rw [he]
  exact outerClockwiseCircle_mem_upperSlitPlane u ht₀ ht₁

/-- The clockwise quarter point belongs to the actual left overlap component. -/
def outerClockwiseQuarterPoint : overlapBase 0 := by
  refine ⟨outerClockwiseRegularCurve (1 / 4), ?_⟩
  rw [mem_regularOpen, outerClockwiseRegularCurve_coordinate]
  change (outerClockwiseCurve (1 / 4) : ℂ) ∈ overlapStrip 0
  rw [outerClockwiseCurve_quarter]
  norm_num [overlapStrip]

/-- The clockwise three-quarter point belongs to the actual right overlap component. -/
def outerClockwiseThreeQuarterPoint : overlapBase 2 := by
  refine ⟨outerClockwiseRegularCurve (3 / 4), ?_⟩
  rw [mem_regularOpen, outerClockwiseRegularCurve_coordinate]
  change (outerClockwiseCurve (3 / 4) : ℂ) ∈ overlapStrip 2
  rw [outerClockwiseCurve_threeQuarters]
  norm_num [overlapStrip]

@[simp] theorem outerClockwiseQuarterPoint_val :
    outerClockwiseQuarterPoint.val = outerClockwiseRegularCurve (1 / 4) := rfl

@[simp] theorem outerClockwiseThreeQuarterPoint_val :
    outerClockwiseThreeQuarterPoint.val = outerClockwiseRegularCurve (3 / 4) := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
