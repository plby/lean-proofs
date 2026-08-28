import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupHomeomorph
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupMeridiansPaths
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupMeridiansOrientation

/-!
# Positive meridians in the actual twice-punctured plane

The four explicit semicircles lift to paths in the literal subtype
`TwicePuncturedPlane`. Their images lie in the respective slit domains,
including the endpoints. Concatenating the upper and lower arcs gives
the two positive meridians at the common basepoint `1/2`.
Their exact complex-coordinate formulas are the radius-`1/2` circles
with increasing angles `2πt` and `π + 2πt`, respectively.
-/

noncomputable section

open Set
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The common basepoint between the two deleted points. -/
def meridianBasepoint : TwicePuncturedPlane := ⟨(1 / 2 : ℂ), by norm_num⟩

/-- The real endpoint on the other side of the puncture at zero. -/
def meridianLeftPoint : TwicePuncturedPlane := ⟨(-1 / 2 : ℂ), by norm_num⟩

/-- The real endpoint on the other side of the puncture at one. -/
def meridianRightPoint : TwicePuncturedPlane := ⟨(3 / 2 : ℂ), by norm_num⟩

@[simp] theorem meridianBasepoint_coe : (meridianBasepoint : ℂ) = 1 / 2 := rfl

@[simp] theorem meridianLeftPoint_coe : (meridianLeftPoint : ℂ) = -1 / 2 := rfl

@[simp] theorem meridianRightPoint_coe : (meridianRightPoint : ℂ) = 3 / 2 := rfl

private def liftPuncturedPath {x y : TwicePuncturedPlane}
    (γ : Path (x : ℂ) (y : ℂ))
    (hγ : ∀ t : unitInterval, γ t ∈ twicePuncturedPlaneDomain) : Path x y where
  toFun t := ⟨γ t, hγ t⟩
  continuous_toFun := γ.continuous.subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

/-- The actual upper path about zero in the twice-punctured plane. -/
def upperZeroPath : Path meridianBasepoint meridianLeftPoint :=
  liftPuncturedPath upperZeroArc upperZeroArc_avoids_punctures

/-- The actual lower path about zero in the twice-punctured plane. -/
def lowerZeroPath : Path meridianBasepoint meridianLeftPoint :=
  liftPuncturedPath lowerZeroArc lowerZeroArc_avoids_punctures

/-- The actual upper path about one in the twice-punctured plane. -/
def upperOnePath : Path meridianBasepoint meridianRightPoint :=
  liftPuncturedPath upperOneArc upperOneArc_avoids_punctures

/-- The actual lower path about one in the twice-punctured plane. -/
def lowerOnePath : Path meridianBasepoint meridianRightPoint :=
  liftPuncturedPath lowerOneArc lowerOneArc_avoids_punctures

@[simp] theorem upperZeroPath_coe (t : unitInterval) :
    (upperZeroPath t : ℂ) = upperZeroArc t := rfl

@[simp] theorem lowerZeroPath_coe (t : unitInterval) :
    (lowerZeroPath t : ℂ) = lowerZeroArc t := rfl

@[simp] theorem upperOnePath_coe (t : unitInterval) :
    (upperOnePath t : ℂ) = upperOneArc t := rfl

@[simp] theorem lowerOnePath_coe (t : unitInterval) :
    (lowerOnePath t : ℂ) = lowerOneArc t := rfl

theorem upperZeroPath_mem_upperSlitPlane (t : unitInterval) :
    (upperZeroPath t : ℂ) ∈ upperSlitPlane := upperZeroArc_mem_upperSlitPlane t

theorem lowerZeroPath_mem_lowerSlitPlane (t : unitInterval) :
    (lowerZeroPath t : ℂ) ∈ lowerSlitPlane := lowerZeroArc_mem_lowerSlitPlane t

theorem upperOnePath_mem_upperSlitPlane (t : unitInterval) :
    (upperOnePath t : ℂ) ∈ upperSlitPlane := upperOneArc_mem_upperSlitPlane t

theorem lowerOnePath_mem_lowerSlitPlane (t : unitInterval) :
    (lowerOnePath t : ℂ) ∈ lowerSlitPlane := lowerOneArc_mem_lowerSlitPlane t

@[simp] theorem upperZeroPath_map_coe :
    upperZeroPath.map continuous_subtype_val = upperZeroArc := by
  ext t
  rfl

@[simp] theorem lowerZeroPath_map_coe :
    lowerZeroPath.map continuous_subtype_val = lowerZeroArc := by
  ext t
  rfl

@[simp] theorem upperOnePath_map_coe :
    upperOnePath.map continuous_subtype_val = upperOneArc := by
  ext t
  rfl

@[simp] theorem lowerOnePath_map_coe :
    lowerOnePath.map continuous_subtype_val = lowerOneArc := by
  ext t
  rfl

/-- The positively oriented meridian about zero, based at `1/2`. -/
def positiveMeridianZero : Path meridianBasepoint meridianBasepoint :=
  upperZeroPath.trans lowerZeroPath.symm

/-- The positively oriented meridian about one, based at `1/2`. -/
def positiveMeridianOne : Path meridianBasepoint meridianBasepoint :=
  lowerOnePath.trans upperOnePath.symm

@[simp] theorem positiveMeridianZero_map_coe :
    positiveMeridianZero.map continuous_subtype_val = meridianZeroComplex := by
  change (upperZeroPath.trans lowerZeroPath.symm).map continuous_subtype_val =
    upperZeroArc.trans lowerZeroArc.symm
  rw [Path.map_trans, ← Path.map_symm, upperZeroPath_map_coe, lowerZeroPath_map_coe]
  rfl

@[simp] theorem positiveMeridianOne_map_coe :
    positiveMeridianOne.map continuous_subtype_val = meridianOneComplex := by
  change (lowerOnePath.trans upperOnePath.symm).map continuous_subtype_val =
    lowerOneArc.trans upperOneArc.symm
  rw [Path.map_trans, ← Path.map_symm, lowerOnePath_map_coe, upperOnePath_map_coe]
  rfl

@[simp] theorem positiveMeridianZero_coe (t : unitInterval) :
    (positiveMeridianZero t : ℂ) = meridianZeroComplex t :=
  congrArg (fun γ : Path (1 / 2 : ℂ) (1 / 2) => γ t) positiveMeridianZero_map_coe

@[simp] theorem positiveMeridianOne_coe (t : unitInterval) :
    (positiveMeridianOne t : ℂ) = meridianOneComplex t :=
  congrArg (fun γ : Path (1 / 2 : ℂ) (1 / 2) => γ t) positiveMeridianOne_map_coe

/-- The actual meridian about zero makes one positive full turn. -/
theorem positiveMeridianZero_apply (t : unitInterval) :
    (positiveMeridianZero t : ℂ) =
      (1 / 2 : ℂ) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (t : ℝ)) := by
  rw [positiveMeridianZero_coe, meridianZeroComplex_apply]

/-- The actual meridian about one makes one positive full turn. -/
theorem positiveMeridianOne_apply (t : unitInterval) :
    (positiveMeridianOne t : ℂ) =
      1 - (1 / 2 : ℂ) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (t : ℝ)) := by
  rw [positiveMeridianOne_coe, meridianOneComplex_apply]

/-- The zero meridian is exactly the positive radius-`1/2` circle. -/
theorem positiveMeridianZero_eq_circleMap (t : unitInterval) :
    (positiveMeridianZero t : ℂ) = circleMap 0 (1 / 2) (2 * Real.pi * (t : ℝ)) := by
  rw [positiveMeridianZero_coe, meridianZeroComplex_eq_circleMap]

/-- The one meridian is exactly the positive radius-`1/2` circle, starting at angle `π`. -/
theorem positiveMeridianOne_eq_circleMap (t : unitInterval) :
    (positiveMeridianOne t : ℂ) =
      circleMap 1 (1 / 2) (Real.pi + 2 * Real.pi * (t : ℝ)) := by
  rw [positiveMeridianOne_coe, meridianOneComplex_eq_circleMap]

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
