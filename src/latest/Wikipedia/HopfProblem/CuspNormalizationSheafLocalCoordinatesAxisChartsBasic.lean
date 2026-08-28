import Wikipedia.HopfProblem.CuspRationalCurves

/-!
# Rescaling arbitrary toric axis charts

For every integral triangle, the actual axis map to a quotient double curve
is a nonzero scalar reparametrization of one of its two defining affine
charts.  The scalar is obtained from the existing twisted lattice action.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricCharts ToricSpace ToricFan Triangle

/-- The defining affine chart with the same orientation as `s`. -/
def axisBaseTriangle (s : Triangle) (i : Fin 3) : Triangle :=
  if s.upper then upperNeighbour i else referenceTriangle

@[simp] theorem axisBaseTriangle_upper (s : Triangle) (i : Fin 3) :
    (axisBaseTriangle s i).upper = s.upper := by
  cases hs : s.upper <;> simp [axisBaseTriangle, hs, referenceTriangle]

/-- The lattice action taking the reference triangle to `s`. -/
def axisShiftVector (s : Triangle) (i : Fin 3) : Fin 2 → ℤ :=
  -cuspVector ![s.a - (axisBaseTriangle s i).a, s.b - (axisBaseTriangle s i).b]

theorem axisBaseTriangle_shift (s : Triangle) (i : Fin 3) :
    (axisBaseTriangle s i).shift (cuspVector (axisShiftVector s i)) = s := by
  unfold axisShiftVector
  simp only [cuspVector_neg, cuspVector_cuspVector, neg_neg]
  apply Triangle.ext
  · change (axisBaseTriangle s i).a + (s.a - (axisBaseTriangle s i).a) = s.a
    omega
  · change (axisBaseTriangle s i).b + (s.b - (axisBaseTriangle s i).b) = s.b
    omega
  · exact axisBaseTriangle_upper s i

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

/-- The nonzero torus multiplier of the selected axis at central time. -/
def axisFactor (s : Triangle) (i : Fin 3) : ℂ :=
  factors s (fibreMultiplier (exponentialMultiplier C (axisShiftVector s i) 0))
    (s.axisIndex i)

theorem axisFactor_ne_zero (s : Triangle) (i : Fin 3) : axisFactor C s i ≠ 0 :=
  factors_nonzero _ _ _

def axisScale (s : Triangle) (i : Fin 3) (z : ℂ) : ℂ := (axisFactor C s i)⁻¹ * z

def axisScaleInv (s : Triangle) (i : Fin 3) (z : ℂ) : ℂ := axisFactor C s i * z

theorem axisScale_holomorphic (s : Triangle) (i : Fin 3) :
    ContDiff ℂ ω (axisScale C s i) := contDiff_const.mul contDiff_id

theorem axisScaleInv_holomorphic (s : Triangle) (i : Fin 3) :
    ContDiff ℂ ω (axisScaleInv C s i) := contDiff_const.mul contDiff_id

def axisScaleHomeomorph (s : Triangle) (i : Fin 3) : ℂ ≃ₜ ℂ where
  toFun := axisScale C s i
  invFun := axisScaleInv C s i
  left_inv z := by simp [axisScale, axisScaleInv, axisFactor_ne_zero]
  right_inv z := by simp [axisScale, axisScaleInv, axisFactor_ne_zero]
  continuous_toFun := (axisScale_holomorphic C s i).continuous
  continuous_invFun := (axisScaleInv_holomorphic C s i).continuous

variable (ε : ℝ) (hε : 0 < ε)

theorem axisMap_eq_base_scaled (s : Triangle) (i : Fin 3) (z : ℂ) :
    axisMap C ε hε s i z =
      axisMap C ε hε (axisBaseTriangle s i) i (axisScale C s i z) := by
  have h := axisMap_shift C ε hε (axisShiftVector s i) (axisBaseTriangle s i) i
    (axisScale C s i z)
  rw [axisBaseTriangle_shift] at h
  change axisMap C ε hε s i (axisFactor C s i * ((axisFactor C s i)⁻¹ * z)) = _ at h
  simpa only [mul_inv_cancel_left₀ (axisFactor_ne_zero C s i)] using h

/-- The actual axis map, with codomain restricted to its double curve. -/
def axisSection (s : Triangle) (i : Fin 3) (z : ℂ) : doubleCurve C ε hε i :=
  ⟨axisMap C ε hε s i z, axisMap_mem_doubleCurve C ε hε s i z⟩

@[simp] theorem axisSection_coe (s : Triangle) (i : Fin 3) (z : ℂ) :
    (axisSection C ε hε s i z : QuotientSpace C ε) = axisMap C ε hε s i z := rfl

theorem axisSection_eq_affineMap_scaled (s : Triangle) (i : Fin 3) :
    axisSection C ε hε s i =
      (curveCharts C ε hε i).affineMap s.upper ∘ axisScale C s i := by
  funext z
  apply Subtype.ext
  rw [axisSection_coe, axisMap_eq_base_scaled]
  cases hs : s.upper <;>
    simp [axisBaseTriangle, hs, TwoAffineCharts.affineMap, curveCharts]

theorem axisSection_range (s : Triangle) (i : Fin 3) :
    range (axisSection C ε hε s i) =
      range ((curveCharts C ε hε i).affineMap s.upper) := by
  rw [axisSection_eq_affineMap_scaled]
  change range ((curveCharts C ε hε i).affineMap s.upper ∘ axisScaleHomeomorph C s i) = _
  rw [range_comp, (axisScaleHomeomorph C s i).surjective.range_eq, image_univ]

theorem axisSection_injective (s : Triangle) (i : Fin 3) :
    Function.Injective (axisSection C ε hε s i) := by
  intro z w h
  exact axisMap_injective C ε hε s i (congrArg Subtype.val h)

theorem axisSection_continuous (s : Triangle) (i : Fin 3) :
    Continuous (axisSection C ε hε s i) :=
  (axisMap_continuous C ε hε s i).subtype_mk _

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
