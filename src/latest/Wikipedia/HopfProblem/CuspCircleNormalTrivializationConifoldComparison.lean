import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldBoundary
import Wikipedia.HopfProblem.ConifoldStandardBoundaryScaling

/-!
# Native chart formulas and arbitrary positive boundary radius

The circle on the toric radius boundary is checked against the unchanged
native diagonal action in each original chart. Composing the proved
toric-link homeomorphism with the explicit conifold homothety and
deformation gives a circle-equivariant map to one fixed smoothing level,
for every positive native normal radius, including small tubular radii.

This identifies the actual local boundary. It does not identify a global
threefold complement or invoke a sphere-recognition assertion.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold

open ToricCharts ConifoldStandardBoundary

/-- A native affine chart point satisfying the literal global radius equation. -/
def toricBoundaryInclusion {r : ℝ} (b : Bool) (z : CoordinateSpace 3)
    (hz : radiusSq (chartCoordinates b z).2 = r ^ 2) : ToricBoundary r :=
  ⟨toricInclusion b z, by
    rw [toricNeighborhoodDiffeomorph_symm_toricInclusion]
    exact hz⟩

@[simp] theorem toricBoundaryInclusion_val {r : ℝ} (b : Bool) (z : CoordinateSpace 3)
    (hz : radiusSq (chartCoordinates b z).2 = r ^ 2) :
    (toricBoundaryInclusion b z hz).val = toricInclusion b z := rfl

/-- The boundary homeomorphism has the original small-resolution formula on both charts. -/
theorem toricBoundaryHomeomorph_toricBoundaryInclusion {r : ℝ} (hr : r ≠ 0)
    (b : Bool) (z : CoordinateSpace 3) (hz : radiusSq (chartCoordinates b z).2 = r ^ 2) :
    (toricBoundaryHomeomorph hr (toricBoundaryInclusion b z hz)).val =
      chartMatrix b (z 1) (z 0, z 2) := by
  rw [toricBoundaryHomeomorph_apply_val, toricBoundaryInclusion_val,
    toricMap_toricInclusion]

/-- The boundary circle action is the actual native diagonal action, not just
an action with isomorphic weights or a replacement tangent representation. -/
theorem toricBoundaryCircle_toricBoundaryInclusion_val {r : ℝ}
    (b : Bool) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (z : CoordinateSpace 3) (hz : radiusSq (chartCoordinates b z).2 = r ^ 2) :
    (toricBoundaryCircle (u : ℂ) hu (toricBoundaryInclusion b z hz)).val =
      toricInclusion b (SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.diagonal u z) := by
  rw [toricBoundaryCircle_val, toricBoundaryInclusion_val]
  have hp : ((toricNeighborhoodDiffeomorph.symm (toricInclusion b z)).1,
      (u : ℂ) • (toricNeighborhoodDiffeomorph.symm (toricInclusion b z)).2) =
      toricNeighborhoodDiffeomorph.symm
        (toricInclusion b
          (SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.diagonal u z)) := by
    simp only [toricNeighborhoodDiffeomorph_symm_toricInclusion,
      chartCoordinates_diagonal b u hu]
    rfl
  rw [hp, toricNeighborhoodDiffeomorph.apply_symm_apply]

/-- Every positive native toric radius level is homeomorphic to the fixed
literal determinant-one smoothing boundary at radius parameter two. -/
def normalizedToricBoundaryHomeomorph {r : ℝ} (hr : 0 < r) :
    ToricBoundary r ≃ₜ SmoothingBoundary 2 :=
  (toricBoundaryHomeomorph (ne_of_gt hr)).trans (normalizedBoundaryHomeomorph hr)

/-- Its forward map is the original native matrix, followed by the explicit
homothety and adjoint-adjugate deformation. -/
@[simp] theorem normalizedToricBoundaryHomeomorph_apply_val {r : ℝ} (hr : 0 < r)
    (y : ToricBoundary r) :
    (normalizedToricBoundaryHomeomorph hr y).val =
      forward 2 (rescaleMatrix r 2 (toricMap y.val)) := rfl

theorem normalizedToricBoundaryHomeomorph_circle {r : ℝ} (hr : 0 < r)
    (u : ℂ) (hu : ‖u‖ = 1) (y : ToricBoundary r) :
    normalizedToricBoundaryHomeomorph hr (toricBoundaryCircle u hu y) =
      smoothingCircle u hu (normalizedToricBoundaryHomeomorph hr y) := by
  change normalizedBoundaryHomeomorph hr
      (toricBoundaryHomeomorph (ne_of_gt hr) (toricBoundaryCircle u hu y)) =
    smoothingCircle u hu
      (normalizedBoundaryHomeomorph hr (toricBoundaryHomeomorph (ne_of_gt hr) y))
  rw [toricBoundaryHomeomorph_circle, normalizedBoundaryHomeomorph_circle]

/-- The exact normalized formula in either unchanged toric affine chart. -/
theorem normalizedToricBoundaryHomeomorph_toricBoundaryInclusion {r : ℝ} (hr : 0 < r)
    (b : Bool) (z : CoordinateSpace 3) (hz : radiusSq (chartCoordinates b z).2 = r ^ 2) :
    (normalizedToricBoundaryHomeomorph hr (toricBoundaryInclusion b z hz)).val =
      forward 2 (rescaleMatrix r 2 (chartMatrix b (z 1) (z 0, z 2))) := by
  rw [normalizedToricBoundaryHomeomorph_apply_val, toricBoundaryInclusion_val,
    toricMap_toricInclusion]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold
