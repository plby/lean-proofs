import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedNormalLinear

/-!
# The genuine normal tangent action along the fixed axis charts

The normal space is the literal quotient of the original global tangent
space by the derivative image of the actual cusp curve parametrization.
The action on it is induced by the derivative of the constructed global
multiplicative action. Its two characters are proved to be `u⁻¹` and `u`.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates

open ToricCharts ToricFan

local notation "E₃" => CoordinateSpace 3
local notation "E₂" => CoordinateSpace 2
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The image of the genuine derivative of the original curve parametrization. -/
def axisTangentRange (a : Triangle) (z : ℂ) : Submodule ℂ (ℂ × ComplexPlane₂) :=
  (mfderiv I₁ IF (globalAxis a) z).range

/-- The genuine geometric normal tangent quotient in the existing global atlas. -/
abbrev AxisNormal (a : Triangle) (z : ℂ) := (ℂ × ComplexPlane₂) ⧸ axisTangentRange a z

theorem axisTangentRange_isClosed (a : Triangle) (z : ℂ) :
    IsClosed (axisTangentRange a z : Set (ℂ × ComplexPlane₂)) :=
  (axisTangentRange a z).closed_of_finiteDimensional

instance axisNormal_t2Space (a : Triangle) (z : ℂ) : T2Space (AxisNormal a z) := by
  let : IsClosed (axisTangentRange a z : Set (ℂ × ComplexPlane₂)) :=
    axisTangentRange_isClosed a z
  infer_instance

/-- The actual coordinate-cover derivative transports the coordinate
normal quotient onto the actual geometric normal quotient. -/
def normalTransportLinearEquiv (a : Triangle) (z : ℂ) :
    CoordinateNormal ≃ₗ[ℂ] AxisNormal a z :=
  Submodule.Quotient.equiv _ _ (tangentEquiv a (axis z)).toLinearEquiv
    (tangentEquiv_axis_range a z)

@[simp] theorem normalTransportLinearEquiv_mk (a : Triangle) (z : ℂ) (w : E₃) :
    normalTransportLinearEquiv a z (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (tangentEquiv a (axis z) w) := rfl

@[simp] theorem normalTransportLinearEquiv_symm_mk (a : Triangle) (z : ℂ)
    (w : ℂ × ComplexPlane₂) :
    (normalTransportLinearEquiv a z).symm (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ((tangentEquiv a (axis z)).symm w) := rfl

/-- Both sides retain their natural quotient topologies. -/
def normalTransport (a : Triangle) (z : ℂ) : CoordinateNormal ≃L[ℂ] AxisNormal a z :=
  { normalTransportLinearEquiv a z with
    continuous_toFun := axisLinear.range.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr
      (continuous_quot_mk.comp (tangentEquiv a (axis z)).continuous)
    continuous_invFun :=
      (axisTangentRange a z).isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr
        (continuous_quot_mk.comp (tangentEquiv a (axis z)).symm.continuous) }

/-- Two actual complex normal coordinates, obtained from the original
chart differential and the genuine tangent quotient. -/
def axisNormalEquiv (a : Triangle) (z : ℂ) : AxisNormal a z ≃L[ℂ] E₂ :=
  (normalTransport a z).symm.trans coordinateNormalEquiv

@[simp] theorem axisNormalEquiv_mk (a : Triangle) (z : ℂ) (w : ℂ × ComplexPlane₂) :
    axisNormalEquiv a z (Submodule.Quotient.mk w) =
      normalProjection ((tangentEquiv a (axis z)).symm w) := rfl

/-- The actual tangent derivative fixes the actual curve tangent line
pointwise, as follows from the differentiated action square. -/
theorem action_fixes_axis_tangent (u : ℂˣ) (a : Triangle) (z t : ℂ) :
    mfderiv IF IF (actionBiholomorph u) (globalAxis a z)
      (mfderiv I₁ IF (globalAxis a) z t) = mfderiv I₁ IF (globalAxis a) z t := by
  rw [globalAxis_mfderiv]
  change mfderiv IF IF (actionBiholomorph u) (globalMap a (axis z))
    (tangentEquiv a (axis z) (axisLinear t)) = tangentEquiv a (axis z) (axisLinear t)
  rw [action_derivative_square, axis_fixed, diagonal_axisLinear]

theorem action_preserves_axis_tangent (u : ℂˣ) (a : Triangle) (z : ℂ) :
    axisTangentRange a z ≤ (axisTangentRange a z).comap
      (mfderiv IF IF (actionBiholomorph u) (globalAxis a z)).toLinearMap := by
  rintro w ⟨t, rfl⟩
  exact ⟨t, (action_fixes_axis_tangent u a z t).symm⟩

/-- The action induced by the genuine global derivative on the literal
normal tangent quotient, rather than an independently imposed action. -/
def normalDerivative (u : ℂˣ) (a : Triangle) (z : ℂ) : AxisNormal a z →ₗ[ℂ] AxisNormal a z :=
  (axisTangentRange a z).mapQ (axisTangentRange a z)
    (mfderiv IF IF (actionBiholomorph u) (globalAxis a z)).toLinearMap
    (action_preserves_axis_tangent u a z)

@[simp] theorem normalDerivative_mk (u : ℂˣ) (a : Triangle) (z : ℂ)
    (w : ℂ × ComplexPlane₂) :
    normalDerivative u a z (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk
        (mfderiv IF IF (actionBiholomorph u) (globalAxis a z) w) := rfl

/-- The two genuine normal weights are `-1` and `+1` at every point
of every actual middle-axis chart, including the triple points. -/
theorem normal_weights (u : ℂˣ) (a : Triangle) (z : ℂ) (v : AxisNormal a z) :
    axisNormalEquiv a z (normalDerivative u a z v) =
      ![(u : ℂ)⁻¹ * (axisNormalEquiv a z v) 0,
        (u : ℂ) * (axisNormalEquiv a z v) 1] := by
  induction v using Submodule.Quotient.induction_on with
  | _ w =>
      let E : E₃ ≃L[ℂ] (ℂ × ComplexPlane₂) := tangentEquiv a (axis z)
      obtain ⟨v, rfl⟩ := E.surjective w
      have hs : (show (ℂ × ComplexPlane₂) →L[ℂ] (ℂ × ComplexPlane₂) from
          mfderiv IF IF (actionBiholomorph u) (globalAxis a z)) (E v) =
          E (diagonal u v) := by
        have h := action_derivative_square u a (axis z) v
        rw [axis_fixed] at h
        exact h
      have hnormal : normalDerivative u a z (Submodule.Quotient.mk (E v)) =
          Submodule.Quotient.mk (E (diagonal u v)) :=
        (normalDerivative_mk u a z (E v)).trans
          (congrArg (fun w : ℂ × ComplexPlane₂ =>
            (Submodule.Quotient.mk w : AxisNormal a z)) hs)
      refine (congrArg (axisNormalEquiv a z) hnormal).trans ?_
      change normalProjection (E.symm (E (diagonal u v))) =
        ![(u : ℂ)⁻¹ * (normalProjection (E.symm (E v))) 0,
          (u : ℂ) * (normalProjection (E.symm (E v))) 1]
      rw [E.symm_apply_apply, E.symm_apply_apply]
      exact normalProjection_diagonal u v

theorem axisNormal_finrank (a : Triangle) (z : ℂ) :
    Module.finrank ℂ (AxisNormal a z) = 2 :=
  (axisNormalEquiv a z).toLinearEquiv.finrank_eq.trans (by simp [CoordinateSpace])

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates
