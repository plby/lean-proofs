import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedCurveNormal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedLocus

/-!
# The two genuine normal weights at every point of the fixed sphere

The action below is induced by the native derivative on the literal
quotient by the tangent range of the actual named curve. Genuine affine
curve charts and the original cusp coordinate covering prove its
characters to be `u⁻¹` and `u` at every point, including both triple points.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCurve

open ToricCharts

local notation "Model" => ℂ × ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local instance : ChartedSpace ℂ (Curve 1) := chartedSpace 1
local instance : IsManifold I₁ ω (Curve 1) := isManifold 1

/-- The native global action derivative at the actual curve point,
written on the unchanged tangent model. -/
def actionDerivative (u : ℂˣ) (x : Curve 1) : Model →L[ℂ] Model :=
  mfderiv IF IF (actionBiholomorph u) (x : Threefold.Space)

theorem actionBiholomorph_inclusion (u : ℂˣ) (x : Curve 1) :
    actionBiholomorph u (x : Threefold.Space) = (x : Threefold.Space) := by
  let := action
  exact (action_fixed_iff x).mpr x.property u

/-- Differentiating the actual fixed-curve inclusion square fixes its
native tangent line pointwise. -/
theorem actionDerivative_inclusionDerivative (u : ℂˣ) (x : Curve 1) (v : ℂ) :
    actionDerivative u x (inclusionDerivative x v) = inclusionDerivative x v := by
  have hfun : actionBiholomorph u ∘ (Subtype.val : Curve 1 → Threefold.Space) =
      (Subtype.val : Curve 1 → Threefold.Space) := funext (actionBiholomorph_inclusion u)
  have hi := (inclusion_holomorphic 1).mdifferentiableAt (by simp) (x := x)
  have ha := (actionBiholomorph u).contMDiff.mdifferentiableAt (by simp)
    (x := (x : Threefold.Space))
  have hc : (show ℂ →L[ℂ] Model from
      mfderiv I₁ IF (actionBiholomorph u ∘ (Subtype.val : Curve 1 → Threefold.Space)) x) =
      (actionDerivative u x).comp (inclusionDerivative x) := mfderiv_comp x ha hi
  have hd : (show ℂ →L[ℂ] Model from
      mfderiv I₁ IF (actionBiholomorph u ∘ (Subtype.val : Curve 1 → Threefold.Space)) x) =
      inclusionDerivative x :=
    congrArg (fun f : Curve 1 → Threefold.Space =>
      (show ℂ →L[ℂ] Model from mfderiv I₁ IF f x)) hfun
  have h := hc.symm.trans hd
  exact congrArg (fun L : ℂ →L[ℂ] Model => L v) h

theorem actionDerivative_preserves_tangent (u : ℂˣ) (x : Curve 1) :
    tangentRange x ≤ (tangentRange x).comap (actionDerivative u x).toLinearMap := by
  rintro w ⟨v, rfl⟩
  exact ⟨v, (actionDerivative_inclusionDerivative u x v).symm⟩

/-- The induced genuine action on the normal tangent quotient of the
actual curve inclusion. It is constructed from the original derivative. -/
def normalAction (u : ℂˣ) (x : Curve 1) : NormalFibre x →ₗ[ℂ] NormalFibre x :=
  (tangentRange x).mapQ (tangentRange x) (actionDerivative u x).toLinearMap
    (actionDerivative_preserves_tangent u x)

@[simp] theorem normalAction_mk (u : ℂˣ) (x : Curve 1) (w : Model) :
    normalAction u x (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (actionDerivative u x w) := rfl

theorem normalAction_continuous (u : ℂˣ) (x : Curve 1) : Continuous (normalAction u x) :=
  (tangentRange x).isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr
    (continuous_quot_mk.comp (actionDerivative u x).continuous)

/-- The actual native normal transport intertwines the two derivative
quotients, not just two abstract representations. -/
theorem axisNormalTransport_intertwines (u : ℂˣ) (b : Bool) (z : ℂ)
    (v : NormalFibre (affineMap b z)) :
    axisNormalTransport b z (normalAction u (affineMap b z) v) =
      FixedCoordinates.normalDerivative u (axisTriangle b) z (axisNormalTransport b z v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ w =>
      have hb : actionDerivative u (affineMap b z) =
          (show Model →L[ℂ] Model from mfderiv IF IF (actionBiholomorph u)
            (FixedCoordinates.globalAxis (axisTriangle b) z)) :=
        congrArg (fun y : Threefold.Space =>
          (show Model →L[ℂ] Model from mfderiv IF IF (actionBiholomorph u) y))
          (affineMap_val b z)
      change (Submodule.Quotient.mk (actionDerivative u (affineMap b z) w) :
        FixedCoordinates.AxisNormal (axisTriangle b) z) =
          Submodule.Quotient.mk
            ((show Model →L[ℂ] Model from mfderiv IF IF (actionBiholomorph u)
              (FixedCoordinates.globalAxis (axisTriangle b) z)) w)
      exact congrArg (fun L : Model →L[ℂ] Model =>
        (Submodule.Quotient.mk (L w) : FixedCoordinates.AxisNormal (axisTriangle b) z)) hb

/-- On either actual affine chart of the fixed sphere, the native
normal action has characters `u⁻¹` and `u`, i.e. weights `-1` and `+1`. -/
theorem normal_weights_affine (u : ℂˣ) (b : Bool) (z : ℂ)
    (v : NormalFibre (affineMap b z)) :
    normalEquiv b z (normalAction u (affineMap b z) v) =
      ![(u : ℂ)⁻¹ * (normalEquiv b z v) 0, (u : ℂ) * (normalEquiv b z v) 1] := by
  change FixedCoordinates.axisNormalEquiv (axisTriangle b) z
    (axisNormalTransport b z (normalAction u (affineMap b z) v)) = _
  rw [axisNormalTransport_intertwines]
  exact FixedCoordinates.normal_weights u (axisTriangle b) z (axisNormalTransport b z v)

/-- Every point of the actual named fixed curve admits genuine complex
normal coordinates with weights `(-1,+1)`, through its native tangent quotient. -/
theorem exists_normal_weights (x : Curve 1) :
    ∃ e : NormalFibre x ≃L[ℂ] CoordinateSpace 2,
      ∀ u : ℂˣ, ∀ v : NormalFibre x,
        e (normalAction u x v) = ![(u : ℂ)⁻¹ * (e v) 0, (u : ℂ) * (e v) 1] := by
  obtain ⟨b, z, rfl⟩ := affineMap_jointly_surjective x
  exact ⟨normalEquiv b z, fun u v => normal_weights_affine u b z v⟩

@[simp] theorem normalAction_one_apply (x : Curve 1) (v : NormalFibre x) :
    normalAction 1 x v = v := by
  obtain ⟨e, he⟩ := exists_normal_weights x
  apply e.injective
  rw [he]
  ext j
  fin_cases j <;> simp

theorem normalAction_mul_apply (u v : ℂˣ) (x : Curve 1) (w : NormalFibre x) :
    normalAction (u * v) x w = normalAction u x (normalAction v x w) := by
  obtain ⟨e, he⟩ := exists_normal_weights x
  apply e.injective
  simp only [he, Units.val_mul]
  ext j
  fin_cases j <;> simp [mul_assoc, mul_comm]

/-- The actual derivative quotient maps form the genuine normal
representation, with no independently imposed action. -/
def normalRepresentation (x : Curve 1) : ℂˣ →* Module.End ℂ (NormalFibre x) where
  toFun u := normalAction u x
  map_one' := by
    apply LinearMap.ext
    intro v
    exact normalAction_one_apply x v
  map_mul' u v := by
    apply LinearMap.ext
    intro w
    exact normalAction_mul_apply u v x w

@[simp] theorem normalRepresentation_apply (x : Curve 1) (u : ℂˣ) (v : NormalFibre x) :
    normalRepresentation x u v = normalAction u x v := rfl

/-- In particular, the actual normal representation has no nonzero
vector fixed by a nonidentity scalar. -/
theorem normalAction_fixed_iff (u : ℂˣ) (hu : u ≠ 1) (x : Curve 1)
    (v : NormalFibre x) : normalAction u x v = v ↔ v = 0 := by
  obtain ⟨e, he⟩ := exists_normal_weights x
  have hune : (u : ℂ) ≠ 1 := fun h => hu (Units.ext h)
  have hinv : (u : ℂ)⁻¹ ≠ 1 := fun h => hune (inv_eq_one.mp h)
  constructor
  · intro h
    have hcoord := (he u v).symm.trans (congrArg e h)
    have h0 : ((u : ℂ)⁻¹ - 1) * e v 0 = 0 := by
      have hh := congrFun hcoord 0
      change (u : ℂ)⁻¹ * e v 0 = e v 0 at hh
      linear_combination hh
    have h1 : ((u : ℂ) - 1) * e v 1 = 0 := by
      have hh := congrFun hcoord 1
      change (u : ℂ) * e v 1 = e v 1 at hh
      linear_combination hh
    have hz : e v = 0 := by
      ext j
      fin_cases j
      · exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hinv)
      · exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hune)
    exact e.injective (hz.trans (map_zero e).symm)
  · rintro rfl
    exact map_zero _

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCurve
