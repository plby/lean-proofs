import Wikipedia.HopfProblem.SpecialPeriodsThreefoldAutomorphisms
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixed

/-!
# The genuine automorphism identity component at its fixed curve

The native subgroup evaluation action of the full automorphism identity
component fixes exactly the original curve `D₀`. Its normal action below
is constructed from the actual automorphism derivative on the original
tangent quotient of that curve. The proved identity-component group
isomorphism identifies this derivative quotient with the existing normal
representation, and therefore gives its two characters `u⁻¹` and `u`.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Aut0

open Automorphisms VerticalAction.FixedCurve ToricCharts

local notation "Model" => ℂ × ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_compact Threefold.space_t2Space

/-- The inverse group parameter describes the actual native
automorphism pointwise, not just an abstract group element. -/
theorem apply_eq_parameter (f : Aut₀) (x : Threefold.Space) :
    (f : Aut) x =
      VerticalAction.actionBiholomorph (identityComponentMulEquiv.symm f) x := by
  exact (congrArg (fun g : Aut₀ => (g : Aut) x)
    (identityComponentMulEquiv.apply_symm_apply f)).symm

theorem coe_eq_parameter (f : Aut₀) :
    (fun x : Threefold.Space => (f : Aut) x) =
      (VerticalAction.actionBiholomorph (identityComponentMulEquiv.symm f) :
        Threefold.Space → Threefold.Space) :=
  funext (apply_eq_parameter f)

/-- The action here is the existing subgroup action inherited from
the full native automorphism group. -/
theorem fixed_iff (x : Threefold.Space) :
    (∀ f : Aut₀, f • x = x) ↔ x ∈ VerticalAction.D₀ := by
  let := VerticalAction.action
  constructor
  · intro h
    apply (VerticalAction.action_fixed_iff x).mp
    intro u
    exact h (identityComponentMulEquiv u)
  · intro h f
    change (f : Aut) x = x
    rw [apply_eq_parameter]
    exact (VerticalAction.action_fixed_iff x).mpr h _

/-- The literal native fixed-point set of the genuine identity
component is the original named cusp double curve. -/
theorem fixedPoints_eq_D₀ :
    MulAction.fixedPoints Aut₀ Threefold.Space = VerticalAction.D₀ := by
  ext x
  exact fixed_iff x

/-- Every actual identity-component automorphism fixes the original
curve inclusion pointwise. -/
theorem apply_inclusion (f : Aut₀) (x : Curve 1) :
    (f : Aut) (x : Threefold.Space) = (x : Threefold.Space) :=
  (fixed_iff x).mpr x.property f

/-- The actual native derivative of an identity-component
automorphism at the original fixed-curve point. -/
def actionDerivativeAut0 (f : Aut₀) (x : Curve 1) : Model →L[ℂ] Model :=
  mfderiv IF IF (fun y : Threefold.Space => (f : Aut) y) (x : Threefold.Space)

/-- Pointwise identification of the original maps also identifies
their genuine native derivatives. -/
theorem actionDerivativeAut0_eq (f : Aut₀) (x : Curve 1) :
    actionDerivativeAut0 f x =
      actionDerivative (identityComponentMulEquiv.symm f) x :=
  congrArg (fun g : Threefold.Space → Threefold.Space =>
    (show Model →L[ℂ] Model from mfderiv IF IF g (x : Threefold.Space)))
    (coe_eq_parameter f)

theorem actionDerivativeAut0_preserves_tangent (f : Aut₀) (x : Curve 1) :
    tangentRange x ≤ (tangentRange x).comap (actionDerivativeAut0 f x).toLinearMap := by
  rw [actionDerivativeAut0_eq]
  exact actionDerivative_preserves_tangent _ x

/-- The normal action of the genuine identity component, defined by
the actual automorphism derivative on the unchanged tangent quotient. -/
def normalActionAut0 (f : Aut₀) (x : Curve 1) : NormalFibre x →ₗ[ℂ] NormalFibre x :=
  (tangentRange x).mapQ (tangentRange x) (actionDerivativeAut0 f x).toLinearMap
    (actionDerivativeAut0_preserves_tangent f x)

/-- The construction is literally `mapQ` of the actual native
automorphism derivative, with the original curve tangent range. -/
theorem normalActionAut0_eq_mapQ (f : Aut₀) (x : Curve 1) :
    normalActionAut0 f x =
      (tangentRange x).mapQ (tangentRange x)
        (mfderiv IF IF (fun y : Threefold.Space => (f : Aut) y)
          (x : Threefold.Space)).toLinearMap
        (actionDerivativeAut0_preserves_tangent f x) := rfl

@[simp] theorem normalActionAut0_mk (f : Aut₀) (x : Curve 1) (w : Model) :
    normalActionAut0 f x (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk
        (mfderiv IF IF (fun y : Threefold.Space => (f : Aut) y) (x : Threefold.Space) w) := rfl

/-- The existing parameterized normal representation equals the
actual derivative quotient for every native identity-component element. -/
theorem normalActionAut0_eq_normalAction (f : Aut₀) (x : Curve 1) :
    normalActionAut0 f x = normalAction (identityComponentMulEquiv.symm f) x := by
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ w =>
      change Submodule.Quotient.mk (actionDerivativeAut0 f x w) =
        (Submodule.Quotient.mk (actionDerivative (identityComponentMulEquiv.symm f) x w) :
          NormalFibre x)
      rw [actionDerivativeAut0_eq]

theorem normalActionAut0_continuous (f : Aut₀) (x : Curve 1) :
    Continuous (normalActionAut0 f x) := by
  rw [normalActionAut0_eq_normalAction]
  exact normalAction_continuous _ x

/-- The proved normal representation precomposed with the inverse of
the actual identity-component group isomorphism. -/
def normalRepresentationAut0 (x : Curve 1) : Aut₀ →* Module.End ℂ (NormalFibre x) :=
  (normalRepresentation x).comp identityComponentMulEquiv.symm.toMulEquiv.toMonoidHom

@[simp] theorem normalRepresentationAut0_apply (x : Curve 1) (f : Aut₀)
    (v : NormalFibre x) :
    normalRepresentationAut0 x f v = normalActionAut0 f x v := by
  change normalAction (identityComponentMulEquiv.symm f) x v = normalActionAut0 f x v
  rw [normalActionAut0_eq_normalAction]

/-- On actual normal quotient classes the transferred representation
is the quotient of the native derivative, without any replaced atlas. -/
@[simp] theorem normalRepresentationAut0_mk (x : Curve 1) (f : Aut₀) (w : Model) :
    normalRepresentationAut0 x f (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk
        (mfderiv IF IF (fun y : Threefold.Space => (f : Aut) y) (x : Threefold.Space) w) := by
  rw [normalRepresentationAut0_apply, normalActionAut0_mk]

/-- At every point of the original fixed curve, one genuine complex
normal coordinate system diagonalizes every identity-component element
with the two characters `u⁻¹` and `u`. -/
theorem exists_normal_weights (x : Curve 1) :
    ∃ e : NormalFibre x ≃L[ℂ] CoordinateSpace 2,
      ∀ f : Aut₀, ∀ v : NormalFibre x,
        e (normalActionAut0 f x v) =
          ![((identityComponentMulEquiv.symm f : ℂˣ) : ℂ)⁻¹ * (e v) 0,
            ((identityComponentMulEquiv.symm f : ℂˣ) : ℂ) * (e v) 1] := by
  obtain ⟨e, he⟩ := VerticalAction.FixedCurve.exists_normal_weights x
  refine ⟨e, ?_⟩
  intro f v
  rw [normalActionAut0_eq_normalAction]
  exact he _ v

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Aut0
