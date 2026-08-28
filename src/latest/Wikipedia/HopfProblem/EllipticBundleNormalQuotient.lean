import Wikipedia.HopfProblem.EllipticBundleNormalAction
import Wikipedia.HopfProblem.EllipticBundleNormalCoveringDerivative

/-!
# Normal tangent quotients and the actual covering differential

The fibres in this file are literal quotients of the ambient tangent model
by the range of the actual central inclusion differential.  The derivative
of the unramified filling covering transports the prequotient tangent image
onto the quotient-surface tangent image.  It therefore induces an actual
linear equivalence of these normal quotient spaces.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic

local notation "IS" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

theorem fillingQuotient_isQuotientCoveringMap (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    letI := familyAction j v hv.1
    IsQuotientCoveringMap (fillingQuotient j v hv) (CyclicGroup j) := by
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  exact FiniteQuotient.project_isQuotientCoveringMap (CyclicGroup j) (Family j)

/-- The actual differential of the unramified filling covering. -/
def fillingDerivativeEquiv (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (a : Family j) : FamilyModel ≃L[ℂ] FamilyModel := by
  letI := (familyPeriods j).totalChartedSpace
  letI := (familyPeriods j).totalSpace_isManifold
  letI := familyAction j v hv.1
  exact CoveringQuotient.coveringDerivativeEquiv
    (fillingQuotient_isQuotientCoveringMap j v hv) (familyAction_holomorphic j v hv.1) a

@[simp] theorem fillingDerivativeEquiv_toContinuousLinearMap (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a : Family j) :
    letI := (familyPeriods j).totalChartedSpace
    (fillingDerivativeEquiv j v hv a).toContinuousLinearMap =
      mfderiv IF IF (fillingQuotient j v hv) a := by
  let := (familyPeriods j).totalChartedSpace
  let := (familyPeriods j).totalSpace_isManifold
  let := familyAction j v hv.1
  exact CoveringQuotient.coveringDerivativeEquiv_toContinuousLinearMap
    (fillingQuotient_isQuotientCoveringMap j v hv) (familyAction_holomorphic j v hv.1) a

@[simp] theorem fillingDerivativeEquiv_apply (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a : Family j) (w : FamilyModel) :
    letI := (familyPeriods j).totalChartedSpace
    fillingDerivativeEquiv j v hv a w = mfderiv IF IF (fillingQuotient j v hv) a w := by
  let := (familyPeriods j).totalChartedSpace
  exact congrArg (fun L : FamilyModel →L[ℂ] FamilyModel => L w)
    (fillingDerivativeEquiv_toContinuousLinearMap j v hv a)

theorem surfaceProjection_mfderiv_surjective (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a : (centralPeriod j).val.Torus) :
    Function.Surjective (mfderiv IS IS (surfaceProjection j (centralPeriod j) v hv) a) := by
  let := affineAction j (centralPeriod j) v hv.1
  exact (CoveringQuotient.covering_mfderiv_bijective
    (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv)
    (affineAction_holomorphic j (centralPeriod j) v hv.1) a).2

/-- Differentiate the actual commuting square of the two central inclusions
and their covering projections. -/
theorem centralDerivative_square (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (a : (centralPeriod j).val.Torus) :
    letI := (familyPeriods j).totalChartedSpace
    ∀ w : ComplexPlane₂,
      fillingDerivativeEquiv j v hv (centralInclusion j a)
          (mfderiv IS IF (centralInclusion j) a w) =
        mfderiv IS IF (centralFibreInclusion j v hv)
          (surfaceProjection j (centralPeriod j) v hv a)
          (mfderiv IS IS (surfaceProjection j (centralPeriod j) v hv) a w) := by
  let := (familyPeriods j).totalChartedSpace
  have he : fillingQuotient j v hv ∘ centralInclusion j =
      centralFibreInclusion j v hv ∘ surfaceProjection j (centralPeriod j) v hv := by
    funext x
    exact (centralFibreInclusion_surfaceProjection j v hv x).symm
  have hgerm : (fillingQuotient j v hv ∘ centralInclusion j) =ᶠ[𝓝 a]
      (centralFibreInclusion j v hv ∘ surfaceProjection j (centralPeriod j) v hv) :=
    Filter.Eventually.of_forall (congrFun he)
  have hd := hgerm.mfderiv_eq (I := IS) (I' := IF)
  rw [mfderiv_comp a
    ((fillingQuotient_holomorphic j v hv).mdifferentiableAt (by simp))
    ((centralInclusion_holomorphic j).mdifferentiableAt (by simp)),
    mfderiv_comp a
      ((centralFibreInclusion_holomorphic j v hv).mdifferentiableAt (by simp))
      ((surfaceProjection_holomorphic j (centralPeriod j) v hv).mdifferentiableAt
        (by simp))] at hd
  intro w
  exact (fillingDerivativeEquiv_apply j v hv (centralInclusion j a)
    (mfderiv IS IF (centralInclusion j) a w)).trans
      (congrArg (fun L : ComplexPlane₂ →L[ℂ] FamilyModel => L w) hd)

/-- The covering differential transports the actual tangent image onto the
actual tangent image downstairs; surjectivity on the source tangent space
is provided by its independent covering derivative. -/
theorem fillingDerivativeEquiv_map_tangentRange (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a : (centralPeriod j).val.Torus) :
    letI := (familyPeriods j).totalChartedSpace
    (mfderiv IS IF (centralInclusion j) a).range.map
      (fillingDerivativeEquiv j v hv (centralInclusion j a)).toLinearEquiv.toLinearMap =
        (mfderiv IS IF (centralFibreInclusion j v hv)
          (surfaceProjection j (centralPeriod j) v hv a)).range := by
  let := (familyPeriods j).totalChartedSpace
  apply le_antisymm
  · rintro w ⟨z, ⟨u, rfl⟩, rfl⟩
    exact ⟨mfderiv IS IS (surfaceProjection j (centralPeriod j) v hv) a u,
      (centralDerivative_square j v hv a u).symm⟩
  · rintro w ⟨u, rfl⟩
    obtain ⟨z, hz⟩ := surfaceProjection_mfderiv_surjective j v hv a u
    refine ⟨mfderiv IS IF (centralInclusion j) a z, ⟨z, rfl⟩, ?_⟩
    exact (centralDerivative_square j v hv a z).trans (congrArg
      (mfderiv IS IF (centralFibreInclusion j v hv)
        (surfaceProjection j (centralPeriod j) v hv a)) hz)

/-- The normal fibre of the prequotient central torus, defined by the actual
inclusion differential. -/
abbrev FamilyNormalFibre (j : Kind) (a : (centralPeriod j).val.Torus) :=
  letI := (familyPeriods j).totalChartedSpace
  FamilyModel ⧸ (mfderiv IS IF (centralInclusion j) a).range

/-- The normal fibre of the embedded central surface, defined by its actual
inclusion differential in the inherited filling atlas. -/
abbrev CentralNormalFibre (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (x : Surface j (centralPeriod j) v hv) :=
  FamilyModel ⧸ (mfderiv IS IF (centralFibreInclusion j v hv) x).range

/-- First-coordinate identification, justified by the proved derivative range. -/
def familyNormalFibreEquiv (j : Kind) (a : (centralPeriod j).val.Torus) :
    FamilyNormalFibre j a ≃ₗ[ℂ] ℂ := by
  letI := (familyPeriods j).totalChartedSpace
  let S : Submodule ℂ FamilyModel := (mfderiv IS IF (centralInclusion j) a).range
  exact (Submodule.quotEquivOfEq S (NormalLinear.vertical ComplexPlane₂)
    (centralInclusion_mfderiv_range j a)).trans
    (NormalLinear.normalEquiv ComplexPlane₂).toLinearEquiv

@[simp] theorem familyNormalFibreEquiv_mk (j : Kind)
    (a : (centralPeriod j).val.Torus) (w : FamilyModel) :
    familyNormalFibreEquiv j a (Submodule.Quotient.mk w) = w.1 := rfl

def centralNormalFibreEquiv (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (x : Surface j (centralPeriod j) v hv) : CentralNormalFibre j v hv x ≃ₗ[ℂ] ℂ := by
  let S : Submodule ℂ FamilyModel := (mfderiv IS IF (centralFibreInclusion j v hv) x).range
  exact (Submodule.quotEquivOfEq S (NormalLinear.vertical ComplexPlane₂)
      (centralFibreInclusion_mfderiv_range j v hv x)).trans
    (NormalLinear.normalEquiv ComplexPlane₂).toLinearEquiv

@[simp] theorem centralNormalFibreEquiv_mk (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j (centralPeriod j) v hv) (w : FamilyModel) :
    centralNormalFibreEquiv j v hv x (Submodule.Quotient.mk w) = w.1 := rfl

/-- The linear normal-fibre equivalence induced by the actual ambient
covering derivative, rather than by a chosen scalar multiplier. -/
def normalCoveringEquiv (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (a : (centralPeriod j).val.Torus) :
    FamilyNormalFibre j a ≃ₗ[ℂ]
      CentralNormalFibre j v hv (surfaceProjection j (centralPeriod j) v hv a) := by
  letI := (familyPeriods j).totalChartedSpace
  exact Submodule.Quotient.equiv _ _
    (fillingDerivativeEquiv j v hv (centralInclusion j a)).toLinearEquiv
    (fillingDerivativeEquiv_map_tangentRange j v hv a)

@[simp] theorem normalCoveringEquiv_mk (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a : (centralPeriod j).val.Torus) (w : FamilyModel) :
    normalCoveringEquiv j v hv a (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (fillingDerivativeEquiv j v hv (centralInclusion j a) w) := rfl

@[simp] theorem normalCoveringEquiv_symm_mk (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a : (centralPeriod j).val.Torus) (w : FamilyModel) :
    (normalCoveringEquiv j v hv a).symm (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ((fillingDerivativeEquiv j v hv (centralInclusion j a)).symm w) := rfl

/-- A specified covering lift gives a linear scalar coordinate on the
actual normal quotient of the embedded central surface. -/
def normalCoordinateAtLift (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (a : (centralPeriod j).val.Torus) (x : Surface j (centralPeriod j) v hv)
    (ha : surfaceProjection j (centralPeriod j) v hv a = x) :
    CentralNormalFibre j v hv x ≃ₗ[ℂ] ℂ := by
  subst x
  exact (normalCoveringEquiv j v hv a).symm.trans (familyNormalFibreEquiv j a)

@[simp] theorem normalCoordinateAtLift_mk (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a : (centralPeriod j).val.Torus)
    (x : Surface j (centralPeriod j) v hv)
    (ha : surfaceProjection j (centralPeriod j) v hv a = x) (w : FamilyModel) :
    normalCoordinateAtLift j v hv a x ha (Submodule.Quotient.mk w) =
      ((fillingDerivativeEquiv j v hv (centralInclusion j a)).symm w).1 := by
  subst x
  rfl

end Wikipedia.HopfProblem.Elliptic
