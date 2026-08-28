import Wikipedia.HopfProblem.EllipticEquivariantCentralNormalCoordinates
import Wikipedia.HopfProblem.EllipticBundleCharacters
import Wikipedia.HopfProblem.EllipticBundleNormalCoveringDerivative

/-!
# Genuine normal tangent quotients for arbitrary equivariant periods

Both normal fibres are literal quotients by the range of the actual
central inclusion differential. The derivative of the supplied family's
unramified covering transports these tangent ranges and induces the
normal-fibre equivalence. Every differential uses the native varying-period
atlas and its genuine covering quotient atlas.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

variable {j : Kind} (D : Equivariant.Data j)

local notation "IS" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

/-- The actual derivative of the supplied family's unramified covering. -/
def fillingDerivativeEquiv (v : Lattice) (hv : AdmissibleTwist j v)
    (a : D.TotalSpace) : FamilyModel ≃L[ℂ] FamilyModel := by
  letI := D.periods.totalChartedSpace
  letI := D.periods.totalSpace_isManifold
  letI := D.action v hv.1
  exact CoveringQuotient.coveringDerivativeEquiv
    (D.quotientCoveringMap v hv) (D.action_holomorphic v hv.1) a

@[simp] theorem fillingDerivativeEquiv_toContinuousLinearMap (v : Lattice)
    (hv : AdmissibleTwist j v) (a : D.TotalSpace) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace v hv
    (D.fillingDerivativeEquiv v hv a).toContinuousLinearMap =
      mfderiv IF IF (D.quotient v hv) a := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.chartedSpace v hv
  let := D.action v hv.1
  exact CoveringQuotient.coveringDerivativeEquiv_toContinuousLinearMap
    (D.quotientCoveringMap v hv) (D.action_holomorphic v hv.1) a

@[simp] theorem fillingDerivativeEquiv_apply (v : Lattice)
    (hv : AdmissibleTwist j v) (a : D.TotalSpace) (w : FamilyModel) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace v hv
    D.fillingDerivativeEquiv v hv a w = mfderiv IF IF (D.quotient v hv) a w := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace v hv
  exact congrArg (fun L : FamilyModel →L[ℂ] FamilyModel => L w)
    (D.fillingDerivativeEquiv_toContinuousLinearMap v hv a)

theorem surfaceProjection_mfderiv_surjective (v : Lattice)
    (hv : AdmissibleTwist j v) (a : D.centralPeriod.val.Torus) :
    Function.Surjective (mfderiv IS IS (surfaceProjection j D.centralPeriod v hv) a) := by
  let := affineAction j D.centralPeriod v hv.1
  exact (CoveringQuotient.covering_mfderiv_bijective
    (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv)
    (affineAction_holomorphic j D.centralPeriod v hv.1) a).2

/-- Differentiate the actual commuting square of the central inclusions
and their covering projections, in their original complex atlases. -/
theorem centralDerivative_square (v : Lattice) (hv : AdmissibleTwist j v)
    (a : D.centralPeriod.val.Torus) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace v hv
    ∀ w : ComplexPlane₂,
      D.fillingDerivativeEquiv v hv (D.centralInclusion a)
          (mfderiv IS IF D.centralInclusion a w) =
        mfderiv IS IF (D.centralFibreInclusion v hv)
          (surfaceProjection j D.centralPeriod v hv a)
          (mfderiv IS IS (surfaceProjection j D.centralPeriod v hv) a w) := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace v hv
  have he : D.quotient v hv ∘ D.centralInclusion =
      D.centralFibreInclusion v hv ∘ surfaceProjection j D.centralPeriod v hv := by
    funext x
    exact (D.centralFibreInclusion_surfaceProjection v hv x).symm
  have hgerm : (D.quotient v hv ∘ D.centralInclusion) =ᶠ[𝓝 a]
      (D.centralFibreInclusion v hv ∘ surfaceProjection j D.centralPeriod v hv) :=
    Filter.Eventually.of_forall (congrFun he)
  have hd := hgerm.mfderiv_eq (I := IS) (I' := IF)
  rw [mfderiv_comp a
    ((D.quotient_holomorphic v hv).mdifferentiableAt (by simp))
    (D.centralInclusion_holomorphic.mdifferentiableAt (by simp)),
    mfderiv_comp a
      ((D.centralFibreInclusion_holomorphic v hv).mdifferentiableAt (by simp))
      ((surfaceProjection_holomorphic j D.centralPeriod v hv).mdifferentiableAt
        (by simp))] at hd
  intro w
  exact (D.fillingDerivativeEquiv_apply v hv (D.centralInclusion a)
    (mfderiv IS IF D.centralInclusion a w)).trans
      (congrArg (fun L : ComplexPlane₂ →L[ℂ] FamilyModel => L w) hd)

/-- The actual ambient covering differential takes the prequotient
central tangent image onto the central surface tangent image. -/
theorem fillingDerivativeEquiv_map_tangentRange (v : Lattice)
    (hv : AdmissibleTwist j v) (a : D.centralPeriod.val.Torus) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace v hv
    (mfderiv IS IF D.centralInclusion a).range.map
      (D.fillingDerivativeEquiv v hv (D.centralInclusion a)).toLinearEquiv.toLinearMap =
        (mfderiv IS IF (D.centralFibreInclusion v hv)
          (surfaceProjection j D.centralPeriod v hv a)).range := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace v hv
  apply le_antisymm
  · rintro w ⟨z, ⟨u, rfl⟩, rfl⟩
    exact ⟨mfderiv IS IS (surfaceProjection j D.centralPeriod v hv) a u,
      (D.centralDerivative_square v hv a u).symm⟩
  · rintro w ⟨u, rfl⟩
    obtain ⟨z, hz⟩ := D.surfaceProjection_mfderiv_surjective v hv a u
    refine ⟨mfderiv IS IF D.centralInclusion a z, ⟨z, rfl⟩, ?_⟩
    exact (D.centralDerivative_square v hv a z).trans (congrArg
      (mfderiv IS IF (D.centralFibreInclusion v hv)
        (surfaceProjection j D.centralPeriod v hv a)) hz)

/-- The genuine normal quotient of the actual central torus before the
finite quotient, using the supplied varying-period atlas. -/
abbrev FamilyNormalFibre (a : D.centralPeriod.val.Torus) :=
  letI := D.periods.totalChartedSpace
  FamilyModel ⧸ (mfderiv IS IF D.centralInclusion a).range

/-- The genuine normal quotient of the central surface in the native
complex atlas of the supplied equivariant filling. -/
abbrev CentralNormalFibre (v : Lattice) (hv : AdmissibleTwist j v)
    (x : Surface j D.centralPeriod v hv) :=
  letI := D.chartedSpace v hv
  FamilyModel ⧸ (mfderiv IS IF (D.centralFibreInclusion v hv) x).range

/-- First-coordinate identification of the actual prequotient normal
space, using the proved range of its inclusion differential. -/
def familyNormalFibreEquiv (a : D.centralPeriod.val.Torus) :
    D.FamilyNormalFibre a ≃ₗ[ℂ] ℂ := by
  letI := D.periods.totalChartedSpace
  let S : Submodule ℂ FamilyModel := (mfderiv IS IF D.centralInclusion a).range
  exact (Submodule.quotEquivOfEq S (NormalLinear.vertical ComplexPlane₂)
    (D.centralInclusion_mfderiv_range a)).trans
    (NormalLinear.normalEquiv ComplexPlane₂).toLinearEquiv

@[simp] theorem familyNormalFibreEquiv_mk
    (a : D.centralPeriod.val.Torus) (w : FamilyModel) :
    D.familyNormalFibreEquiv a (Submodule.Quotient.mk w) = w.1 := rfl

def centralNormalFibreEquiv (v : Lattice) (hv : AdmissibleTwist j v)
    (x : Surface j D.centralPeriod v hv) : D.CentralNormalFibre v hv x ≃ₗ[ℂ] ℂ := by
  letI := D.chartedSpace v hv
  let S : Submodule ℂ FamilyModel := (mfderiv IS IF (D.centralFibreInclusion v hv) x).range
  exact (Submodule.quotEquivOfEq S (NormalLinear.vertical ComplexPlane₂)
      (D.centralFibreInclusion_mfderiv_range v hv x)).trans
    (NormalLinear.normalEquiv ComplexPlane₂).toLinearEquiv

@[simp] theorem centralNormalFibreEquiv_mk (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j D.centralPeriod v hv) (w : FamilyModel) :
    D.centralNormalFibreEquiv v hv x (Submodule.Quotient.mk w) = w.1 := rfl

/-- The actual ambient covering derivative induces this linear equivalence
of the two genuine normal quotient spaces. -/
def normalCoveringEquiv (v : Lattice) (hv : AdmissibleTwist j v)
    (a : D.centralPeriod.val.Torus) :
    D.FamilyNormalFibre a ≃ₗ[ℂ]
      D.CentralNormalFibre v hv (surfaceProjection j D.centralPeriod v hv a) := by
  letI := D.periods.totalChartedSpace
  letI := D.chartedSpace v hv
  exact Submodule.Quotient.equiv _ _
    (D.fillingDerivativeEquiv v hv (D.centralInclusion a)).toLinearEquiv
    (D.fillingDerivativeEquiv_map_tangentRange v hv a)

@[simp] theorem normalCoveringEquiv_mk (v : Lattice)
    (hv : AdmissibleTwist j v) (a : D.centralPeriod.val.Torus) (w : FamilyModel) :
    D.normalCoveringEquiv v hv a (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (D.fillingDerivativeEquiv v hv (D.centralInclusion a) w) := rfl

@[simp] theorem normalCoveringEquiv_symm_mk (v : Lattice)
    (hv : AdmissibleTwist j v) (a : D.centralPeriod.val.Torus) (w : FamilyModel) :
    (D.normalCoveringEquiv v hv a).symm (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ((D.fillingDerivativeEquiv v hv (D.centralInclusion a)).symm w) := rfl

/-- A chosen covering lift supplies a scalar coordinate on the actual
central normal quotient, by the inverse covering differential. -/
def normalCoordinateAtLift (v : Lattice) (hv : AdmissibleTwist j v)
    (a : D.centralPeriod.val.Torus) (x : Surface j D.centralPeriod v hv)
    (ha : surfaceProjection j D.centralPeriod v hv a = x) :
    D.CentralNormalFibre v hv x ≃ₗ[ℂ] ℂ := by
  subst x
  exact (D.normalCoveringEquiv v hv a).symm.trans (D.familyNormalFibreEquiv a)

@[simp] theorem normalCoordinateAtLift_mk (v : Lattice)
    (hv : AdmissibleTwist j v) (a : D.centralPeriod.val.Torus)
    (x : Surface j D.centralPeriod v hv)
    (ha : surfaceProjection j D.centralPeriod v hv a = x) (w : FamilyModel) :
    D.normalCoordinateAtLift v hv a x ha (Submodule.Quotient.mk w) =
      ((D.fillingDerivativeEquiv v hv (D.centralInclusion a)).symm w).1 := by
  subst x
  rfl

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
