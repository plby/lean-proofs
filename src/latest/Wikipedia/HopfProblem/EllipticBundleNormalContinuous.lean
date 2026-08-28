import Wikipedia.HopfProblem.EllipticBundleNormal
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuous normal-fibre identifications

All normal fibres retain their natural submodule-quotient topology.  The
actual tangent images are closed by the proved vertical-range identities.
Finite-dimensional continuity then upgrades the existing geometric linear
identifications to continuous linear equivalences without changing their maps.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.Elliptic

local notation "IS" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

theorem familyNormalTangentRange_isClosed (j : Kind) (a : (centralPeriod j).val.Torus) :
    letI := (familyPeriods j).totalChartedSpace
    let S : Submodule ℂ FamilyModel := (mfderiv IS IF (centralInclusion j) a).range
    IsClosed (S : Set FamilyModel) := by
  let := (familyPeriods j).totalChartedSpace
  let S : Submodule ℂ FamilyModel := (mfderiv IS IF (centralInclusion j) a).range
  change IsClosed (S : Set FamilyModel)
  have hS : S = NormalLinear.vertical ComplexPlane₂ := centralInclusion_mfderiv_range j a
  rw [hS]
  exact NormalLinear.isClosed_vertical ComplexPlane₂

theorem centralNormalTangentRange_isClosed (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j (centralPeriod j) v hv) :
    let S : Submodule ℂ FamilyModel := (mfderiv IS IF (centralFibreInclusion j v hv) x).range
    IsClosed (S : Set FamilyModel) := by
  let S : Submodule ℂ FamilyModel := (mfderiv IS IF (centralFibreInclusion j v hv) x).range
  change IsClosed (S : Set FamilyModel)
  have hS : S = NormalLinear.vertical ComplexPlane₂ :=
    centralFibreInclusion_mfderiv_range j v hv x
  rw [hS]
  exact NormalLinear.isClosed_vertical ComplexPlane₂

/-- Hausdorffness of the existing quotient topology, not a transported topology. -/
instance familyNormalFibre_t2Space (j : Kind) (a : (centralPeriod j).val.Torus) :
    T2Space (FamilyNormalFibre j a) := by
  let := (familyPeriods j).totalChartedSpace
  let S : Submodule ℂ FamilyModel := (mfderiv IS IF (centralInclusion j) a).range
  let : IsClosed (S : Set FamilyModel) := familyNormalTangentRange_isClosed j a
  exact inferInstanceAs (T2Space (FamilyModel ⧸ S))

/-- Hausdorffness follows from closedness of the actual central tangent image. -/
instance centralNormalFibre_t2Space (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j (centralPeriod j) v hv) :
    T2Space (CentralNormalFibre j v hv x) := by
  let S : Submodule ℂ FamilyModel := (mfderiv IS IF (centralFibreInclusion j v hv) x).range
  let : IsClosed (S : Set FamilyModel) := centralNormalTangentRange_isClosed j v hv x
  exact inferInstanceAs (T2Space (FamilyModel ⧸ S))

instance familyNormalFibre_finiteDimensional (j : Kind) (a : (centralPeriod j).val.Torus) :
    FiniteDimensional ℂ (FamilyNormalFibre j a) :=
  (familyNormalFibreEquiv j a).symm.finiteDimensional

instance centralNormalFibre_finiteDimensional (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j (centralPeriod j) v hv) :
    FiniteDimensional ℂ (CentralNormalFibre j v hv x) :=
  (centralNormalFibreEquiv j v hv x).symm.finiteDimensional

/-- The existing first-coordinate identification, with both maps continuous. -/
def familyNormalFibreContinuousEquiv (j : Kind) (a : (centralPeriod j).val.Torus) :
    FamilyNormalFibre j a ≃L[ℂ] ℂ :=
  (familyNormalFibreEquiv j a).toContinuousLinearEquiv

@[simp] theorem familyNormalFibreContinuousEquiv_toLinearEquiv
    (j : Kind) (a : (centralPeriod j).val.Torus) :
    (familyNormalFibreContinuousEquiv j a).toLinearEquiv = familyNormalFibreEquiv j a := rfl

@[simp] theorem familyNormalFibreContinuousEquiv_mk
    (j : Kind) (a : (centralPeriod j).val.Torus) (w : FamilyModel) :
    familyNormalFibreContinuousEquiv j a (Submodule.Quotient.mk w) = w.1 := rfl

def centralNormalFibreContinuousEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j (centralPeriod j) v hv) :
    CentralNormalFibre j v hv x ≃L[ℂ] ℂ :=
  (centralNormalFibreEquiv j v hv x).toContinuousLinearEquiv

@[simp] theorem centralNormalFibreContinuousEquiv_toLinearEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j (centralPeriod j) v hv) :
    (centralNormalFibreContinuousEquiv j v hv x).toLinearEquiv =
      centralNormalFibreEquiv j v hv x := rfl

@[simp] theorem centralNormalFibreContinuousEquiv_mk (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j (centralPeriod j) v hv) (w : FamilyModel) :
    centralNormalFibreContinuousEquiv j v hv x (Submodule.Quotient.mk w) = w.1 := rfl

/-- The actual covering differential induces a continuous equivalence of
normal quotients, with their natural quotient topologies. -/
def normalCoveringContinuousEquiv (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (a : (centralPeriod j).val.Torus) :
    FamilyNormalFibre j a ≃L[ℂ]
      CentralNormalFibre j v hv (surfaceProjection j (centralPeriod j) v hv a) :=
  (normalCoveringEquiv j v hv a).toContinuousLinearEquiv

@[simp] theorem normalCoveringContinuousEquiv_toLinearEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a : (centralPeriod j).val.Torus) :
    (normalCoveringContinuousEquiv j v hv a).toLinearEquiv =
      normalCoveringEquiv j v hv a := rfl

@[simp] theorem normalCoveringContinuousEquiv_mk (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a : (centralPeriod j).val.Torus) (w : FamilyModel) :
    normalCoveringContinuousEquiv j v hv a (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (fillingDerivativeEquiv j v hv (centralInclusion j a) w) := rfl

def normalCoordinateAtLiftContinuousEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a : (centralPeriod j).val.Torus)
    (x : Surface j (centralPeriod j) v hv)
    (ha : surfaceProjection j (centralPeriod j) v hv a = x) :
    CentralNormalFibre j v hv x ≃L[ℂ] ℂ :=
  (normalCoordinateAtLift j v hv a x ha).toContinuousLinearEquiv

@[simp] theorem normalCoordinateAtLiftContinuousEquiv_toLinearEquiv
    (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (a : (centralPeriod j).val.Torus) (x : Surface j (centralPeriod j) v hv)
    (ha : surfaceProjection j (centralPeriod j) v hv a = x) :
    (normalCoordinateAtLiftContinuousEquiv j v hv a x ha).toLinearEquiv =
      normalCoordinateAtLift j v hv a x ha := rfl

@[simp] theorem normalCoordinateAtLiftContinuousEquiv_mk
    (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (a : (centralPeriod j).val.Torus) (x : Surface j (centralPeriod j) v hv)
    (ha : surfaceProjection j (centralPeriod j) v hv a = x) (w : FamilyModel) :
    normalCoordinateAtLiftContinuousEquiv j v hv a x ha (Submodule.Quotient.mk w) =
      ((fillingDerivativeEquiv j v hv (centralInclusion j a)).symm w).1 :=
  normalCoordinateAtLift_mk j v hv a x ha w

namespace NormalBundle

variable (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)

/-- The geometric local coordinate is continuous in the normal-fibre quotient
topology, with continuous inverse. -/
def localCoordinateContinuous (i x : Surface j (centralPeriod j) v hv)
    (hx : x ∈ baseSet j v hv i) : CentralNormalFibre j v hv x ≃L[ℂ] ℂ :=
  (localCoordinate j v hv i x hx).toContinuousLinearEquiv

@[simp] theorem localCoordinateContinuous_toLinearEquiv
    (i x : Surface j (centralPeriod j) v hv) (hx : x ∈ baseSet j v hv i) :
    (localCoordinateContinuous j v hv i x hx).toLinearEquiv =
      localCoordinate j v hv i x hx := rfl

/-- Bundle fibres and the literal normal tangent quotients are continuously
complex-linearly equivalent in their independently given topologies. -/
def fibreIdentificationContinuous (x : Surface j (centralPeriod j) v hv) :
    (core j v hv).Fiber x ≃L[ℂ] CentralNormalFibre j v hv x := by
  change ℂ ≃L[ℂ] CentralNormalFibre j v hv x
  exact (localCoordinateContinuous j v hv x x (mem_baseSet j v hv x)).symm

@[simp] theorem fibreIdentificationContinuous_toLinearEquiv
    (x : Surface j (centralPeriod j) v hv) :
    (fibreIdentificationContinuous j v hv x).toLinearEquiv =
      fibreIdentification j v hv x := rfl

theorem localCoordinateContinuous_fibreIdentificationContinuous
    (i x : Surface j (centralPeriod j) v hv) (hx : x ∈ baseSet j v hv i)
    (z : (core j v hv).Fiber x) :
    localCoordinateContinuous j v hv i x hx (fibreIdentificationContinuous j v hv x z) =
      ((core j v hv).localTriv i ⟨x, z⟩).2 :=
  localCoordinate_fibreIdentification j v hv i x hx z

end NormalBundle

end Wikipedia.HopfProblem.Elliptic
