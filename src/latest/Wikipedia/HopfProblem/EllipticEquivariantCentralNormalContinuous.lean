import Wikipedia.HopfProblem.EllipticEquivariantCentralNormalBundle
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuous normal-fibre identifications for arbitrary equivariant periods

All normal fibres retain their natural submodule-quotient topology for the
supplied period map and its native finite-quotient atlas.  The
actual tangent images are closed by the proved vertical-range identities.
Finite-dimensional continuity then upgrades the existing geometric linear
identifications to continuous linear equivalences without changing their maps.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

local notation "IS" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

variable {j : Kind} (D : Equivariant.Data j)

theorem familyNormalTangentRange_isClosed (a : D.centralPeriod.val.Torus) :
    letI := D.periods.totalChartedSpace
    let S : Submodule ℂ FamilyModel := (mfderiv IS IF (D.centralInclusion) a).range
    IsClosed (S : Set FamilyModel) := by
  let := D.periods.totalChartedSpace
  let S : Submodule ℂ FamilyModel := (mfderiv IS IF (D.centralInclusion) a).range
  change IsClosed (S : Set FamilyModel)
  have hS : S = NormalLinear.vertical ComplexPlane₂ := centralInclusion_mfderiv_range D a
  rw [hS]
  exact NormalLinear.isClosed_vertical ComplexPlane₂

theorem centralNormalTangentRange_isClosed (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j D.centralPeriod v hv) :
    letI := D.chartedSpace v hv
    let S : Submodule ℂ FamilyModel := (mfderiv IS IF (centralFibreInclusion D v hv) x).range
    IsClosed (S : Set FamilyModel) := by
  let := D.chartedSpace v hv
  let S : Submodule ℂ FamilyModel := (mfderiv IS IF (centralFibreInclusion D v hv) x).range
  change IsClosed (S : Set FamilyModel)
  have hS : S = NormalLinear.vertical ComplexPlane₂ :=
    centralFibreInclusion_mfderiv_range D v hv x
  rw [hS]
  exact NormalLinear.isClosed_vertical ComplexPlane₂

/-- Hausdorffness of the existing quotient topology, not a transported topology. -/
instance familyNormalFibre_t2Space (a : D.centralPeriod.val.Torus) :
    T2Space (FamilyNormalFibre D a) := by
  let := D.periods.totalChartedSpace
  let S : Submodule ℂ FamilyModel := (mfderiv IS IF (D.centralInclusion) a).range
  let : IsClosed (S : Set FamilyModel) := familyNormalTangentRange_isClosed D a
  exact inferInstanceAs (T2Space (FamilyModel ⧸ S))

/-- Hausdorffness follows from closedness of the actual central tangent image. -/
instance centralNormalFibre_t2Space (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j D.centralPeriod v hv) :
    T2Space (CentralNormalFibre D v hv x) := by
  let := D.chartedSpace v hv
  let S : Submodule ℂ FamilyModel := (mfderiv IS IF (centralFibreInclusion D v hv) x).range
  let : IsClosed (S : Set FamilyModel) := centralNormalTangentRange_isClosed D v hv x
  exact inferInstanceAs (T2Space (FamilyModel ⧸ S))

instance familyNormalFibre_finiteDimensional (a : D.centralPeriod.val.Torus) :
    FiniteDimensional ℂ (FamilyNormalFibre D a) :=
  (familyNormalFibreEquiv D a).symm.finiteDimensional

instance centralNormalFibre_finiteDimensional (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j D.centralPeriod v hv) :
    FiniteDimensional ℂ (CentralNormalFibre D v hv x) :=
  (centralNormalFibreEquiv D v hv x).symm.finiteDimensional

/-- The existing first-coordinate identification, with both maps continuous. -/
def familyNormalFibreContinuousEquiv (a : D.centralPeriod.val.Torus) :
    FamilyNormalFibre D a ≃L[ℂ] ℂ :=
  (familyNormalFibreEquiv D a).toContinuousLinearEquiv

@[simp] theorem familyNormalFibreContinuousEquiv_toLinearEquiv
    (a : D.centralPeriod.val.Torus) :
    (familyNormalFibreContinuousEquiv D a).toLinearEquiv = familyNormalFibreEquiv D a := rfl

@[simp] theorem familyNormalFibreContinuousEquiv_mk
    (a : D.centralPeriod.val.Torus) (w : FamilyModel) :
    familyNormalFibreContinuousEquiv D a (Submodule.Quotient.mk w) = w.1 := rfl

def centralNormalFibreContinuousEquiv (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j D.centralPeriod v hv) :
    CentralNormalFibre D v hv x ≃L[ℂ] ℂ :=
  (centralNormalFibreEquiv D v hv x).toContinuousLinearEquiv

@[simp] theorem centralNormalFibreContinuousEquiv_toLinearEquiv (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j D.centralPeriod v hv) :
    (centralNormalFibreContinuousEquiv D v hv x).toLinearEquiv =
      centralNormalFibreEquiv D v hv x := rfl

@[simp] theorem centralNormalFibreContinuousEquiv_mk (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j D.centralPeriod v hv) (w : FamilyModel) :
    centralNormalFibreContinuousEquiv D v hv x (Submodule.Quotient.mk w) = w.1 := rfl

/-- The actual covering differential induces a continuous equivalence of
normal quotients, with their natural quotient topologies. -/
def normalCoveringContinuousEquiv (v : Lattice) (hv : AdmissibleTwist j v)
    (a : D.centralPeriod.val.Torus) :
    FamilyNormalFibre D a ≃L[ℂ]
      CentralNormalFibre D v hv (surfaceProjection j D.centralPeriod v hv a) :=
  (normalCoveringEquiv D v hv a).toContinuousLinearEquiv

@[simp] theorem normalCoveringContinuousEquiv_toLinearEquiv (v : Lattice)
    (hv : AdmissibleTwist j v) (a : D.centralPeriod.val.Torus) :
    (normalCoveringContinuousEquiv D v hv a).toLinearEquiv =
      normalCoveringEquiv D v hv a := rfl

@[simp] theorem normalCoveringContinuousEquiv_mk (v : Lattice)
    (hv : AdmissibleTwist j v) (a : D.centralPeriod.val.Torus) (w : FamilyModel) :
    normalCoveringContinuousEquiv D v hv a (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (fillingDerivativeEquiv D v hv (centralInclusion D a) w) := rfl

def normalCoordinateAtLiftContinuousEquiv (v : Lattice)
    (hv : AdmissibleTwist j v) (a : D.centralPeriod.val.Torus)
    (x : Surface j D.centralPeriod v hv)
    (ha : surfaceProjection j D.centralPeriod v hv a = x) :
    CentralNormalFibre D v hv x ≃L[ℂ] ℂ :=
  (normalCoordinateAtLift D v hv a x ha).toContinuousLinearEquiv

@[simp] theorem normalCoordinateAtLiftContinuousEquiv_toLinearEquiv
    (v : Lattice) (hv : AdmissibleTwist j v)
    (a : D.centralPeriod.val.Torus) (x : Surface j D.centralPeriod v hv)
    (ha : surfaceProjection j D.centralPeriod v hv a = x) :
    (normalCoordinateAtLiftContinuousEquiv D v hv a x ha).toLinearEquiv =
      normalCoordinateAtLift D v hv a x ha := rfl

@[simp] theorem normalCoordinateAtLiftContinuousEquiv_mk
    (v : Lattice) (hv : AdmissibleTwist j v)
    (a : D.centralPeriod.val.Torus) (x : Surface j D.centralPeriod v hv)
    (ha : surfaceProjection j D.centralPeriod v hv a = x) (w : FamilyModel) :
    normalCoordinateAtLiftContinuousEquiv D v hv a x ha (Submodule.Quotient.mk w) =
      ((fillingDerivativeEquiv D v hv (centralInclusion D a)).symm w).1 :=
  normalCoordinateAtLift_mk D v hv a x ha w

namespace NormalBundle

variable (v : Lattice) (hv : AdmissibleTwist j v)

/-- The geometric local coordinate is continuous in the normal-fibre quotient
topology, with continuous inverse. -/
def localCoordinateContinuous (i x : Surface j D.centralPeriod v hv)
    (hx : x ∈ baseSet D v hv i) : CentralNormalFibre D v hv x ≃L[ℂ] ℂ :=
  (localCoordinate D v hv i x hx).toContinuousLinearEquiv

@[simp] theorem localCoordinateContinuous_toLinearEquiv
    (i x : Surface j D.centralPeriod v hv) (hx : x ∈ baseSet D v hv i) :
    (localCoordinateContinuous D v hv i x hx).toLinearEquiv =
      localCoordinate D v hv i x hx := rfl

/-- Bundle fibres and the literal normal tangent quotients are continuously
complex-linearly equivalent in their independently given topologies. -/
def fibreIdentificationContinuous (x : Surface j D.centralPeriod v hv) :
    (core D v hv).Fiber x ≃L[ℂ] CentralNormalFibre D v hv x := by
  change ℂ ≃L[ℂ] CentralNormalFibre D v hv x
  exact (localCoordinateContinuous D v hv x x (mem_baseSet D v hv x)).symm

@[simp] theorem fibreIdentificationContinuous_toLinearEquiv
    (x : Surface j D.centralPeriod v hv) :
    (fibreIdentificationContinuous D v hv x).toLinearEquiv =
      fibreIdentification D v hv x := rfl

theorem localCoordinateContinuous_fibreIdentificationContinuous
    (i x : Surface j D.centralPeriod v hv) (hx : x ∈ baseSet D v hv i)
    (z : (core D v hv).Fiber x) :
    localCoordinateContinuous D v hv i x hx (fibreIdentificationContinuous D v hv x z) =
      ((core D v hv).localTriv i ⟨x, z⟩).2 :=
  localCoordinate_fibreIdentification D v hv i x hx z

end NormalBundle

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
