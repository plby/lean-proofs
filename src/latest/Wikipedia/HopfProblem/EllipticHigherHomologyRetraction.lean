import Wikipedia.HopfProblem.EllipticEquivariantCentralTopologyHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Actual higher homology under the elliptic central inclusion

The genuine strong deformation retraction of the full elliptic filling
onto its central surface induces isomorphisms on Mathlib's integral
singular homology in every degree.  The forward maps are precisely those
of the actual central inclusion, and the inverse maps are those of the
actual radial retraction.  The period-torus covering commutes with these
isomorphisms as an actual induced map, not merely an abstract group map.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The literal finite covering from the central period torus. -/
def periodCover (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : C(p.val.Torus, Surface j p v hv) :=
  ⟨surfaceProjection j p v hv, surfaceProjection_continuous j p v hv⟩

theorem periodCover_isCoveringMap (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : IsCoveringMap (periodCover j p v hv) :=
  surfaceProjection_isCoveringMap j p v hv

variable {j : Kind} (D : Equivariant.Data j)

/-- Every-degree singular homology equivalence induced by the actual
central-surface inclusion in the actual equivariant filling. -/
def centralSurfaceHomologyEquiv (v : Lattice) (hv : AdmissibleTwist j v) (n : ℕ) :
    SingularHomology (Surface j D.centralPeriod v hv) n ≃ₗ[ℤ]
      SingularHomology (D.Space v hv) n :=
  homotopyEquivHomologyEquiv (D.fillingSurfaceHomotopyEquiv v hv) n

@[simp] theorem centralSurfaceHomologyEquiv_toLinearMap
    (v : Lattice) (hv : AdmissibleTwist j v) (n : ℕ) :
    (centralSurfaceHomologyEquiv D v hv n).toLinearMap =
      singularHomologyMap (D.surfaceIntoFilling v hv) n := rfl

@[simp] theorem centralSurfaceHomologyEquiv_apply
    (v : Lattice) (hv : AdmissibleTwist j v) (n : ℕ)
    (a : SingularHomology (Surface j D.centralPeriod v hv) n) :
    centralSurfaceHomologyEquiv D v hv n a =
      singularHomologyMap (D.surfaceIntoFilling v hv) n a := rfl

@[simp] theorem centralSurfaceHomologyEquiv_symm_apply
    (v : Lattice) (hv : AdmissibleTwist j v) (n : ℕ)
    (a : SingularHomology (D.Space v hv) n) :
    (centralSurfaceHomologyEquiv D v hv n).symm a =
      singularHomologyMap (D.fillingSurfaceRetraction v hv) n a := rfl

/-- The actual central inclusion is an isomorphism on higher homology,
with no assumption on the desired homology groups. -/
theorem centralInclusion_homology_bijective (v : Lattice)
    (hv : AdmissibleTwist j v) (n : ℕ) :
    Function.Bijective (singularHomologyMap (D.surfaceIntoFilling v hv) n) :=
  (centralSurfaceHomologyEquiv D v hv n).bijective

/-- The higher-degree construction agrees with the previously constructed
first-Hurewicz equivalence in degree one. -/
theorem centralSurfaceHomologyEquiv_one (v : Lattice) (hv : AdmissibleTwist j v)
    (a : Surface j D.centralPeriod v hv) :
    centralSurfaceHomologyEquiv D v hv 1 = D.centralSurfaceSingularH1Equiv v hv a := by
  apply LinearEquiv.toLinearMap_injective
  rw [centralSurfaceHomologyEquiv_toLinearMap,
    D.centralSurfaceSingularH1Equiv_toLinearMap]

/-- The literal map from the central period torus into the full filling. -/
def periodTorusIntoFilling (v : Lattice) (hv : AdmissibleTwist j v) :
    C(D.centralPeriod.val.Torus, D.Space v hv) :=
  (D.surfaceIntoFilling v hv).comp (periodCover j D.centralPeriod v hv)

@[simp] theorem periodTorusIntoFilling_apply (v : Lattice) (hv : AdmissibleTwist j v)
    (x : D.centralPeriod.val.Torus) :
    periodTorusIntoFilling D v hv x =
      D.centralFibreInclusion v hv (surfaceProjection j D.centralPeriod v hv x) := rfl

/-- Naturality for the actual finite covering and central inclusion in
every degree, including the required degrees two, three, and four. -/
theorem centralSurfaceHomologyEquiv_periodCover
    (v : Lattice) (hv : AdmissibleTwist j v) (n : ℕ)
    (a : SingularHomology D.centralPeriod.val.Torus n) :
    centralSurfaceHomologyEquiv D v hv n
      (singularHomologyMap (periodCover j D.centralPeriod v hv) n a) =
        singularHomologyMap (periodTorusIntoFilling D v hv) n a := by
  rw [centralSurfaceHomologyEquiv_apply, periodTorusIntoFilling, singularHomologyMap_comp]
  rfl

/-- The map into the full filling kills exactly the same actual torus
classes as the finite covering of the central surface. -/
theorem periodTorusIntoFilling_homology_ker (v : Lattice)
    (hv : AdmissibleTwist j v) (n : ℕ) :
    LinearMap.ker (singularHomologyMap (periodTorusIntoFilling D v hv) n) =
      LinearMap.ker (singularHomologyMap (periodCover j D.centralPeriod v hv) n) := by
  ext a
  change singularHomologyMap (periodTorusIntoFilling D v hv) n a = 0 ↔ _
  rw [← centralSurfaceHomologyEquiv_periodCover]
  exact (centralSurfaceHomologyEquiv D v hv n).map_eq_zero_iff

end Wikipedia.HopfProblem.Elliptic.HigherHomology
