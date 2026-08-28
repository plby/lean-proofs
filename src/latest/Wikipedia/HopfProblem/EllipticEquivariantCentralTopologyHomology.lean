import Wikipedia.HopfProblem.EllipticEquivariantCentralTopologySurface
import Wikipedia.HopfProblem.EllipticFirstHomologySingular
import Wikipedia.HopfProblem.FirstHurewiczNaturality

/-!
# Actual central-surface singular homology for arbitrary equivariant periods

The genuine central-surface inclusion of a supplied equivariant period
family induces an isomorphism on integral singular first homology.  Its
map is Mathlib's actual singular homology map, identified by naturality of
the first Hurewicz isomorphism and the literal radial deformation.

The generic filling consequently has free, torsion-free integral first
homology of rank two.  These are statements about the supplied family's
actual quotient topology; no comparison of complex atlases is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

open FirstHurewicz

variable {j : Kind} (D : Equivariant.Data j)

/-- The actual filling has the same underlying quotient topology as the
path-connected concrete filling. -/
instance fillingPathConnected (v : Lattice) (hv : AdmissibleTwist j v) :
    PathConnectedSpace (D.Space v hv) :=
  Elliptic.fillingPathConnected j v hv

/-- Abelianization of the fundamental-group isomorphism induced by the
actual central-surface inclusion. -/
def centralSurfaceAbelianizationEquiv (v : Lattice) (hv : AdmissibleTwist j v)
    (a : Surface j D.centralPeriod v hv) :
    AbelianPi1 (Surface j D.centralPeriod v hv) a ≃ₗ[ℤ]
      AbelianPi1 (D.Space v hv) (D.centralFibreInclusion v hv a) :=
  abelianizationLinearCongr (D.fillingSurfaceFundamentalGroupEquiv v hv a)

@[simp] theorem centralSurfaceAbelianizationEquiv_toLinearMap
    (v : Lattice) (hv : AdmissibleTwist j v)
    (a : Surface j D.centralPeriod v hv) :
    (D.centralSurfaceAbelianizationEquiv v hv a).toLinearMap =
      inducedAbelianPi1 (D.surfaceIntoFilling v hv) a := rfl

/-- The first singular homology isomorphism induced by the actual
central-surface inclusion, via the natural first Hurewicz isomorphism. -/
def centralSurfaceSingularH1Equiv (v : Lattice) (hv : AdmissibleTwist j v)
    (a : Surface j D.centralPeriod v hv) :
    SingularH1 (Surface j D.centralPeriod v hv) ≃ₗ[ℤ] SingularH1 (D.Space v hv) :=
  (firstHurewiczEquiv a).symm.trans
    ((D.centralSurfaceAbelianizationEquiv v hv a).trans
      (firstHurewiczEquiv (D.centralFibreInclusion v hv a)))

@[simp] theorem centralSurfaceSingularH1Equiv_hurewicz
    (v : Lattice) (hv : AdmissibleTwist j v)
    (a : Surface j D.centralPeriod v hv)
    (c : AbelianPi1 (Surface j D.centralPeriod v hv) a) :
    D.centralSurfaceSingularH1Equiv v hv a (firstHurewiczEquiv a c) =
      firstHurewiczEquiv (D.centralFibreInclusion v hv a)
        (D.centralSurfaceAbelianizationEquiv v hv a c) := by
  change firstHurewiczEquiv (D.centralFibreInclusion v hv a)
    (D.centralSurfaceAbelianizationEquiv v hv a
      ((firstHurewiczEquiv a).symm (firstHurewiczEquiv a c))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- This equivalence is exactly the actual induced singular homology map,
not an independently chosen isomorphism of rank-two modules. -/
theorem centralSurfaceSingularH1Equiv_toLinearMap
    (v : Lattice) (hv : AdmissibleTwist j v)
    (a : Surface j D.centralPeriod v hv) :
    (D.centralSurfaceSingularH1Equiv v hv a).toLinearMap =
      inducedHomology (D.surfaceIntoFilling v hv) := by
  apply LinearMap.ext
  intro c
  obtain ⟨b, rfl⟩ := (firstHurewiczEquiv a).surjective c
  change D.centralSurfaceSingularH1Equiv v hv a (firstHurewiczEquiv a b) = _
  rw [D.centralSurfaceSingularH1Equiv_hurewicz]
  exact (firstHurewiczEquiv_natural (D.surfaceIntoFilling v hv) a b).symm

/-- The central-surface inclusion induces an isomorphism on actual integral
singular first homology for every supplied equivariant period family. -/
theorem centralSurface_singularH1_bijective (v : Lattice)
    (hv : AdmissibleTwist j v) :
    Function.Bijective (inducedHomology (D.surfaceIntoFilling v hv)) := by
  rw [← D.centralSurfaceSingularH1Equiv_toLinearMap v hv
    (affineCoverProjection j D.centralPeriod v hv 0)]
  exact (D.centralSurfaceSingularH1Equiv v hv
    (affineCoverProjection j D.centralPeriod v hv 0)).bijective

/-- Rank-two coordinates for the actual generic filling, transported
through the actual central-surface inclusion. -/
def fillingSingularH1RankTwoEquiv (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) :
    SingularH1 (D.Space v hv) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (D.centralSurfaceSingularH1Equiv v hv
    (affineCoverProjection j D.centralPeriod v hv y)).symm.trans
      (surfaceSingularH1RankTwoEquiv j D.centralPeriod v hv y)

/-- The rank-two marking agrees with the arbitrary-period surface marking
under the actual induced map on singular homology. -/
@[simp] theorem fillingSingularH1RankTwoEquiv_inclusion
    (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates)
    (c : SingularH1 (Surface j D.centralPeriod v hv)) :
    D.fillingSingularH1RankTwoEquiv v hv y
        (inducedHomology (D.surfaceIntoFilling v hv) c) =
      surfaceSingularH1RankTwoEquiv j D.centralPeriod v hv y c := by
  rw [← D.centralSurfaceSingularH1Equiv_toLinearMap v hv
    (affineCoverProjection j D.centralPeriod v hv y)]
  change surfaceSingularH1RankTwoEquiv j D.centralPeriod v hv y
    ((D.centralSurfaceSingularH1Equiv v hv
      (affineCoverProjection j D.centralPeriod v hv y)).symm
        (D.centralSurfaceSingularH1Equiv v hv
          (affineCoverProjection j D.centralPeriod v hv y) c)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem fillingSingularH1_free (v : Lattice) (hv : AdmissibleTwist j v) :
    Module.Free ℤ (SingularH1 (D.Space v hv)) :=
  Module.Free.of_equiv (D.fillingSingularH1RankTwoEquiv v hv 0).symm

theorem fillingSingularH1_finite (v : Lattice) (hv : AdmissibleTwist j v) :
    Module.Finite ℤ (SingularH1 (D.Space v hv)) :=
  Module.Finite.of_surjective (D.fillingSingularH1RankTwoEquiv v hv 0).symm.toLinearMap
    (D.fillingSingularH1RankTwoEquiv v hv 0).symm.surjective

theorem fillingSingularH1_finrank (v : Lattice) (hv : AdmissibleTwist j v) :
    Module.finrank ℤ (SingularH1 (D.Space v hv)) = 2 := by
  rw [(D.fillingSingularH1RankTwoEquiv v hv 0).finrank_eq]
  simp

theorem fillingSingularH1_torsionFree (v : Lattice) (hv : AdmissibleTwist j v) :
    Module.IsTorsionFree ℤ (SingularH1 (D.Space v hv)) := by
  let := D.fillingSingularH1_free v hv
  infer_instance

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
