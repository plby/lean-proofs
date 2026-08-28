import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologySpaces

/-!
# Actual pullbacks in elliptic cohomology coordinates

Central inclusion and the proved radial retraction preserve the native
cohomology coordinates.  They are inverse isomorphisms on actual singular
cohomology.  Evaluation identifies pullback by the literal finite period
cover with the dual of its actual homology map; no covering matrix is
assumed in these formulas.
-/

noncomputable section

open scoped BigOperators ContinuousMap

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris SingularCohomologyFree

/-- Pullback by the actual period cover is dual to its actual homology map. -/
theorem periodCover_cohomology_evaluate (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n)
    (b : SingularHomology p.val.Torus n) :
    singularEvaluation p.val.Torus n
        (singularCohomologyPullback (periodCover j p j.twist (mainTwist_admissible j)) n a) b =
      ∑ i, surfaceCohomologyCoordinates j p n a i *
        surfaceHomologyCoordinates j p n
          (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) n b) i := by
  rw [singularEvaluation_naturality]
  exact surfaceCohomologyCoordinates_evaluate j p n a _

variable {j : Kind} (D : Equivariant.Data j)

/-- The actual central inclusion induces the identity in dual coordinates. -/
theorem surfaceCohomologyCoordinates_centralInclusion (n : ℕ)
    (a : SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n) :
    surfaceCohomologyCoordinates j D.centralPeriod n
        (singularCohomologyPullback
          (D.surfaceIntoFilling j.twist (mainTwist_admissible j)) n a) =
      fillingCohomologyCoordinates D n a :=
  cohomologyCoordinatesOfHomology_naturality ellipticBettiNumber
    (surfaceHomologyCoordinates j D.centralPeriod) (fillingHomologyCoordinates D)
    (D.surfaceIntoFilling j.twist (mainTwist_admissible j)) n
    (fillingHomologyCoordinates_centralInclusion D n) a

/-- The actual radial retraction induces the inverse identity in coordinates. -/
theorem fillingCohomologyCoordinates_retraction (n : ℕ)
    (a : SingularCohomology
      (Surface j D.centralPeriod j.twist (mainTwist_admissible j)) n) :
    fillingCohomologyCoordinates D n
        (singularCohomologyPullback
          (D.fillingSurfaceRetraction j.twist (mainTwist_admissible j)) n a) =
      surfaceCohomologyCoordinates j D.centralPeriod n a :=
  cohomologyCoordinatesOfHomology_naturality ellipticBettiNumber
    (fillingHomologyCoordinates D) (surfaceHomologyCoordinates j D.centralPeriod)
    (D.fillingSurfaceRetraction j.twist (mainTwist_admissible j)) n (fun _ => rfl) a

/-- The actual central-inclusion pullback, bundled as an isomorphism. -/
def centralSurfaceCohomologyEquiv (n : ℕ) :
    SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n ≃ₗ[ℤ]
      SingularCohomology (Surface j D.centralPeriod j.twist (mainTwist_admissible j)) n :=
  (fillingCohomologyCoordinates D n).trans
    (surfaceCohomologyCoordinates j D.centralPeriod n).symm

@[simp] theorem centralSurfaceCohomologyEquiv_apply (n : ℕ)
    (a : SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n) :
    centralSurfaceCohomologyEquiv D n a =
      singularCohomologyPullback (D.surfaceIntoFilling j.twist (mainTwist_admissible j)) n a := by
  apply (surfaceCohomologyCoordinates j D.centralPeriod n).injective
  change surfaceCohomologyCoordinates j D.centralPeriod n
    ((surfaceCohomologyCoordinates j D.centralPeriod n).symm
      (fillingCohomologyCoordinates D n a)) = _
  rw [LinearEquiv.apply_symm_apply, surfaceCohomologyCoordinates_centralInclusion]

@[simp] theorem centralSurfaceCohomologyEquiv_symm_apply (n : ℕ)
    (a : SingularCohomology
      (Surface j D.centralPeriod j.twist (mainTwist_admissible j)) n) :
    (centralSurfaceCohomologyEquiv D n).symm a =
      singularCohomologyPullback
        (D.fillingSurfaceRetraction j.twist (mainTwist_admissible j)) n a := by
  apply (fillingCohomologyCoordinates D n).injective
  change fillingCohomologyCoordinates D n
    ((fillingCohomologyCoordinates D n).symm
      (surfaceCohomologyCoordinates j D.centralPeriod n a)) = _
  rw [LinearEquiv.apply_symm_apply, fillingCohomologyCoordinates_retraction]

@[simp] theorem centralSurfaceCohomologyEquiv_toLinearMap (n : ℕ) :
    (centralSurfaceCohomologyEquiv D n).toLinearMap =
      singularCohomologyPullback (D.surfaceIntoFilling j.twist (mainTwist_admissible j)) n := by
  apply LinearMap.ext
  intro a
  exact centralSurfaceCohomologyEquiv_apply D n a

@[simp] theorem centralSurfaceCohomologyEquiv_symm_toLinearMap (n : ℕ) :
    (centralSurfaceCohomologyEquiv D n).symm.toLinearMap =
      singularCohomologyPullback
        (D.fillingSurfaceRetraction j.twist (mainTwist_admissible j)) n := by
  apply LinearMap.ext
  intro a
  exact centralSurfaceCohomologyEquiv_symm_apply D n a

theorem centralInclusion_cohomology_bijective (n : ℕ) :
    Function.Bijective
      (singularCohomologyPullback (D.surfaceIntoFilling j.twist (mainTwist_admissible j)) n) := by
  rw [← centralSurfaceCohomologyEquiv_toLinearMap]
  exact (centralSurfaceCohomologyEquiv D n).bijective

theorem retraction_cohomology_bijective (n : ℕ) :
    Function.Bijective
      (singularCohomologyPullback
        (D.fillingSurfaceRetraction j.twist (mainTwist_admissible j)) n) := by
  rw [← centralSurfaceCohomologyEquiv_symm_toLinearMap]
  exact (centralSurfaceCohomologyEquiv D n).symm.bijective

/-- The literal factorization through the central surface gives the actual
commuting pullback diagram, in every degree. -/
theorem centralSurfaceCohomologyEquiv_periodCover (n : ℕ)
    (a : SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n) :
    singularCohomologyPullback
        (periodCover j D.centralPeriod j.twist (mainTwist_admissible j)) n
        (centralSurfaceCohomologyEquiv D n a) =
      singularCohomologyPullback
        (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) n a := by
  rw [centralSurfaceCohomologyEquiv_apply, periodTorusIntoFilling,
    singularCohomologyPullback_comp]
  rfl

/-- The full-filling period-torus map has the same actual covering
homology coordinates in the evaluation pairing. -/
theorem periodTorusIntoFilling_cohomology_evaluate (n : ℕ)
    (a : SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n)
    (b : SingularHomology D.centralPeriod.val.Torus n) :
    singularEvaluation D.centralPeriod.val.Torus n
        (singularCohomologyPullback
          (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) n a) b =
      ∑ i, fillingCohomologyCoordinates D n a i *
        surfaceHomologyCoordinates j D.centralPeriod n
          (singularHomologyMap
            (periodCover j D.centralPeriod j.twist (mainTwist_admissible j)) n b) i := by
  rw [singularEvaluation_naturality, fillingCohomologyCoordinates_evaluate,
    ← centralSurfaceHomologyEquiv_periodCover D j.twist (mainTwist_admissible j) n b]
  simp only [centralSurfaceHomologyEquiv_apply,
    fillingHomologyCoordinates_centralInclusion]

end Wikipedia.HopfProblem.Elliptic.HigherHomology
