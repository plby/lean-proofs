import Wikipedia.HopfProblem.EllipticFirstHomologySingular
import Wikipedia.HopfProblem.EllipticFirstHomologyNaturality
import Wikipedia.HopfProblem.FirstHurewiczNaturality

/-!
# Actual singular homology of the central-surface inclusion

The inclusion of each central elliptic surface into its filling induces
an isomorphism on Mathlib's integral singular first homology. The induced
map is identified using the proved natural first Hurewicz isomorphism,
so the affine-generator and lattice markings are preserved by the actual
singular homology functor map, not by a replacement algebraic map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic

open FirstHurewicz

/-- The singular first-homology isomorphism of the actual central-surface
inclusion, constructed by the natural Hurewicz isomorphisms. -/
def centralSurfaceSingularH1Equiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    SingularH1 (Surface j (centralPeriod j) v hv) ≃ₗ[ℤ] SingularH1 (Filling j v hv) :=
  (surfaceHurewiczEquiv j (centralPeriod j) v hv y).symm.trans
    ((centralSurfaceAbelianizationEquiv j v hv y).trans (fillingHurewiczEquiv j v hv y))

@[simp] theorem centralSurfaceSingularH1Equiv_hurewicz (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates)
    (a : SurfaceAbelianization j (centralPeriod j) v hv y) :
    centralSurfaceSingularH1Equiv j v hv y
        (surfaceHurewiczEquiv j (centralPeriod j) v hv y a) =
      fillingHurewiczEquiv j v hv y (centralSurfaceAbelianizationEquiv j v hv y a) := by
  change fillingHurewiczEquiv j v hv y (centralSurfaceAbelianizationEquiv j v hv y
    ((surfaceHurewiczEquiv j (centralPeriod j) v hv y).symm
      (surfaceHurewiczEquiv j (centralPeriod j) v hv y a))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The isomorphism is exactly Mathlib's singular homology map of the
already constructed continuous central-surface embedding. -/
theorem centralSurfaceSingularH1Equiv_toLinearMap (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    (centralSurfaceSingularH1Equiv j v hv y).toLinearMap =
      inducedHomology (surfaceIntoFilling j v hv) := by
  apply LinearMap.ext
  intro a
  obtain ⟨c, rfl⟩ := (surfaceHurewiczEquiv j (centralPeriod j) v hv y).surjective a
  change centralSurfaceSingularH1Equiv j v hv y
    (surfaceHurewiczEquiv j (centralPeriod j) v hv y c) = _
  rw [centralSurfaceSingularH1Equiv_hurewicz]
  exact (firstHurewiczEquiv_natural (surfaceIntoFilling j v hv)
    (affineCoverProjection j (centralPeriod j) v hv y) c).symm

/-- In particular, the actual induced map on singular first homology is bijective. -/
theorem centralSurface_singularH1_bijective (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    Function.Bijective (inducedHomology (surfaceIntoFilling j v hv)) := by
  rw [← centralSurfaceSingularH1Equiv_toLinearMap j v hv y]
  exact (centralSurfaceSingularH1Equiv j v hv y).bijective

/-- The actual inclusion preserves every marked lattice translation class. -/
@[simp] theorem centralSurface_singularH1_translation (j : Kind) (v w : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    inducedHomology (surfaceIntoFilling j v hv)
        (surfaceSingularTranslation j (centralPeriod j) v hv y w) =
      fillingSingularTranslation j v hv y w := by
  rw [← centralSurfaceSingularH1Equiv_toLinearMap j v hv y]
  change centralSurfaceSingularH1Equiv j v hv y
    (surfaceHurewiczEquiv j (centralPeriod j) v hv y
      (surfaceAbelianTranslation j (centralPeriod j) v hv y w)) = _
  rw [centralSurfaceSingularH1Equiv_hurewicz, centralSurfaceAbelianizationEquiv_translation,
    fillingHurewiczEquiv_translation]

/-- The actual inclusion preserves the affine-generator singular homology class. -/
@[simp] theorem centralSurface_singularH1_generator (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    inducedHomology (surfaceIntoFilling j v hv)
        (surfaceSingularGenerator j (centralPeriod j) v hv y) =
      fillingSingularGenerator j v hv y := by
  rw [← centralSurfaceSingularH1Equiv_toLinearMap j v hv y]
  change centralSurfaceSingularH1Equiv j v hv y
    (surfaceHurewiczEquiv j (centralPeriod j) v hv y
      (surfaceAbelianGenerator j (centralPeriod j) v hv y)) = _
  rw [centralSurfaceSingularH1Equiv_hurewicz, centralSurfaceAbelianizationEquiv_generator,
    fillingHurewiczEquiv_generator]

/-- The source's main rank-two marking is unchanged by the actual central
inclusion on singular homology. -/
theorem mainFillingSingularH1Equiv_centralSurface (j : Kind) (y : RealCoordinates)
    (a : SingularH1 (MainSurface j (centralPeriod j))) :
    mainFillingSingularH1Equiv j y
        (inducedHomology (surfaceIntoFilling j j.twist (mainTwist_admissible j)) a) =
      mainSurfaceSingularH1Equiv j (centralPeriod j) y a := by
  obtain ⟨c, rfl⟩ := (surfaceHurewiczEquiv j (centralPeriod j) j.twist
    (mainTwist_admissible j) y).surjective a
  rw [← centralSurfaceSingularH1Equiv_toLinearMap j j.twist (mainTwist_admissible j) y]
  change mainFillingSingularH1Equiv j y
    (centralSurfaceSingularH1Equiv j j.twist (mainTwist_admissible j) y
      (surfaceHurewiczEquiv j (centralPeriod j) j.twist (mainTwist_admissible j) y c)) = _
  rw [centralSurfaceSingularH1Equiv_hurewicz]
  change mainFillingAbelianizationEquiv j y
      ((fillingHurewiczEquiv j j.twist (mainTwist_admissible j) y).symm
        (fillingHurewiczEquiv j j.twist (mainTwist_admissible j) y
          (centralSurfaceAbelianizationEquiv j j.twist (mainTwist_admissible j) y c))) =
    mainSurfaceAbelianizationEquiv j (centralPeriod j) y
      ((surfaceHurewiczEquiv j (centralPeriod j) j.twist (mainTwist_admissible j) y).symm
        (surfaceHurewiczEquiv j (centralPeriod j) j.twist (mainTwist_admissible j) y c))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact mainFillingAbelianizationEquiv_centralSurface j y c

end Wikipedia.HopfProblem.Elliptic
