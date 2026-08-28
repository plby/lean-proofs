import Wikipedia.HopfProblem.EllipticFirstHomologyGroups
import Wikipedia.HopfProblem.FirstHurewiczEquivalence

/-!
# Integral singular homology of the actual elliptic surfaces and fillings

The target of the Hurewicz map is the actual degree-one homology of
Mathlib's singular chain complex with integral coefficients. The marked
translations and affine generators below are their genuine singular
homology classes, obtained from the already constructed loop groups.
The proved first Hurewicz isomorphism then gives the free rank-two
computation, including the exact translation kernel, image index, and
the source's main-twist coordinates.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic

open FirstHurewicz

/-- Every filling point is joined radially to the central surface, and
the actual central surface is path connected. -/
instance fillingPathConnected (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    PathConnectedSpace (Filling j v hv) where
  nonempty := ⟨surfaceIntoFilling j v hv
    (Classical.choice (PathConnectedSpace.nonempty
      (X := Surface j (centralPeriod j) v hv)))⟩
  joined x y := by
    let H := (fillingSurfaceStrongDeformationRetraction j v hv).toHomotopy
    have hx : Joined x (surfaceIntoFilling j v hv (fillingSurfaceRetraction j v hv x)) :=
      ⟨H.evalAt x⟩
    have hy : Joined y (surfaceIntoFilling j v hv (fillingSurfaceRetraction j v hv y)) :=
      ⟨H.evalAt y⟩
    have hxy := (PathConnectedSpace.joined
      (fillingSurfaceRetraction j v hv x) (fillingSurfaceRetraction j v hv y)).map
        (surfaceIntoFilling j v hv).continuous
    exact hx.trans (hxy.trans hy.symm)

/-- The genuine first Hurewicz isomorphism for the actual quotient surface. -/
def surfaceHurewiczEquiv (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    SurfaceAbelianization j p v hv y ≃ₗ[ℤ] SingularH1 (Surface j p v hv) :=
  firstHurewiczEquiv (affineCoverProjection j p v hv y)

/-- The genuine first Hurewicz isomorphism for the actual filling. -/
def fillingHurewiczEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    FillingAbelianization j v hv y ≃ₗ[ℤ] SingularH1 (Filling j v hv) :=
  firstHurewiczEquiv (centralFibreInclusion j v hv
    (affineCoverProjection j (centralPeriod j) v hv y))

@[simp] theorem surfaceHurewiczEquiv_apply
    (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) (a : SurfaceAbelianization j p v hv y) :
    surfaceHurewiczEquiv j p v hv y a =
      hurewiczMap (affineCoverProjection j p v hv y) a := rfl

@[simp] theorem fillingHurewiczEquiv_apply
    (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) (a : FillingAbelianization j v hv y) :
    fillingHurewiczEquiv j v hv y a =
      hurewiczMap (centralFibreInclusion j v hv
        (affineCoverProjection j (centralPeriod j) v hv y)) a := rfl

/-- The marked integral translation classes in actual singular homology
of the surface. -/
def surfaceSingularTranslation (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    Lattice →ₗ[ℤ] SingularH1 (Surface j p v hv) :=
  (hurewiczMap (affineCoverProjection j p v hv y)).comp
    (surfaceAbelianTranslation j p v hv y)

/-- The affine generator as an actual singular homology class. -/
def surfaceSingularGenerator (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    SingularH1 (Surface j p v hv) :=
  hurewiczMap (affineCoverProjection j p v hv y)
    (surfaceAbelianGenerator j p v hv y)

/-- The marked integral translation classes in actual singular homology
of the filling. -/
def fillingSingularTranslation (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    Lattice →ₗ[ℤ] SingularH1 (Filling j v hv) :=
  (hurewiczMap (centralFibreInclusion j v hv
    (affineCoverProjection j (centralPeriod j) v hv y))).comp
      (fillingAbelianTranslation j v hv y)

/-- The filling's affine generator as an actual singular homology class. -/
def fillingSingularGenerator (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) : SingularH1 (Filling j v hv) :=
  hurewiczMap (centralFibreInclusion j v hv
    (affineCoverProjection j (centralPeriod j) v hv y)) (fillingAbelianGenerator j v hv y)

@[simp] theorem surfaceSingularTranslation_eq_hurewicz
    (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) (w : Lattice) :
    surfaceSingularTranslation j p v hv y w =
      hurewiczFunction (affineCoverProjection j p v hv y)
        (surfaceTranslationHom j p v hv y (Multiplicative.ofAdd w)) := rfl

@[simp] theorem surfaceSingularGenerator_eq_hurewicz
    (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) :
    surfaceSingularGenerator j p v hv y =
      hurewiczFunction (affineCoverProjection j p v hv y)
        (surfaceAffineGenerator j p v hv y) := rfl

@[simp] theorem fillingSingularTranslation_eq_hurewicz
    (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) (w : Lattice) :
    fillingSingularTranslation j v hv y w =
      hurewiczFunction (centralFibreInclusion j v hv
        (affineCoverProjection j (centralPeriod j) v hv y))
          (fillingTranslationHom j v hv y (Multiplicative.ofAdd w)) := rfl

@[simp] theorem fillingSingularGenerator_eq_hurewicz
    (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    fillingSingularGenerator j v hv y =
      hurewiczFunction (centralFibreInclusion j v hv
        (affineCoverProjection j (centralPeriod j) v hv y))
          (fillingAffineGenerator j v hv y) := rfl

@[simp] theorem surfaceHurewiczEquiv_translation
    (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) (w : Lattice) :
    surfaceHurewiczEquiv j p v hv y (surfaceAbelianTranslation j p v hv y w) =
      surfaceSingularTranslation j p v hv y w := rfl

@[simp] theorem surfaceHurewiczEquiv_generator
    (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) :
    surfaceHurewiczEquiv j p v hv y (surfaceAbelianGenerator j p v hv y) =
      surfaceSingularGenerator j p v hv y := rfl

@[simp] theorem fillingHurewiczEquiv_translation
    (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) (w : Lattice) :
    fillingHurewiczEquiv j v hv y (fillingAbelianTranslation j v hv y w) =
      fillingSingularTranslation j v hv y w := rfl

@[simp] theorem fillingHurewiczEquiv_generator
    (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    fillingHurewiczEquiv j v hv y (fillingAbelianGenerator j v hv y) =
      fillingSingularGenerator j v hv y := rfl

/-- The actual integral singular first homology of every admissible
elliptic quotient surface is free of rank two. -/
def surfaceSingularH1RankTwoEquiv (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    SingularH1 (Surface j p v hv) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceHurewiczEquiv j p v hv y).symm.trans
    (surfaceAbelianizationRankTwoEquiv j p v hv y)

/-- The actual integral singular first homology of every admissible
elliptic logarithmic filling is likewise free of rank two. -/
def fillingSingularH1RankTwoEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    SingularH1 (Filling j v hv) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (fillingHurewiczEquiv j v hv y).symm.trans
    (fillingAbelianizationRankTwoEquiv j v hv y)

@[simp] theorem surfaceSingularH1RankTwoEquiv_hurewicz
    (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) (a : SurfaceAbelianization j p v hv y) :
    surfaceSingularH1RankTwoEquiv j p v hv y (surfaceHurewiczEquiv j p v hv y a) =
      surfaceAbelianizationRankTwoEquiv j p v hv y a := by
  change surfaceAbelianizationRankTwoEquiv j p v hv y
    ((surfaceHurewiczEquiv j p v hv y).symm (surfaceHurewiczEquiv j p v hv y a)) = _
  rw [LinearEquiv.symm_apply_apply]

@[simp] theorem fillingSingularH1RankTwoEquiv_hurewicz
    (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) (a : FillingAbelianization j v hv y) :
    fillingSingularH1RankTwoEquiv j v hv y (fillingHurewiczEquiv j v hv y a) =
      fillingAbelianizationRankTwoEquiv j v hv y a := by
  change fillingAbelianizationRankTwoEquiv j v hv y
    ((fillingHurewiczEquiv j v hv y).symm (fillingHurewiczEquiv j v hv y a)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem surfaceSingularH1_free (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : Module.Free ℤ (SingularH1 (Surface j p v hv)) :=
  Module.Free.of_equiv (surfaceSingularH1RankTwoEquiv j p v hv 0).symm

theorem surfaceSingularH1_finite (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : Module.Finite ℤ (SingularH1 (Surface j p v hv)) :=
  Module.Finite.of_surjective (surfaceSingularH1RankTwoEquiv j p v hv 0).symm.toLinearMap
    (surfaceSingularH1RankTwoEquiv j p v hv 0).symm.surjective

theorem surfaceSingularH1_finrank (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : Module.finrank ℤ (SingularH1 (Surface j p v hv)) = 2 := by
  rw [(surfaceSingularH1RankTwoEquiv j p v hv 0).finrank_eq]
  simp

theorem surfaceSingularH1_torsionFree (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : Module.IsTorsionFree ℤ (SingularH1 (Surface j p v hv)) := by
  let := surfaceSingularH1_free j p v hv
  infer_instance

theorem fillingSingularH1_free (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Module.Free ℤ (SingularH1 (Filling j v hv)) :=
  Module.Free.of_equiv (fillingSingularH1RankTwoEquiv j v hv 0).symm

theorem fillingSingularH1_finite (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Module.Finite ℤ (SingularH1 (Filling j v hv)) :=
  Module.Finite.of_surjective (fillingSingularH1RankTwoEquiv j v hv 0).symm.toLinearMap
    (fillingSingularH1RankTwoEquiv j v hv 0).symm.surjective

theorem fillingSingularH1_finrank (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Module.finrank ℤ (SingularH1 (Filling j v hv)) = 2 := by
  rw [(fillingSingularH1RankTwoEquiv j v hv 0).finrank_eq]
  simp

theorem fillingSingularH1_torsionFree (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Module.IsTorsionFree ℤ (SingularH1 (Filling j v hv)) := by
  let := fillingSingularH1_free j v hv
  infer_instance

/-- No additional translation is killed when passing from the computed
abelianization to actual singular homology. -/
theorem surfaceSingularTranslation_ker (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    LinearMap.ker (surfaceSingularTranslation j p v hv y) =
      LinearMap.range (coinvariantDifference j) := by
  rw [← surfaceAbelianTranslation_ker j p v hv y]
  ext w
  change surfaceHurewiczEquiv j p v hv y (surfaceAbelianTranslation j p v hv y w) = 0 ↔
    surfaceAbelianTranslation j p v hv y w = 0
  exact (surfaceHurewiczEquiv j p v hv y).map_eq_zero_iff

theorem fillingSingularTranslation_ker (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    LinearMap.ker (fillingSingularTranslation j v hv y) =
      LinearMap.range (coinvariantDifference j) := by
  rw [← fillingAbelianTranslation_ker j v hv y]
  ext w
  change fillingHurewiczEquiv j v hv y (fillingAbelianTranslation j v hv y w) = 0 ↔
    fillingAbelianTranslation j v hv y w = 0
  exact (fillingHurewiczEquiv j v hv y).map_eq_zero_iff

/-- The translation image has the exact source index in actual singular homology. -/
theorem surfaceSingularTranslation_range_index (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    (LinearMap.range (surfaceSingularTranslation j p v hv y)).toAddSubgroup.index =
      j.order := by
  have hcomp : surfaceSingularTranslation j p v hv y =
      (surfaceHurewiczEquiv j p v hv y).toLinearMap.comp
        (surfaceAbelianTranslation j p v hv y) := rfl
  rw [hcomp, LinearMap.range_comp, Submodule.map_toAddSubgroup]
  exact (AddSubgroup.index_map_equiv _
    (surfaceHurewiczEquiv j p v hv y).toAddEquiv).trans
      (surfaceAbelianTranslation_range_index j p v hv y)

theorem fillingSingularTranslation_range_index (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    (LinearMap.range (fillingSingularTranslation j v hv y)).toAddSubgroup.index =
      j.order := by
  have hcomp : fillingSingularTranslation j v hv y =
      (fillingHurewiczEquiv j v hv y).toLinearMap.comp
        (fillingAbelianTranslation j v hv y) := rfl
  rw [hcomp, LinearMap.range_comp, Submodule.map_toAddSubgroup]
  exact (AddSubgroup.index_map_equiv _
    (fillingHurewiczEquiv j v hv y).toAddEquiv).trans
      (fillingAbelianTranslation_range_index j v hv y)

/-- Main-twist coordinates on actual singular homology, normalized so
the affine generator has coordinates `(1,0)`. -/
def mainSurfaceSingularH1Equiv (j : Kind) (p : FixedPeriod j) (y : RealCoordinates) :
    SingularH1 (MainSurface j p) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceHurewiczEquiv j p j.twist (mainTwist_admissible j) y).symm.trans
    (mainSurfaceAbelianizationEquiv j p y)

def mainFillingSingularH1Equiv (j : Kind) (y : RealCoordinates) :
    SingularH1 (MainFilling j) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (fillingHurewiczEquiv j j.twist (mainTwist_admissible j) y).symm.trans
    (mainFillingAbelianizationEquiv j y)

@[simp] theorem mainSurfaceSingularH1Equiv_translation
    (j : Kind) (p : FixedPeriod j) (y : RealCoordinates) (w : Lattice) :
    mainSurfaceSingularH1Equiv j p y
        (surfaceSingularTranslation j p j.twist (mainTwist_admissible j) y w) =
      ![mainAbelianSign j * (j.order : ℤ) * γ w, psi j w] := by
  change mainSurfaceAbelianizationEquiv j p y
    ((surfaceHurewiczEquiv j p j.twist (mainTwist_admissible j) y).symm
      (surfaceHurewiczEquiv j p j.twist (mainTwist_admissible j) y
        (surfaceAbelianTranslation j p j.twist (mainTwist_admissible j) y w))) = _
  rw [LinearEquiv.symm_apply_apply, mainSurfaceAbelianizationEquiv_translation]

@[simp] theorem mainSurfaceSingularH1Equiv_generator
    (j : Kind) (p : FixedPeriod j) (y : RealCoordinates) :
    mainSurfaceSingularH1Equiv j p y
        (surfaceSingularGenerator j p j.twist (mainTwist_admissible j) y) = ![1, 0] := by
  change mainSurfaceAbelianizationEquiv j p y
    ((surfaceHurewiczEquiv j p j.twist (mainTwist_admissible j) y).symm
      (surfaceHurewiczEquiv j p j.twist (mainTwist_admissible j) y
        (surfaceAbelianGenerator j p j.twist (mainTwist_admissible j) y))) = _
  rw [LinearEquiv.symm_apply_apply, mainSurfaceAbelianizationEquiv_generator]

@[simp] theorem mainFillingSingularH1Equiv_translation
    (j : Kind) (y : RealCoordinates) (w : Lattice) :
    mainFillingSingularH1Equiv j y
        (fillingSingularTranslation j j.twist (mainTwist_admissible j) y w) =
      ![mainAbelianSign j * (j.order : ℤ) * γ w, psi j w] := by
  change mainFillingAbelianizationEquiv j y
    ((fillingHurewiczEquiv j j.twist (mainTwist_admissible j) y).symm
      (fillingHurewiczEquiv j j.twist (mainTwist_admissible j) y
        (fillingAbelianTranslation j j.twist (mainTwist_admissible j) y w))) = _
  rw [LinearEquiv.symm_apply_apply, mainFillingAbelianizationEquiv_translation]

@[simp] theorem mainFillingSingularH1Equiv_generator
    (j : Kind) (y : RealCoordinates) :
    mainFillingSingularH1Equiv j y
        (fillingSingularGenerator j j.twist (mainTwist_admissible j) y) = ![1, 0] := by
  change mainFillingAbelianizationEquiv j y
    ((fillingHurewiczEquiv j j.twist (mainTwist_admissible j) y).symm
      (fillingHurewiczEquiv j j.twist (mainTwist_admissible j) y
        (fillingAbelianGenerator j j.twist (mainTwist_admissible j) y))) = _
  rw [LinearEquiv.symm_apply_apply, mainFillingAbelianizationEquiv_generator]

end Wikipedia.HopfProblem.Elliptic
