import Wikipedia.HopfProblem.EllipticFirstHomologyRankTwo

/-!
# Abelianizations of the actual elliptic surface and filling loop groups

The universal affine covering identifies the actual surface fundamental
group with the actual affine subgroup. The strong deformation retraction
does the same for the actual filling. Here those proved identifications
are applied to abelianizations, with their integral translation maps,
exact kernels, image indices, and the source's main-twist markings.

The statements are deliberately about `Abelianization (FundamentalGroup ...)`.
No unproved comparison with singular homology is part of their definitions.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic

/-- A group isomorphism induces an integral linear isomorphism of additive
abelianizations. -/
def abelianizationLinearCongr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Additive (Abelianization G) ≃ₗ[ℤ] Additive (Abelianization H) :=
  e.abelianizationCongr.toAdditive.toIntLinearEquiv

@[simp] theorem abelianizationLinearCongr_of {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (g : G) :
    abelianizationLinearCongr e (Additive.ofMul (Abelianization.of g)) =
      Additive.ofMul (Abelianization.of (e g)) := rfl

abbrev SurfaceAbelianization (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :=
  Additive (Abelianization (FundamentalGroup (Surface j p v hv)
    (affineCoverProjection j p v hv y)))

abbrev FillingAbelianization (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) :=
  Additive (Abelianization (FundamentalGroup (Filling j v hv)
    (centralFibreInclusion j v hv (affineCoverProjection j (centralPeriod j) v hv y))))

def surfaceAbelianizationDeckEquiv (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    SurfaceAbelianization j p v hv y ≃ₗ[ℤ] DeckAbelianization j v :=
  abelianizationLinearCongr (surfaceFundamentalGroupDeckEquiv j p v hv y)

def fillingAbelianizationDeckEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    FillingAbelianization j v hv y ≃ₗ[ℤ] DeckAbelianization j v :=
  abelianizationLinearCongr (fillingFundamentalGroupDeckEquiv j v hv y)

/-- The actual marked translation classes on the surface. -/
def surfaceAbelianTranslation (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    Lattice →ₗ[ℤ] SurfaceAbelianization j p v hv y :=
  ((Abelianization.of.comp (surfaceTranslationHom j p v hv y)).toAdditiveRight).toIntLinearMap

def surfaceAbelianGenerator (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) : SurfaceAbelianization j p v hv y :=
  Additive.ofMul (Abelianization.of (surfaceAffineGenerator j p v hv y))

/-- The actual marked translation classes in the filling. -/
def fillingAbelianTranslation (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) : Lattice →ₗ[ℤ] FillingAbelianization j v hv y :=
  ((Abelianization.of.comp (fillingTranslationHom j v hv y)).toAdditiveRight).toIntLinearMap

def fillingAbelianGenerator (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) : FillingAbelianization j v hv y :=
  Additive.ofMul (Abelianization.of (fillingAffineGenerator j v hv y))

@[simp] theorem surfaceAbelianizationDeckEquiv_translation
    (j : Kind) (p : FixedPeriod j) (v w : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) :
    surfaceAbelianizationDeckEquiv j p v hv y (surfaceAbelianTranslation j p v hv y w) =
      deckAbelianTranslation j v w := by
  change Additive.ofMul (Abelianization.of (surfaceFundamentalGroupDeckEquiv j p v hv y
    (surfaceTranslationHom j p v hv y (Multiplicative.ofAdd w)))) = _
  rw [surfaceFundamentalGroupDeckEquiv_translation]
  rfl

@[simp] theorem surfaceAbelianizationDeckEquiv_generator
    (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) :
    surfaceAbelianizationDeckEquiv j p v hv y (surfaceAbelianGenerator j p v hv y) =
      deckAbelianGenerator j v := by
  change Additive.ofMul (Abelianization.of (surfaceFundamentalGroupDeckEquiv j p v hv y
    (surfaceAffineGenerator j p v hv y))) = _
  rw [surfaceFundamentalGroupDeckEquiv_generator]
  rfl

@[simp] theorem fillingAbelianizationDeckEquiv_translation
    (j : Kind) (v w : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    fillingAbelianizationDeckEquiv j v hv y (fillingAbelianTranslation j v hv y w) =
      deckAbelianTranslation j v w := by
  change Additive.ofMul (Abelianization.of (fillingFundamentalGroupDeckEquiv j v hv y
    (fillingTranslationHom j v hv y (Multiplicative.ofAdd w)))) = _
  rw [fillingFundamentalGroupDeckEquiv_translation]
  rfl

@[simp] theorem fillingAbelianizationDeckEquiv_generator
    (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    fillingAbelianizationDeckEquiv j v hv y (fillingAbelianGenerator j v hv y) =
      deckAbelianGenerator j v := by
  change Additive.ofMul (Abelianization.of (fillingFundamentalGroupDeckEquiv j v hv y
    (fillingAffineGenerator j v hv y))) = _
  rw [fillingFundamentalGroupDeckEquiv_generator]
  rfl

/-- The actual surface loop-group abelianization is free of rank two for
every admissible twist. -/
def surfaceAbelianizationRankTwoEquiv (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    SurfaceAbelianization j p v hv y ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceAbelianizationDeckEquiv j p v hv y).trans (deckAbelianizationRankTwoEquiv j v hv)

/-- The actual filling loop-group abelianization is likewise free of rank two. -/
def fillingAbelianizationRankTwoEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    FillingAbelianization j v hv y ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (fillingAbelianizationDeckEquiv j v hv y).trans (deckAbelianizationRankTwoEquiv j v hv)

theorem surfaceAbelianization_free (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    Module.Free ℤ (SurfaceAbelianization j p v hv y) :=
  Module.Free.of_equiv (surfaceAbelianizationRankTwoEquiv j p v hv y).symm

theorem surfaceAbelianization_finrank (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    Module.finrank ℤ (SurfaceAbelianization j p v hv y) = 2 := by
  rw [(surfaceAbelianizationRankTwoEquiv j p v hv y).finrank_eq]
  simp

theorem surfaceAbelianization_torsionFree (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    Module.IsTorsionFree ℤ (SurfaceAbelianization j p v hv y) := by
  let := surfaceAbelianization_free j p v hv y
  infer_instance

theorem fillingAbelianization_free (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    Module.Free ℤ (FillingAbelianization j v hv y) :=
  Module.Free.of_equiv (fillingAbelianizationRankTwoEquiv j v hv y).symm

theorem fillingAbelianization_finrank (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    Module.finrank ℤ (FillingAbelianization j v hv y) = 2 := by
  rw [(fillingAbelianizationRankTwoEquiv j v hv y).finrank_eq]
  simp

theorem fillingAbelianization_torsionFree (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    Module.IsTorsionFree ℤ (FillingAbelianization j v hv y) := by
  let := fillingAbelianization_free j v hv y
  infer_instance

theorem surfaceAbelianTranslation_ker (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    LinearMap.ker (surfaceAbelianTranslation j p v hv y) =
      LinearMap.range (coinvariantDifference j) := by
  rw [← deckAbelianTranslation_ker j v hv]
  ext w
  change surfaceAbelianTranslation j p v hv y w = 0 ↔ deckAbelianTranslation j v w = 0
  constructor
  · intro h
    have he := congrArg (surfaceAbelianizationDeckEquiv j p v hv y) h
    simpa only [surfaceAbelianizationDeckEquiv_translation, map_zero] using he
  · intro h
    apply (surfaceAbelianizationDeckEquiv j p v hv y).injective
    simpa only [surfaceAbelianizationDeckEquiv_translation, map_zero] using h

theorem fillingAbelianTranslation_ker (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    LinearMap.ker (fillingAbelianTranslation j v hv y) =
      LinearMap.range (coinvariantDifference j) := by
  rw [← deckAbelianTranslation_ker j v hv]
  ext w
  change fillingAbelianTranslation j v hv y w = 0 ↔ deckAbelianTranslation j v w = 0
  constructor
  · intro h
    have he := congrArg (fillingAbelianizationDeckEquiv j v hv y) h
    simpa only [fillingAbelianizationDeckEquiv_translation, map_zero] using he
  · intro h
    apply (fillingAbelianizationDeckEquiv j v hv y).injective
    simpa only [fillingAbelianizationDeckEquiv_translation, map_zero] using h

theorem surfaceAbelianTranslation_range_index (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    (LinearMap.range (surfaceAbelianTranslation j p v hv y)).toAddSubgroup.index = j.order := by
  have hcomp : (surfaceAbelianizationDeckEquiv j p v hv y).toLinearMap.comp
      (surfaceAbelianTranslation j p v hv y) = deckAbelianTranslation j v := by
    apply LinearMap.ext
    exact fun w => surfaceAbelianizationDeckEquiv_translation j p v w hv y
  calc
    _ = (LinearMap.range (deckAbelianTranslation j v)).toAddSubgroup.index := by
      rw [← hcomp, LinearMap.range_comp, Submodule.map_toAddSubgroup]
      exact (AddSubgroup.index_map_equiv _
        (surfaceAbelianizationDeckEquiv j p v hv y).toAddEquiv).symm
    _ = j.order := deckAbelianTranslation_range_index j v hv

theorem fillingAbelianTranslation_range_index (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    (LinearMap.range (fillingAbelianTranslation j v hv y)).toAddSubgroup.index = j.order := by
  have hcomp : (fillingAbelianizationDeckEquiv j v hv y).toLinearMap.comp
      (fillingAbelianTranslation j v hv y) = deckAbelianTranslation j v := by
    apply LinearMap.ext
    exact fun w => fillingAbelianizationDeckEquiv_translation j v w hv y
  calc
    _ = (LinearMap.range (deckAbelianTranslation j v)).toAddSubgroup.index := by
      rw [← hcomp, LinearMap.range_comp, Submodule.map_toAddSubgroup]
      exact (AddSubgroup.index_map_equiv _
        (fillingAbelianizationDeckEquiv j v hv y).toAddEquiv).symm
    _ = j.order := deckAbelianTranslation_range_index j v hv

/-- Main-twist surface coordinates with the affine generator equal to `(1,0)`. -/
def mainSurfaceAbelianizationEquiv (j : Kind) (p : FixedPeriod j) (y : RealCoordinates) :
    SurfaceAbelianization j p j.twist (mainTwist_admissible j) y ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceAbelianizationDeckEquiv j p j.twist (mainTwist_admissible j) y).trans
    (mainDeckAbelianizationEquiv j)

def mainFillingAbelianizationEquiv (j : Kind) (y : RealCoordinates) :
    FillingAbelianization j j.twist (mainTwist_admissible j) y ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (fillingAbelianizationDeckEquiv j j.twist (mainTwist_admissible j) y).trans
    (mainDeckAbelianizationEquiv j)

@[simp] theorem mainSurfaceAbelianizationEquiv_translation
    (j : Kind) (p : FixedPeriod j) (y : RealCoordinates) (w : Lattice) :
    mainSurfaceAbelianizationEquiv j p y
        (surfaceAbelianTranslation j p j.twist (mainTwist_admissible j) y w) =
      ![mainAbelianSign j * (j.order : ℤ) * γ w, psi j w] := by
  change mainDeckAbelianizationEquiv j (surfaceAbelianizationDeckEquiv j p j.twist
    (mainTwist_admissible j) y (surfaceAbelianTranslation j p j.twist
      (mainTwist_admissible j) y w)) = _
  rw [surfaceAbelianizationDeckEquiv_translation, mainDeckAbelianizationEquiv_translation]

@[simp] theorem mainSurfaceAbelianizationEquiv_generator
    (j : Kind) (p : FixedPeriod j) (y : RealCoordinates) :
    mainSurfaceAbelianizationEquiv j p y
        (surfaceAbelianGenerator j p j.twist (mainTwist_admissible j) y) = ![1, 0] := by
  change mainDeckAbelianizationEquiv j (surfaceAbelianizationDeckEquiv j p j.twist
    (mainTwist_admissible j) y (surfaceAbelianGenerator j p j.twist
      (mainTwist_admissible j) y)) = _
  rw [surfaceAbelianizationDeckEquiv_generator, mainDeckAbelianizationEquiv_generator]

@[simp] theorem mainFillingAbelianizationEquiv_translation
    (j : Kind) (y : RealCoordinates) (w : Lattice) :
    mainFillingAbelianizationEquiv j y
        (fillingAbelianTranslation j j.twist (mainTwist_admissible j) y w) =
      ![mainAbelianSign j * (j.order : ℤ) * γ w, psi j w] := by
  change mainDeckAbelianizationEquiv j (fillingAbelianizationDeckEquiv j j.twist
    (mainTwist_admissible j) y (fillingAbelianTranslation j j.twist
      (mainTwist_admissible j) y w)) = _
  rw [fillingAbelianizationDeckEquiv_translation, mainDeckAbelianizationEquiv_translation]

@[simp] theorem mainFillingAbelianizationEquiv_generator
    (j : Kind) (y : RealCoordinates) :
    mainFillingAbelianizationEquiv j y
        (fillingAbelianGenerator j j.twist (mainTwist_admissible j) y) = ![1, 0] := by
  change mainDeckAbelianizationEquiv j (fillingAbelianizationDeckEquiv j j.twist
    (mainTwist_admissible j) y (fillingAbelianGenerator j j.twist
      (mainTwist_admissible j) y)) = _
  rw [fillingAbelianizationDeckEquiv_generator, mainDeckAbelianizationEquiv_generator]

end Wikipedia.HopfProblem.Elliptic
