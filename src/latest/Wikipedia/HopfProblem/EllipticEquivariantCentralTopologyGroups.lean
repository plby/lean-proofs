import Wikipedia.HopfProblem.EllipticEquivariantCentralTopologySurface
import Wikipedia.HopfProblem.EllipticFillingTopologyNormalForms
import Wikipedia.HopfProblem.EllipticFundamentalGroupPresentation

/-!
# Affine fundamental groups of the actual equivariant-period fillings

The proved retraction onto the supplied family's genuine central surface
transports the existing universal-cover normal forms and deck-group
description.  Translation loops and the affine generator are mapped by
the actual inclusion, so the resulting presentation retains its geometric
marking for arbitrary equivariant period data.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

variable {j : Kind} (D : Equivariant.Data j)

/-- The geometric affine-residue and lattice normal form for actual loops
in the supplied family's filling. -/
def fillingFundamentalGroupNormalFormEquiv (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) :
    FundamentalGroup (D.Space v hv)
        (D.centralFibreInclusion v hv (affineCoverProjection j D.centralPeriod v hv y)) ≃
      Fin j.order × Lattice :=
  (D.fillingSurfaceFundamentalGroupEquiv v hv
    (affineCoverProjection j D.centralPeriod v hv y)).symm.toEquiv.trans
      (surfaceFundamentalGroupNormalFormEquiv j D.centralPeriod v hv y)

@[simp] theorem fillingFundamentalGroupNormalFormEquiv_surface (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates)
    (γ : FundamentalGroup (Surface j D.centralPeriod v hv)
      (affineCoverProjection j D.centralPeriod v hv y)) :
    D.fillingFundamentalGroupNormalFormEquiv v hv y
        (FundamentalGroup.map (D.surfaceIntoFilling v hv)
          (affineCoverProjection j D.centralPeriod v hv y) γ) =
      surfaceFundamentalGroupNormalFormEquiv j D.centralPeriod v hv y γ := by
  change surfaceFundamentalGroupNormalFormEquiv j D.centralPeriod v hv y
    ((D.fillingSurfaceFundamentalGroupEquiv v hv _).symm
      (D.fillingSurfaceFundamentalGroupEquiv v hv _ γ)) = _
  rw [MulEquiv.symm_apply_apply]

/-- The actual loop group is the same affine deck group, via the
central-surface inclusion and the proved universal cover. -/
def fillingFundamentalGroupDeckEquiv (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) :
    FundamentalGroup (D.Space v hv)
        (D.centralFibreInclusion v hv (affineCoverProjection j D.centralPeriod v hv y)) ≃*
      AffineDeckGroup j v :=
  (D.fillingSurfaceFundamentalGroupEquiv v hv
    (affineCoverProjection j D.centralPeriod v hv y)).symm.trans
      (surfaceFundamentalGroupDeckEquiv j D.centralPeriod v hv y)

@[simp] theorem fillingFundamentalGroupDeckEquiv_surface (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates)
    (γ : FundamentalGroup (Surface j D.centralPeriod v hv)
      (affineCoverProjection j D.centralPeriod v hv y)) :
    D.fillingFundamentalGroupDeckEquiv v hv y
        (FundamentalGroup.map (D.surfaceIntoFilling v hv)
          (affineCoverProjection j D.centralPeriod v hv y) γ) =
      surfaceFundamentalGroupDeckEquiv j D.centralPeriod v hv y γ := by
  change surfaceFundamentalGroupDeckEquiv j D.centralPeriod v hv y
    ((D.fillingSurfaceFundamentalGroupEquiv v hv _).symm
      (D.fillingSurfaceFundamentalGroupEquiv v hv _ γ)) = _
  rw [MulEquiv.symm_apply_apply]

/-- The actual inclusion sends marked central translation loops into the filling. -/
def fillingTranslationHom (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) : Multiplicative Lattice →*
      FundamentalGroup (D.Space v hv)
        (D.centralFibreInclusion v hv (affineCoverProjection j D.centralPeriod v hv y)) :=
  (D.fillingSurfaceFundamentalGroupEquiv v hv
    (affineCoverProjection j D.centralPeriod v hv y)).toMonoidHom.comp
      (surfaceTranslationHom j D.centralPeriod v hv y)

/-- The actual inclusion sends the marked central affine loop into the filling. -/
def fillingAffineGenerator (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) : FundamentalGroup (D.Space v hv)
      (D.centralFibreInclusion v hv (affineCoverProjection j D.centralPeriod v hv y)) :=
  D.fillingSurfaceFundamentalGroupEquiv v hv
    (affineCoverProjection j D.centralPeriod v hv y)
    (surfaceAffineGenerator j D.centralPeriod v hv y)

@[simp] theorem fillingFundamentalGroupDeckEquiv_translation (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) (w : Multiplicative Lattice) :
    D.fillingFundamentalGroupDeckEquiv v hv y (D.fillingTranslationHom v hv y w) =
      deckTranslationHom j v w := by
  change D.fillingFundamentalGroupDeckEquiv v hv y
    (FundamentalGroup.map (D.surfaceIntoFilling v hv) _
      (surfaceTranslationHom j D.centralPeriod v hv y w)) = _
  rw [D.fillingFundamentalGroupDeckEquiv_surface, surfaceFundamentalGroupDeckEquiv_translation]

@[simp] theorem fillingFundamentalGroupDeckEquiv_generator (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    D.fillingFundamentalGroupDeckEquiv v hv y (D.fillingAffineGenerator v hv y) =
      deckGenerator j v := by
  change D.fillingFundamentalGroupDeckEquiv v hv y
    (FundamentalGroup.map (D.surfaceIntoFilling v hv) _
      (surfaceAffineGenerator j D.centralPeriod v hv y)) = _
  rw [D.fillingFundamentalGroupDeckEquiv_surface, surfaceFundamentalGroupDeckEquiv_generator]

theorem fillingTranslationHom_injective (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) : Function.Injective (D.fillingTranslationHom v hv y) :=
  (D.fillingSurfaceFundamentalGroupEquiv v hv _).injective.comp
    (surfaceTranslationHom_injective j D.centralPeriod v hv y)

/-- The monodromy relation holds for the geometrically marked filling loops. -/
theorem fillingAffineGenerator_translation (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) (w : Lattice) :
    D.fillingAffineGenerator v hv y *
        D.fillingTranslationHom v hv y (Multiplicative.ofAdd w) =
      D.fillingTranslationHom v hv y (Multiplicative.ofAdd (j.matrix *ᵥ w)) *
        D.fillingAffineGenerator v hv y := by
  apply (D.fillingFundamentalGroupDeckEquiv v hv y).injective
  simpa only [map_mul, D.fillingFundamentalGroupDeckEquiv_generator,
    D.fillingFundamentalGroupDeckEquiv_translation, latticeMonodromy_apply] using
      deckGenerator_translation j v w

theorem fillingAffineGenerator_conj_translation (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) (w : Lattice) :
    D.fillingAffineGenerator v hv y *
        D.fillingTranslationHom v hv y (Multiplicative.ofAdd w) *
        (D.fillingAffineGenerator v hv y)⁻¹ =
      D.fillingTranslationHom v hv y (Multiplicative.ofAdd (j.matrix *ᵥ w)) := by
  rw [D.fillingAffineGenerator_translation, mul_inv_cancel_right]

/-- The prescribed logarithmic twist is the affine generator's order power. -/
theorem fillingAffineGenerator_pow_order (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) :
    D.fillingAffineGenerator v hv y ^ j.order =
      D.fillingTranslationHom v hv y (Multiplicative.ofAdd v) := by
  apply (D.fillingFundamentalGroupDeckEquiv v hv y).injective
  simpa only [map_pow, D.fillingFundamentalGroupDeckEquiv_generator,
    D.fillingFundamentalGroupDeckEquiv_translation] using deckGenerator_pow_order j v hv.1

/-- These marked generators give unique affine normal forms for every loop. -/
theorem filling_normalForm_bijective (v : Lattice) (hv : AdmissibleTwist j v)
    (y : RealCoordinates) :
    Function.Bijective (CyclicNormalForms.normalForm
      (D.fillingTranslationHom v hv y) (D.fillingAffineGenerator v hv y) j.order) := by
  have he : CyclicNormalForms.normalForm (D.fillingTranslationHom v hv y)
      (D.fillingAffineGenerator v hv y) j.order =
      D.fillingSurfaceFundamentalGroupEquiv v hv
        (affineCoverProjection j D.centralPeriod v hv y) ∘
          CyclicNormalForms.normalForm (surfaceTranslationHom j D.centralPeriod v hv y)
            (surfaceAffineGenerator j D.centralPeriod v hv y) j.order := by
    funext a
    change D.fillingSurfaceFundamentalGroupEquiv v hv _
        (surfaceTranslationHom j D.centralPeriod v hv y (Multiplicative.ofAdd a.1)) *
        D.fillingSurfaceFundamentalGroupEquiv v hv _
          (surfaceAffineGenerator j D.centralPeriod v hv y) ^ a.2.val =
      D.fillingSurfaceFundamentalGroupEquiv v hv _
        (surfaceTranslationHom j D.centralPeriod v hv y (Multiplicative.ofAdd a.1) *
          surfaceAffineGenerator j D.centralPeriod v hv y ^ a.2.val)
    rw [map_mul, map_pow]
  rw [he]
  exact (D.fillingSurfaceFundamentalGroupEquiv v hv _).bijective.comp
    (surface_normalForm_bijective j D.centralPeriod v hv y)

/-- The actual filling group has the source's affine presentation. -/
theorem fillingFundamentalGroup_presentation {H : Type*} [Group H]
    (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates)
    (τ : Multiplicative Lattice →* H) (k : H)
    (hkconj : ∀ w, k * τ (Multiplicative.ofAdd w) =
      τ (Multiplicative.ofAdd (j.matrix *ᵥ w)) * k)
    (hkpow : k ^ j.order = τ (Multiplicative.ofAdd v)) :
    ∃! F : FundamentalGroup (D.Space v hv)
        (D.centralFibreInclusion v hv (affineCoverProjection j D.centralPeriod v hv y)) →* H,
      (∀ w, F (D.fillingTranslationHom v hv y (Multiplicative.ofAdd w)) =
        τ (Multiplicative.ofAdd w)) ∧ F (D.fillingAffineGenerator v hv y) = k :=
  CyclicNormalForms.existsUnique_hom_of_normalForms
    (D.fillingTranslationHom v hv y) (D.fillingAffineGenerator v hv y)
    j.order j.order_pos (latticeMonodromy j) v
    (D.fillingAffineGenerator_translation v hv y) (D.fillingAffineGenerator_pow_order v hv y)
    (D.filling_normalForm_bijective v hv y) τ k hkconj hkpow

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
