import Wikipedia.HopfProblem.EllipticFirstHomologyDual
import Wikipedia.HopfProblem.EllipticFirstHomologyGroups

/-!
# Integral characters of the actual elliptic loop-group abelianizations

The translation-compatible equivalences with the actual affine deck
abelianization transport the dual restriction calculation to the actual
surface and filling fundamental groups. The resulting image and unique
extension statements concern their genuine abelianizations; no comparison
with singular cohomology is assumed.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic

/-- Transport integral additive characters through an integral linear
equivalence by precomposing with its inverse. -/
def integerCharacterTransport {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃ₗ[ℤ] B) : (A →+ ℤ) ≃ₗ[ℤ] (B →+ ℤ) :=
  e.toAddEquiv.addMonoidHomCongrLeft.toIntLinearEquiv

@[simp] theorem integerCharacterTransport_apply {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] (e : A ≃ₗ[ℤ] B) (f : A →+ ℤ) (b : B) :
    integerCharacterTransport e f b = f (e.symm b) := rfl

section Surface

variable (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates)

/-- Restrict a character of the actual surface loop-group abelianization
along its actual marked lattice translations. -/
def surfaceAbelianRestriction :
    (SurfaceAbelianization j p v hv y →+ ℤ) →ₗ[ℤ] (Lattice →ₗ[ℤ] ℤ) where
  toFun f := f.toIntLinearMap.comp (surfaceAbelianTranslation j p v hv y)
  map_add' f g := by apply LinearMap.ext; intro w; rfl
  map_smul' a f := by apply LinearMap.ext; intro w; rfl

@[simp] theorem surfaceAbelianRestriction_apply
    (f : SurfaceAbelianization j p v hv y →+ ℤ) (w : Lattice) :
    surfaceAbelianRestriction j p v hv y f w =
      f (surfaceAbelianTranslation j p v hv y w) := rfl

def surfaceAbelianCharacterDeckEquiv :
    (SurfaceAbelianization j p v hv y →+ ℤ) ≃ₗ[ℤ] (DeckAbelianization j v →+ ℤ) :=
  integerCharacterTransport (surfaceAbelianizationDeckEquiv j p v hv y)

/-- The actual translation marking intertwines the two restriction maps. -/
theorem surfaceAbelianRestriction_eq_deck
    (f : SurfaceAbelianization j p v hv y →+ ℤ) :
    surfaceAbelianRestriction j p v hv y f =
      deckAbelianRestriction j v (surfaceAbelianCharacterDeckEquiv j p v hv y f) := by
  apply LinearMap.ext
  intro w
  change f (surfaceAbelianTranslation j p v hv y w) =
    f ((surfaceAbelianizationDeckEquiv j p v hv y).symm (deckAbelianTranslation j v w))
  rw [← surfaceAbelianizationDeckEquiv_translation j p v w hv y,
    LinearEquiv.symm_apply_apply]

theorem surfaceAbelianRestriction_eq_comp :
    surfaceAbelianRestriction j p v hv y =
      (deckAbelianRestriction j v).comp
        (surfaceAbelianCharacterDeckEquiv j p v hv y).toLinearMap := by
  apply LinearMap.ext
  exact surfaceAbelianRestriction_eq_deck j p v hv y

theorem surfaceAbelianRestriction_injective :
    Function.Injective (surfaceAbelianRestriction j p v hv y) := by
  rw [surfaceAbelianRestriction_eq_comp]
  exact (deckAbelianRestriction_injective j v hv).comp
    (surfaceAbelianCharacterDeckEquiv j p v hv y).injective

theorem surfaceAbelianRestriction_range_eq_deck :
    LinearMap.range (surfaceAbelianRestriction j p v hv y) =
      LinearMap.range (deckAbelianRestriction j v) := by
  rw [surfaceAbelianRestriction_eq_comp]
  exact LinearMap.range_comp_of_range_eq_top _
    (surfaceAbelianCharacterDeckEquiv j p v hv y).range

/-- Exact image of restriction from actual surface loop-group characters. -/
theorem surfaceAbelianRestriction_range (ξ : Lattice →ₗ[ℤ] ℤ) :
    ξ ∈ LinearMap.range (surfaceAbelianRestriction j p v hv y) ↔
      (∀ w, ξ (j.matrix *ᵥ w) = ξ w) ∧ (j.order : ℤ) ∣ ξ v := by
  rw [surfaceAbelianRestriction_range_eq_deck]
  exact deckAbelianRestriction_range j v hv ξ

theorem surfaceAbelianRestriction_range_coefficients (ξ : Lattice →ₗ[ℤ] ℤ) :
    ξ ∈ LinearMap.range (surfaceAbelianRestriction j p v hv y) ↔
      ∃ c : Fin 2 → ℤ, ξ = coinvariantFunctional j c ∧
        (j.order : ℤ) ∣ γ v * c 0 + psi j v * c 1 := by
  rw [surfaceAbelianRestriction_range_eq_deck]
  exact deckAbelianRestriction_range_coefficients j v hv ξ

theorem existsUnique_surfaceAbelian_extension (ξ : Lattice →ₗ[ℤ] ℤ)
    (hξ : ∀ w, ξ (j.matrix *ᵥ w) = ξ w) (hdiv : (j.order : ℤ) ∣ ξ v) :
    ∃! f : SurfaceAbelianization j p v hv y →+ ℤ,
      surfaceAbelianRestriction j p v hv y f = ξ := by
  obtain ⟨f, hf⟩ := (surfaceAbelianRestriction_range j p v hv y ξ).mpr ⟨hξ, hdiv⟩
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact surfaceAbelianRestriction_injective j p v hv y (hg.trans hf.symm)

end Surface

section Filling

variable (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates)

/-- Restrict a character of the actual filling loop-group abelianization
along its actual marked lattice translations. -/
def fillingAbelianRestriction :
    (FillingAbelianization j v hv y →+ ℤ) →ₗ[ℤ] (Lattice →ₗ[ℤ] ℤ) where
  toFun f := f.toIntLinearMap.comp (fillingAbelianTranslation j v hv y)
  map_add' f g := by apply LinearMap.ext; intro w; rfl
  map_smul' a f := by apply LinearMap.ext; intro w; rfl

@[simp] theorem fillingAbelianRestriction_apply
    (f : FillingAbelianization j v hv y →+ ℤ) (w : Lattice) :
    fillingAbelianRestriction j v hv y f w = f (fillingAbelianTranslation j v hv y w) := rfl

def fillingAbelianCharacterDeckEquiv :
    (FillingAbelianization j v hv y →+ ℤ) ≃ₗ[ℤ] (DeckAbelianization j v →+ ℤ) :=
  integerCharacterTransport (fillingAbelianizationDeckEquiv j v hv y)

theorem fillingAbelianRestriction_eq_deck
    (f : FillingAbelianization j v hv y →+ ℤ) :
    fillingAbelianRestriction j v hv y f =
      deckAbelianRestriction j v (fillingAbelianCharacterDeckEquiv j v hv y f) := by
  apply LinearMap.ext
  intro w
  change f (fillingAbelianTranslation j v hv y w) =
    f ((fillingAbelianizationDeckEquiv j v hv y).symm (deckAbelianTranslation j v w))
  rw [← fillingAbelianizationDeckEquiv_translation j v w hv y,
    LinearEquiv.symm_apply_apply]

theorem fillingAbelianRestriction_eq_comp :
    fillingAbelianRestriction j v hv y =
      (deckAbelianRestriction j v).comp
        (fillingAbelianCharacterDeckEquiv j v hv y).toLinearMap := by
  apply LinearMap.ext
  exact fillingAbelianRestriction_eq_deck j v hv y

theorem fillingAbelianRestriction_injective :
    Function.Injective (fillingAbelianRestriction j v hv y) := by
  rw [fillingAbelianRestriction_eq_comp]
  exact (deckAbelianRestriction_injective j v hv).comp
    (fillingAbelianCharacterDeckEquiv j v hv y).injective

theorem fillingAbelianRestriction_range_eq_deck :
    LinearMap.range (fillingAbelianRestriction j v hv y) =
      LinearMap.range (deckAbelianRestriction j v) := by
  rw [fillingAbelianRestriction_eq_comp]
  exact LinearMap.range_comp_of_range_eq_top _
    (fillingAbelianCharacterDeckEquiv j v hv y).range

/-- The actual filling characters have the same invariant-and-divisibility
image as the surface characters. -/
theorem fillingAbelianRestriction_range (ξ : Lattice →ₗ[ℤ] ℤ) :
    ξ ∈ LinearMap.range (fillingAbelianRestriction j v hv y) ↔
      (∀ w, ξ (j.matrix *ᵥ w) = ξ w) ∧ (j.order : ℤ) ∣ ξ v := by
  rw [fillingAbelianRestriction_range_eq_deck]
  exact deckAbelianRestriction_range j v hv ξ

theorem fillingAbelianRestriction_range_coefficients (ξ : Lattice →ₗ[ℤ] ℤ) :
    ξ ∈ LinearMap.range (fillingAbelianRestriction j v hv y) ↔
      ∃ c : Fin 2 → ℤ, ξ = coinvariantFunctional j c ∧
        (j.order : ℤ) ∣ γ v * c 0 + psi j v * c 1 := by
  rw [fillingAbelianRestriction_range_eq_deck]
  exact deckAbelianRestriction_range_coefficients j v hv ξ

theorem existsUnique_fillingAbelian_extension (ξ : Lattice →ₗ[ℤ] ℤ)
    (hξ : ∀ w, ξ (j.matrix *ᵥ w) = ξ w) (hdiv : (j.order : ℤ) ∣ ξ v) :
    ∃! f : FillingAbelianization j v hv y →+ ℤ,
      fillingAbelianRestriction j v hv y f = ξ := by
  obtain ⟨f, hf⟩ := (fillingAbelianRestriction_range j v hv y ξ).mpr ⟨hξ, hdiv⟩
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact fillingAbelianRestriction_injective j v hv y (hg.trans hf.symm)

end Filling

/-- The source's chosen surface twists give exactly `⟨3γ,ψ₁⟩` and
`⟨4γ,ψ₂⟩` as the actual integral-character restriction images. -/
theorem mainSurfaceAbelianRestriction_range (j : Kind) (p : FixedPeriod j)
    (y : RealCoordinates) :
    LinearMap.range (surfaceAbelianRestriction j p j.twist (mainTwist_admissible j) y) =
      Submodule.span ℤ
        {((j.order : ℤ) • (LinearMap.proj 0 : Lattice →ₗ[ℤ] ℤ)), psi j} := by
  rw [surfaceAbelianRestriction_range_eq_deck, mainDeckAbelianRestriction_range]

/-- The same source markings hold for the actual elliptic fillings. -/
theorem mainFillingAbelianRestriction_range (j : Kind) (y : RealCoordinates) :
    LinearMap.range (fillingAbelianRestriction j j.twist (mainTwist_admissible j) y) =
      Submodule.span ℤ
        {((j.order : ℤ) • (LinearMap.proj 0 : Lattice →ₗ[ℤ] ℤ)), psi j} := by
  rw [fillingAbelianRestriction_range_eq_deck, mainDeckAbelianRestriction_range]

end Wikipedia.HopfProblem.Elliptic
