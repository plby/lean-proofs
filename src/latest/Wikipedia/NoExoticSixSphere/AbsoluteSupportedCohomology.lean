import Wikipedia.NoExoticSixSphere.SupportedModTwoCohomology
import Wikipedia.NoExoticSixSphere.AbsoluteSupportedHomology

/-!
# Forgetting cohomology support through the original quotient projection

Support extension commutes with the original map to absolute cohomology.
For whole-space support the integral chain projection is an isomorphism,
so its actual cochain dual and cohomology map are isomorphisms as well.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X : Type} [TopologicalSpace X]

/-- The original cochain maps commute when the support is extended. -/
theorem extendCochain_toAbsolute {K L : Set X} (h : K ⊆ L) :
    extendCochain h ≫ RelativeModTwoCochains.toAbsoluteMap Lᶜ =
      RelativeModTwoCochains.toAbsoluteMap Kᶜ := by
  have he := RelativeCoefficients.projection_mapChain (ModuleCat.of ℤ ℤ)
    (ContinuousMap.id X)
    (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from fun _ hx hy => hx (h hy))
  rw [RelativeCoefficients.spaceMap_id, Category.id_comp] at he
  exact (ModTwoDualComplex.map_comp
    (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ) Lᶜ)
    (SupportedRelativeHomology.restrictChain (ModuleCat.of ℤ ℤ) h)).symm.trans
      (congrArg ModTwoDualComplex.map he)

/-- Forgetting support commutes with extension on genuine cohomology. -/
theorem toAbsolute_extend {K L : Set X} (h : K ⊆ L) (p : ℕ) (a : Cohomology K p) :
    RelativeModTwoCochains.toAbsoluteCohomology Lᶜ p (extend h p a) =
      RelativeModTwoCochains.toAbsoluteCohomology Kᶜ p a := by
  have he := congrArg (fun f : complex K ⟶ ModTwoCapProduct.cochainComplex X =>
    (HomologicalComplex.homologyMap f p).hom) (extendCochain_toAbsolute h)
  rw [HomologicalComplex.homologyMap_comp] at he
  exact LinearMap.congr_fun he a

/-- The original whole-support precomposition gives an actual cohomology equivalence. -/
def absoluteEquiv (p : ℕ) :
    Cohomology (Set.univ : Set X) p ≃ₗ[ℤ] ModTwoCapProduct.Cohomology X p := by
  have : IsIso (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ)
      ((Set.univ : Set X)ᶜ)) := by
    rw [Set.compl_univ]
    exact RelativeCoefficients.projection_empty_isIso (ModuleCat.of ℤ ℤ)
  let e := ModTwoDualComplex.mapIso
    (asIso (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ) ((Set.univ : Set X)ᶜ)))
  exact ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) p).mapIso
    e).toLinearEquiv

theorem absoluteEquiv_toLinearMap (p : ℕ) :
    (absoluteEquiv (X := X) p).toLinearMap =
      RelativeModTwoCochains.toAbsoluteCohomology ((Set.univ : Set X)ᶜ) p := rfl

end NoExoticSixSphere.SupportedModTwoCohomology
