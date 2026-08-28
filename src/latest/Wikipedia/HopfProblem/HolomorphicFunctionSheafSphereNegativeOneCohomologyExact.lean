import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneSheaf
import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationSheaf
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDolbeaultSheafExact

/-!
# The actual infinity-ideal short exact sequence on the sphere

The ideal is the original sheaf of holomorphic functions vanishing at
infinity.  Evaluation of actual holomorphic germs gives the morphism to
the actual scalar skyscraper.  Its kernel is the literal ideal on every
open set, and constant functions lift every skyscraper section.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneCohomology

open CuspNormalization.SheafEvaluation
open HolomorphicSheafCohomology.DolbeaultLocal

attribute [local instance] Classical.propDecidable

/-- The native complex scalar skyscraper supported at the actual infinity point. -/
abbrev infinitySkyscraper : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of RiemannSphere) :=
  scalarSkyscraper (∞ : RiemannSphere)

/-- The actual sheaf morphism induced by evaluation of original holomorphic germs. -/
def infinityEvaluation : sphereSheaf ⟶ infinitySkyscraper :=
  toSkyscraper sphereSheaf (∞ : RiemannSphere) (AddCommGrpCat.of ℂ)
    (AddCommGrpCat.ofHom (holomorphicStalkEval 𝓘(ℂ) (∞ : RiemannSphere)))

/-- On every neighborhood of infinity the map is literal function evaluation. -/
theorem infinityEvaluation_app (U : Opens RiemannSphere) (hU : (∞ : RiemannSphere) ∈ U)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) :
    (skyscraperSectionIso (X := TopCat.of RiemannSphere)
      ∞ (AddCommGrpCat.of ℂ) U hU).hom (infinityEvaluation.hom.app (op U) s) = s ⟨∞, hU⟩ := by
  exact (ConcreteCategory.congr_hom
    (toSkyscraper_app sphereSheaf (∞ : RiemannSphere) (AddCommGrpCat.of ℂ)
      (AddCommGrpCat.ofHom (holomorphicStalkEval 𝓘(ℂ) (∞ : RiemannSphere))) U hU) s).trans
    (holomorphicStalkEval_germ 𝓘(ℂ) U (∞ : RiemannSphere) hU s)

/-- Constant functions lift every skyscraper section; away from infinity
the target section group is terminal. -/
theorem infinityEvaluation_app_surjective (U : Opens RiemannSphere) :
    Function.Surjective (infinityEvaluation.hom.app (op U)) := by
  intro t
  by_cases hU : (∞ : RiemannSphere) ∈ U
  · let e := skyscraperSectionIso (X := TopCat.of RiemannSphere)
      ∞ (AddCommGrpCat.of ℂ) U hU
    let s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U :=
      ⟨fun _ => e.hom t, contMDiff_const⟩
    refine ⟨s, ?_⟩
    apply e.addCommGroupIsoToAddEquiv.injective
    exact infinityEvaluation_app U hU s
  · refine ⟨0, ?_⟩
    apply AddCommGrpCat.asHom_injective
    exact (skyscraperSectionIsTerminal (X := TopCat.of RiemannSphere)
      ∞ (AddCommGrpCat.of ℂ) U hU).hom_ext _ _

/-- The original infinity-ideal inclusion is a monomorphism of actual sheaves. -/
instance negativeOneInclusion_mono : Mono negativeOneInclusion := by
  let : ∀ U : (Opens (TopCat.of RiemannSphere))ᵒᵖ,
      Mono (negativeOneInclusion.hom.app U) := fun U =>
    ConcreteCategory.mono_of_injective _ (negativeOneInclusion_app_injective U.unop)
  let : Mono negativeOneInclusion.hom := NatTrans.mono_of_mono_app _
  exact CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono
    (Opens.grothendieckTopology (TopCat.of RiemannSphere)) AddCommGrpCat negativeOneInclusion

/-- Actual component surjectivity makes evaluation an epimorphism of sheaves. -/
instance infinityEvaluation_epi : Epi infinityEvaluation := by
  let : ∀ U : (Opens (TopCat.of RiemannSphere))ᵒᵖ,
      Epi (infinityEvaluation.hom.app U) := fun U =>
    ConcreteCategory.epi_of_surjective _ (infinityEvaluation_app_surjective U.unop)
  let : Epi infinityEvaluation.hom := NatTrans.epi_of_epi_app _
  exact CategoryTheory.Sheaf.Hom.epi_of_presheaf_epi
    (Opens.grothendieckTopology (TopCat.of RiemannSphere)) AddCommGrpCat infinityEvaluation

/-- Actual ideal sections evaluate to zero at infinity. -/
theorem negativeOneInclusion_infinityEvaluation :
    negativeOneInclusion ≫ infinityEvaluation = 0 := by
  apply skyscraper_hom_ext
  intro U hU
  apply AddCommGrpCat.ext
  intro s
  change (skyscraperSectionIso (X := TopCat.of RiemannSphere)
      ∞ (AddCommGrpCat.of ℂ) U hU).hom (infinityEvaluation.hom.app (op U) s.val) =
    (skyscraperSectionIso (X := TopCat.of RiemannSphere)
      ∞ (AddCommGrpCat.of ℂ) U hU).hom 0
  exact (infinityEvaluation_app U hU s.val).trans
    ((s.property hU).trans
      (skyscraperSectionIso (X := TopCat.of RiemannSphere)
        ∞ (AddCommGrpCat.of ℂ) U hU).hom.hom.map_zero.symm)

/-- The original ideal, holomorphic sheaf, and actual scalar skyscraper. -/
abbrev idealComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0}
    (TopCat.of RiemannSphere)) :=
  ShortComplex.mk negativeOneInclusion infinityEvaluation negativeOneInclusion_infinityEvaluation

/-- The actual section kernel is exactly the original vanishing ideal. -/
theorem idealComplex_exact : idealComplex.Exact := by
  apply exact_of_section_kernels idealComplex
  intro U s hs
  refine ⟨⟨s, ?_⟩, rfl⟩
  intro hU
  exact (infinityEvaluation_app U hU s).symm.trans
    ((congrArg (skyscraperSectionIso (X := TopCat.of RiemannSphere)
      ∞ (AddCommGrpCat.of ℂ) U hU).hom hs).trans
      (skyscraperSectionIso (X := TopCat.of RiemannSphere)
        ∞ (AddCommGrpCat.of ℂ) U hU).hom.hom.map_zero)

/-- The genuine short exact sequence `0 → O(-∞) → O → C_∞ → 0`. -/
theorem idealComplex_shortExact : idealComplex.ShortExact :=
  { exact := idealComplex_exact }

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneCohomology
