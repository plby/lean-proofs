import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibreMap
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClass
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardComparison

/-!
# The actual cohomology class of a literally restricted Čech cocycle

The constructed space-changing extension map identifies the genuine
cohomology map with the class of the restricted cocycle. For a finite
closed map, the original exact-pushforward comparison is an equivalence,
so this gives the literal restriction formula in the source cohomology.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechFibre

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension
open CuspNormalization.SheafCohomologyFinitePushforward

private theorem extClass_comparison
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [HasExt.{0} C] [HasExt.{0} D]
    {S : ShortComplex C} {E : ShortComplex D}
    (hS : S.ShortExact) (hE : E.ShortExact) (φ : E ⟶ S.map R) :
    hE.extClass.comp (Ext.mk₀ φ.τ₁) (add_zero 1) =
      ExtComparison.comparison R φ.τ₃ S.X₁ 1 hS.extClass := by
  change hE.extClass.comp (Ext.mk₀ φ.τ₁) (add_zero 1) =
    (Ext.mk₀ φ.τ₃).comp (hS.extClass.mapExactFunctor R) (zero_add 1)
  rw [Ext.mapExactFunctor_extClass]
  exact hE.extClass_naturality (hS.map_of_exact R) φ

variable {T X : TopCat.{0}} [T2Space T] (f : T ⟶ X)
  (hf : IsClosedMap f) (hfinite : ∀ x : X, (f ⁻¹' {x}).Finite)
  {F : AbelianSheaf X} {G : AbelianSheaf T}
  (κ : F ⟶ (pushforward f).obj G) {ι : Type} {U : ι → Opens X}
  (c : CechOneCocycle F U) (hU : ∀ x : X, ∃ j : ι, x ∈ U j)

/-- The original cohomology map sends the original Čech class to the
canonical finite-pushforward image of the literally restricted class. -/
theorem map_classOf :
    CategoryTheory.Sheaf.H.map κ 1 (classOf c hU) =
      cohomologyForward f hf hfinite G 1
        (classOf (pullbackCocycle f κ c) (pullbackCover_covers f hU)) := by
  exact @extClass_comparison
    (AbelianSheaf T) (AbelianSheaf X) _ _ _ _ (pushforward f) (pushforward_additive f)
    (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
    (pushforward_preservesFiniteColimits f hf hfinite)
    (abelianSheaf_hasExt T) (abelianSheaf_hasExt X)
    (complex (pullbackCocycle f κ c)) (complex c)
    (complex_shortExact (pullbackCocycle f κ c) (pullbackCover_covers f hU))
    (complex_shortExact c hU) (pullbackComplexMap f κ c)

/-- Actual finite closed pushforward comparison identifies cohomology
restriction with literal restriction of the original Čech cocycle. -/
theorem cohomologyEquiv_map_classOf :
    cohomologyEquiv f hf hfinite G 1
        (CategoryTheory.Sheaf.H.map κ 1 (classOf c hU)) =
      classOf (pullbackCocycle f κ c) (pullbackCover_covers f hU) := by
  rw [map_classOf f hf hfinite κ c hU]
  exact (cohomologyEquiv f hf hfinite G 1).apply_symm_apply _

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechFibre
