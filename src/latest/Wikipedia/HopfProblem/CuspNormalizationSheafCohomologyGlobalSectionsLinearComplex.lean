import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsDifferentials
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsCoefficientComplex
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionCusp

/-!
# The actual global-section complex is the displayed complex, complex linearly

The arrows keep the actual sheaf-morphism components as their underlying
functions. Forgetting their proved complex linearity gives precisely the
global complex of the actual normalization augmented resolution.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

open SheafResolution SheafCohomologyResolution CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual first global-section arrow, with its proved complex linearity. -/
def globalDeltaZero : Sections (normalizationSheaf C ε hε) →ₗ[ℂ]
    Sections (boundarySheaf C ε hε hε1 hC hR) where
  toFun := (globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
    (deltaZero C ε hε hε1 hC hR)
  map_add' a b := map_add _ a b
  map_smul' c s := by
    rw [deltaZero_global_eq_zero]
    change (0 : Sections (boundarySheaf C ε hε hε1 hC hR)) = c • 0
    exact (smul_zero c).symm

/-- The actual last global-section arrow, with its proved complex linearity. -/
def globalDeltaOne : Sections (boundarySheaf C ε hε hε1 hC hR) →ₗ[ℂ]
    Sections (tripleSheaf C ε hε) where
  toFun := (globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
    (deltaOne C ε hε hε1 hC hR)
  map_add' a b := map_add _ a b
  map_smul' c s := by
    apply (tripleGlobalLinearEquiv C ε hε).injective
    funext t
    simp only [deltaOne_global_scalar, map_smul, Pi.smul_apply,
      smul_add, smul_sub, RingHom.id_apply]

/-- The complex of actual sections and actual arrows, now retaining
their pointwise complex vector-space structures. -/
def globalLinearComplex : ShortComplex (ModuleCat ℂ) :=
  ShortComplex.moduleCatMk (globalDeltaZero C ε hε hε1 hC hR)
    (globalDeltaOne C ε hε hε1 hC hR) (by
      apply LinearMap.ext
      intro s
      exact ConcreteCategory.congr_hom
        ((boundaryComplex C ε hε hε1 hC hR).map
          (globalSectionsFunctor (TopCat.of (CentralSpace C ε)))).zero s)

/-- Forgetting only the scalar structure gives the literal global
complex of the actual normalization resolution, with exactly its arrows. -/
theorem globalLinearComplex_forget :
    (globalLinearComplex C ε hε hε1 hC hR).map (forget₂ (ModuleCat ℂ) AddCommGrpCat) =
      (normalizationAugmentedResolution C ε hε hε1 hC hR).globalComplex := rfl

/-- The actual global complex is complex-linearly isomorphic to
ℂ →₀ ℂ³ → ℂ² with the two literal identical signed rows. -/
def globalCoefficientComplexIso : globalLinearComplex C ε hε hε1 hC hR ≅ coefficientComplex :=
  ShortComplex.isoMk (normalizationGlobalLinearEquiv C ε hε).toModuleIso
    (boundaryGlobalLinearEquiv C ε hε hε1 hC hR).toModuleIso
    (tripleGlobalLinearEquiv C ε hε).toModuleIso
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      change 0 = boundaryGlobalLinearEquiv C ε hε hε1 hC hR
        ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
          (deltaZero C ε hε hε1 hC hR) s)
      rw [deltaZero_global_eq_zero]
      exact (map_zero (boundaryGlobalLinearEquiv C ε hε hε1 hC hR)).symm)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      funext t
      exact (deltaOne_global_scalar C ε hε hε1 hC hR s t).symm)

/-- The actual boundary global-section space has dimension three. -/
theorem boundaryGlobal_finrank :
    Module.finrank ℂ (Sections (boundarySheaf C ε hε hε1 hC hR)) = 3 :=
  (boundaryGlobalLinearEquiv C ε hε hε1 hC hR).finrank_eq.trans (Module.finrank_fin_fun ℂ)

/-- The actual two-point global-section space has dimension two. -/
theorem tripleGlobal_finrank : Module.finrank ℂ (Sections (tripleSheaf C ε hε)) = 2 :=
  (tripleGlobalLinearEquiv C ε hε).finrank_eq.trans (Module.finrank_fin_fun ℂ)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
