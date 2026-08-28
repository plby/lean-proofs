import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionData
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionGlobalBiproduct
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionForget
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionGlobalMaps

/-!
# The actual sheaf scalar endomorphisms induce the canonical global-complex scalar map
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution

open SheafResolution SheafCohomologyResolution SheafCohomologyGlobalSections
open CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

theorem normalizationScalar_global (c : ℂ) (s : Sections (normalizationSheaf C ε hε)) :
    (globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
      (normalizationScalarEnd C ε hε c) s = c • s := rfl

theorem curveScalar_global (k : Fin 3) (c : ℂ)
    (s : Sections (curveSheaf C ε hε hε1 hC hR k)) :
    (globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
      (curveScalarEnd C ε hε hε1 hC hR k c) s = c • s := rfl

theorem boundaryScalar_global (c : ℂ) (s : Sections (boundarySheaf C ε hε hε1 hC hR)) :
    (globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
      (boundaryScalarEnd C ε hε hε1 hC hR c) s = c • s :=
  finiteGlobalScalar_apply (curveSheaf C ε hε hε1 hC hR)
    (curveScalarEnd C ε hε hε1 hC hR) (curveScalar_global C ε hε hε1 hC hR) c s

theorem triplePointScalar_global (t : Fin 2) (c : ℂ)
    (s : Sections (triplePointSheaf C ε hε t)) :
    (globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
      (triplePointScalarEnd C ε hε t c) s = c • s := by
  apply (triplePointGlobalLinearEquiv C ε hε t).injective
  rw [map_smul]
  exact skyscraperScalarEnd_apply (X := TopCat.of (CentralSpace C ε))
    (triplePoint C ε hε t) c ⊤ (by trivial) s

theorem tripleScalar_global (c : ℂ) (s : Sections (tripleSheaf C ε hε)) :
    (globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
      (tripleScalarEnd C ε hε c) s = c • s :=
  finiteGlobalScalar_apply (triplePointSheaf C ε hε)
    (triplePointScalarEnd C ε hε) (triplePointScalar_global C ε hε) c s

/-- The actual global map of the sheaf scalar endomorphism is exactly the
forgotten complex-linear scalar map of the original section complex. -/
theorem globalScalarMap_eq (c : ℂ) :
    (scalarResolutionHom C ε hε hε1 hC hR c).globalMap =
      forgottenScalarMap (globalLinearComplex C ε hε hε1 hC hR) c := by
  apply ShortComplex.hom_ext
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact normalizationScalar_global C ε hε c s
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact boundaryScalar_global C ε hε hε1 hC hR c s
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact tripleScalar_global C ε hε c s

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
