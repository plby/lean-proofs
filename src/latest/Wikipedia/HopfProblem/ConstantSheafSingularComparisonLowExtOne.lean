import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtTruncation
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections

/-!
# Native degree-one sheaf cohomology from a cochain resolution

Global sections are evaluated on the top open set. The map from the
truncated complex is the actual inclusion of cycles, so its homology
comparison retains the canonical map of the full complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt

open CuspNormalization.SheafCohomologyResolution

namespace CochainResolution

variable {X : TopCat.{0}} (R : CochainResolution (TopCat.Sheaf AddCommGrpCat.{0} X))

/-- Literal global sections, degree by degree, of the original complex. -/
def globalCochainComplex : CochainComplex AddCommGrpCat.{0} ℕ :=
  ((globalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℕ)).obj R.K

/-- The actual inclusion of the truncated global section complex. -/
def globalShortInclusion : R.truncation.globalComplex ⟶
    R.globalCochainComplex.sc' 0 1 2 :=
  (globalSectionsFunctor X).mapShortComplex.map R.shortInclusion

instance globalShortInclusion_quasiIso : ShortComplex.QuasiIso R.globalShortInclusion := by
  have : Epi R.globalShortInclusion.τ₁ := by
    change Epi ((globalSectionsFunctor X).map (𝟙 (R.K.X 0)))
    rw [(globalSectionsFunctor X).map_id]
    infer_instance
  have : IsIso R.globalShortInclusion.τ₂ := by
    change IsIso ((globalSectionsFunctor X).map (𝟙 (R.K.X 1)))
    rw [(globalSectionsFunctor X).map_id]
    infer_instance
  have : Mono R.globalShortInclusion.τ₃ :=
    inferInstanceAs (Mono ((globalSectionsFunctor X).map (kernel.ι (R.K.d 2 3))))
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono R.globalShortInclusion

/-- The canonical degree-one homology comparison induced by the
actual inclusion of the truncated complex. -/
def globalFirstHomologyIso : R.truncation.globalComplex.homology ≅
    R.globalCochainComplex.homology 1 :=
  asIso (ShortComplex.homologyMap R.globalShortInclusion) ≪≫
    (ShortComplex.homologyMapIso
      (R.globalCochainComplex.isoSc' 0 1 2
        ((ComplexShape.up ℕ).prev_eq' (by rfl))
        ((ComplexShape.up ℕ).next_eq' (by rfl)))).symm

/-- Genuine native degree-one sheaf cohomology is the actual
degree-one homology of global sections of the cochain resolution. -/
def h1Iso [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 1) ≅
      R.globalCochainComplex.homology 1 := by
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)›
  exact R.truncation.h1Iso ≪≫ R.globalFirstHomologyIso

end CochainResolution

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt
