import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalCocycles
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalQuasiIsoCriteria

/-!
# Genuine positive singular cohomology equals cohomology of global cochain sheaves

The map is the original singular cochain map induced by the native
sheafification unit. Its native homology map is an isomorphism because
actual cocycles lift and actual boundaries are detected. No cohomology
object or cohomology map is replaced by a model in the conclusion.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})
  [NormalSpace X] [ParacompactSpace X]

/-- The actual global-unit comparison induces isomorphisms in every
positive degree, for every abelian coefficient group. -/
theorem globalCochainComparison_homology_isIso (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (globalCochainComparison X A) (n + 1)) := by
  apply GlobalQuasiIsoCriteria.isIso_homologyMap_succ_of_cycle_lifts
    (globalCochainComparison X A) n
  · exact globalCochainComparison_cycle_lift X A n
  · intro φ hφ hb
    obtain ⟨s, hs⟩ := hb
    exact globalCochainComparison_boundary_detect X A n φ hφ s hs

/-- The native positive cohomology isomorphism induced by the original
sheafification unit on the original singular cochain complex. -/
def globalCochainCohomologyIso (n : ℕ) :
    (singularCochainComplex X A).homology (n + 1) ≅
      (globalSheafCochainComplex X A).homology (n + 1) := by
  letI := globalCochainComparison_homology_isIso X A n
  exact asIso (HomologicalComplex.homologyMap (globalCochainComparison X A) (n + 1))

@[simp]
theorem globalCochainCohomologyIso_hom (n : ℕ) :
    (globalCochainCohomologyIso X A n).hom =
      HomologicalComplex.homologyMap (globalCochainComparison X A) (n + 1) := rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
