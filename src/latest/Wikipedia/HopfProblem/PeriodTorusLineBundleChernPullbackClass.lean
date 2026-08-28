import Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullbackFactor
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullbackPeriods
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernClassEvaluation

/-!
# Naturality of the genuine first Chern class under compatible linear pullback

The actual period loops and their native homology products are transported
by the descended torus map.  Their proved Chern-number evaluations and the
exact pulled-back logarithmic pairing then identify the native singular
cohomology classes.  No map on cohomology or Chern-class formula is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomologyPontryagin PeriodTorusCohomology
open PeriodTorusAppellHumbert PeriodTorusLineBundleClassification
open PeriodTorusLineBundle.Chern

variable {p q : PeriodDomain} (L : LatticeLinearMap p q) (F : FactorOfAutomorphy q)

/-- The pulled-back native factor bundle has the pulled-back genuine first Chern class. -/
theorem firstChernClass_pullback :
    firstChernClass (pullbackFactor L F) =
      singularCohomologyPullback L.torusContinuousMap 2 (firstChernClass F) := by
  apply cohomology_ext_periodLoops p
  intro x y
  rw [firstChernClass_evaluate_periodLoops, factorLogAlternatingForm_pullback,
    singularEvaluation_naturality, L.torusContinuousMap_product11_periodLoops,
    firstChernClass_evaluate_periodLoops, L.coordinateMap_symm, L.coordinateMap_symm]

/-- Literal integral periods keep the sign fixed by the original positive period loops. -/
theorem firstChernClass_pullback_evaluate_periodLoops (x y : Lattice) :
    singularEvaluation p.Torus 2 (firstChernClass (pullbackFactor L F))
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) =
      -factorLogAlternatingForm F (L.latticeMap (p.latticeEquiv.symm x))
        (L.latticeMap (p.latticeEquiv.symm y)) := by
  rw [firstChernClass_evaluate_periodLoops, factorLogAlternatingForm_pullback]

end Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback
