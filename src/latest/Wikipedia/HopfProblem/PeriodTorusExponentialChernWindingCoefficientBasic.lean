import Wikipedia.HopfProblem.PeriodTorusExponentialChernCoefficients
import Wikipedia.HopfProblem.PeriodTorusExponentialChernLocalLifts
import Wikipedia.HopfProblem.ExponentialChernComparisonLocalCochains
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernClass

/-!
# The original winding cochain with exponential coefficients

This is literal coefficient postcomposition of the previously constructed
native boundary-winding cochain by the original map `n ↦ 2πi n`.
Closedness follows from the actual cochain map.  The comparison with the
negative factor-log cochain is a theorem about those same cochains and
the actual lattice labels, not the definition of a Chern class.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusExponentialChern

open FirstHurewicz ConstantSheafSingularComparison
open PeriodTorusAppellHumbert PeriodTorusLineBundleChernLog
open PeriodTorusLineBundle.ChernCocycle
open ExponentialChernComparison

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- The actual native winding cochain, postcomposed with the original
ordinary-exponential coefficient map. -/
def windingComplexCochain : Cochains p.Torus (AddCommGrpCat.of ℂ) 2 :=
  (coefficientMap p.Torus
    (AddCommGrpCat.ofHom HolomorphicExponentialSheaf.integerScalarHom)).f 2
      (PeriodTorusLineBundle.Chern.firstChernCochain F).toAddMonoidHom

/-- This is the literal original native-source cochain map. -/
theorem windingComplexCochain_eq_native_map :
    windingComplexCochain F = (Coefficients.exponentialCochainMap p).f 2
      (PeriodTorusLineBundle.Chern.firstChernCochain F) := rfl

@[simp]
theorem windingComplexCochain_apply (c : Chains p.Torus 2) :
    windingComplexCochain F c =
      (PeriodTorusLineBundle.Chern.firstChernCochain F c : ℂ) * logPeriod := rfl

/-- Closedness of the original winding cochain survives the actual
coefficient chain map. -/
theorem windingComplexCochain_closed :
    (singularCochainComplex p.Torus (AddCommGrpCat.of ℂ)).d 2 3
      (windingComplexCochain F) = 0 := by
  have h := ConcreteCategory.congr_hom ((Coefficients.exponentialCochainMap p).comm 2 3)
    (PeriodTorusLineBundle.Chern.firstChernCochain F)
  change (singularCochainComplex p.Torus (AddCommGrpCat.of ℂ)).d 2 3
      (windingComplexCochain F) =
    (Coefficients.exponentialCochainMap p).f 3
      (((SingularCohomologyFree.singularCochainComplex p.Torus).d 2 3).hom
        (PeriodTorusLineBundle.Chern.firstChernCochain F)) at h
  rw [PeriodTorusLineBundle.Chern.firstChernCochain_closed] at h
  exact h.trans ((Coefficients.exponentialCochainMap p).f 3).hom.map_zero

/-- The same closedness in the native short-complex kernel convention. -/
theorem windingComplexCochain_closed_sc :
    ((singularCochainComplex p.Torus (AddCommGrpCat.of ℂ)).sc 2).g
      (windingComplexCochain F) = 0 := by
  change (singularCochainComplex p.Torus (AddCommGrpCat.of ℂ)).d 2
    ((ComplexShape.up ℕ).next 2) (windingComplexCochain F) = 0
  rw [CochainComplex.next]
  exact windingComplexCochain_closed F

/-- Forgetting only scalar structure, the original winding cochain is
the negative factor cocycle evaluated on the actual lattice edge labels. -/
theorem windingIntegralCochain_eq_neg :
    (PeriodTorusLineBundle.Chern.firstChernCochain F).toAddMonoidHom =
      -LocalCochains.integralTwoCochain (latticeEdgeCocycle p) (factorCocycle F) := by
  rw [PeriodTorusLineBundle.Chern.firstChernCochain_eq_twoCochain,
    twoCochain_neg, factorCoordinateCocycle, twoCochain_comap,
    LocalCochains.integralTwoCochain_eq_original]
  rfl

/-- The literal complex winding cochain equals the negative period
multiple of the original logarithmic cocycle, with its actual labels. -/
theorem windingComplexCochain_eq_neg_periodTwoCochain :
    windingComplexCochain F =
      -LocalCochains.periodTwoCochain (latticeEdgeCocycle p) (factorCocycle F)
        logPeriod := by
  rw [windingComplexCochain, windingIntegralCochain_eq_neg, map_neg,
    LocalCochains.periodTwoCochain_eq_coefficientMap]
  rfl

end Wikipedia.HopfProblem.PeriodTorusExponentialChern
