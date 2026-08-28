import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationRealModelPeriodicity
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochain
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneCriterion

/-!
# Every actual holomorphic factor has a type `(1,1)` integral form

The integer coefficients are extracted from the actual logarithmic
commutator. A smooth primitive of the constructed additive cocycle is
produced by the lattice partition theorem, and actual torus averaging
then proves the type condition. No Appell--Humbert classification, Chern
comparison, or type condition is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusAppellHumbert PeriodTorusTypeOneOne

/-- Type `(1,1)` is a consequence of the holomorphic cocycle laws of the
given actual factor of automorphy. -/
theorem factorIntegralCoefficients_typeOneOne {p : PeriodDomain}
    (F : FactorOfAutomorphy p) : IsTypeOneOne (tangentForm p (factorIntegralCoefficients F)) := by
  obtain ⟨u, hu, hshift⟩ :=
    PeriodTorusLineBundleClassificationLatticeCochain.exists_smooth_lattice_coboundary p
      (realModelCocycle_contDiff F) (realModelCocycle_add F)
  exact factor_typeOneOne_of_realModel_primitive F hu hshift

/-- The source period polynomial vanishes for the actual factor's derived
integer alternating coefficients. -/
theorem factorIntegralCoefficients_periodPolynomial {p : PeriodDomain}
    (F : FactorOfAutomorphy p) : periodPolynomial p.val (factorIntegralCoefficients F) = 0 :=
  (tangentForm_isTypeOneOne_iff p (factorIntegralCoefficients F)).mp
    (factorIntegralCoefficients_typeOneOne F)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
