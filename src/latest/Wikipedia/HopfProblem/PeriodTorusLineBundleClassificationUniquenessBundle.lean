import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniquenessData
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniquenessGauge
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniquenessTheta

/-!
# Uniqueness of unitary data under actual holomorphic bundle isomorphism

The hypothesis is an analytic, fibre-linear isomorphism of the native
bundles constructed from the two data.  Its nonvanishing entire gauge is
derived from the actual total-space map.  The positivity and zero-form
theta theorems then determine both the Hermitian form and the arbitrary
unitary semicharacter.  No Appell--Humbert classification or universal-cover
triviality theorem is assumed here.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniqueness

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative

variable {p : PeriodDomain}

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

/-- A genuine holomorphic bundle isomorphism determines equality of all
unitary Appell--Humbert data, and its extracted gauge is constant. -/
theorem datum_eq_and_gauge_constant (D E : UnitaryDatum p)
    (e : BundleIso D.factor E.factor) :
    D = E ∧ ∀ z, gauge e z = gauge e 0 := by
  have h := hermitian_data_eq_of_nonvanishing_gauge p D.form E.form
    D.hermitian E.hermitian D.multiplier E.multiplier
    D.norm_multiplier E.norm_multiplier (gauge e)
    ((gauge_contDiff e).differentiable (by simp)) (gauge_ne_zero e)
    (fun l z => by
      simpa only [UnitaryDatum.factor_coe] using gauge_automorphy e l z)
  exact ⟨UnitaryDatum.ext h.1 h.2.1, h.2.2⟩

/-- Injectivity of the Appell--Humbert construction for actual native
holomorphic line bundles, including all unitary character twists. -/
theorem unitaryDatum_eq_of_bundleIso (D E : UnitaryDatum p)
    (e : BundleIso D.factor E.factor) : D = E :=
  (datum_eq_and_gauge_constant D E e).1

theorem unitaryDatum_eq_iff_nonempty_bundleIso (D E : UnitaryDatum p) :
    D = E ↔ Nonempty (BundleIso D.factor E.factor) := by
  constructor
  · intro h
    subst E
    exact ⟨AnalyticBundleIso.refl (I := IC) (Core.data D.factor).core.Fiber⟩
  · rintro ⟨e⟩
    exact unitaryDatum_eq_of_bundleIso D E e

/-- Every actual isomorphism has one constant nonzero scalar on the
universal-cover coordinates.  This formula refers to the original native
total-space map through the independently proved quotient identification. -/
theorem bundleIso_covering_formula (D E : UnitaryDatum p)
    (e : BundleIso D.factor E.factor) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ z c,
      e.diffeomorph (Core.fromAssociated D.factor (associatedMap D.factor (z, c))) =
        Core.fromAssociated E.factor (associatedMap E.factor (z, a * c)) := by
  refine ⟨gauge e 0, gauge_ne_zero e 0, ?_⟩
  intro z c
  apply Core.toAssociated_injective E.factor
  rw [Core.toAssociated_fromAssociated]
  change quotientMap e (associatedMap D.factor (z, c)) =
    associatedMap E.factor (z, gauge e 0 * c)
  rw [quotientMap_gauge, (datum_eq_and_gauge_constant D E e).2 z]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniqueness
