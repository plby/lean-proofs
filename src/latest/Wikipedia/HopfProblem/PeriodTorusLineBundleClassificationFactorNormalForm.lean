import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorNormalFormGauge
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationAdditiveNormalForm
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCharacterGaugeIso
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniquenessBundle

/-!
# Appell--Humbert normal form for every actual holomorphic factor

Every genuine factor of automorphy is transformed to unitary
Appell--Humbert data by a constructed nowhere-zero entire gauge. The
gauge gives an actual analytic, fibrewise linear isomorphism of native
line bundles. The previously proved geometric uniqueness theorem makes
the resulting unitary data unique.

No logarithm, integer adjustment, type condition, smooth or periodic
primitive, character decomposition, or entire gauge is assumed here.
Descent from an arbitrary native bundle, as opposed to an actual factor,
is a separate theorem.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationUniqueness
open scoped ContDiff

variable {p : PeriodDomain}

/-- Every actual factor admits a genuine entire unitary Appell--Humbert
gauge, with no classification hypothesis. -/
theorem exists_unitaryDatum_gauge (F : FactorOfAutomorphy p) :
    ∃ (D : UnitaryDatum p) (a : ComplexPlane₂ → ℂ), ContDiff ℂ ω a ∧
      (∀ z, a z ≠ 0) ∧ ∀ l : p.lattice, ∀ z,
        a (z + l) * (D.factor.factor l z : ℂ) = (F.factor l z : ℂ) * a z := by
  obtain ⟨c, g, hg, hk⟩ := exists_holomorphic_additive_normal_form p
    (factorComparisonLog_holomorphic F) (factorComparisonLog_add F)
  exact ⟨normalizedFactorDatum F (normalizingCharacter c), normalizingGauge (p := p) c g,
    normalizingGauge_holomorphic (p := p) c hg, normalizingGauge_ne_zero (p := p) c g,
    normalizedFactorDatum_gauge_relation F c g hk⟩

/-- The normal form is an isomorphism of the actual native holomorphic
line bundles, not only a scalar factor identity. -/
theorem exists_unitaryDatum_bundleIso (F : FactorOfAutomorphy p) :
    ∃ D : UnitaryDatum p, Nonempty (BundleIso D.factor F) := by
  obtain ⟨D, a, ha, hne, hrel⟩ := exists_unitaryDatum_gauge F
  exact ⟨D, ⟨gaugeBundleIso D.factor F a ha hne hrel⟩⟩

/-- The constructed Hermitian form is exactly the form attached to the
actual integral logarithmic coefficients, with no sign relabeling. -/
theorem exists_unitaryDatum_bundleIso_with_form (F : FactorOfAutomorphy p) :
    ∃ D : UnitaryDatum p,
      D.form = integralHermitian p (factorIntegralCoefficients F)
        (factorIntegralCoefficients_typeOneOne F) ∧ Nonempty (BundleIso D.factor F) := by
  obtain ⟨c, g, hg, hk⟩ := exists_holomorphic_additive_normal_form p
    (factorComparisonLog_holomorphic F) (factorComparisonLog_add F)
  refine ⟨normalizedFactorDatum F (normalizingCharacter c), rfl, ?_⟩
  exact ⟨gaugeBundleIso _ F (normalizingGauge (p := p) c g)
    (normalizingGauge_holomorphic (p := p) c hg)
    (normalizingGauge_ne_zero (p := p) c g)
    (normalizedFactorDatum_gauge_relation F c g hk)⟩

/-- Every native unitary normal form has the same explicitly derived
Hermitian form. -/
theorem unitaryDatum_form_eq_factorIntegral (F : FactorOfAutomorphy p)
    (D : UnitaryDatum p) (e : BundleIso D.factor F) :
    D.form = integralHermitian p (factorIntegralCoefficients F)
      (factorIntegralCoefficients_typeOneOne F) := by
  obtain ⟨E, hE, ⟨eE⟩⟩ := exists_unitaryDatum_bundleIso_with_form F
  have hDE := unitaryDatum_eq_of_bundleIso D E (e.trans eE.symm)
  rw [hDE]
  exact hE

/-- Existence and uniqueness for arbitrary genuine factors, retaining the
full unitary semicharacter as part of the data. -/
theorem existsUnique_unitaryDatum_bundleIso (F : FactorOfAutomorphy p) :
    ∃! D : UnitaryDatum p, Nonempty (BundleIso D.factor F) := by
  obtain ⟨D, ⟨e⟩⟩ := exists_unitaryDatum_bundleIso F
  refine ⟨D, ⟨e⟩, ?_⟩
  rintro D' ⟨e'⟩
  exact unitaryDatum_eq_of_bundleIso D' D (e'.trans e.symm)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
