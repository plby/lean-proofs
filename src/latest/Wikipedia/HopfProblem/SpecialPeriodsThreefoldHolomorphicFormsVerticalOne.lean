import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCoefficientDetection

/-!
# The second vertical coefficient detects the first one

The actual derivative constraint in Lemma 9.15, together with the
proved nonvanishing of the first special-period derivative on the
regular locus, kills both vertical coefficients as soon as the second
coefficient vanishes. No generic nonvanishing condition is assumed.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open HolomorphicDifferentialForms (Form)

attribute [local instance] chartedSpace coverChartedSpace cover_isManifold space_isManifold

theorem fibreOne_first_eq_zero_of_second (θ : Form Model Threefold.Space 1)
    (z : TriangleRegularPoint) (hsecond : fibreOne θ z 1 = 0) : fibreOne θ z 0 = 0 := by
  have h := fibreOne_periodDerivative θ z (Pi.single (1 : Fin 4) 1)
  simp only [dotProduct, Fin.sum_univ_two, hsecond, zero_mul, add_zero] at h
  have hτ := PeriodFamilyHolomorphicForms.specialPeriodDerivative_tau triangleRegularDomain z
  change PeriodFamilyHolomorphicForms.periodDerivative specialPeriodMap z.val
      (Pi.single (1 : Fin 4) 1) 0 =
    TriangleHolomorphicDifferentials.scalarDeriv specialTau z.val at hτ
  rw [hτ] at h
  exact (mul_eq_zero.mp h).resolve_right
    (TriangleHolomorphicDifferentials.specialTau_scalarDeriv_ne_zero z)

theorem fibreOne_eq_zero_of_second (θ : Form Model Threefold.Space 1)
    (hsecond : ∀ z, fibreOne θ z 1 = 0) : fibreOne θ = 0 := by
  funext z i
  fin_cases i
  · exact fibreOne_first_eq_zero_of_second θ z (hsecond z)
  · exact hsecond z

theorem oneForm_eq_zero_of_base_and_second (θ : Form Model Threefold.Space 1)
    (hbase : baseOne θ = 0) (hsecond : ∀ z, fibreOne θ z 1 = 0) : θ = 0 :=
  (oneForm_eq_zero_iff_coefficients θ).mpr
    ⟨hbase, fibreOne_eq_zero_of_second θ hsecond⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
