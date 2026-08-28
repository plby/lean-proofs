import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarPlane
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarReducedUnits
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarReducedTransport

/-!
# Actual reduced analytic pairs with isolated common zeros

Simultaneous regularizing coordinates and convergent preparation reduce a
pair of actual analytic germs to polynomials over the one-variable germ
ring. Polynomial reduction retains a prime-power Bézout relation. Restoring
the preparation units preserves that relation, hence both cancellation
and isolation of common zeros of every pair of analytic representatives.
The resulting data are transported through the actual linear germ-ring
equivalence back to the original coordinates.

No factoriality of the two-variable analytic ring, coherence assumption,
or formal replacement of the analytic germs is used.
-/

open Set Filter Topology Polynomial
open Wikipedia.HopfProblem.CuspNormalization.Germs
open Wikipedia.HopfProblem.CuspNormalization.Germs.CoordinateDivision
open Wikipedia.HopfProblem.CuspNormalization.Germs.PolynomialGerms

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarReduced

/-- Regular actual germs admit reduced representatives whose common zero
is isolated for every choice of analytic representatives. -/
theorem exists_regular_reduced_pair (p q : O₂)
    (hp : axisRestriction p ≠ 0) (hq : axisRestriction q ≠ 0) :
    ∃ a b : O₂, b ≠ 0 ∧ p * b = q * a ∧
      (∀ h : O₂, b ∣ h * a ↔ b ∣ h) ∧ IsolatedCommonZero a b := by
  obtain ⟨P, _, u, hpu⟩ := PolarPlane.exists_preparation_of_axis_ne_zero p hp
  obtain ⟨Q, hQ, v, hqv⟩ := PolarPlane.exists_preparation_of_axis_ne_zero q hq
  obtain ⟨a₀, b₀, c, _, hb₀, htb₀, ha₀, hb₀eq, hbez⟩ :=
    PolarPolynomial.exists_reduced_image_data polynomialGerm
      PolarPlane.coefficient_image_factorization
      firstCoordinateGerm_not_dvd_polynomialGerm_of_isUnit_leadingCoeff
      P Q (hQ.leadingCoeff.symm ▸ isUnit_one)
  let a : O₂ := a₀ * (u : O₂)
  let b : O₂ := b₀ * (v : O₂)
  have hb : b ≠ 0 := mul_ne_zero hb₀ v.ne_zero
  have htb : ¬ firstCoordinateGerm ∣ b := by
    dsimp [b]
    rwa [v.isUnit.dvd_mul_right]
  obtain ⟨n, w, A, C, hrel⟩ := bezout_prime_power_mul_units hbez u v
  refine ⟨a, b, hb, ?_, ?_, ?_⟩
  · dsimp [a, b]
    rw [hpu, hqv, ← ha₀, ← hb₀eq]
    ring
  · intro h
    exact PolarCancellation.dvd_mul_iff_of_bezout_prime_power firstCoordinateGerm_prime htb
      ⟨n, w, A, C, hrel⟩ h
  · exact isolatedCommonZero_of_germ_relation w.isUnit hrel htb

/-- Every pair of actual two-variable analytic germs with nonzero
denominator has a reduced pair and representative-independent isolation
of its common zero. -/
theorem exists_reduced_pair_data (p q : O₂) (hq : q ≠ 0) :
    ∃ a b : O₂, b ≠ 0 ∧ p * b = q * a ∧
      (∀ h : O₂, b ∣ h * a ↔ b ∣ h) ∧ IsolatedCommonZero a b := by
  by_cases hp : p = 0
  · refine ⟨0, 1, one_ne_zero, ?_, ?_, isolatedCommonZero_zero_one⟩
    · simp [hp]
    · intro h
      simp
  obtain ⟨e, heP, heQ⟩ := Coordinates.exists_pair_regularizing_germ_coordinates p q hp hq
  let T := Coordinates.linearPullbackEquiv e
  obtain ⟨a, b, hb, hpq, hcancel, hisolated⟩ :=
    exists_regular_reduced_pair (T p) (T q) heP heQ
  obtain ⟨hb', hpq', hcancel'⟩ :=
    reduced_pair_relations_transport T p q a b hb hpq hcancel
  refine ⟨T.symm a, T.symm b, hb', hpq', hcancel', ?_⟩
  apply isolatedCommonZero_of_linearPullback e
  change IsolatedCommonZero (T (T.symm a)) (T (T.symm b))
  simpa only [RingEquiv.apply_symm_apply] using hisolated

/-- The reduced-pair theorem with its common-zero conclusion displayed
explicitly for arbitrary analytic representatives of the chosen germs. -/
theorem exists_reduced_pair (p q : O₂) (hq : q ≠ 0) :
    ∃ a b : O₂, b ≠ 0 ∧ p * b = q * a ∧
      (∀ h : O₂, b ∣ h * a ↔ b ∣ h) ∧
      ∀ (f g : ℂ × ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0),
        ofAnalytic f hf = a → ofAnalytic g hg = b →
        ∀ᶠ z in 𝓝 (0 : ℂ × ℂ), f z = 0 → g z = 0 → z = 0 :=
  exists_reduced_pair_data p q hq

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarReduced
