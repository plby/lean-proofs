import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Common-unit uniqueness of reduced fraction pairs

Over a factorial integral domain, two relatively prime numerator-denominator
pairs representing the same fraction differ by one common unit.  Euclid's
lemma first identifies their denominators up to a unit; cancellation by a
nonzero denominator gives that very same unit on the numerators.  The zero
numerator case is included.  This is a purely algebraic statement and makes
no factoriality assertion about any analytic local ring.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarAlgebra

variable {R K : Type*} [CommRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]

private theorem fraction_eq_iff_cross_mul {p q p' q' : R}
    (hq : q ≠ 0) (hq' : q' ≠ 0) :
    algebraMap R K p / algebraMap R K q =
        algebraMap R K p' / algebraMap R K q' ↔ p * q' = p' * q := by
  have hqK : algebraMap R K q ≠ 0 :=
    fun h => hq ((IsFractionRing.injective R K) (h.trans (map_zero (algebraMap R K)).symm))
  have hqK' : algebraMap R K q' ≠ 0 :=
    fun h => hq' ((IsFractionRing.injective R K) (h.trans (map_zero (algebraMap R K)).symm))
  rw [div_eq_div_iff hqK hqK']
  constructor
  · intro h
    apply IsFractionRing.injective R K
    simpa only [map_mul] using h
  · intro h
    simpa only [map_mul] using congrArg (algebraMap R K) h

variable [IsDomain R] [UniqueFactorizationMonoid R]

/-- The denominators of equal reduced fractions are associated. -/
theorem reduced_fraction_denominators_associated {p q p' q' : R}
    (hq : q ≠ 0) (hq' : q' ≠ 0)
    (hpq : IsRelPrime p q) (hpq' : IsRelPrime p' q')
    (he : algebraMap R K p / algebraMap R K q =
      algebraMap R K p' / algebraMap R K q') : Associated q q' := by
  have hc := (fraction_eq_iff_cross_mul hq hq').mp he
  apply associated_of_dvd_dvd
  · apply hpq.symm.dvd_of_dvd_mul_left
    exact ⟨p', hc.trans (mul_comm p' q)⟩
  · apply hpq'.symm.dvd_of_dvd_mul_left
    exact ⟨p, hc.symm.trans (mul_comm p q')⟩

/-- Equal reduced fraction pairs differ by one common unit, including
when their numerators vanish. -/
theorem reduced_fraction_common_unit {p q p' q' : R}
    (hq : q ≠ 0) (hq' : q' ≠ 0)
    (hpq : IsRelPrime p q) (hpq' : IsRelPrime p' q')
    (he : algebraMap R K p / algebraMap R K q =
      algebraMap R K p' / algebraMap R K q') :
    ∃ u : Rˣ, p' = (u : R) * p ∧ q' = (u : R) * q := by
  obtain ⟨u, hu⟩ := reduced_fraction_denominators_associated hq hq' hpq hpq' he
  have hc := (fraction_eq_iff_cross_mul hq hq').mp he
  refine ⟨u, ?_, hu.symm.trans (mul_comm q (u : R))⟩
  apply mul_right_cancel₀ hq
  calc
    p' * q = p * q' := hc.symm
    _ = (u : R) * p * q := by rw [← hu]; ac_rfl

/-- Equality of reduced fractions is exactly simultaneous multiplication
of their two entries by the same unit. -/
theorem reduced_fraction_eq_iff_common_unit {p q p' q' : R}
    (hq : q ≠ 0) (hq' : q' ≠ 0)
    (hpq : IsRelPrime p q) (hpq' : IsRelPrime p' q') :
    algebraMap R K p / algebraMap R K q =
        algebraMap R K p' / algebraMap R K q' ↔
      ∃ u : Rˣ, p' = (u : R) * p ∧ q' = (u : R) * q := by
  constructor
  · exact reduced_fraction_common_unit hq hq' hpq hpq'
  · rintro ⟨u, hp, hqu⟩
    apply (fraction_eq_iff_cross_mul hq hq').mpr
    rw [hp, hqu]
    ac_rfl

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarAlgebra
