import Mathlib.RingTheory.Localization.NumDen

/-!
# Reduced presentations in the fraction field of a factorial domain

Mathlib's reduced numerator and denominator give a presentation with a
nonzero denominator and relatively prime factors.  This is a generic
algebraic statement; it supplies no factoriality instance for an analytic
local ring.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarAlgebra

variable (R : Type*) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Every fraction has a reduced presentation with an actual nonzero
denominator in the original domain. -/
theorem exists_reduced_representation (x : K) :
    ∃ p q : R, q ≠ 0 ∧ IsRelPrime p q ∧ algebraMap R K p / algebraMap R K q = x :=
  ⟨IsFractionRing.num R x, IsFractionRing.den R x,
    mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den R x).property,
    IsFractionRing.num_den_reduced R x, IsFractionRing.mk'_num_den' R x⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarAlgebra
