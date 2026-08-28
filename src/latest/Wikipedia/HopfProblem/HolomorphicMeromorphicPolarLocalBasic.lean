import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarStalk
import Wikipedia.HopfProblem.HolomorphicMeromorphicRegular

/-!
# Local denominator generators away from common zeros

If one member of a local numerator/denominator pair is a unit, the
denominator generates the full denominator ideal. Thus a pair with only
one possible common zero generates its denominator ideals everywhere
once this is proved at that point. No coherence theorem is assumed.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarLocal

open PolarAlgebra

section Algebra

variable {A K : Type*} [CommRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]

omit [IsDomain A] in
theorem denominatorIdeal_eq_span_of_isUnit_numerator (p q : A)
    (hq : q ≠ 0) (hp : IsUnit p) :
    denominatorIdeal A (algebraMap A K p / algebraMap A K q) =
      Ideal.span ({q} : Set A) := by
  ext h
  rw [mem_denominatorIdeal_div_iff A p q hq, Ideal.mem_span_singleton]
  exact hp.dvd_mul_right

theorem denominatorIdeal_eq_span_of_isUnit_denominator (p q : A) (hq : IsUnit q) :
    denominatorIdeal A (algebraMap A K p / algebraMap A K q) =
      Ideal.span ({q} : Set A) := by
  ext h
  rw [mem_denominatorIdeal_div_iff A p q hq.ne_zero, Ideal.mem_span_singleton]
  exact iff_of_true hq.dvd hq.dvd

theorem denominatorIdeal_eq_span_of_isUnit_or (p q : A) (hq : q ≠ 0)
    (hu : IsUnit p ∨ IsUnit q) :
    denominatorIdeal A (algebraMap A K p / algebraMap A K q) =
      Ideal.span ({q} : Set A) :=
  hu.elim (denominatorIdeal_eq_span_of_isUnit_numerator p q hq)
    (denominatorIdeal_eq_span_of_isUnit_denominator p q)

end Algebra

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

omit [I.Boundaryless] [IsManifold I ω M] in
/-- A nonzero ordinary value gives a unit in the original categorical
holomorphic stalk. -/
theorem holomorphicGerm_isUnit_of_value_ne_zero {U : Opens M}
    (f : HolomorphicFunctionSheaf.Section I M U) (x : U) (hx : f x ≠ 0) :
    IsUnit (holomorphicGerm I M U x f) := by
  apply (HolomorphicFunctionSheaf.isUnit_stalk_iff I M x.val _).mpr
  change HolomorphicFunctionSheaf.stalkEval I M x.val
    ((HolomorphicFunctionSheaf.presheaf I M).germ U x.val x.property f) ≠ 0
  rwa [HolomorphicFunctionSheaf.stalkEval_germ]

/-- At any point where the numerator and denominator do not both vanish,
the actual denominator germ generates the entire denominator ideal. -/
theorem fraction_denominatorIdeal_eq_span_of_no_common_zero {U : Opens M}
    (p q : HolomorphicFunctionSheaf.Section I M U) (x : U)
    (hq : holomorphicGerm I M U x q ≠ 0) (hnz : p x ≠ 0 ∨ q x ≠ 0) :
    denominatorIdeal (HolomorphicStalk I M x.val) (fraction I M U p q x) =
      Ideal.span ({holomorphicGerm I M U x q} : Set _) := by
  apply denominatorIdeal_eq_span_of_isUnit_or _ _ hq
  exact hnz.imp (holomorphicGerm_isUnit_of_value_ne_zero I M p x)
    (holomorphicGerm_isUnit_of_value_ne_zero I M q x)

/-- Isolated common zeros allow denominator generation to be checked only
at the exceptional center, using the actual native local functions. -/
theorem fraction_denominatorIdeal_eq_span_of_isolated_common_zero {U : Opens M}
    (p q : HolomorphicFunctionSheaf.Section I M U) (x : U)
    (hq : ∀ y : U, holomorphicGerm I M U y q ≠ 0)
    (hcenter : denominatorIdeal (HolomorphicStalk I M x.val) (fraction I M U p q x) =
      Ideal.span ({holomorphicGerm I M U x q} : Set _))
    (hisolated : ∀ y : U, p y = 0 → q y = 0 → y.val = x.val) :
    ∀ y : U, denominatorIdeal (HolomorphicStalk I M y.val) (fraction I M U p q y) =
      Ideal.span ({holomorphicGerm I M U y q} : Set _) := by
  intro y
  by_cases hy : y = x
  · subst y
    exact hcenter
  apply fraction_denominatorIdeal_eq_span_of_no_common_zero I M p q y (hq y)
  by_cases hp : p y = 0
  · right
    intro hqzero
    exact hy (Subtype.ext (hisolated y hp hqzero))
  · exact Or.inl hp

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarLocal
