import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorTypeOneOne
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLogCanonical

/-!
# The actual holomorphic logarithmic difference from the canonical factor

The canonical factor is constructed only after the actual factor's type
condition has been proved. Equality of their genuine alternating logarithmic
pairings supplies an integer adjustment. Their adjusted logarithmic
difference is an entire additive lattice cocycle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex PeriodTorusAppellHumbert
open scoped ContDiff

variable {p : PeriodDomain}

def factorReference (F : FactorOfAutomorphy p) : FactorOfAutomorphy p :=
  integralFactor p (factorIntegralCoefficients F) (factorIntegralCoefficients_typeOneOne F)

theorem factorReference_alternatingForm (F : FactorOfAutomorphy p) :
    factorLogAlternatingForm (factorReference F) = factorLogAlternatingForm F := by
  ext l m
  rw [factorReference, canonicalFactorLogAlternatingForm_apply, factorIntegralCoefficients_spec]

theorem exists_factorComparisonAdjustment (F : FactorOfAutomorphy p) :
    ∃ a : p.lattice → ℤ, a 0 = 0 ∧ ∀ l m,
      factorLogIntegerCocycle F l m - factorLogIntegerCocycle (factorReference F) l m =
        a (l + m) - a l - a m := by
  apply (factorLog_hasIntegerLogDefect F).exists_coboundary_of_same_alternatingForm
    (factorLog_hasIntegerLogDefect (factorReference F))
    (factorLog_zero F) (factorLog_zero (factorReference F))
  exact (factorReference_alternatingForm F).symm

def factorComparisonAdjustment (F : FactorOfAutomorphy p) : p.lattice → ℤ :=
  (exists_factorComparisonAdjustment F).choose

theorem factorComparisonAdjustment_spec (F : FactorOfAutomorphy p) (l m : p.lattice) :
    factorLogIntegerCocycle F l m - factorLogIntegerCocycle (factorReference F) l m =
      factorComparisonAdjustment F (l + m) - factorComparisonAdjustment F l -
        factorComparisonAdjustment F m :=
  (exists_factorComparisonAdjustment F).choose_spec.2 l m

/-- An actual entire additive cocycle, not a hypothesized normal form. -/
def factorComparisonLog (F : FactorOfAutomorphy p) (l : p.lattice) (z : ComplexPlane₂) : ℂ :=
  factorLog F l z - factorLog (factorReference F) l z -
    (factorComparisonAdjustment F l : ℂ) * (2 * (Real.pi : ℂ) * I)

theorem factorComparisonLog_holomorphic (F : FactorOfAutomorphy p) (l : p.lattice) :
    ContDiff ℂ ω (factorComparisonLog F l) :=
  ((factorLog_holomorphic F l).sub (factorLog_holomorphic (factorReference F) l)).sub
    contDiff_const

theorem factorComparisonLog_add (F : FactorOfAutomorphy p) (l m : p.lattice)
    (z : ComplexPlane₂) :
    factorComparisonLog F (l + m) z =
      factorComparisonLog F l (z + m) + factorComparisonLog F m z := by
  have hf := factorLog_hasIntegerLogDefect F l m z
  have hg := factorLog_hasIntegerLogDefect (factorReference F) l m z
  have ha := factorComparisonAdjustment_spec F l m
  have haC : (factorLogIntegerCocycle F l m : ℂ) -
      (factorLogIntegerCocycle (factorReference F) l m : ℂ) =
      (factorComparisonAdjustment F (l + m) : ℂ) -
        (factorComparisonAdjustment F l : ℂ) - (factorComparisonAdjustment F m : ℂ) := by
    exact_mod_cast ha
  dsimp only [factorComparisonLog]
  linear_combination hf - hg + (2 * (Real.pi : ℂ) * I) * haC

/-- Exponentiation recovers the quotient of the original actual factors. -/
theorem factorComparisonLog_exp (F : FactorOfAutomorphy p) (l : p.lattice)
    (z : ComplexPlane₂) :
    Complex.exp (factorComparisonLog F l z) =
      (F.factor l z : ℂ) / ((factorReference F).factor l z : ℂ) := by
  simp only [factorComparisonLog, Complex.exp_sub, factorLog_exp,
    Complex.exp_int_mul_two_pi_mul_I, div_one]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
