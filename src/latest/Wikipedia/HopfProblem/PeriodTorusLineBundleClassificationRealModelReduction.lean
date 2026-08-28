import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationRealModelBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorCoefficients
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCocycleSplitting

/-!
# Reducing an actual factor logarithm to a smooth additive cocycle

The integer adjustment is constructed from the proved splitting of symmetric
integer lattice cocycles. The remaining functions obey an exact additive
cocycle equation. No type `(1,1)` condition or normal-form hypothesis is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex PeriodTorusAppellHumbert
open scoped ContDiff

variable {p : PeriodDomain}

theorem exists_factorIntegerAdjustment (F : FactorOfAutomorphy p) :
    ∃ a : p.lattice → ℤ, a 0 = 0 ∧ ∀ l m,
      factorLogIntegerCocycle F l m - realModelIntegerCocycle p (factorIntegralCoefficients F) l m =
        a (l + m) - a l - a m := by
  apply (factorLog_hasIntegerLogDefect F).exists_coboundary_of_same_commutator
    (realModelLog_hasIntegerLogDefect p (factorIntegralCoefficients F))
    (factorLog_zero F) (realModelLog_zero p (factorIntegralCoefficients F))
  intro l m
  rw [realModelIntegerCocycle_commutator, factorIntegralCoefficients_spec]
  rfl

def factorIntegerAdjustment (F : FactorOfAutomorphy p) : p.lattice → ℤ :=
  (exists_factorIntegerAdjustment F).choose

@[simp]
theorem factorIntegerAdjustment_zero (F : FactorOfAutomorphy p) :
    factorIntegerAdjustment F 0 = 0 := (exists_factorIntegerAdjustment F).choose_spec.1

theorem factorIntegerAdjustment_spec (F : FactorOfAutomorphy p) (l m : p.lattice) :
    factorLogIntegerCocycle F l m - realModelIntegerCocycle p (factorIntegralCoefficients F) l m =
      factorIntegerAdjustment F (l + m) - factorIntegerAdjustment F l -
        factorIntegerAdjustment F m :=
  (exists_factorIntegerAdjustment F).choose_spec.2 l m

/-- The smooth logarithmic difference after the constructed integer adjustment. -/
def realModelCocycle (F : FactorOfAutomorphy p) (l : p.lattice) (z : ComplexPlane₂) : ℂ :=
  factorLog F l z - realModelLog p (factorIntegralCoefficients F) l z -
    (factorIntegerAdjustment F l : ℂ) * (2 * (Real.pi : ℂ) * I)

@[simp]
theorem realModelCocycle_zero (F : FactorOfAutomorphy p) (z : ComplexPlane₂) :
    realModelCocycle F 0 z = 0 := by
  simp only [realModelCocycle, factorLog_zero, realModelLog_zero,
    factorIntegerAdjustment_zero, Int.cast_zero, zero_mul, sub_self]

theorem realModelCocycle_contDiff (F : FactorOfAutomorphy p) (l : p.lattice) :
    ContDiff ℝ ∞ (realModelCocycle F l) :=
  (((factorLog_holomorphic F l).of_le le_top).restrict_scalars ℝ).sub
    (realModelLog_contDiff p (factorIntegralCoefficients F) l) |>.sub contDiff_const

/-- The remaining logarithms satisfy an actual additive lattice cocycle equation. -/
theorem realModelCocycle_add (F : FactorOfAutomorphy p) (l m : p.lattice)
    (z : ComplexPlane₂) :
    realModelCocycle F (l + m) z = realModelCocycle F l (z + m) + realModelCocycle F m z := by
  have hf := factorLog_hasIntegerLogDefect F l m z
  have hm := realModelLog_hasIntegerLogDefect p (factorIntegralCoefficients F) l m z
  have ha := factorIntegerAdjustment_spec F l m
  have haC : (factorLogIntegerCocycle F l m : ℂ) -
      (realModelIntegerCocycle p (factorIntegralCoefficients F) l m : ℂ) =
      (factorIntegerAdjustment F (l + m) : ℂ) -
        (factorIntegerAdjustment F l : ℂ) - (factorIntegerAdjustment F m : ℂ) := by
    exact_mod_cast ha
  dsimp only [realModelCocycle]
  linear_combination hf - hm + (2 * (Real.pi : ℂ) * I) * haC

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
