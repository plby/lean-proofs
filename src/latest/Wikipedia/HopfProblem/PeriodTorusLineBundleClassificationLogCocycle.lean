import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLogFactor
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLogCocycleAlgebra

/-!
# The integer cocycle and alternating pairing of an actual factor

All algebraic hypotheses are discharged by the constructed normalized
entire logarithms. These statements concern the actual factor; they do not
assume a logarithm, a cocycle, or an alternating pairing as extra input.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex PeriodTorusAppellHumbert

variable {p : PeriodDomain}

theorem factorLog_hasIntegerLogDefect (F : FactorOfAutomorphy p) :
    HasIntegerLogDefect p (factorLog F) (factorLogIntegerCocycle F) := by
  intro l m z
  exact factorLogIntegerCocycle_spec F l m z

theorem factorLogIntegerCocycle_cocycle (F : FactorOfAutomorphy p) (l m k : p.lattice) :
    factorLogIntegerCocycle F l m + factorLogIntegerCocycle F (l + m) k =
      factorLogIntegerCocycle F m k + factorLogIntegerCocycle F l (m + k) :=
  (factorLog_hasIntegerLogDefect F).cocycle l m k

@[simp]
theorem factorLogIntegerCocycle_zero_left (F : FactorOfAutomorphy p) (l : p.lattice) :
    factorLogIntegerCocycle F 0 l = 0 :=
  (factorLog_hasIntegerLogDefect F).zero_left (factorLog_zero F) l

@[simp]
theorem factorLogIntegerCocycle_zero_right (F : FactorOfAutomorphy p) (l : p.lattice) :
    factorLogIntegerCocycle F l 0 = 0 :=
  (factorLog_hasIntegerLogDefect F).zero_right (factorLog_zero F) l

/-- Antisymmetrization of the genuine integer logarithmic cocycle. -/
def factorLogAlternatingForm (F : FactorOfAutomorphy p) : LinearMap.BilinForm ℤ p.lattice :=
  integerLogAlternatingForm (factorLog_hasIntegerLogDefect F)

@[simp]
theorem factorLogAlternatingForm_apply (F : FactorOfAutomorphy p) (l m : p.lattice) :
    factorLogAlternatingForm F l m = factorLogIntegerCocycle F l m - factorLogIntegerCocycle F m l :=
  rfl

theorem factorLogAlternatingForm_isAlt (F : FactorOfAutomorphy p) :
    (factorLogAlternatingForm F).IsAlt :=
  integerLogAlternatingForm_isAlt (factorLog_hasIntegerLogDefect F)

/-- The sign is fixed by the actual positive-translation convention. -/
theorem factorLogAlternatingForm_log_difference (F : FactorOfAutomorphy p)
    (l m : p.lattice) (z : ComplexPlane₂) :
    (factorLogAlternatingForm F l m : ℂ) * (2 * (Real.pi : ℂ) * I) =
      factorLog F m (z + l) - factorLog F m z - factorLog F l (z + m) + factorLog F l z :=
  integerLogAlternatingForm_log_difference (factorLog_hasIntegerLogDefect F) l m z

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
