import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLogBasic
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertData

/-!
# Normalized entire logarithms of actual factors

For the positive-translation convention the logarithmic defect is
`b (l + m) z - b l (z + m) - b m z`. Its exponential is one, and
connectedness makes it a single integer multiple of `2π I`, independent
of the point of the covering plane.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex PeriodTorusAppellHumbert
open scoped ContDiff

variable {p : PeriodDomain}

/-- The actual normalized entire logarithm of each nonvanishing factor. -/
def factorLog (F : FactorOfAutomorphy p) (l : p.lattice) : ComplexPlane₂ → ℂ :=
  normalizedEntireLog (fun z => (F.factor l z : ℂ))
    (F.holomorphic_factor l).analyticOnNhd (F.factor_ne_zero l)

theorem factorLog_analytic (F : FactorOfAutomorphy p) (l : p.lattice) :
    AnalyticOnNhd ℂ (factorLog F l) Set.univ :=
  normalizedEntireLog_analytic _ _ _

theorem factorLog_holomorphic (F : FactorOfAutomorphy p) (l : p.lattice) :
    ContDiff ℂ ω (factorLog F l) :=
  (factorLog_analytic F l).contDiff

@[simp]
theorem factorLog_exp (F : FactorOfAutomorphy p) (l : p.lattice) (z : ComplexPlane₂) :
    Complex.exp (factorLog F l z) = (F.factor l z : ℂ) :=
  normalizedEntireLog_exp _ _ _ z

theorem factorLog_at_zero (F : FactorOfAutomorphy p) (l : p.lattice) :
    factorLog F l 0 = Complex.log (F.factor l 0 : ℂ) :=
  normalizedEntireLog_zero _ _ _

@[simp]
theorem factorLog_zero (F : FactorOfAutomorphy p) (z : ComplexPlane₂) :
    factorLog F 0 z = 0 := by
  have he (w : ComplexPlane₂) : Complex.exp (factorLog F 0 w) = 1 := by simp
  rw [continuous_exp_eq_one_constant (factorLog F 0) (factorLog_holomorphic F 0).continuous he,
    factorLog_at_zero, F.factor_zero_coe, Complex.log_one]

/-- The logarithmic defect for the actual positive lattice action. -/
def factorLogDefect (F : FactorOfAutomorphy p) (l m : p.lattice) (z : ComplexPlane₂) : ℂ :=
  factorLog F (l + m) z - factorLog F l (z + m) - factorLog F m z

theorem factorLogDefect_holomorphic (F : FactorOfAutomorphy p) (l m : p.lattice) :
    ContDiff ℂ ω (factorLogDefect F l m) := by
  exact ((factorLog_holomorphic F (l + m)).sub
    ((factorLog_holomorphic F l).comp (contDiff_id.add contDiff_const))).sub
      (factorLog_holomorphic F m)

theorem factorLogDefect_exp (F : FactorOfAutomorphy p) (l m : p.lattice)
    (z : ComplexPlane₂) : Complex.exp (factorLogDefect F l m z) = 1 := by
  simp only [factorLogDefect, Complex.exp_sub, factorLog_exp]
  rw [div_div, F.factor_add_coe]
  exact div_self (mul_ne_zero (F.factor_ne_zero l (z + m)) (F.factor_ne_zero m z))

theorem factorLogDefect_constant (F : FactorOfAutomorphy p) (l m : p.lattice)
    (z : ComplexPlane₂) : factorLogDefect F l m z = factorLogDefect F l m 0 :=
  continuous_exp_eq_one_constant _ (factorLogDefect_holomorphic F l m).continuous
    (factorLogDefect_exp F l m) z

theorem factorLogDefect_exists_int (F : FactorOfAutomorphy p) (l m : p.lattice) :
    ∃ n : ℤ, ∀ z, factorLogDefect F l m z = (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (factorLogDefect_exp F l m 0)
  exact ⟨n, fun z => (factorLogDefect_constant F l m z).trans hn⟩

/-- The integer defect is selected only after proving constancy and integrality. -/
def factorLogIntegerCocycle (F : FactorOfAutomorphy p) (l m : p.lattice) : ℤ :=
  (factorLogDefect_exists_int F l m).choose

theorem factorLogIntegerCocycle_spec (F : FactorOfAutomorphy p) (l m : p.lattice)
    (z : ComplexPlane₂) :
    factorLogDefect F l m z = (factorLogIntegerCocycle F l m : ℂ) * (2 * (Real.pi : ℂ) * I) :=
  (factorLogDefect_exists_int F l m).choose_spec z

/-- The additive logarithmic law is an identity for the constructed entire logarithms. -/
theorem factorLog_add (F : FactorOfAutomorphy p) (l m : p.lattice) (z : ComplexPlane₂) :
    factorLog F (l + m) z = factorLog F l (z + m) + factorLog F m z +
      (factorLogIntegerCocycle F l m : ℂ) * (2 * (Real.pi : ℂ) * I) := by
  have h := factorLogIntegerCocycle_spec F l m z
  dsimp [factorLogDefect] at h
  linear_combination h

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
