import Wikipedia.HopfProblem.PeriodTorusLineBundleChernLogBasic

/-!
# Actual integer branch corrections for factor logarithms

Two continuous logarithms of the same nowhere-zero function differ by
one integer multiple of `2πi` on the connected covering plane.  This
constructs the integer one-cochain comparing their actual logarithmic
defects.  The correction is the negative standard coboundary.

In particular the chosen principal-normalized logarithms of a canonical
factor and its explicit Appell--Humbert logarithm give cohomologous
integer cocycles, with the branch correction and sign displayed exactly.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleChernLog

open PeriodTorusLineBundleClassification PeriodTorusAppellHumbert PeriodTorusTypeOneOne
open PeriodTorusLineBundle.ChernCocycle

/-- Equality of actual exponential lifts gives a single integer difference on the whole plane. -/
theorem continuous_logDifference_exists_int (b c : ComplexPlane₂ → ℂ)
    (hb : Continuous b) (hc : Continuous c)
    (he : ∀ z, Complex.exp (b z) = Complex.exp (c z)) :
    ∃ n : ℤ, ∀ z, b z - c z = (n : ℂ) * logPeriod := by
  have hExp (z : ComplexPlane₂) : Complex.exp (b z - c z) = 1 := by
    rw [Complex.exp_sub, he z, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hExp 0)
  refine ⟨n, fun z => ?_⟩
  exact (continuous_exp_eq_one_constant (fun w => b w - c w)
    (hb.sub hc) hExp z).trans hn

variable {p : PeriodDomain}
  (b c : p.lattice → ComplexPlane₂ → ℂ)
  (hb : ∀ l, Continuous (b l)) (hc : ∀ l, Continuous (c l))
  (he : ∀ l z, Complex.exp (b l z) = Complex.exp (c l z))

/-- The actual integer one-cochain is selected after proving its global logarithmic meaning. -/
def logBranchDifference (l : p.lattice) : ℤ :=
  (continuous_logDifference_exists_int (b l) (c l) (hb l) (hc l) (he l)).choose

theorem logBranchDifference_spec (l : p.lattice) (z : ComplexPlane₂) :
    b l z - c l z = (logBranchDifference b c hb hc he l : ℂ) * logPeriod :=
  (continuous_logDifference_exists_int (b l) (c l) (hb l) (hc l) (he l)).choose_spec z

theorem logBranchDifference_add (l : p.lattice) (z : ComplexPlane₂) :
    b l z = c l z + (logBranchDifference b c hb hc he l : ℂ) * logPeriod := by
  linear_combination logBranchDifference_spec b c hb hc he l z

/-- Logarithms normalized at the zero lattice element have a normalized integer branch change. -/
theorem logBranchDifference_zero (hb0 : ∀ z, b 0 z = 0) (hc0 : ∀ z, c 0 z = 0) :
    logBranchDifference b c hb hc he 0 = 0 := by
  have h := logBranchDifference_spec b c hb hc he 0 0
  rw [hb0 0, hc0 0, sub_self] at h
  have hn : (logBranchDifference b c hb hc he 0 : ℂ) = 0 :=
    (mul_eq_zero.mp h.symm).resolve_right logPeriod_ne_zero
  exact_mod_cast hn

/-- The actual integer cocycles differ by the displayed branch coboundary. -/
theorem logDefect_compare {n n' : p.lattice → p.lattice → ℤ}
    (hn : HasIntegerLogDefect p b n) (hn' : HasIntegerLogDefect p c n') :
    n = fun l m => n' l m + logCoboundary (logBranchDifference b c hb hc he) l m := by
  have hs := logDefect_integerShift hn' (logBranchDifference b c hb hc he)
  apply hn.unique
  intro l m z
  rw [logBranchDifference_add b c hb hc he (l + m) z,
    logBranchDifference_add b c hb hc he l (z + m),
    logBranchDifference_add b c hb hc he m z]
  exact hs l m z

theorem logDefect_compare_apply {n n' : p.lattice → p.lattice → ℤ}
    (hn : HasIntegerLogDefect p b n) (hn' : HasIntegerLogDefect p c n')
    (l m : p.lattice) :
    n l m = n' l m + logCoboundary (logBranchDifference b c hb hc he) l m :=
  congrFun (congrFun (logDefect_compare b c hb hc he hn hn') l) m

include hb hc he in
/-- Antisymmetrization is independent of the actual logarithmic branch choices. -/
theorem logDefect_compare_antisymm {n n' : p.lattice → p.lattice → ℤ}
    (hn : HasIntegerLogDefect p b n) (hn' : HasIntegerLogDefect p c n')
    (l m : p.lattice) : n l m - n m l = n' l m - n' m l := by
  rw [logDefect_compare_apply b c hb hc he hn hn' l m,
    logDefect_compare_apply b c hb hc he hn hn' m l,
    logCoboundary_comm (logBranchDifference b c hb hc he) m l]
  ring

/-- The chosen factor logarithm compared with any actual continuous logarithm of that factor. -/
def factorLogBranch (F : FactorOfAutomorphy p) (b : p.lattice → ComplexPlane₂ → ℂ)
    (hb : ∀ l, Continuous (b l))
    (he : ∀ l z, Complex.exp (b l z) = (F.factor l z : ℂ)) : p.lattice → ℤ :=
  logBranchDifference (factorLog F) b (fun l => (factorLog_holomorphic F l).continuous) hb
    (fun l z => (factorLog_exp F l z).trans (he l z).symm)

theorem factorLogBranch_spec (F : FactorOfAutomorphy p)
    (b : p.lattice → ComplexPlane₂ → ℂ) (hb : ∀ l, Continuous (b l))
    (he : ∀ l z, Complex.exp (b l z) = (F.factor l z : ℂ))
    (l : p.lattice) (z : ComplexPlane₂) :
    factorLog F l z - b l z = (factorLogBranch F b hb he l : ℂ) * logPeriod :=
  logBranchDifference_spec (factorLog F) b
    (fun l => (factorLog_holomorphic F l).continuous) hb
    (fun l z => (factorLog_exp F l z).trans (he l z).symm) l z

theorem factorLogBranch_zero (F : FactorOfAutomorphy p)
    (b : p.lattice → ComplexPlane₂ → ℂ) (hb : ∀ l, Continuous (b l))
    (he : ∀ l z, Complex.exp (b l z) = (F.factor l z : ℂ))
    (hb0 : ∀ z, b 0 z = 0) : factorLogBranch F b hb he 0 = 0 :=
  logBranchDifference_zero (factorLog F) b
    (fun l => (factorLog_holomorphic F l).continuous) hb
    (fun l z => (factorLog_exp F l z).trans (he l z).symm) (factorLog_zero F) hb0

/-- The adapter to actual singular cochains retains the negative standard-coboundary sign. -/
theorem factorCocycle_of_log (F : FactorOfAutomorphy p)
    (b : p.lattice → ComplexPlane₂ → ℂ) (hb : ∀ l, Continuous (b l))
    (he : ∀ l z, Complex.exp (b l z) = (F.factor l z : ℂ))
    (n : p.lattice → p.lattice → ℤ) (hn : HasIntegerLogDefect p b n) :
    factorCocycle F = integerCocycleOfLogDefect hn +
      -IntegralTwoCocycle.coboundary (factorLogBranch F b hb he) := by
  ext l m
  change factorLogIntegerCocycle F l m = n l m +
    -(factorLogBranch F b hb he l + factorLogBranch F b hb he m -
      factorLogBranch F b hb he (l + m))
  rw [← logCoboundary_eq_neg_standard]
  exact logDefect_compare_apply (factorLog F) b
    (fun l => (factorLog_holomorphic F l).continuous) hb
    (fun l z => (factorLog_exp F l z).trans (he l z).symm)
    (factorLog_hasIntegerLogDefect F) hn l m

/-- The integer branch change from the explicit canonical logarithm to the chosen one. -/
def canonicalLogBranch (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) : p.lattice → ℤ :=
  factorLogBranch (integralFactor p E hType) (canonicalLog p E hType)
    (fun l => (canonicalLog_holomorphic p E hType l).continuous)
    (canonicalLog_exp p E hType)

theorem canonicalLogBranch_spec (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (l : p.lattice) (z : ComplexPlane₂) :
    factorLog (integralFactor p E hType) l z - canonicalLog p E hType l z =
      (canonicalLogBranch p E hType l : ℂ) * logPeriod :=
  factorLogBranch_spec (integralFactor p E hType) (canonicalLog p E hType)
    (fun l => (canonicalLog_holomorphic p E hType l).continuous)
    (canonicalLog_exp p E hType) l z

@[simp] theorem canonicalLogBranch_zero (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) : canonicalLogBranch p E hType 0 = 0 :=
  factorLogBranch_zero (integralFactor p E hType) (canonicalLog p E hType)
    (fun l => (canonicalLog_holomorphic p E hType l).continuous)
    (canonicalLog_exp p E hType) (canonicalLog_zero p E hType)

/-- The chosen canonical cocycle is the literal upper-triangular cocycle
modulo its actual integer branch change. -/
theorem factorCocycle_canonical_eq (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) :
    factorCocycle (integralFactor p E hType) = canonicalCocycle p E +
      -IntegralTwoCocycle.coboundary (canonicalLogBranch p E hType) := by
  have hk : integerCocycleOfLogDefect (canonicalLog_hasIntegerLogDefect p E hType) =
      canonicalCocycle p E := by
    ext l m
    rfl
  rw [← hk]
  exact factorCocycle_of_log (integralFactor p E hType) (canonicalLog p E hType)
    (fun l => (canonicalLog_holomorphic p E hType l).continuous)
    (canonicalLog_exp p E hType) (canonicalIntegerCocycle p E)
    (canonicalLog_hasIntegerLogDefect p E hType)

end Wikipedia.HopfProblem.PeriodTorusLineBundleChernLog
