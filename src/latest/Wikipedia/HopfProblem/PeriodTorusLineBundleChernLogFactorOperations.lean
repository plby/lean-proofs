import Wikipedia.HopfProblem.PeriodTorusLineBundleChernLogBranches
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniquenessGauge

/-!
# Products and actual bundle-isomorphism gauges for factor logarithms

Pointwise multiplication constructs a genuine holomorphic factor.  The
sum of the two actual factor logarithms is a logarithm of that product.
An actual analytic bundle isomorphism likewise supplies its entire
nonvanishing gauge and hence an entire gauge logarithm.  The chosen
principal-normalized factor logarithms are compared with these candidates
by their actual integer branch corrections, with the negative standard
coboundary sign retained throughout.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleChernLog

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassification
open PeriodTorusLineBundleClassificationUniqueness
open PeriodTorusLineBundle.ChernCocycle
open scoped ContDiff

variable {p : PeriodDomain}

/-- The genuine pointwise product of two actual holomorphic factors. -/
def factorProduct (F G : FactorOfAutomorphy p) : FactorOfAutomorphy p where
  factor l z := F.factor l z * G.factor l z
  factor_zero z := by rw [F.factor_zero, G.factor_zero, mul_one]
  factor_add l m z := by
    rw [F.factor_add, G.factor_add]
    ac_rfl
  holomorphic_factor l := (F.holomorphic_factor l).mul (G.holomorphic_factor l)

@[simp] theorem factorProduct_factor (F G : FactorOfAutomorphy p)
    (l : p.lattice) (z : ComplexPlane₂) :
    (factorProduct F G).factor l z = F.factor l z * G.factor l z := rfl

@[simp] theorem factorProduct_coe (F G : FactorOfAutomorphy p)
    (l : p.lattice) (z : ComplexPlane₂) :
    ((factorProduct F G).factor l z : ℂ) = (F.factor l z : ℂ) * (G.factor l z : ℂ) := rfl

/-- The sum of the chosen actual logarithms, before renormalizing the product branch. -/
def factorProductLog (F G : FactorOfAutomorphy p) (l : p.lattice) (z : ComplexPlane₂) : ℂ :=
  factorLog F l z + factorLog G l z

theorem factorProductLog_holomorphic (F G : FactorOfAutomorphy p) (l : p.lattice) :
    ContDiff ℂ ω (factorProductLog F G l) :=
  (factorLog_holomorphic F l).add (factorLog_holomorphic G l)

theorem factorProductLog_continuous (F G : FactorOfAutomorphy p) (l : p.lattice) :
    Continuous (factorProductLog F G l) :=
  (factorProductLog_holomorphic F G l).continuous

theorem factorProductLog_exp (F G : FactorOfAutomorphy p) (l : p.lattice)
    (z : ComplexPlane₂) :
    Complex.exp (factorProductLog F G l z) = ((factorProduct F G).factor l z : ℂ) := by
  simp only [factorProductLog, Complex.exp_add, factorLog_exp, factorProduct_coe]

@[simp] theorem factorProductLog_zero (F G : FactorOfAutomorphy p) (z : ComplexPlane₂) :
    factorProductLog F G 0 z = 0 := by
  simp [factorProductLog]

/-- The unrenormalized product logarithm has the sum of the actual integer defects. -/
theorem factorProductLog_hasIntegerLogDefect (F G : FactorOfAutomorphy p) :
    HasIntegerLogDefect p (factorProductLog F G)
      (fun l m => factorLogIntegerCocycle F l m + factorLogIntegerCocycle G l m) :=
  logDefect_add (factorLog_hasIntegerLogDefect F) (factorLog_hasIntegerLogDefect G)

/-- The actual integer change from the summed logarithm to the chosen product logarithm. -/
def factorProductLogBranch (F G : FactorOfAutomorphy p) : p.lattice → ℤ :=
  factorLogBranch (factorProduct F G) (factorProductLog F G)
    (factorProductLog_continuous F G) (factorProductLog_exp F G)

theorem factorProductLogBranch_spec (F G : FactorOfAutomorphy p)
    (l : p.lattice) (z : ComplexPlane₂) :
    factorLog (factorProduct F G) l z - factorProductLog F G l z =
      (factorProductLogBranch F G l : ℂ) * logPeriod :=
  factorLogBranch_spec (factorProduct F G) (factorProductLog F G)
    (factorProductLog_continuous F G) (factorProductLog_exp F G) l z

@[simp] theorem factorProductLogBranch_zero (F G : FactorOfAutomorphy p) :
    factorProductLogBranch F G 0 = 0 :=
  factorLogBranch_zero (factorProduct F G) (factorProductLog F G)
    (factorProductLog_continuous F G) (factorProductLog_exp F G) (factorProductLog_zero F G)

/-- The chosen product cocycle is additive up to its actual negative branch coboundary. -/
theorem factorCocycle_product (F G : FactorOfAutomorphy p) :
    factorCocycle (factorProduct F G) = (factorCocycle F + factorCocycle G) +
      -IntegralTwoCocycle.coboundary (factorProductLogBranch F G) := by
  have hk : integerCocycleOfLogDefect (factorProductLog_hasIntegerLogDefect F G) =
      factorCocycle F + factorCocycle G := by
    ext l m
    rfl
  rw [← hk]
  exact factorCocycle_of_log (factorProduct F G) (factorProductLog F G)
    (factorProductLog_continuous F G) (factorProductLog_exp F G)
    (fun l m => factorLogIntegerCocycle F l m + factorLogIntegerCocycle G l m)
    (factorProductLog_hasIntegerLogDefect F G)

variable {F G : FactorOfAutomorphy p}

/-- An entire logarithm of the gauge extracted from the actual native bundle isomorphism. -/
def gaugeLog (e : BundleIso F G) : ComplexPlane₂ → ℂ :=
  normalizedEntireLog (gauge e) (gauge_contDiff e).analyticOnNhd (gauge_ne_zero e)

theorem gaugeLog_exp (e : BundleIso F G) (z : ComplexPlane₂) :
    Complex.exp (gaugeLog e z) = gauge e z :=
  normalizedEntireLog_exp _ _ _ z

theorem gaugeLog_holomorphic (e : BundleIso F G) : ContDiff ℂ ω (gaugeLog e) :=
  normalizedEntireLog_holomorphic _ _ _

/-- The original factor logarithm changed by the actual bundle-isomorphism gauge logarithm. -/
def bundleIsoLog (e : BundleIso F G) : p.lattice → ComplexPlane₂ → ℂ :=
  logGauge (factorLog F) (gaugeLog e)

/-- The actual gauge transformation law makes this a logarithm of the target factor. -/
theorem bundleIsoLog_exp (e : BundleIso F G) (l : p.lattice) (z : ComplexPlane₂) :
    Complex.exp (bundleIsoLog e l z) = (G.factor l z : ℂ) := by
  rw [bundleIsoLog, logGauge_exp, factorLog_exp, gaugeLog_exp, gaugeLog_exp]
  apply (div_eq_iff (gauge_ne_zero e z)).mpr
  simpa only [mul_comm (gauge e (z + l)) (F.factor l z : ℂ)] using
    gauge_factor_relation e l z

theorem bundleIsoLog_holomorphic (e : BundleIso F G) (l : p.lattice) :
    ContDiff ℂ ω (bundleIsoLog e l) :=
  ((factorLog_holomorphic F l).add
    ((gaugeLog_holomorphic e).comp (contDiff_id.add contDiff_const))).sub
      (gaugeLog_holomorphic e)

theorem bundleIsoLog_continuous (e : BundleIso F G) (l : p.lattice) :
    Continuous (bundleIsoLog e l) :=
  (bundleIsoLog_holomorphic e l).continuous

@[simp] theorem bundleIsoLog_zero (e : BundleIso F G) (z : ComplexPlane₂) :
    bundleIsoLog e 0 z = 0 :=
  logGauge_zero (factorLog_zero F) (gaugeLog e) z

/-- The entire gauge logarithm cancels from the exact positive integer defect. -/
theorem bundleIsoLog_hasIntegerLogDefect (e : BundleIso F G) :
    HasIntegerLogDefect p (bundleIsoLog e) (factorLogIntegerCocycle F) :=
  logDefect_gauge (factorLog_hasIntegerLogDefect F) (gaugeLog e)

/-- The actual integer change from the gauge logarithm to the chosen target logarithm. -/
def bundleIsoLogBranch (e : BundleIso F G) : p.lattice → ℤ :=
  factorLogBranch G (bundleIsoLog e) (bundleIsoLog_continuous e) (bundleIsoLog_exp e)

theorem bundleIsoLogBranch_spec (e : BundleIso F G) (l : p.lattice) (z : ComplexPlane₂) :
    factorLog G l z - bundleIsoLog e l z = (bundleIsoLogBranch e l : ℂ) * logPeriod :=
  factorLogBranch_spec G (bundleIsoLog e) (bundleIsoLog_continuous e) (bundleIsoLog_exp e) l z

@[simp] theorem bundleIsoLogBranch_zero (e : BundleIso F G) : bundleIsoLogBranch e 0 = 0 :=
  factorLogBranch_zero G (bundleIsoLog e) (bundleIsoLog_continuous e)
    (bundleIsoLog_exp e) (bundleIsoLog_zero e)

/-- An actual analytic bundle isomorphism changes the chosen factor cocycle by this
actual negative branch coboundary. -/
theorem factorCocycle_bundleIso (e : BundleIso F G) :
    factorCocycle G = factorCocycle F +
      -IntegralTwoCocycle.coboundary (bundleIsoLogBranch e) := by
  have hk : integerCocycleOfLogDefect (bundleIsoLog_hasIntegerLogDefect e) =
      factorCocycle F := by
    ext l m
    rfl
  rw [← hk]
  exact factorCocycle_of_log G (bundleIsoLog e) (bundleIsoLog_continuous e)
    (bundleIsoLog_exp e) (factorLogIntegerCocycle F) (bundleIsoLog_hasIntegerLogDefect e)

end Wikipedia.HopfProblem.PeriodTorusLineBundleChernLog
