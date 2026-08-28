import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspLogCoefficients
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspComparisonNormalForms
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspOrderTransfer

/-!
# Analytic cusp extensions of the actual regular-cover coefficients

The functions below are constructed from the native reference-chart
pullback of an arbitrary genuine global holomorphic form. The exact
covering comparison identifies them with the original regular-family
coefficients. For a one-form, comparison of the three filled axes and
the proved fibre independence gives the two vertical coefficients by
subtraction. Every constructed function is analytic and zero at the cusp.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open ToricCharts CuspUniformization CuspFamily Triangle HolomorphicDifferentialForms
open HolomorphicDifferentialForms.Coordinates

local notation "EL" => ℂ × ComplexPlane₂
local notation "E₃" => CoordinateSpace 3
local notation "e₀" => (Pi.single (0 : Fin 3) (1 : ℂ) : E₃)
local notation "e₁" => (Pi.single (1 : Fin 3) (1 : ℂ) : E₃)
local notation "e₂" => (Pi.single (2 : Fin 3) (1 : ℂ) : E₃)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The analytic extension of the one-form's normalized horizontal coefficient. -/
def baseOneCuspCoefficient (θ : Form EL Threefold.Space 1) : ℂ → ℂ :=
  vanishingAxisCoefficient θ 0 ![e₀]

/-- The analytic vertical coefficients are the differences of the actual transverse axes. -/
def fibreOneCuspCoefficient (θ : Form EL Threefold.Space 1) (i : Fin 2) (q : ℂ) : ℂ :=
  vanishingAxisCoefficient θ i.succ ![(Pi.single i.succ 1 : E₃)] q -
    baseOneCuspCoefficient θ q

/-- The analytic extensions of the normalized mixed two-form coefficients. -/
def mixedTwoCuspCoefficient (θ : Form EL Threefold.Space 2) (i : Fin 2) : ℂ → ℂ :=
  vanishingAxisCoefficient θ 0 ![e₀, (Pi.single i.succ 1 : E₃)]

/-- The analytic extension of the normalized top-form coefficient. -/
def topCuspCoefficient (θ : Form EL Threefold.Space 3) : ℂ → ℂ :=
  vanishingAxisCoefficient θ 0 ![e₀, e₁, e₂]

theorem baseOneCuspCoefficient_analyticAt_zero (θ : Form EL Threefold.Space 1) :
    AnalyticAt ℂ (baseOneCuspCoefficient θ) 0 :=
  vanishingAxisCoefficient_analyticAt_zero θ 0 ![e₀]

theorem fibreOneCuspCoefficient_analyticAt_zero (θ : Form EL Threefold.Space 1) (i : Fin 2) :
    AnalyticAt ℂ (fibreOneCuspCoefficient θ i) 0 :=
  (vanishingAxisCoefficient_analyticAt_zero θ i.succ ![(Pi.single i.succ 1 : E₃)]).sub
    (baseOneCuspCoefficient_analyticAt_zero θ)

theorem mixedTwoCuspCoefficient_analyticAt_zero (θ : Form EL Threefold.Space 2) (i : Fin 2) :
    AnalyticAt ℂ (mixedTwoCuspCoefficient θ i) 0 :=
  vanishingAxisCoefficient_analyticAt_zero θ 0 ![e₀, (Pi.single i.succ 1 : E₃)]

theorem topCuspCoefficient_analyticAt_zero (θ : Form EL Threefold.Space 3) :
    AnalyticAt ℂ (topCuspCoefficient θ) 0 :=
  vanishingAxisCoefficient_analyticAt_zero θ 0 ![e₀, e₁, e₂]

@[simp] theorem baseOneCuspCoefficient_zero (θ : Form EL Threefold.Space 1) :
    baseOneCuspCoefficient θ 0 = 0 := vanishingAxisCoefficient_zero θ 0 ![e₀]

@[simp] theorem fibreOneCuspCoefficient_zero (θ : Form EL Threefold.Space 1) (i : Fin 2) :
    fibreOneCuspCoefficient θ i 0 = 0 := by simp [fibreOneCuspCoefficient]

@[simp] theorem mixedTwoCuspCoefficient_zero (θ : Form EL Threefold.Space 2) (i : Fin 2) :
    mixedTwoCuspCoefficient θ i 0 = 0 :=
  vanishingAxisCoefficient_zero θ 0 ![e₀, (Pi.single i.succ 1 : E₃)]

@[simp] theorem topCuspCoefficient_zero (θ : Form EL Threefold.Space 3) :
    topCuspCoefficient θ 0 = 0 := vanishingAxisCoefficient_zero θ 0 ![e₀, e₁, e₂]

@[simp] theorem toRegularCover_logPoint_base (s : LogBase CuspGeometry.data.radius)
    (ζ : ComplexPlane₂) : (toRegularCover (logPoint s ζ)).1 = cuspRegularBase s := rfl

@[simp] theorem toRegularCover_logAxisPoint_base (k : Fin 3)
    (s : LogBase CuspGeometry.data.radius) :
    (toRegularCover (logAxisPoint k s)).1 = cuspRegularBase s := rfl

theorem logAxisDirection_succ (i : Fin 2) : logAxisDirection i.succ = (1, Pi.single i 1) := by
  apply Prod.ext
  · rfl
  · ext j
    fin_cases i <;> fin_cases j <;> simp [logAxisDirection, logAxisFibre]

/-- The true normalized horizontal coefficient agrees with the analytic filled-axis function. -/
theorem baseOne_cusp_expansion (θ : Form EL Threefold.Space 1)
    (s : LogBase CuspGeometry.data.radius) :
    (width : ℂ) * RegularCover.baseOne θ (cuspRegularBase s) =
      baseOneCuspCoefficient θ (exponential s) := by
  have h := log_oneBaseCoefficient_eq_baseOne θ (logPoint s 0)
  simp only [oneBaseCoefficient_apply, EllipticShear.basis_zero,
    toRegularCover_logPoint_base] at h
  exact h.symm.trans (one_logBase_evaluation θ s)

/-- Both original vertical one-form coefficients extend and vanish at the filled cusp. -/
theorem fibreOne_cusp_expansion (θ : Form EL Threefold.Space 1)
    (s : LogBase CuspGeometry.data.radius) (i : Fin 2) :
    RegularCover.fibreOne θ (cuspRegularBase s) i =
      fibreOneCuspCoefficient θ i (exponential s) := by
  have h := log_one_base_fibre_evaluation_normalForm θ (logAxisPoint i.succ s) i
  rw [toRegularCover_logAxisPoint_base] at h
  have haxis := one_logAxis_evaluation θ i.succ s
  rw [logAxisDirection_succ] at haxis
  have hs := h.symm.trans haxis
  rw [baseOne_cusp_expansion θ s] at hs
  change RegularCover.fibreOne θ (cuspRegularBase s) i =
    vanishingAxisCoefficient θ i.succ ![(Pi.single i.succ 1 : E₃)] (exponential s) -
      baseOneCuspCoefficient θ (exponential s)
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans hs)

/-- The two actual normalized mixed coefficients agree with their analytic vanishing extensions. -/
theorem mixedTwo_cusp_expansion (θ : Form EL Threefold.Space 2)
    (s : LogBase CuspGeometry.data.radius) (i : Fin 2) :
    (width : ℂ) * RegularCover.mixedTwo θ (cuspRegularBase s) i =
      mixedTwoCuspCoefficient θ i (exponential s) := by
  have h := log_twoMixedCoefficient_eq_mixedTwo_apply θ (logPoint s 0) i
  simp only [twoMixedCoefficient_apply, EllipticShear.basis_zero,
    EllipticShear.basis_succ, toRegularCover_logPoint_base] at h
  exact h.symm.trans (two_logMixed_evaluation θ s i)

/-- The actual normalized top coefficient has the source's first-order cusp extension. -/
theorem top_cusp_expansion (θ : Form EL Threefold.Space 3)
    (s : LogBase CuspGeometry.data.radius) :
    (width : ℂ) * RegularCover.baseTop θ (cuspRegularBase s) =
      topCuspCoefficient θ (exponential s) := by
  have h := log_topCoefficient_eq_baseTop θ (logPoint s 0)
  have h₁ : basis (1 : Fin 3) = ((0, Pi.single (0 : Fin 2) 1) : EL) :=
    EllipticShear.basis_succ 0
  have h₂ : basis (2 : Fin 3) = ((0, Pi.single (1 : Fin 2) 1) : EL) :=
    EllipticShear.basis_succ 1
  simp only [topCoefficient_apply, EllipticShear.basis_zero, h₁, h₂,
    toRegularCover_logPoint_base] at h
  exact h.symm.trans (three_logTop_evaluation θ s)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
