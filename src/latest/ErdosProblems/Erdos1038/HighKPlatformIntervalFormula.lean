import ErdosProblems.Erdos1038.HighKPlatformInterval

/-!
# Stable platform formulas as exact interval expressions

The variables are, in order, `k`, `x₋`, `x₊`, `L`, and `π`.  The last two
are variables rather than decimal constants, so their independently proved
rational enclosures can be supplied to the checker.
-/

set_option warningAsError false

namespace Erdos1038

noncomputable section

open HighKIntervalExpr

attribute [simp] HighKIntervalExpr.evalReal

inductive HighKPlatformEdge where
  | affine
  | constant
deriving DecidableEq, Repr

def highKPlatformEdge : HighKPlatformEdge → ℝ → ℝ
  | .affine, k => 1153 / 500 - k / 4
  | .constant, _ => 9 / 5

def platformExteriorW (k a x : ℝ) : ℝ :=
  let rho0 := (Real.sqrt 2 - Real.sqrt a) /
    (Real.sqrt 2 + Real.sqrt a)
  let Kx := Real.sqrt ((a - x) * (2 - x))
  let rhox := platformRadius a / (platformCenter a - x + Kx)
  k * Real.log |x| +
    Real.log ((platformCenter a - x + Kx) / 2) -
      2 * k * Real.log (1 - rho0 * rhox)

def platformExteriorWx (k a x : ℝ) : ℝ :=
  let rho0 := (Real.sqrt 2 - Real.sqrt a) /
    (Real.sqrt 2 + Real.sqrt a)
  let Kx := Real.sqrt ((a - x) * (2 - x))
  let rhox := platformRadius a / (platformCenter a - x + Kx)
  k / x - 1 / Kx +
    2 * k * rho0 * rhox / (Kx * (1 - rho0 * rhox))

theorem platformExteriorW_eq (k a x : ℝ) :
    platformExteriorW k a x =
      k * Real.log |x| +
        Real.log ((platformCenter a - x + platformCrossingScale a x) / 2) -
      2 * k * Real.log (1 -
        ((Real.sqrt 2 - Real.sqrt a) / (Real.sqrt 2 + Real.sqrt a)) *
          platformRho a x) := by
  rfl

theorem platformExteriorWx_eq (k a x : ℝ) :
    platformExteriorWx k a x =
      k / x - 1 / platformCrossingScale a x +
        2 * k *
          ((Real.sqrt 2 - Real.sqrt a) / (Real.sqrt 2 + Real.sqrt a)) *
          platformRho a x /
        (platformCrossingScale a x *
          (1 - ((Real.sqrt 2 - Real.sqrt a) /
            (Real.sqrt 2 + Real.sqrt a)) * platformRho a x)) := by
  rfl

def platformEffectiveConstant
    (ell k a xMinus xPlus sigmaMinus sigmaPlus : ℝ) : ℝ :=
  platformPotentialConstant k a +
    (ell - (xPlus - xMinus)) /
      platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus

/-- Stable cancellation-free formula for the adjoint mass. -/
def platformAdjointMassRho
    (a xMinus xPlus sigmaMinus sigmaPlus : ℝ) : ℝ :=
  2 * sigmaMinus * platformRho a xMinus /
      (1 - platformRho a xMinus) +
    2 * sigmaPlus * platformRho a xPlus /
      (1 - platformRho a xPlus)

theorem platformAdjointMass_eq_rho
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2) :
    platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus =
      platformAdjointMassRho
        a xMinus xPlus sigmaMinus sigmaPlus := by
  have hrm := platformRho_mem_Ioo hxMinus ha2
  have hrp := platformRho_mem_Ioo hxPlus ha2
  rw [platformAdjointMass, adjointNormalization_eq_poisson_zero
    hxMinus hxPlus ha2,
    platformPoissonKernel_zero hrm.2.ne,
    platformPoissonKernel_zero hrp.2.ne]
  unfold platformAdjointMassRho
  field_simp [sub_ne_zero.mpr hrm.2.ne', sub_ne_zero.mpr hrp.2.ne']
  ring

namespace HighKPlatformFormula

abbrev E := HighKIntervalExpr 5

@[simp] def er (r : Rat) : E := .rat r
@[simp] def e0 : E := er 0
@[simp] def e1 : E := er 1
@[simp] def e2 : E := er 2
@[simp] def e4 : E := er 4

@[simp] def kE : E := .var 0
@[simp] def xmE : E := .var 1
@[simp] def xpE : E := .var 2
@[simp] def LE : E := .var 3
@[simp] def piE : E := .var 4

@[simp] theorem evalReal_sub (v : Fin 5 → ℝ) (p q : E) :
    evalReal v (.sub p q) = evalReal v p - evalReal v q := by
  simp [HighKIntervalExpr.sub, sub_eq_add_neg]

@[simp] theorem evalReal_div (v : Fin 5 → ℝ) (p q : E) :
    evalReal v (.div p q) = evalReal v p / evalReal v q := by
  simp [HighKIntervalExpr.div, evalReal, div_eq_mul_inv]

@[simp] theorem evalReal_sq (v : Fin 5 → ℝ) (p : E) :
    evalReal v (.sq p) = (evalReal v p) ^ 2 := by
  simp [HighKIntervalExpr.sq, evalReal, pow_two]

def aE : HighKPlatformEdge → E
  | .affine => .sub (er (1153 / 500)) (.div kE (er 4))
  | .constant => er (9 / 5)

def centerE (edge : HighKPlatformEdge) : E :=
  .div (.add (aE edge) e2) e2

def radiusE (edge : HighKPlatformEdge) : E :=
  .div (.sub e2 (aE edge)) e2

def capacityE (edge : HighKPlatformEdge) : E :=
  .div (.sub e2 (aE edge)) e4

def sqrtTwoE (sqrtSteps : Nat) : E := .sqrt sqrtSteps e2

def sqrtAE (sqrtSteps : Nat) (edge : HighKPlatformEdge) : E :=
  .sqrt sqrtSteps (aE edge)

def rhoZeroE (sqrtSteps : Nat) (edge : HighKPlatformEdge) : E :=
  .div (.sub (sqrtTwoE sqrtSteps) (sqrtAE sqrtSteps edge))
    (.add (sqrtTwoE sqrtSteps) (sqrtAE sqrtSteps edge))

def crossingScaleE (sqrtSteps : Nat) (edge : HighKPlatformEdge)
    (x : E) : E :=
  .sqrt sqrtSteps (.mul (.sub (aE edge) x) (.sub e2 x))

def rhoE (sqrtSteps : Nat) (edge : HighKPlatformEdge) (x : E) : E :=
  .div (radiusE edge)
    (.add (.sub (centerE edge) x) (crossingScaleE sqrtSteps edge x))

def absLogArgumentE (minus : Bool) (x : E) : E :=
  if minus then .neg x else x

def exteriorWE (logTerms sqrtSteps : Nat) (edge : HighKPlatformEdge)
    (minus : Bool) (x : E) : E :=
  .sub
    (.add (.mul kE (.log logTerms (absLogArgumentE minus x)))
      (.log logTerms (.div
        (.add (.sub (centerE edge) x) (crossingScaleE sqrtSteps edge x)) e2)))
    (.mul (.mul e2 kE) (.log logTerms
      (.sub e1 (.mul (rhoZeroE sqrtSteps edge)
        (rhoE sqrtSteps edge x)))))

def exteriorWxE (sqrtSteps : Nat) (edge : HighKPlatformEdge)
    (x : E) : E :=
  .add (.sub (.div kE x) (.inv (crossingScaleE sqrtSteps edge x)))
    (.div
      (.mul (.mul (.mul e2 kE) (rhoZeroE sqrtSteps edge))
        (rhoE sqrtSteps edge x))
      (.mul (crossingScaleE sqrtSteps edge x)
        (.sub e1 (.mul (rhoZeroE sqrtSteps edge)
          (rhoE sqrtSteps edge x)))))

def sigmaMinusE (sqrtSteps : Nat) (edge : HighKPlatformEdge) : E :=
  .neg (.inv (exteriorWxE sqrtSteps edge xmE))

def sigmaPlusE (sqrtSteps : Nat) (edge : HighKPlatformEdge) : E :=
  .inv (exteriorWxE sqrtSteps edge xpE)

def apiE (sqrtSteps : Nat) (edge : HighKPlatformEdge) : E :=
  .sub (.add kE e1)
    (.div (.mul kE (.sqrt sqrtSteps (.mul e2 (aE edge)))) e2)

def bpiTermE (sqrtSteps : Nat) (edge : HighKPlatformEdge)
    (sigma x : E) : E :=
  let rho := rhoE sqrtSteps edge x
  .div (.mul (.mul e4 sigma) rho) (.sub e1 (.sq rho))

def bpiE (sqrtSteps : Nat) (edge : HighKPlatformEdge) : E :=
  .add (bpiTermE sqrtSteps edge (sigmaMinusE sqrtSteps edge) xmE)
    (bpiTermE sqrtSteps edge (sigmaPlusE sqrtSteps edge) xpE)

def adjointMassTermE (sqrtSteps : Nat) (edge : HighKPlatformEdge)
    (sigma x : E) : E :=
  let rho := rhoE sqrtSteps edge x
  .div (.mul (.mul e2 sigma) rho) (.sub e1 rho)

def adjointMassE (sqrtSteps : Nat) (edge : HighKPlatformEdge) : E :=
  .add (adjointMassTermE sqrtSteps edge
      (sigmaMinusE sqrtSteps edge) xmE)
    (adjointMassTermE sqrtSteps edge
      (sigmaPlusE sqrtSteps edge) xpE)

def d0E (sqrtSteps : Nat) (edge : HighKPlatformEdge) : E :=
  .div (.add (.add (aE edge) e2)
    (.mul e2 (.sqrt sqrtSteps (.mul e2 (aE edge))))) e4

def potentialConstantE (logTerms sqrtSteps : Nat)
    (edge : HighKPlatformEdge) : E :=
  .add (.log logTerms (capacityE edge))
    (.mul kE (.log logTerms (d0E sqrtSteps edge)))

def mainWidthE : E := .sub xpE xmE

def ceffE (logTerms sqrtSteps : Nat) (edge : HighKPlatformEdge) : E :=
  .add (potentialConstantE logTerms sqrtSteps edge)
    (.div (.sub LE mainWidthE) (adjointMassE sqrtSteps edge))

def qmaxE (sqrtSteps : Nat) (edge : HighKPlatformEdge) : E :=
  .div piE (apiE sqrtSteps edge)

def rmaxE (sqrtSteps : Nat) (edge : HighKPlatformEdge) : E :=
  .div (.mul piE (adjointMassE sqrtSteps edge)) (bpiE sqrtSteps edge)

def penaltyE (logTerms sqrtSteps : Nat) (edge : HighKPlatformEdge) : E :=
  .neg (.div (.mul piE (ceffE logTerms sqrtSteps edge))
    (apiE sqrtSteps edge))

def sincE (trigDoubles : Nat) (q : E) : E :=
  .div (.sin trigDoubles q) q

def sincNumeratorE (trigDoubles : Nat) (q : E) : E :=
  .sub (.sin trigDoubles q) (.mul q (.cos trigDoubles q))

def affineDerivativeE (logTerms sqrtSteps trigDoubles : Nat)
    (edge : HighKPlatformEdge) (q : E) : E :=
  .add (.neg (.div (penaltyE logTerms sqrtSteps edge) (.sq q)))
    (.mul
      (.mul e2 (.sub (sincE trigDoubles q)
        (sincE trigDoubles (rmaxE sqrtSteps edge))))
      (.neg (.div (sincNumeratorE trigDoubles q) (.sq q))))

@[simp] theorem aE_eval (edge : HighKPlatformEdge) (v : Fin 5 → ℝ) :
    evalReal v (aE edge) = highKPlatformEdge edge (v 0) := by
  cases edge <;>
    simp [aE, highKPlatformEdge, div_eq_mul_inv, sub_eq_add_neg]

@[simp] theorem centerE_eval (edge : HighKPlatformEdge)
    (v : Fin 5 → ℝ) :
    evalReal v (centerE edge) =
      platformCenter (highKPlatformEdge edge (v 0)) := by
  simp [centerE, platformCenter]

@[simp] theorem radiusE_eval (edge : HighKPlatformEdge)
    (v : Fin 5 → ℝ) :
    evalReal v (radiusE edge) =
      platformRadius (highKPlatformEdge edge (v 0)) := by
  simp [radiusE, platformRadius]

@[simp] theorem capacityE_eval (edge : HighKPlatformEdge)
    (v : Fin 5 → ℝ) :
    evalReal v (capacityE edge) =
      platformCapacity (highKPlatformEdge edge (v 0)) := by
  simp [capacityE, platformCapacity]

@[simp] theorem crossingScaleE_eval (sqrtSteps : Nat)
    (edge : HighKPlatformEdge) (x : E) (v : Fin 5 → ℝ) :
    evalReal v (crossingScaleE sqrtSteps edge x) =
      platformCrossingScale (highKPlatformEdge edge (v 0))
        (evalReal v x) := by
  simp [crossingScaleE, platformCrossingScale]

@[simp] theorem rhoE_eval (sqrtSteps : Nat)
    (edge : HighKPlatformEdge) (x : E) (v : Fin 5 → ℝ) :
    evalReal v (rhoE sqrtSteps edge x) =
      platformRho (highKPlatformEdge edge (v 0)) (evalReal v x) := by
  simp [rhoE, platformRho]

@[simp] theorem rhoZeroE_eval (sqrtSteps : Nat)
    (edge : HighKPlatformEdge) (v : Fin 5 → ℝ) :
    evalReal v (rhoZeroE sqrtSteps edge) =
      (Real.sqrt 2 - Real.sqrt (highKPlatformEdge edge (v 0))) /
        (Real.sqrt 2 + Real.sqrt (highKPlatformEdge edge (v 0))) := by
  simp [rhoZeroE, sqrtTwoE, sqrtAE]

theorem exteriorWE_eval_minus (logTerms sqrtSteps : Nat)
    (edge : HighKPlatformEdge) {k xm xp ell pi : ℝ} (hxm : xm < 0) :
    evalReal ![k, xm, xp, ell, pi]
        (exteriorWE logTerms sqrtSteps edge true xmE) =
      platformExteriorW k (highKPlatformEdge edge k) xm := by
  rw [platformExteriorW_eq]
  simp [exteriorWE, absLogArgumentE, abs_of_neg hxm]

theorem exteriorWE_eval_plus (logTerms sqrtSteps : Nat)
    (edge : HighKPlatformEdge) {k xm xp ell pi : ℝ} (hxp : 0 < xp) :
    evalReal ![k, xm, xp, ell, pi]
        (exteriorWE logTerms sqrtSteps edge false xpE) =
      platformExteriorW k (highKPlatformEdge edge k) xp := by
  rw [platformExteriorW_eq]
  simp [exteriorWE, absLogArgumentE, abs_of_pos hxp]

@[simp] theorem exteriorWxE_eval (sqrtSteps : Nat)
    (edge : HighKPlatformEdge) (x : E) (v : Fin 5 → ℝ) :
    evalReal v (exteriorWxE sqrtSteps edge x) =
      platformExteriorWx (v 0) (highKPlatformEdge edge (v 0))
        (evalReal v x) := by
  rw [platformExteriorWx_eq]
  simp [exteriorWxE]

@[simp] theorem sigmaMinusE_eval (sqrtSteps : Nat)
    (edge : HighKPlatformEdge) (k xm xp ell pi : ℝ) :
    evalReal ![k, xm, xp, ell, pi] (sigmaMinusE sqrtSteps edge) =
      -1 / platformExteriorWx k (highKPlatformEdge edge k) xm := by
  simp [sigmaMinusE, div_eq_mul_inv]

@[simp] theorem sigmaPlusE_eval (sqrtSteps : Nat)
    (edge : HighKPlatformEdge) (k xm xp ell pi : ℝ) :
    evalReal ![k, xm, xp, ell, pi] (sigmaPlusE sqrtSteps edge) =
      1 / platformExteriorWx k (highKPlatformEdge edge k) xp := by
  simp [sigmaPlusE, div_eq_mul_inv]

@[simp] theorem apiE_eval (sqrtSteps : Nat)
    (edge : HighKPlatformEdge) (k xm xp ell pi : ℝ) :
    evalReal ![k, xm, xp, ell, pi] (apiE sqrtSteps edge) =
      platformAPi k (highKPlatformEdge edge k) := by
  simp [apiE, platformAPi, platformAngularDensity,
    platformDensityCoefficient, platformAngularDistance_pi,
    evalReal, aE_eval, sub, div]
  ring

@[simp] theorem bpiE_eval (sqrtSteps : Nat)
    (edge : HighKPlatformEdge) {k xm xp ell pi : ℝ}
    (hxm : xm < highKPlatformEdge edge k)
    (hxp : xp < highKPlatformEdge edge k)
    (ha2 : highKPlatformEdge edge k < 2) :
    evalReal ![k, xm, xp, ell, pi] (bpiE sqrtSteps edge) =
      platformBPi (highKPlatformEdge edge k) xm xp
        (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
        (1 / platformExteriorWx k (highKPlatformEdge edge k) xp) := by
  rw [platformBPi_eq_rho hxm hxp ha2]
  simp [bpiE, bpiTermE, div_eq_mul_inv, sub_eq_add_neg]

@[simp] theorem adjointMassE_eval (sqrtSteps : Nat)
    (edge : HighKPlatformEdge) {k xm xp ell pi : ℝ}
    (hxm : xm < highKPlatformEdge edge k)
    (hxp : xp < highKPlatformEdge edge k)
    (ha2 : highKPlatformEdge edge k < 2) :
    evalReal ![k, xm, xp, ell, pi] (adjointMassE sqrtSteps edge) =
      platformAdjointMass (highKPlatformEdge edge k) xm xp
        (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
        (1 / platformExteriorWx k (highKPlatformEdge edge k) xp) := by
  rw [platformAdjointMass_eq_rho hxm hxp ha2]
  simp [adjointMassE, adjointMassTermE, platformAdjointMassRho,
    div_eq_mul_inv, sub_eq_add_neg]

@[simp] theorem d0E_eval (sqrtSteps : Nat)
    (edge : HighKPlatformEdge) (k xm xp ell pi : ℝ) :
    evalReal ![k, xm, xp, ell, pi] (d0E sqrtSteps edge) =
      platformD0 (highKPlatformEdge edge k) := by
  simp [d0E, platformD0, div_eq_mul_inv]

@[simp] theorem potentialConstantE_eval (logTerms sqrtSteps : Nat)
    (edge : HighKPlatformEdge) (k xm xp ell pi : ℝ) :
    evalReal ![k, xm, xp, ell, pi]
        (potentialConstantE logTerms sqrtSteps edge) =
      platformPotentialConstant k (highKPlatformEdge edge k) := by
  simp [potentialConstantE, platformPotentialConstant, evalReal,
    capacityE_eval, d0E_eval]

@[simp] theorem mainWidthE_eval (k xm xp ell pi : ℝ) :
    evalReal ![k, xm, xp, ell, pi] mainWidthE = xp - xm := by
  simp [mainWidthE, sub_eq_add_neg]

@[simp] theorem ceffE_eval (logTerms sqrtSteps : Nat)
    (edge : HighKPlatformEdge) {k xm xp ell pi : ℝ}
    (hxm : xm < highKPlatformEdge edge k)
    (hxp : xp < highKPlatformEdge edge k)
    (ha2 : highKPlatformEdge edge k < 2) :
    evalReal ![k, xm, xp, ell, pi] (ceffE logTerms sqrtSteps edge) =
      platformEffectiveConstant ell k (highKPlatformEdge edge k) xm xp
        (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
        (1 / platformExteriorWx k (highKPlatformEdge edge k) xp) := by
  simp [ceffE, platformEffectiveConstant,
    adjointMassE_eval sqrtSteps edge hxm hxp ha2,
    div_eq_mul_inv, sub_eq_add_neg]

@[simp] theorem qmaxE_eval (sqrtSteps : Nat)
    (edge : HighKPlatformEdge) (k xm xp ell : ℝ) :
    evalReal ![k, xm, xp, ell, Real.pi] (qmaxE sqrtSteps edge) =
      platformReferenceCircleRadiusCap k (highKPlatformEdge edge k) := by
  simp [qmaxE, platformReferenceCircleRadiusCap, div_eq_mul_inv]

@[simp] theorem rmaxE_eval (sqrtSteps : Nat)
    (edge : HighKPlatformEdge) {k xm xp ell : ℝ}
    (hxm : xm < highKPlatformEdge edge k)
    (hxp : xp < highKPlatformEdge edge k)
    (ha2 : highKPlatformEdge edge k < 2) :
    evalReal ![k, xm, xp, ell, Real.pi] (rmaxE sqrtSteps edge) =
      platformAdjointCircleRadiusCap (highKPlatformEdge edge k) xm xp
        (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
        (1 / platformExteriorWx k (highKPlatformEdge edge k) xp) := by
  simp [rmaxE, platformAdjointCircleRadiusCap,
    adjointMassE_eval sqrtSteps edge hxm hxp ha2,
    bpiE_eval sqrtSteps edge hxm hxp ha2, div_eq_mul_inv]

@[simp] theorem penaltyE_eval (logTerms sqrtSteps : Nat)
    (edge : HighKPlatformEdge) {k xm xp ell : ℝ}
    (hxm : xm < highKPlatformEdge edge k)
    (hxp : xp < highKPlatformEdge edge k)
    (ha2 : highKPlatformEdge edge k < 2) :
    evalReal ![k, xm, xp, ell, Real.pi]
        (penaltyE logTerms sqrtSteps edge) =
      circleEffectivePenalty
        (platformAPi k (highKPlatformEdge edge k))
        (platformEffectiveConstant ell k (highKPlatformEdge edge k) xm xp
          (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
          (1 / platformExteriorWx k (highKPlatformEdge edge k) xp)) := by
  change -(Real.pi *
      evalReal ![k, xm, xp, ell, Real.pi]
        (ceffE logTerms sqrtSteps edge) /
      evalReal ![k, xm, xp, ell, Real.pi] (apiE sqrtSteps edge)) = _
  rw [ceffE_eval logTerms sqrtSteps edge hxm hxp ha2, apiE_eval]
  unfold circleEffectivePenalty
  ring

@[simp] theorem sincE_eval (trigDoubles : Nat) (q : E)
    (v : Fin 5 → ℝ) (hq : evalReal v q ≠ 0) :
    evalReal v (sincE trigDoubles q) = Real.sinc (evalReal v q) := by
  rw [Real.sinc_of_ne_zero hq]
  simp [sincE, div_eq_mul_inv]

@[simp] theorem sincNumeratorE_eval (trigDoubles : Nat) (q : E)
    (v : Fin 5 → ℝ) :
    evalReal v (sincNumeratorE trigDoubles q) =
      sincNumerator (evalReal v q) := by
  simp [sincNumeratorE, sincNumerator]

theorem affineDerivativeE_eval (logTerms sqrtSteps trigDoubles : Nat)
    (edge : HighKPlatformEdge) (q : E) {k xm xp ell : ℝ}
    (hxm : xm < highKPlatformEdge edge k)
    (hxp : xp < highKPlatformEdge edge k)
    (ha2 : highKPlatformEdge edge k < 2)
    (hq : evalReal ![k, xm, xp, ell, Real.pi] q ≠ 0)
    (hr : platformAdjointCircleRadiusCap
      (highKPlatformEdge edge k) xm xp
        (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
        (1 / platformExteriorWx k (highKPlatformEdge edge k) xp) ≠ 0) :
    evalReal ![k, xm, xp, ell, Real.pi]
        (affineDerivativeE logTerms sqrtSteps trigDoubles edge q) =
      affineCircleScalarDerivative
        (platformAPi k (highKPlatformEdge edge k))
        (platformEffectiveConstant ell k (highKPlatformEdge edge k) xm xp
          (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
          (1 / platformExteriorWx k (highKPlatformEdge edge k) xp))
        (platformAdjointCircleRadiusCap (highKPlatformEdge edge k) xm xp
          (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
          (1 / platformExteriorWx k (highKPlatformEdge edge k) xp))
        (evalReal ![k, xm, xp, ell, Real.pi] q) := by
  have hrEval : evalReal ![k, xm, xp, ell, Real.pi]
      (rmaxE sqrtSteps edge) ≠ 0 := by
    simpa [rmaxE_eval sqrtSteps edge hxm hxp ha2] using! hr
  simp [affineDerivativeE, affineCircleScalarDerivative,
    sincE_eval _ _ _ hq, sincE_eval _ _ _ hrEval,
    penaltyE_eval logTerms sqrtSteps edge hxm hxp ha2,
    rmaxE_eval sqrtSteps edge hxm hxp ha2,
    div_eq_mul_inv, sub_eq_add_neg]

end HighKPlatformFormula

end

end Erdos1038
