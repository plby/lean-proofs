import Mathlib

/-!
# The three-circle / four-bar finiteness lemma

The coordinates are normalized as in Section 5 of the mathematical write-up.
The proof uses adjugate numerators and never divides by their determinant.
-/

namespace Erdos215.Circle

open Polynomial

noncomputable section

def normSq (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2

/-- The normalized system (5.4), including the unit direction equation. -/
def NormalizedSolution
    (A B C R S d u v : ℝ) (z : ℝ × ℝ × ℝ × ℝ) : Prop :=
  let x := z.1
  let y := z.2.1
  let X := z.2.2.1
  let Y := z.2.2.2
  x ^ 2 + y ^ 2 = 1 ∧
    X ^ 2 + Y ^ 2 = 1 ∧
    (x + d * X - A) ^ 2 + (y + d * Y) ^ 2 = R ^ 2 ∧
    (x + u * X - v * Y - B) ^ 2 +
      (y + v * X + u * Y - C) ^ 2 = S ^ 2

private def fCert (A B C d u v : ℝ) : ℝ :=
  A * B * d * v - 2 * A * B * u * v - A * C * d * u + A * C * u ^ 2 -
    A * C * v ^ 2 - B ^ 2 * d * v + 2 * B ^ 2 * u * v + 2 * B * C * d * u -
    2 * B * C * u ^ 2 + 2 * B * C * v ^ 2 + C ^ 2 * d * v - 2 * C ^ 2 * u * v

private def gCert (A B C d u v : ℝ) : ℝ :=
  -A * B * d * u + A * B * u ^ 2 - A * B * v ^ 2 - A * C * d * v +
    2 * A * C * u * v + B ^ 2 * d * u - B ^ 2 * u ^ 2 + B ^ 2 * v ^ 2 +
    2 * B * C * d * v - 4 * B * C * u * v - C ^ 2 * d * u + C ^ 2 * u ^ 2 -
    C ^ 2 * v ^ 2

private def hOne (A B C d u v : ℝ) : ℝ :=
  -A * B * v - A * C * d + 2 * A * C * u + B ^ 2 * v + 2 * B * C * d -
    4 * B * C * u - C ^ 2 * v

private def hTwo (A B C d u v : ℝ) : ℝ :=
  -A * B * d + 2 * A * B * u + A * C * v + B ^ 2 * d - 2 * B ^ 2 * u -
    2 * B * C * v - C ^ 2 * d + 2 * C ^ 2 * u

private lemma bezout_certificate (A B C d u v : ℝ) :
    hOne A B C d u v * fCert A B C d u v +
        hTwo A B C d u v * gCert A B C d u v =
      u * (B ^ 2 + C ^ 2) * (u - d) * (2 * u - d) * ((A - B) ^ 2 + C ^ 2) := by
  simp only [hOne, hTwo, fCert, gCert]
  ring

private def eOneZero (A B C d v : ℝ) : ℝ :=
  -A * B * d + A * C * v + B ^ 2 * d - 2 * B * C * v - C ^ 2 * d

private def eTwoZero (A B C d v : ℝ) : ℝ :=
  A * B * v + A * C * d - B ^ 2 * v - 2 * B * C * d + C ^ 2 * v

private lemma zero_case_sum_certificate (A B C d v : ℝ) :
    eOneZero A B C d v ^ 2 + eTwoZero A B C d v ^ 2 =
      (B ^ 2 + C ^ 2) * (d ^ 2 + v ^ 2) * ((A - B) ^ 2 + C ^ 2) := by
  simp only [eOneZero, eTwoZero]
  ring

private def eOneD (A B C d v : ℝ) : ℝ :=
  A * B * d + A * C * v - B ^ 2 * d - 2 * B * C * v + C ^ 2 * d

private def eTwoD (A B C d v : ℝ) : ℝ :=
  A * B * v - A * C * d - B ^ 2 * v + 2 * B * C * d + C ^ 2 * v

private lemma d_case_sum_certificate (A B C d v : ℝ) :
    eOneD A B C d v ^ 2 + eTwoD A B C d v ^ 2 =
      (B ^ 2 + C ^ 2) * (d ^ 2 + v ^ 2) * ((A - B) ^ 2 + C ^ 2) := by
  simp only [eOneD, eTwoD]
  ring

private lemma f_zero_case (A B C d v : ℝ) :
    fCert A B C d 0 v = -v * eOneZero A B C d v := by
  simp only [fCert, eOneZero]
  ring

private lemma g_zero_case (A B C d v : ℝ) :
    gCert A B C d 0 v = -v * eTwoZero A B C d v := by
  simp only [gCert, eTwoZero]
  ring

private lemma f_d_case (A B C d v : ℝ) :
    fCert A B C d d v = -v * eOneD A B C d v := by
  simp only [fCert, eOneD]
  ring

private lemma g_d_case (A B C d v : ℝ) :
    gCert A B C d d v = -v * eTwoD A B C d v := by
  simp only [gCert, eTwoD]
  ring

private lemma half_case_f (A B C d u v : ℝ) (h : 2 * u = d) :
    4 * fCert A B C d u v = -C * (A - 2 * B) * (d ^ 2 + 4 * v ^ 2) := by
  rw [← h]
  simp only [fCert]
  ring

private lemma half_case_g (A B C d u v : ℝ) (h : 2 * u = d) :
    4 * gCert A B C d u v =
      -(A * B - B ^ 2 + C ^ 2) * (d ^ 2 + 4 * v ^ 2) := by
  rw [← h]
  simp only [gCert]
  ring

/-- The seven-term trigonometric polynomial occurring after adjugate
elimination in (5.5). -/
def directionExpr (q00 q01 q10 q11 q20 q21 q30 : ℝ) (p : ℝ × ℝ) : ℝ :=
  q00 + q01 * p.2 + q10 * p.1 + q11 * p.1 * p.2 + q20 * p.1 ^ 2 +
    q21 * p.1 ^ 2 * p.2 + q30 * p.1 ^ 3

/-- The standard rational parametrization of the unit circle, omitting
`(-1,0)`. -/
def circleParam (t : ℝ) : ℝ × ℝ :=
  ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2))

def circleSlope (p : ℝ × ℝ) : ℝ := p.2 / (1 + p.1)

@[simp]
lemma circleParam_mem (t : ℝ) : normSq (circleParam t) = 1 := by
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  simp only [normSq, circleParam]
  field_simp [hden]
  ring

lemma circleParam_circleSlope {p : ℝ × ℝ} (hunit : normSq p = 1)
    (hne : p ≠ (-1, 0)) : circleParam (circleSlope p) = p := by
  rcases p with ⟨x, y⟩
  have hxy : x ^ 2 + y ^ 2 = 1 := hunit
  have hx : 1 + x ≠ 0 := by
    intro hx
    have hxeq : x = -1 := by linarith
    have hyeq : y = 0 := by nlinarith
    exact hne (by simp [hxeq, hyeq])
  have ht : 1 + (y / (1 + x)) ^ 2 ≠ 0 := by positivity
  ext <;> simp only [circleParam, circleSlope, Prod.fst, Prod.snd]
  · field_simp [hx, ht]
    nlinarith
  · field_simp [hx, ht]
    have hy := congrArg (fun z : ℝ ↦ 2 * y * z) hxy
    nlinarith [hy]

lemma circleSlope_injOn :
    Set.InjOn circleSlope {p : ℝ × ℝ | normSq p = 1 ∧ p ≠ (-1, 0)} := by
  intro p hp q hq hpq
  rw [← circleParam_circleSlope hp.1 hp.2, ← circleParam_circleSlope hq.1 hq.2, hpq]

/-- Clearing the common denominator after the unit-circle parametrization. -/
def directionPoly (q00 q01 q10 q11 q20 q21 q30 : ℝ) : Polynomial ℝ :=
  monomial 0 (q00 + q10 + q20 + q30) +
    monomial 1 (2 * q01 + 2 * q11 + 2 * q21) +
    monomial 2 (3 * q00 + q10 - q20 - 3 * q30) +
    monomial 3 (4 * q01 - 4 * q21) +
    monomial 4 (3 * q00 - q10 - q20 + 3 * q30) +
    monomial 5 (2 * q01 - 2 * q11 + 2 * q21) +
    monomial 6 (q00 - q10 + q20 - q30)

lemma directionPoly_eval (q00 q01 q10 q11 q20 q21 q30 t : ℝ) :
    (directionPoly q00 q01 q10 q11 q20 q21 q30).eval t =
      (1 + t ^ 2) ^ 3 *
        directionExpr q00 q01 q10 q11 q20 q21 q30 (circleParam t) := by
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  simp [directionPoly, directionExpr, circleParam]
  field_simp [hden]
  ring

lemma directionPoly_expansion (q00 q01 q10 q11 q20 q21 q30 : ℝ) :
    directionPoly q00 q01 q10 q11 q20 q21 q30 =
      monomial 0 (q00 + q10 + q20 + q30) +
      monomial 1 (2 * q01 + 2 * q11 + 2 * q21) +
      monomial 2 (3 * q00 + q10 - q20 - 3 * q30) +
      monomial 3 (4 * q01 - 4 * q21) +
      monomial 4 (3 * q00 - q10 - q20 + 3 * q30) +
      monomial 5 (2 * q01 - 2 * q11 + 2 * q21) +
      monomial 6 (q00 - q10 + q20 - q30) := by
  rfl

/-- Linear independence of the seven reduced circle monomials.  For the
main argument only the `X²Y` and `X³` coefficients are needed. -/
lemma directionPoly_eq_zero_forces_last
    (q00 q01 q10 q11 q20 q21 q30 : ℝ)
    (hzero : directionPoly q00 q01 q10 q11 q20 q21 q30 = 0) :
    q21 = 0 ∧ q30 = 0 := by
  rw [directionPoly_expansion] at hzero
  have h0 := congrArg (fun p : Polynomial ℝ ↦ p.coeff 0) hzero
  have h1 := congrArg (fun p : Polynomial ℝ ↦ p.coeff 1) hzero
  have h2 := congrArg (fun p : Polynomial ℝ ↦ p.coeff 2) hzero
  have h3 := congrArg (fun p : Polynomial ℝ ↦ p.coeff 3) hzero
  have h4 := congrArg (fun p : Polynomial ℝ ↦ p.coeff 4) hzero
  have h5 := congrArg (fun p : Polynomial ℝ ↦ p.coeff 5) hzero
  have h6 := congrArg (fun p : Polynomial ℝ ↦ p.coeff 6) hzero
  simp only [coeff_add, coeff_monomial, coeff_zero] at h0 h1 h2 h3 h4 h5 h6
  norm_num at h0 h1 h2 h3 h4 h5 h6
  constructor <;> nlinarith

lemma infinite_param_zero_forces_last
    (q00 q01 q10 q11 q20 q21 q30 : ℝ)
    (hinf : Set.Infinite {t : ℝ |
      directionExpr q00 q01 q10 q11 q20 q21 q30 (circleParam t) = 0}) :
    q21 = 0 ∧ q30 = 0 := by
  have hroots : Set.Infinite {t : ℝ |
      (directionPoly q00 q01 q10 q11 q20 q21 q30).IsRoot t} := by
    apply hinf.mono
    intro t ht
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot]
    rw [directionPoly_eval, ht, mul_zero]
  exact directionPoly_eq_zero_forces_last q00 q01 q10 q11 q20 q21 q30
    ((directionPoly q00 q01 q10 q11 q20 q21 q30).eq_zero_of_infinite_isRoot hroots)

lemma infinite_circle_zero_forces_last
    (q00 q01 q10 q11 q20 q21 q30 : ℝ) (D : Set (ℝ × ℝ))
    (hinf : D.Infinite) (hunit : ∀ p ∈ D, normSq p = 1)
    (hzero : ∀ p ∈ D, directionExpr q00 q01 q10 q11 q20 q21 q30 p = 0) :
    q21 = 0 ∧ q30 = 0 := by
  let D' : Set (ℝ × ℝ) := D \ {(-1, 0)}
  have hD'inf : D'.Infinite := hinf.diff (Set.finite_singleton (-1, 0))
  have hinj : Set.InjOn circleSlope D' := by
    apply circleSlope_injOn.mono
    intro p hp
    exact ⟨hunit p hp.1, hp.2⟩
  have himage : (circleSlope '' D').Infinite := hD'inf.image hinj
  apply infinite_param_zero_forces_last q00 q01 q10 q11 q20 q21 q30
  apply himage.mono
  rintro t ⟨p, hp, rfl⟩
  change directionExpr q00 q01 q10 q11 q20 q21 q30
    (circleParam (circleSlope p)) = 0
  rw [circleParam_circleSlope (hunit p hp.1) hp.2]
  exact hzero p hp.1

/-! ## The determinant-free eliminant -/

private def alphaOne (A d X : ℝ) : ℝ := 2 * (d * X - A)
private def betaOne (d Y : ℝ) : ℝ := 2 * d * Y
private def gammaOne (A R d X : ℝ) : ℝ :=
  d ^ 2 + A ^ 2 + 1 - R ^ 2 - 2 * A * d * X

private def qx (u v X Y : ℝ) : ℝ := u * X - v * Y
private def qy (u v X Y : ℝ) : ℝ := v * X + u * Y
private def alphaTwo (B u v X Y : ℝ) : ℝ := 2 * (qx u v X Y - B)
private def betaTwo (C u v X Y : ℝ) : ℝ := 2 * (qy u v X Y - C)
private def gammaTwo (B C S u v X Y : ℝ) : ℝ :=
  u ^ 2 + v ^ 2 + B ^ 2 + C ^ 2 + 1 - S ^ 2 -
    2 * B * qx u v X Y - 2 * C * qy u v X Y

private def delta (A B C d u v X Y : ℝ) : ℝ :=
  alphaOne A d X * betaTwo C u v X Y - alphaTwo B u v X Y * betaOne d Y
private def numX (A B C R S d u v X Y : ℝ) : ℝ :=
  betaOne d Y * gammaTwo B C S u v X Y -
    betaTwo C u v X Y * gammaOne A R d X
private def numY (A B C R S d u v X Y : ℝ) : ℝ :=
  alphaTwo B u v X Y * gammaOne A R d X -
    alphaOne A d X * gammaTwo B C S u v X Y

/-- Equation (5.5a), with no division by `delta`. -/
def eliminant (A B C R S d u v X Y : ℝ) : ℝ :=
  (numX A B C R S d u v X Y ^ 2 + numY A B C R S d u v X Y ^ 2 -
    delta A B C d u v X Y ^ 2) / 4

/-- The denominator-cleared eliminant after substituting the rational
parametrization of the unit circle. -/
private def pDen : Polynomial ℝ := 1 + X ^ 2
private def pXN : Polynomial ℝ := 1 - X ^ 2
private def pYN : Polynomial ℝ := 2 * X
private def pA1 (A d : ℝ) : Polynomial ℝ :=
  2 * (Polynomial.C d * pXN - Polynomial.C A * pDen)
private def pB1 (d : ℝ) : Polynomial ℝ := 2 * Polynomial.C d * pYN
private def pG1 (A R d : ℝ) : Polynomial ℝ :=
  Polynomial.C (d ^ 2 + A ^ 2 + 1 - R ^ 2) * pDen -
    2 * Polynomial.C (A * d) * pXN
private def pQX (u v : ℝ) : Polynomial ℝ :=
  Polynomial.C u * pXN - Polynomial.C v * pYN
private def pQY (u v : ℝ) : Polynomial ℝ :=
  Polynomial.C v * pXN + Polynomial.C u * pYN
private def pA2 (B u v : ℝ) : Polynomial ℝ :=
  2 * (pQX u v - Polynomial.C B * pDen)
private def pB2 (C u v : ℝ) : Polynomial ℝ :=
  2 * (pQY u v - Polynomial.C C * pDen)
private def pG2 (B C S u v : ℝ) : Polynomial ℝ :=
  Polynomial.C (u ^ 2 + v ^ 2 + B ^ 2 + C ^ 2 + 1 - S ^ 2) * pDen -
    2 * Polynomial.C B * pQX u v - 2 * Polynomial.C C * pQY u v
private def pDelta (A B C d u v : ℝ) : Polynomial ℝ :=
  pA1 A d * pB2 C u v - pA2 B u v * pB1 d
private def pNumX (A B C R S d u v : ℝ) : Polynomial ℝ :=
  pB1 d * pG2 B C S u v - pB2 C u v * pG1 A R d
private def pNumY (A B C R S d u v : ℝ) : Polynomial ℝ :=
  pA2 B u v * pG1 A R d - pA1 A d * pG2 B C S u v

private def parameterElimPoly (A B C R S d u v : ℝ) : Polynomial ℝ :=
  pNumX A B C R S d u v ^ 2 + pNumY A B C R S d u v ^ 2 -
    pDelta A B C d u v ^ 2

private lemma pDen_eval (t : ℝ) : pDen.eval t = 1 + t ^ 2 := by simp [pDen]
private lemma pA1_eval (A d t : ℝ) :
    (pA1 A d).eval t = (1 + t ^ 2) * alphaOne A d (circleParam t).1 := by
  have h : 1 + t ^ 2 ≠ 0 := by positivity
  simp [pA1, pXN, pDen, circleParam, alphaOne]
  field_simp [h]
private lemma pB1_eval (d t : ℝ) :
    (pB1 d).eval t = (1 + t ^ 2) * betaOne d (circleParam t).2 := by
  have h : 1 + t ^ 2 ≠ 0 := by positivity
  simp [pB1, pYN, circleParam, betaOne]
  field_simp [h]
private lemma pQX_eval (u v t : ℝ) :
    (pQX u v).eval t = (1 + t ^ 2) * qx u v (circleParam t).1 (circleParam t).2 := by
  have h : 1 + t ^ 2 ≠ 0 := by positivity
  simp [pQX, pXN, pYN, circleParam, qx]
  field_simp [h]
private lemma pQY_eval (u v t : ℝ) :
    (pQY u v).eval t = (1 + t ^ 2) * qy u v (circleParam t).1 (circleParam t).2 := by
  have h : 1 + t ^ 2 ≠ 0 := by positivity
  simp [pQY, pXN, pYN, circleParam, qy]
  field_simp [h]
private lemma pG1_eval (A R d t : ℝ) :
    (pG1 A R d).eval t = (1 + t ^ 2) * gammaOne A R d (circleParam t).1 := by
  have h : 1 + t ^ 2 ≠ 0 := by positivity
  simp [pG1, pDen, pXN, circleParam, gammaOne]
  field_simp [h]
private lemma pA2_eval (B u v t : ℝ) :
    (pA2 B u v).eval t =
      (1 + t ^ 2) * alphaTwo B u v (circleParam t).1 (circleParam t).2 := by
  simp only [pA2, eval_mul, eval_sub, pQX_eval, eval_ofNat, eval_C, pDen_eval,
    alphaTwo]
  ring
private lemma pB2_eval (C u v t : ℝ) :
    (pB2 C u v).eval t =
      (1 + t ^ 2) * betaTwo C u v (circleParam t).1 (circleParam t).2 := by
  simp only [pB2, eval_mul, eval_sub, pQY_eval, eval_ofNat, eval_C, pDen_eval,
    betaTwo]
  ring
private lemma pG2_eval (B C S u v t : ℝ) :
    (pG2 B C S u v).eval t =
      (1 + t ^ 2) * gammaTwo B C S u v (circleParam t).1 (circleParam t).2 := by
  simp only [pG2, eval_sub, eval_mul, eval_C, eval_ofNat, pDen_eval, pQX_eval,
    pQY_eval, gammaTwo]
  ring
private lemma pDelta_eval (A B C d u v t : ℝ) :
    (pDelta A B C d u v).eval t =
      (1 + t ^ 2) ^ 2 * delta A B C d u v (circleParam t).1 (circleParam t).2 := by
  rw [pDelta, eval_sub, eval_mul, eval_mul, pA1_eval, pB2_eval, pA2_eval, pB1_eval]
  simp only [delta]
  ring
private lemma pNumX_eval (A B C R S d u v t : ℝ) :
    (pNumX A B C R S d u v).eval t =
      (1 + t ^ 2) ^ 2 * numX A B C R S d u v (circleParam t).1 (circleParam t).2 := by
  rw [pNumX, eval_sub, eval_mul, eval_mul, pB1_eval, pG2_eval, pB2_eval, pG1_eval]
  simp only [numX]
  ring
private lemma pNumY_eval (A B C R S d u v t : ℝ) :
    (pNumY A B C R S d u v).eval t =
      (1 + t ^ 2) ^ 2 * numY A B C R S d u v (circleParam t).1 (circleParam t).2 := by
  rw [pNumY, eval_sub, eval_mul, eval_mul, pA2_eval, pG1_eval, pA1_eval, pG2_eval]
  simp only [numY]
  ring

private lemma parameterElimPoly_eval (A B C R S d u v t : ℝ) :
    (parameterElimPoly A B C R S d u v).eval t =
      4 * (1 + t ^ 2) ^ 4 *
        eliminant A B C R S d u v (circleParam t).1 (circleParam t).2 := by
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  rw [parameterElimPoly, eval_sub, eval_add, eval_pow, eval_pow, eval_pow,
    pNumX_eval, pNumY_eval, pDelta_eval]
  simp only [eliminant]
  field_simp

private def oddCoeffFunctional (p : Polynomial ℝ) : ℝ :=
  3 * p.coeff 1 + p.coeff 5 - 2 * p.coeff 3

private def evenCoeffFunctional (p : Polynomial ℝ) : ℝ :=
  4 * p.coeff 0 - 3 * p.coeff 2 + 2 * p.coeff 4 - p.coeff 6

private lemma oddCoeffFunctional_add (p q : Polynomial ℝ) :
    oddCoeffFunctional (p + q) = oddCoeffFunctional p + oddCoeffFunctional q := by
  simp only [oddCoeffFunctional, coeff_add]
  ring

private lemma oddCoeffFunctional_sub (p q : Polynomial ℝ) :
    oddCoeffFunctional (p - q) = oddCoeffFunctional p - oddCoeffFunctional q := by
  simp only [oddCoeffFunctional, coeff_sub]
  ring

private lemma evenCoeffFunctional_add (p q : Polynomial ℝ) :
    evenCoeffFunctional (p + q) = evenCoeffFunctional p + evenCoeffFunctional q := by
  simp only [evenCoeffFunctional, coeff_add]
  ring

private lemma evenCoeffFunctional_sub (p q : Polynomial ℝ) :
    evenCoeffFunctional (p - q) = evenCoeffFunctional p - evenCoeffFunctional q := by
  simp only [evenCoeffFunctional, coeff_sub]
  ring

private lemma oddCoeffFunctional_sq (p : Polynomial ℝ) :
    oddCoeffFunctional (p ^ 2) =
      6 * p.coeff 0 * p.coeff 1 + 2 * p.coeff 0 * p.coeff 5 +
      2 * p.coeff 1 * p.coeff 4 + 2 * p.coeff 2 * p.coeff 3 -
      4 * p.coeff 0 * p.coeff 3 - 4 * p.coeff 1 * p.coeff 2 := by
  simp only [oddCoeffFunctional, pow_two, coeff_mul]
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

private lemma evenCoeffFunctional_sq (p : Polynomial ℝ) :
    evenCoeffFunctional (p ^ 2) =
      4 * p.coeff 0 ^ 2 - 6 * p.coeff 0 * p.coeff 2 - 3 * p.coeff 1 ^ 2 +
      4 * p.coeff 0 * p.coeff 4 + 4 * p.coeff 1 * p.coeff 3 +
      2 * p.coeff 2 ^ 2 - 2 * p.coeff 0 * p.coeff 6 -
      2 * p.coeff 1 * p.coeff 5 - 2 * p.coeff 2 * p.coeff 4 - p.coeff 3 ^ 2 := by
  simp only [evenCoeffFunctional, pow_two, coeff_mul]
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

private def quadPoly (a b c : ℝ) : Polynomial ℝ :=
  Polynomial.C a + Polynomial.C b * X + Polynomial.C c * X ^ 2

private def quarticPoly (a b c d e : ℝ) : Polynomial ℝ :=
  Polynomial.C a + Polynomial.C b * X + Polynomial.C c * X ^ 2 +
    Polynomial.C d * X ^ 3 + Polynomial.C e * X ^ 4

private lemma quadPoly_mul (a b c d e f : ℝ) :
    quadPoly a b c * quadPoly d e f =
      quarticPoly (a * d) (a * e + b * d) (a * f + b * e + c * d)
        (b * f + c * e) (c * f) := by
  simp only [quadPoly, quarticPoly]
  norm_num [map_add, map_mul, Polynomial.C_ofNat]
  ring

@[simp] private lemma quarticPoly_coeff_zero (a b c d e : ℝ) :
    (quarticPoly a b c d e).coeff 0 = a := by simp [quarticPoly]
@[simp] private lemma quarticPoly_coeff_one (a b c d e : ℝ) :
    (quarticPoly a b c d e).coeff 1 = b := by simp [quarticPoly]
@[simp] private lemma quarticPoly_coeff_two (a b c d e : ℝ) :
    (quarticPoly a b c d e).coeff 2 = c := by simp [quarticPoly]
@[simp] private lemma quarticPoly_coeff_three (a b c d e : ℝ) :
    (quarticPoly a b c d e).coeff 3 = d := by simp [quarticPoly]
@[simp] private lemma quarticPoly_coeff_four (a b c d e : ℝ) :
    (quarticPoly a b c d e).coeff 4 = e := by simp [quarticPoly]
@[simp] private lemma quarticPoly_coeff_five (a b c d e : ℝ) :
    (quarticPoly a b c d e).coeff 5 = 0 := by simp [quarticPoly]
@[simp] private lemma quarticPoly_coeff_six (a b c d e : ℝ) :
    (quarticPoly a b c d e).coeff 6 = 0 := by simp [quarticPoly]

private lemma pA1_quad (A d : ℝ) :
    pA1 A d = quadPoly (2 * (d - A)) 0 (-2 * (d + A)) := by
  simp only [pA1, pXN, pDen, quadPoly]
  norm_num [map_add, map_sub, map_mul, map_neg]
  simp only [Polynomial.C_ofNat]
  ring
private lemma pB1_quad (d : ℝ) : pB1 d = quadPoly 0 (4 * d) 0 := by
  simp only [pB1, pYN, quadPoly]
  norm_num [map_add, map_sub, map_mul, map_neg]
  simp only [Polynomial.C_ofNat]
  ring
private lemma pG1_quad (A R d : ℝ) :
    pG1 A R d =
      quadPoly (d ^ 2 + A ^ 2 + 1 - R ^ 2 - 2 * A * d) 0
        (d ^ 2 + A ^ 2 + 1 - R ^ 2 + 2 * A * d) := by
  simp only [pG1, pDen, pXN, quadPoly]
  norm_num [map_add, map_sub, map_mul, map_neg]
  simp only [Polynomial.C_ofNat]
  ring
private lemma pA2_quad (B u v : ℝ) :
    pA2 B u v = quadPoly (2 * (u - B)) (-4 * v) (-2 * (u + B)) := by
  simp only [pA2, pQX, pXN, pYN, pDen, quadPoly]
  norm_num [map_add, map_sub, map_mul, map_neg]
  simp only [Polynomial.C_ofNat]
  ring
private lemma pB2_quad (C u v : ℝ) :
    pB2 C u v = quadPoly (2 * (v - C)) (4 * u) (-2 * (v + C)) := by
  simp only [pB2, pQY, pXN, pYN, pDen, quadPoly]
  norm_num [map_add, map_sub, map_mul, map_neg]
  simp only [Polynomial.C_ofNat]
  ring
private lemma pG2_quad (B C S u v : ℝ) :
    pG2 B C S u v =
      quadPoly
        (u ^ 2 + v ^ 2 + B ^ 2 + C ^ 2 + 1 - S ^ 2 - 2 * B * u - 2 * C * v)
        (4 * B * v - 4 * C * u)
        (u ^ 2 + v ^ 2 + B ^ 2 + C ^ 2 + 1 - S ^ 2 + 2 * B * u + 2 * C * v) := by
  simp only [pG2, pQX, pQY, pDen, pXN, pYN, quadPoly]
  norm_num [map_add, map_sub, map_mul, map_neg]
  simp only [Polynomial.C_ofNat]
  ring

private lemma parameterElimPoly_odd_certificate (A B C R S d u v : ℝ) :
    oddCoeffFunctional (parameterElimPoly A B C R S d u v) =
      256 * A * d * fCert A B C d u v := by
  rw [parameterElimPoly, oddCoeffFunctional_sub, oddCoeffFunctional_add,
    oddCoeffFunctional_sq, oddCoeffFunctional_sq, oddCoeffFunctional_sq]
  simp only [pNumX, pNumY, pDelta]
  rw [pB1_quad, pG2_quad, pB2_quad, pG1_quad, pA2_quad, pA1_quad]
  repeat' rw [quadPoly_mul]
  simp only [coeff_add, coeff_sub, quarticPoly_coeff_zero, quarticPoly_coeff_one,
    quarticPoly_coeff_two, quarticPoly_coeff_three, quarticPoly_coeff_four,
    quarticPoly_coeff_five, fCert]
  ring

private lemma parameterElimPoly_even_certificate (A B C R S d u v : ℝ) :
    evenCoeffFunctional (parameterElimPoly A B C R S d u v) =
      256 * A * d * gCert A B C d u v := by
  rw [parameterElimPoly, evenCoeffFunctional_sub, evenCoeffFunctional_add,
    evenCoeffFunctional_sq, evenCoeffFunctional_sq, evenCoeffFunctional_sq]
  simp only [pNumX, pNumY, pDelta]
  rw [pB1_quad, pG2_quad, pB2_quad, pG1_quad, pA2_quad, pA1_quad]
  repeat' rw [quadPoly_mul]
  simp only [coeff_add, coeff_sub, quarticPoly_coeff_zero, quarticPoly_coeff_one,
    quarticPoly_coeff_two, quarticPoly_coeff_three, quarticPoly_coeff_four,
    quarticPoly_coeff_five, quarticPoly_coeff_six, gCert]
  ring

private lemma certs_not_both_zero
    {A B C d u v : ℝ} (hd : 0 < d)
    (hc13 : 0 < B ^ 2 + C ^ 2) (hc23 : 0 < (A - B) ^ 2 + C ^ 2)
    (ht13 : 0 < u ^ 2 + v ^ 2) (ht23 : 0 < (u - d) ^ 2 + v ^ 2) :
    fCert A B C d u v ≠ 0 ∨ gCert A B C d u v ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨hF, hG⟩
  have hb := bezout_certificate A B C d u v
  rw [hF, hG] at hb
  simp only [mul_zero, zero_mul, add_zero] at hb
  have hbc : B ^ 2 + C ^ 2 ≠ 0 := ne_of_gt hc13
  have hac : (A - B) ^ 2 + C ^ 2 ≠ 0 := ne_of_gt hc23
  have hprod : u * (u - d) * (2 * u - d) = 0 := by
    have hz : u * (B ^ 2 + C ^ 2) * (u - d) * (2 * u - d) = 0 :=
      (mul_eq_zero.mp hb.symm).resolve_right hac
    rcases mul_eq_zero.mp hz with hz | hz
    · rcases mul_eq_zero.mp hz with hz | hud
      · have hu : u = 0 := (mul_eq_zero.mp hz).resolve_right hbc
        simp [hu]
      · simp [hud]
    · simp [hz]
  rcases mul_eq_zero.mp hprod with huud | hhalf
  · rcases mul_eq_zero.mp huud with hu | hud
    · have hv : v ≠ 0 := by
        intro hv
        rw [hu, hv] at ht13
        norm_num at ht13
      have hF0 : fCert A B C d 0 v = 0 := by simpa [hu] using hF
      have hG0 : gCert A B C d 0 v = 0 := by simpa [hu] using hG
      have he1 : eOneZero A B C d v = 0 := by
        have hh := f_zero_case A B C d v
        rw [hF0] at hh
        exact (mul_eq_zero.mp hh.symm).resolve_left (neg_ne_zero.mpr hv)
      have he2 : eTwoZero A B C d v = 0 := by
        have hh := g_zero_case A B C d v
        rw [hG0] at hh
        exact (mul_eq_zero.mp hh.symm).resolve_left (neg_ne_zero.mpr hv)
      have hs := zero_case_sum_certificate A B C d v
      rw [he1, he2] at hs
      norm_num at hs
      have hdv : 0 < d ^ 2 + v ^ 2 := by positivity
      rcases hs with (h | h) | h
      · exact hbc h
      · exact (ne_of_gt hdv) h
      · exact hac h
    · have hu : u = d := sub_eq_zero.mp hud
      have hv : v ≠ 0 := by
        intro hv
        rw [hu, hv] at ht23
        norm_num at ht23
      have hFd : fCert A B C d d v = 0 := by simpa [hu] using hF
      have hGd : gCert A B C d d v = 0 := by simpa [hu] using hG
      have he1 : eOneD A B C d v = 0 := by
        have hh := f_d_case A B C d v
        rw [hFd] at hh
        exact (mul_eq_zero.mp hh.symm).resolve_left (neg_ne_zero.mpr hv)
      have he2 : eTwoD A B C d v = 0 := by
        have hh := g_d_case A B C d v
        rw [hGd] at hh
        exact (mul_eq_zero.mp hh.symm).resolve_left (neg_ne_zero.mpr hv)
      have hs := d_case_sum_certificate A B C d v
      rw [he1, he2] at hs
      norm_num at hs
      have hdv : 0 < d ^ 2 + v ^ 2 := by positivity
      rcases hs with (h | h) | h
      · exact hbc h
      · exact (ne_of_gt hdv) h
      · exact hac h
  · have hhalf' : 2 * u = d := sub_eq_zero.mp hhalf
    have hfac : d ^ 2 + 4 * v ^ 2 ≠ 0 := by positivity
    have hf := half_case_f A B C d u v hhalf'
    have hg := half_case_g A B C d u v hhalf'
    rw [hF] at hf
    rw [hG] at hg
    have hcf : C * (A - 2 * B) = 0 := by
      have hz : (-C * (A - 2 * B)) * (d ^ 2 + 4 * v ^ 2) = 0 := by
        simpa using hf.symm
      have := (mul_eq_zero.mp hz).resolve_right hfac
      simpa only [neg_mul, neg_eq_zero] using this
    have habc : A * B - B ^ 2 + C ^ 2 = 0 := by
      have hz : (-(A * B - B ^ 2 + C ^ 2)) * (d ^ 2 + 4 * v ^ 2) = 0 := by
        simpa using hg.symm
      exact neg_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hfac)
    rcases mul_eq_zero.mp hcf with hC | hAB
    · rw [hC] at hc13 hc23 habc
      norm_num at hc13 hc23 habc
      have hB : B ≠ 0 := by nlinarith
      have hAmB : A - B ≠ 0 := by nlinarith
      exact hAmB ((mul_eq_zero.mp (by nlinarith [habc] : B * (A - B) = 0)).resolve_left hB)
    · have hA2B : A = 2 * B := sub_eq_zero.mp hAB
      rw [hA2B] at habc
      nlinarith

private lemma normalizedSolution_eliminant
    {A B C R S d u v x y X Y : ℝ}
    (hz : NormalizedSolution A B C R S d u v (x, y, X, Y)) :
    eliminant A B C R S d u v X Y = 0 := by
  rcases hz with ⟨hxy, hXY, h2, h3⟩
  have hl1 : alphaOne A d X * x + betaOne d Y * y + gammaOne A R d X = 0 := by
    simp only [alphaOne, betaOne, gammaOne]
    nlinarith
  have hl2 : alphaTwo B u v X Y * x + betaTwo C u v X Y * y +
      gammaTwo B C S u v X Y = 0 := by
    simp only [alphaTwo, betaTwo, gammaTwo, qx, qy]
    nlinarith
  have hx : delta A B C d u v X Y * x = numX A B C R S d u v X Y := by
    simp only [delta, numX]
    linear_combination betaTwo C u v X Y * hl1 - betaOne d Y * hl2
  have hy : delta A B C d u v X Y * y = numY A B C R S d u v X Y := by
    simp only [delta, numY]
    linear_combination alphaOne A d X * hl2 - alphaTwo B u v X Y * hl1
  rw [eliminant, ← hx, ← hy]
  have :
      ((delta A B C d u v X Y * x) ^ 2 + (delta A B C d u v X Y * y) ^ 2 -
          delta A B C d u v X Y ^ 2) / 4 =
        delta A B C d u v X Y ^ 2 * (x ^ 2 + y ^ 2 - 1) / 4 := by ring
  rw [this, hxy]
  ring

private def solutionDirections (A B C R S d u v : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ x y, NormalizedSolution A B C R S d u v (x, y, p.1, p.2)}

private lemma solutionDirections_finite
    {A B C R S d u v : ℝ} (hA : 0 < A) (hd : 0 < d)
    (hc13 : 0 < B ^ 2 + C ^ 2) (hc23 : 0 < (A - B) ^ 2 + C ^ 2)
    (ht13 : 0 < u ^ 2 + v ^ 2) (ht23 : 0 < (u - d) ^ 2 + v ^ 2) :
    (solutionDirections A B C R S d u v).Finite := by
  by_contra hfin
  have hinf : (solutionDirections A B C R S d u v).Infinite := hfin
  let D' := solutionDirections A B C R S d u v \ {(-1, 0)}
  have hD'inf : D'.Infinite := hinf.sdiff (Set.finite_singleton (-1, 0))
  have hunit : ∀ p ∈ D', normSq p = 1 := by
    rintro p ⟨⟨x, y, hsol⟩, -⟩
    exact hsol.2.1
  have hinj : Set.InjOn circleSlope D' := by
    apply circleSlope_injOn.mono
    intro p hp
    exact ⟨hunit p hp, hp.2⟩
  have himage : (circleSlope '' D').Infinite := hD'inf.image hinj
  have hroots : Set.Infinite {t : ℝ |
      (parameterElimPoly A B C R S d u v).IsRoot t} := by
    apply himage.mono
    rintro t ⟨p, hp, rfl⟩
    rcases hp.1 with ⟨x, y, hsol⟩
    have helim := normalizedSolution_eliminant hsol
    have heval := parameterElimPoly_eval A B C R S d u v (circleSlope p)
    rw [circleParam_circleSlope hsol.2.1 hp.2, helim, mul_zero] at heval
    change (parameterElimPoly A B C R S d u v).IsRoot (circleSlope p)
    simpa only [Polynomial.IsRoot] using heval
  have hpzero : parameterElimPoly A B C R S d u v = 0 :=
    (parameterElimPoly A B C R S d u v).eq_zero_of_infinite_isRoot hroots
  have hodd := parameterElimPoly_odd_certificate A B C R S d u v
  have heven := parameterElimPoly_even_certificate A B C R S d u v
  rw [hpzero] at hodd heven
  simp only [oddCoeffFunctional, evenCoeffFunctional, coeff_zero, mul_zero, add_zero,
    sub_zero, zero_mul] at hodd heven
  have hscale : 256 * A * d ≠ 0 := by positivity
  have hF : fCert A B C d u v = 0 := by
    exact (mul_eq_zero.mp (by simpa [mul_assoc] using hodd.symm)).resolve_left hscale
  have hG : gCert A B C d u v = 0 := by
    exact (mul_eq_zero.mp (by simpa [mul_assoc] using heven.symm)).resolve_left hscale
  rcases certs_not_both_zero hd hc13 hc23 ht13 ht23 with hF' | hG'
  · exact hF' hF
  · exact hG' hG

private def linePolyY (a b k : ℝ) : Polynomial ℝ :=
  (Polynomial.C k - Polynomial.C b * X) ^ 2 +
    Polynomial.C (a ^ 2) * X ^ 2 - Polynomial.C (a ^ 2)

private def linePolyX (a b k : ℝ) : Polynomial ℝ :=
  (Polynomial.C k - Polynomial.C a * X) ^ 2 +
    Polynomial.C (b ^ 2) * X ^ 2 - Polynomial.C (b ^ 2)

private lemma linePolyY_ne_zero {a b k : ℝ} (ha : a ≠ 0) : linePolyY a b k ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℝ ↦ p.coeff 2) h
  norm_num [linePolyY, pow_two, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    coeff_X] at hc
  nlinarith [sq_pos_of_ne_zero ha]

private lemma linePolyX_ne_zero {a b k : ℝ} (hb : b ≠ 0) : linePolyX a b k ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℝ ↦ p.coeff 2) h
  norm_num [linePolyX, pow_two, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    coeff_X] at hc
  nlinarith [sq_pos_of_ne_zero hb]

private lemma finite_unitCircle_line {a b k : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) :
    Set.Finite {p : ℝ × ℝ | normSq p = 1 ∧ a * p.1 + b * p.2 = k} := by
  rcases hab with ha | hb
  · have hroots : Set.Finite {y : ℝ | (linePolyY a b k).IsRoot y} :=
      Polynomial.finite_setOfPred_isRoot (linePolyY_ne_zero ha)
    apply (hroots.image (fun y ↦ ((k - b * y) / a, y))).subset
    rintro ⟨x, y⟩ ⟨hunit, hline⟩
    have hx : k - b * y = a * x := by linarith
    refine ⟨y, ?_, ?_⟩
    · change (linePolyY a b k).eval y = 0
      simp only [linePolyY, eval_sub, eval_add, eval_pow, eval_mul, eval_C, eval_X]
      rw [hx]
      simp only [normSq, Prod.fst, Prod.snd] at hunit
      nlinarith
    · ext <;> simp only [Prod.fst, Prod.snd]
      field_simp [ha]
      linarith
  · have hroots : Set.Finite {x : ℝ | (linePolyX a b k).IsRoot x} :=
      Polynomial.finite_setOfPred_isRoot (linePolyX_ne_zero hb)
    apply (hroots.image (fun x ↦ (x, (k - a * x) / b))).subset
    rintro ⟨x, y⟩ ⟨hunit, hline⟩
    have hy : k - a * x = b * y := by linarith
    refine ⟨x, ?_, ?_⟩
    · change (linePolyX a b k).eval x = 0
      simp only [linePolyX, eval_sub, eval_add, eval_pow, eval_mul, eval_C, eval_X]
      rw [hy]
      simp only [normSq, Prod.fst, Prod.snd] at hunit
      nlinarith
    · ext <;> simp only [Prod.fst, Prod.snd]
      field_simp [hb]
      linarith

private lemma finite_two_circles {a b r2 : ℝ}
    (hneq : a ≠ 0 ∨ b ≠ 0 ∨ r2 ≠ 1) :
    Set.Finite {p : ℝ × ℝ |
      normSq p = 1 ∧ (p.1 - a) ^ 2 + (p.2 - b) ^ 2 = r2} := by
  by_cases hab : a ≠ 0 ∨ b ≠ 0
  · apply (finite_unitCircle_line
      (a := a) (b := b) (k := (1 + a ^ 2 + b ^ 2 - r2) / 2) hab).subset
    rintro ⟨x, y⟩ ⟨hunit, hcircle⟩
    refine ⟨hunit, ?_⟩
    simp only [normSq, Prod.fst, Prod.snd] at hunit
    nlinarith
  · have ha : a = 0 := not_ne_iff.mp (not_or.mp hab).1
    have hb : b = 0 := not_ne_iff.mp (not_or.mp hab).2
    have hr : r2 ≠ 1 := by
      rcases hneq with ha' | hb' | hr
      · exact (ha' ha).elim
      · exact (hb' hb).elim
      · exact hr
    apply Set.finite_empty.subset
    rintro ⟨x, y⟩ ⟨hunit, hcircle⟩
    simp only [ha, hb, sub_zero, normSq, Prod.fst, Prod.snd] at hunit hcircle
    exact hr (by nlinarith)

private def solutionFiber (A B C R S d u v X Y : ℝ) : Set (ℝ × ℝ) :=
  {p | NormalizedSolution A B C R S d u v (p.1, p.2, X, Y)}

private lemma solutionFiber_finite
    {A B C R S d u v X Y : ℝ} (hA : 0 < A) (hd : 0 < d)
    (hunit : X ^ 2 + Y ^ 2 = 1)
    (hnot : ¬ (A = d ∧ B = u ∧ C = v ∧ R ^ 2 = 1 ∧ S ^ 2 = 1)) :
    (solutionFiber A B C R S d u v X Y).Finite := by
  by_cases hsecond : A - d * X ≠ 0 ∨ -d * Y ≠ 0 ∨ R ^ 2 ≠ 1
  · apply (finite_two_circles hsecond).subset
    rintro ⟨x, y⟩ hsol
    rcases hsol with ⟨hxy, hXY, h2, h3⟩
    refine ⟨hxy, ?_⟩
    nlinarith
  · push Not at hsecond
    rcases hsecond with ⟨ha, hy, hR⟩
    by_cases hthird : B - qx u v X Y ≠ 0 ∨ C - qy u v X Y ≠ 0 ∨ S ^ 2 ≠ 1
    · apply (finite_two_circles hthird).subset
      rintro ⟨x, y⟩ hsol
      rcases hsol with ⟨hxy, hXY, h2, h3⟩
      refine ⟨hxy, ?_⟩
      simp only [qx, qy] at hthird ⊢
      nlinarith
    · push Not at hthird
      rcases hthird with ⟨hB, hC, hS⟩
      have hY : Y = 0 := by
        have hd0 : d ≠ 0 := ne_of_gt hd
        have hdy : d * Y = 0 := by nlinarith
        exact (mul_eq_zero.mp hdy).resolve_left hd0
      have hXsq : X ^ 2 = 1 := by nlinarith
      have hXeq : X = A / d := by
        apply (eq_div_iff (ne_of_gt hd)).2
        nlinarith
      have hXpos : 0 < X := by rw [hXeq]; positivity
      have hX : X = 1 := by nlinarith
      have hAd : A = d := by nlinarith
      have hBu : B = u := by
        simp only [qx, hX, hY, mul_one, mul_zero, sub_zero, add_zero] at hB
        linarith
      have hCv : C = v := by
        simp only [qy, hX, hY, mul_one, mul_zero, add_zero] at hC
        linarith
      exact (hnot ⟨hAd, hBu, hCv, hR, hS⟩).elim

/-- Normalized three-circle rigidity, algebraic orientation.  The hypotheses
say that the three fixed centers and the three target vertices are pairwise
distinct.  The sole flexible case is the equal-radius congruent placement. -/
theorem circle_congruent_finite
    {A B C R S d u v : ℝ} (hA : 0 < A) (hd : 0 < d)
    (hc13 : 0 < B ^ 2 + C ^ 2) (hc23 : 0 < (A - B) ^ 2 + C ^ 2)
    (ht13 : 0 < u ^ 2 + v ^ 2) (ht23 : 0 < (u - d) ^ 2 + v ^ 2)
    (hnot : ¬ (A = d ∧ B = u ∧ C = v ∧ R ^ 2 = 1 ∧ S ^ 2 = 1)) :
    Set.Finite {z : ℝ × ℝ × ℝ × ℝ |
      NormalizedSolution A B C R S d u v z} := by
  let D := solutionDirections A B C R S d u v
  have hD : D.Finite := solutionDirections_finite hA hd hc13 hc23 ht13 ht23
  let liftFiber : (ℝ × ℝ) → (ℝ × ℝ) → (ℝ × ℝ × ℝ × ℝ) :=
    fun p q ↦ (q.1, q.2, p.1, p.2)
  let fibers : (ℝ × ℝ) → Set (ℝ × ℝ × ℝ × ℝ) :=
    fun p ↦ liftFiber p '' solutionFiber A B C R S d u v p.1 p.2
  have hFibers : ∀ p ∈ D, (fibers p).Finite := by
    intro p hp
    rcases hp with ⟨x, y, hsol⟩
    apply Set.Finite.image
    exact solutionFiber_finite hA hd hsol.2.1 hnot
  have hUnion : (⋃ p ∈ D, fibers p).Finite := hD.biUnion hFibers
  apply hUnion.subset
  intro z hz
  rcases z with ⟨x, y, X, Y⟩
  have hp : (X, Y) ∈ D := ⟨x, y, hz⟩
  simp only [Set.mem_iUnion]
  refine ⟨(X, Y), ⟨hp, ?_⟩⟩
  refine ⟨(x, y), hz, ?_⟩
  rfl

end

end Erdos215.Circle
