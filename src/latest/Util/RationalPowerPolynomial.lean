import Mathlib.Tactic

/-!
# Transparent rational power polynomials

Power polynomials are represented by coefficient lists in ascending degree
order.  This representation has transparent equality, so generated exact
coefficient identities can be checked by kernel reduction.
-/

namespace Arxiv2407_19026

noncomputable section

abbrev RationalPowerPolynomial := List ℚ

def rationalPowerAdd :
    RationalPowerPolynomial → RationalPowerPolynomial →
      RationalPowerPolynomial
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: rationalPowerAdd p q

def rationalPowerNeg
    (p : RationalPowerPolynomial) : RationalPowerPolynomial :=
  p.map (-·)

def rationalPowerSub
    (p q : RationalPowerPolynomial) :
    RationalPowerPolynomial :=
  rationalPowerAdd p (rationalPowerNeg q)

def rationalPowerScale (a : ℚ)
    (p : RationalPowerPolynomial) : RationalPowerPolynomial :=
  p.map (a * ·)

def rationalPowerShift :
    RationalPowerPolynomial → RationalPowerPolynomial
  | [] => []
  | p => 0 :: p

def rationalPowerMul :
    RationalPowerPolynomial → RationalPowerPolynomial →
      RationalPowerPolynomial
  | [], _ => []
  | a :: p, q =>
      rationalPowerAdd (rationalPowerScale a q)
        (rationalPowerShift (rationalPowerMul p q))

def rationalPowerPow
    (p : RationalPowerPolynomial) :
    ℕ → RationalPowerPolynomial
  | 0 => [1]
  | n + 1 => rationalPowerMul p (rationalPowerPow p n)

def rationalPowerComp :
    RationalPowerPolynomial → RationalPowerPolynomial →
      RationalPowerPolynomial
  | [], _ => []
  | a :: p, q =>
      rationalPowerAdd [a]
        (rationalPowerMul q (rationalPowerComp p q))

def rationalPowerEval :
    RationalPowerPolynomial → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => a + x * rationalPowerEval p x

lemma rationalPowerEval_add
    (p q : RationalPowerPolynomial) (x : ℝ) :
    rationalPowerEval (rationalPowerAdd p q) x =
      rationalPowerEval p x + rationalPowerEval q x := by
  induction p generalizing q with
  | nil =>
      simp [rationalPowerAdd, rationalPowerEval]
  | cons a p ih =>
      cases q with
      | nil =>
          simp [rationalPowerAdd, rationalPowerEval]
      | cons b q =>
          simp only [rationalPowerAdd, rationalPowerEval]
          rw [ih]
          norm_num
          ring

lemma rationalPowerEval_neg
    (p : RationalPowerPolynomial) (x : ℝ) :
    rationalPowerEval (rationalPowerNeg p) x =
      -rationalPowerEval p x := by
  induction p with
  | nil =>
      simp [rationalPowerNeg, rationalPowerEval]
  | cons a p ih =>
      change
        rationalPowerEval (rationalPowerNeg p) x =
          -rationalPowerEval p x at ih
      change
        ((-a : ℚ) : ℝ) +
            x * rationalPowerEval (rationalPowerNeg p) x =
          -((a : ℝ) + x * rationalPowerEval p x)
      rw [ih]
      norm_num
      ring

lemma rationalPowerEval_sub
    (p q : RationalPowerPolynomial) (x : ℝ) :
    rationalPowerEval (rationalPowerSub p q) x =
      rationalPowerEval p x - rationalPowerEval q x := by
  rw [rationalPowerSub, rationalPowerEval_add,
    rationalPowerEval_neg]
  ring

lemma rationalPowerEval_scale
    (a : ℚ) (p : RationalPowerPolynomial) (x : ℝ) :
    rationalPowerEval (rationalPowerScale a p) x =
      a * rationalPowerEval p x := by
  induction p with
  | nil =>
      simp [rationalPowerScale, rationalPowerEval]
  | cons b p ih =>
      change
        rationalPowerEval (rationalPowerScale a p) x =
          a * rationalPowerEval p x at ih
      change
        ((a * b : ℚ) : ℝ) +
            x * rationalPowerEval (rationalPowerScale a p) x =
          (a : ℝ) *
            ((b : ℝ) + x * rationalPowerEval p x)
      rw [ih]
      norm_num
      ring

lemma rationalPowerEval_shift
    (p : RationalPowerPolynomial) (x : ℝ) :
    rationalPowerEval (rationalPowerShift p) x =
      x * rationalPowerEval p x := by
  cases p <;> simp [rationalPowerShift, rationalPowerEval]

lemma rationalPowerEval_mul
    (p q : RationalPowerPolynomial) (x : ℝ) :
    rationalPowerEval (rationalPowerMul p q) x =
      rationalPowerEval p x * rationalPowerEval q x := by
  induction p with
  | nil =>
      simp [rationalPowerMul, rationalPowerEval]
  | cons a p ih =>
      simp [rationalPowerMul, rationalPowerEval,
        rationalPowerEval_add, rationalPowerEval_scale,
        rationalPowerEval_shift, ih]
      ring

lemma rationalPowerEval_pow
    (p : RationalPowerPolynomial) (n : ℕ) (x : ℝ) :
    rationalPowerEval (rationalPowerPow p n) x =
      rationalPowerEval p x ^ n := by
  induction n with
  | zero =>
      simp [rationalPowerPow, rationalPowerEval]
  | succ n ih =>
      simp [rationalPowerPow, rationalPowerEval_mul, ih,
        pow_succ]
      ring

lemma rationalPowerEval_comp
    (p q : RationalPowerPolynomial) (x : ℝ) :
    rationalPowerEval (rationalPowerComp p q) x =
      rationalPowerEval p (rationalPowerEval q x) := by
  induction p with
  | nil =>
      simp [rationalPowerComp, rationalPowerEval]
  | cons a p ih =>
      simp [rationalPowerComp, rationalPowerEval,
        rationalPowerEval_add, rationalPowerEval_mul, ih]

end

end Arxiv2407_19026
