import Util.RationalPowerPolynomial

/-!
# Transparent integer power polynomials

Integer power polynomials are represented by coefficient lists in ascending
degree order.  The representation has transparent equality, so generated
coefficient identities can be checked by kernel reduction.
-/

namespace Arxiv2407_19026

noncomputable section

def evalIntegerPower : List ℤ → ℝ → ℝ
  | [], _ => 0
  | coefficient :: coefficients, x =>
      coefficient + x * evalIntegerPower coefficients x

def integerPowerAdd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: integerPowerAdd p q

def integerPowerScale (a : ℤ) : List ℤ → List ℤ
  | [] => []
  | b :: p => a * b :: integerPowerScale a p

def integerPowerShift : List ℤ → List ℤ
  | [] => []
  | p => 0 :: p

def integerPowerMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q =>
      integerPowerAdd (integerPowerScale a q)
        (integerPowerShift (integerPowerMul p q))

def integerPowerOneSubPow : ℕ → List ℤ
  | 0 => [1]
  | n + 1 =>
      integerPowerMul [1, -1] (integerPowerOneSubPow n)

def integerPowerBernstein : ℕ → List ℕ → List ℤ
  | _, [] => []
  | 0, coefficient :: _ => [coefficient]
  | n + 1, coefficient :: coefficients =>
      integerPowerAdd
        (integerPowerScale coefficient
          (integerPowerOneSubPow (n + 1)))
        (integerPowerShift
          (integerPowerBernstein n coefficients))

def integerPowerLinearTail (left width previous : ℤ) :
    List ℤ → List ℤ
  | [] => [width * previous]
  | coefficient :: coefficients =>
      (left * coefficient + width * previous) ::
        integerPowerLinearTail
          left width coefficient coefficients

def integerPowerLinear (left width : ℤ) :
    List ℤ → List ℤ
  | [] => []
  | coefficient :: coefficients =>
      left * coefficient ::
        integerPowerLinearTail
          left width coefficient coefficients

def integerPowerAffine (denominator : ℕ)
    (left width : ℤ) : List ℤ → List ℤ
  | [] => []
  | coefficient :: coefficients =>
      integerPowerAdd
        [coefficient * denominator ^ coefficients.length]
        (integerPowerLinear left width
          (integerPowerAffine
            denominator left width coefficients))

def rationalPowerFromIntegers
    (scale : ℕ) : List ℤ → RationalPowerPolynomial
  | [] => []
  | coefficient :: coefficients =>
      (coefficient : ℚ) / scale ::
        rationalPowerFromIntegers scale coefficients

/-- Remove trailing zero coefficients from an integer power polynomial. -/
def integerPowerTrim : List ℤ → List ℤ
  | [] => []
  | coefficient :: coefficients =>
      match integerPowerTrim coefficients with
      | [] => if coefficient = 0 then [] else [coefficient]
      | tail => coefficient :: tail

lemma evalIntegerPower_add
    (p q : List ℤ) (x : ℝ) :
    evalIntegerPower (integerPowerAdd p q) x =
      evalIntegerPower p x + evalIntegerPower q x := by
  induction p generalizing q with
  | nil =>
      simp [integerPowerAdd, evalIntegerPower]
  | cons a p ih =>
      cases q with
      | nil =>
          simp [integerPowerAdd, evalIntegerPower]
      | cons b q =>
          simp only [integerPowerAdd, evalIntegerPower]
          rw [ih]
          norm_num
          ring

lemma evalIntegerPower_scale
    (a : ℤ) (p : List ℤ) (x : ℝ) :
    evalIntegerPower (integerPowerScale a p) x =
      a * evalIntegerPower p x := by
  induction p with
  | nil =>
      simp [integerPowerScale, evalIntegerPower]
  | cons b p ih =>
      simp only [integerPowerScale, evalIntegerPower]
      rw [ih]
      norm_num
      ring

lemma evalIntegerPower_shift
    (p : List ℤ) (x : ℝ) :
    evalIntegerPower (integerPowerShift p) x =
      x * evalIntegerPower p x := by
  cases p <;> simp [integerPowerShift, evalIntegerPower]

lemma evalIntegerPower_mul
    (p q : List ℤ) (x : ℝ) :
    evalIntegerPower (integerPowerMul p q) x =
      evalIntegerPower p x * evalIntegerPower q x := by
  induction p with
  | nil =>
      simp [integerPowerMul, evalIntegerPower]
  | cons a p ih =>
      simp [integerPowerMul, evalIntegerPower,
        evalIntegerPower_add, evalIntegerPower_scale,
        evalIntegerPower_shift, ih]
      ring

lemma evalIntegerPower_trim (coefficients : List ℤ) (x : ℝ) :
    evalIntegerPower (integerPowerTrim coefficients) x =
      evalIntegerPower coefficients x := by
  induction coefficients with
  | nil => rfl
  | cons coefficient coefficients ih =>
      rw [integerPowerTrim]
      cases htrim : integerPowerTrim coefficients with
      | nil =>
        have htail : evalIntegerPower coefficients x = 0 := by
          rw [← ih, htrim]
          rfl
        by_cases hcoefficient : coefficient = 0 <;>
          simp [hcoefficient, evalIntegerPower, htail]
      | cons head tail =>
        have htail :
            evalIntegerPower (head :: tail) x =
              evalIntegerPower coefficients x := by
          rw [← htrim]
          exact ih
        change (coefficient : ℝ) +
            x * evalIntegerPower (head :: tail) x =
          (coefficient : ℝ) + x * evalIntegerPower coefficients x
        rw [htail]

lemma evalIntegerPower_oneSubPow (n : ℕ) (x : ℝ) :
    evalIntegerPower (integerPowerOneSubPow n) x =
      (1 - x) ^ n := by
  induction n with
  | zero =>
      simp [integerPowerOneSubPow, evalIntegerPower]
  | succ n ih =>
      rw [integerPowerOneSubPow, evalIntegerPower_mul, ih]
      simp [evalIntegerPower]
      ring

lemma evalIntegerPower_bernstein
    (n : ℕ) (coefficients : List ℕ) (x : ℝ) :
    evalIntegerPower (integerPowerBernstein n coefficients) x =
      ∑ i ∈ Finset.range (n + 1),
        (coefficients.getD i 0 : ℝ) * x ^ i *
          (1 - x) ^ (n - i) := by
  induction n generalizing coefficients with
  | zero =>
      cases coefficients <;>
        simp [integerPowerBernstein, evalIntegerPower]
  | succ n ih =>
      cases coefficients with
      | nil =>
          simp [integerPowerBernstein, evalIntegerPower]
      | cons coefficient coefficients =>
          rw [integerPowerBernstein, evalIntegerPower_add,
            evalIntegerPower_scale, evalIntegerPower_shift,
            evalIntegerPower_oneSubPow, ih]
          rw [Finset.sum_range_succ' _ (n + 1)]
          simp only [List.getD_cons_zero,
            List.getD_cons_succ, pow_zero, mul_one]
          rw [Finset.mul_sum, add_comm]
          apply congrArg₂ (· + ·)
          · apply Finset.sum_congr rfl
            intro i _
            simp only [Nat.succ_sub_succ_eq_sub, pow_succ]
            ring
          · norm_num

lemma integerPowerLinearTail_eq
    (left width previous : ℤ) (p : List ℤ) :
    integerPowerLinearTail left width previous p =
      integerPowerAdd (integerPowerScale left p)
        (width * previous :: integerPowerScale width p) := by
  induction p generalizing previous with
  | nil =>
      simp [integerPowerLinearTail,
        integerPowerAdd, integerPowerScale]
  | cons coefficient coefficients ih =>
      simp only [integerPowerLinearTail,
        integerPowerScale, integerPowerAdd]
      rw [ih]

lemma integerPowerLinear_eq
    (left width : ℤ) (p : List ℤ) :
    integerPowerLinear left width p =
      integerPowerAdd (integerPowerScale left p)
        (integerPowerShift
          (integerPowerScale width p)) := by
  cases p with
  | nil =>
      simp [integerPowerLinear, integerPowerScale,
        integerPowerShift, integerPowerAdd]
  | cons coefficient coefficients =>
      simp only [integerPowerLinear, integerPowerScale,
        integerPowerShift, integerPowerAdd]
      rw [integerPowerLinearTail_eq]
      norm_num

lemma evalIntegerPower_linear
    (left width : ℤ) (p : List ℤ) (x : ℝ) :
    evalIntegerPower (integerPowerLinear left width p) x =
      ((left : ℝ) + width * x) *
        evalIntegerPower p x := by
  rw [integerPowerLinear_eq, evalIntegerPower_add,
    evalIntegerPower_scale, evalIntegerPower_shift,
    evalIntegerPower_scale]
  ring

lemma rationalPowerEval_fromIntegers
    (scale : ℕ) (coefficients : List ℤ) (x : ℝ)
    (hscale : scale ≠ 0) :
    rationalPowerEval
        (rationalPowerFromIntegers scale coefficients) x =
      evalIntegerPower coefficients x / scale := by
  induction coefficients with
  | nil =>
      simp [rationalPowerFromIntegers,
        rationalPowerEval, evalIntegerPower]
  | cons coefficient coefficients ih =>
      simp only [rationalPowerFromIntegers,
        rationalPowerEval, evalIntegerPower]
      rw [ih]
      norm_num
      field_simp [hscale]

/-!
`ScaledIntegerPower` carries one positive common denominator for an entire
power polynomial.  It is used for large exact certificates: polynomial
arithmetic then takes place in `ℤ`, rather than repeatedly normalizing one
rational number per coefficient and per intermediate product.
-/

structure ScaledIntegerPower where
  scale : ℕ
  coefficients : List ℤ
  scale_ne_zero : scale ≠ 0

namespace ScaledIntegerPower

def integerNatQuotient (numerator denominator : ℕ) : ℤ :=
  Int.ofNat (numerator / denominator)

def eval (p : ScaledIntegerPower) (x : ℝ) : ℝ :=
  evalIntegerPower p.coefficients x / p.scale

def zero : ScaledIntegerPower where
  scale := 1
  coefficients := []
  scale_ne_zero := by norm_num

def ofIntegers (scale : ℕ) (coefficients : List ℤ)
    (hscale : scale ≠ 0) : ScaledIntegerPower where
  scale := scale
  coefficients := coefficients
  scale_ne_zero := hscale

/-- Normalize a scaled integer polynomial by dropping trailing zeros. -/
def trim (p : ScaledIntegerPower) : ScaledIntegerPower where
  scale := p.scale
  coefficients := integerPowerTrim p.coefficients
  scale_ne_zero := p.scale_ne_zero

def constant (numerator : ℤ) (denominator : ℕ)
    (hdenominator : denominator ≠ 0) : ScaledIntegerPower :=
  ofIntegers denominator [numerator] hdenominator

def add (p q : ScaledIntegerPower) : ScaledIntegerPower where
  scale := Nat.lcm p.scale q.scale
  coefficients :=
    integerPowerAdd
      (integerPowerScale
        (integerNatQuotient (Nat.lcm p.scale q.scale) p.scale)
        p.coefficients)
      (integerPowerScale
        (integerNatQuotient (Nat.lcm p.scale q.scale) q.scale)
        q.coefficients)
  scale_ne_zero := Nat.lcm_ne_zero p.scale_ne_zero q.scale_ne_zero

def neg (p : ScaledIntegerPower) : ScaledIntegerPower where
  scale := p.scale
  coefficients := integerPowerScale (-1) p.coefficients
  scale_ne_zero := p.scale_ne_zero

def sub (p q : ScaledIntegerPower) : ScaledIntegerPower :=
  add p (neg q)

def scaleBy (numerator : ℤ) (denominator : ℕ)
    (hdenominator : denominator ≠ 0)
    (p : ScaledIntegerPower) : ScaledIntegerPower where
  scale := denominator * p.scale
  coefficients := integerPowerScale numerator p.coefficients
  scale_ne_zero := Nat.mul_ne_zero hdenominator p.scale_ne_zero

def mul (p q : ScaledIntegerPower) : ScaledIntegerPower where
  scale := p.scale * q.scale
  coefficients := integerPowerMul p.coefficients q.coefficients
  scale_ne_zero := Nat.mul_ne_zero p.scale_ne_zero q.scale_ne_zero

def pow (p : ScaledIntegerPower) : ℕ → ScaledIntegerPower
  | 0 => constant 1 1 (by norm_num)
  | n + 1 => mul p (pow p n)

def compAux (coefficientScale : ℕ)
    (hCoefficientScale : coefficientScale ≠ 0) :
    List ℤ → ScaledIntegerPower → ScaledIntegerPower
  | [], _ => zero
  | coefficient :: coefficients, q =>
      add (constant coefficient coefficientScale hCoefficientScale)
        (mul q
          (compAux coefficientScale hCoefficientScale coefficients q))

def comp (p q : ScaledIntegerPower) : ScaledIntegerPower :=
  compAux p.scale p.scale_ne_zero p.coefficients q

def Equivalent (p q : ScaledIntegerPower) : Prop :=
  integerPowerScale q.scale p.coefficients =
    integerPowerScale p.scale q.coefficients

lemma eval_zero (x : ℝ) : zero.eval x = 0 := by
  simp [zero, eval, evalIntegerPower]

lemma eval_ofIntegers (scale : ℕ) (coefficients : List ℤ)
    (hscale : scale ≠ 0) (x : ℝ) :
    (ofIntegers scale coefficients hscale).eval x =
      evalIntegerPower coefficients x / scale := by
  rfl

lemma eval_trim (p : ScaledIntegerPower) (x : ℝ) :
    p.trim.eval x = p.eval x := by
  simp [trim, eval, evalIntegerPower_trim]

lemma eval_constant (numerator : ℤ) (denominator : ℕ)
    (hdenominator : denominator ≠ 0) (x : ℝ) :
    (constant numerator denominator hdenominator).eval x =
      numerator / denominator := by
  simp [constant, eval_ofIntegers, evalIntegerPower]

lemma eval_add (p q : ScaledIntegerPower) (x : ℝ) :
    (add p q).eval x = p.eval x + q.eval x := by
  have hp := Nat.div_mul_cancel (Nat.dvd_lcm_left p.scale q.scale)
  have hq := Nat.div_mul_cancel (Nat.dvd_lcm_right p.scale q.scale)
  have hpReal :
      ((Int.ofNat (Nat.lcm p.scale q.scale / p.scale) : ℤ) : ℝ) *
          p.scale =
        Nat.lcm p.scale q.scale := by
    norm_num
    exact_mod_cast hp
  have hqReal :
      ((Int.ofNat (Nat.lcm p.scale q.scale / q.scale) : ℤ) : ℝ) *
          q.scale =
        Nat.lcm p.scale q.scale := by
    norm_num
    exact_mod_cast hq
  simp only [eval]
  rw [add, evalIntegerPower_add,
    evalIntegerPower_scale, evalIntegerPower_scale]
  simp only [integerNatQuotient]
  field_simp [p.scale_ne_zero, q.scale_ne_zero]
  calc
    _ =
        (((Int.ofNat (Nat.lcm p.scale q.scale / p.scale) : ℤ) : ℝ) *
            p.scale) *
              (evalIntegerPower p.coefficients x * q.scale) +
          (((Int.ofNat (Nat.lcm p.scale q.scale / q.scale) : ℤ) : ℝ) *
            q.scale) *
              (evalIntegerPower q.coefficients x * p.scale) := by
        ring
    _ = _ := by
      rw [hpReal, hqReal]
      ring

lemma eval_neg (p : ScaledIntegerPower) (x : ℝ) :
    (neg p).eval x = -p.eval x := by
  simp only [eval]
  rw [neg, evalIntegerPower_scale]
  norm_num
  ring

lemma eval_sub (p q : ScaledIntegerPower) (x : ℝ) :
    (sub p q).eval x = p.eval x - q.eval x := by
  rw [sub, eval_add, eval_neg]
  ring

lemma eval_scaleBy (numerator : ℤ) (denominator : ℕ)
    (hdenominator : denominator ≠ 0)
    (p : ScaledIntegerPower) (x : ℝ) :
    (scaleBy numerator denominator hdenominator p).eval x =
      (numerator / denominator) * p.eval x := by
  simp only [eval]
  rw [scaleBy, evalIntegerPower_scale]
  norm_num
  field_simp [hdenominator, p.scale_ne_zero]

lemma eval_mul (p q : ScaledIntegerPower) (x : ℝ) :
    (mul p q).eval x = p.eval x * q.eval x := by
  simp only [eval]
  rw [mul, evalIntegerPower_mul]
  norm_num
  field_simp [p.scale_ne_zero, q.scale_ne_zero]

lemma eval_pow (p : ScaledIntegerPower) (n : ℕ) (x : ℝ) :
    (pow p n).eval x = p.eval x ^ n := by
  induction n with
  | zero => simp [pow, eval_constant]
  | succ n ih =>
      rw [pow, eval_mul, ih, pow_succ]
      ring

lemma eval_compAux (coefficientScale : ℕ)
    (hCoefficientScale : coefficientScale ≠ 0)
    (coefficients : List ℤ) (q : ScaledIntegerPower) (x : ℝ) :
    (compAux coefficientScale hCoefficientScale coefficients q).eval x =
      evalIntegerPower coefficients (q.eval x) /
        coefficientScale := by
  induction coefficients with
  | nil => simp [compAux, eval_zero, evalIntegerPower]
  | cons coefficient coefficients ih =>
      rw [compAux, eval_add, eval_constant, eval_mul, ih]
      simp only [evalIntegerPower]
      field_simp [hCoefficientScale]

lemma eval_comp (p q : ScaledIntegerPower) (x : ℝ) :
    (comp p q).eval x = p.eval (q.eval x) := by
  rw [comp, eval_compAux, eval]
  rfl

lemma eval_eq_of_equivalent {p q : ScaledIntegerPower}
    (h : Equivalent p q) (x : ℝ) : p.eval x = q.eval x := by
  have heval := congrArg (fun coefficients =>
    evalIntegerPower coefficients x) h
  rw [evalIntegerPower_scale, evalIntegerPower_scale] at heval
  simp only [eval]
  norm_num at heval ⊢
  field_simp [p.scale_ne_zero, q.scale_ne_zero]
  linear_combination heval

def Represents (p : ScaledIntegerPower)
    (q : RationalPowerPolynomial) : Prop :=
  ∀ x, p.eval x = rationalPowerEval q x

lemma represents_trim {p : ScaledIntegerPower}
    {q : RationalPowerPolynomial} (hp : Represents p q) :
    Represents p.trim q := by
  intro x
  rw [eval_trim, hp]

lemma represents_fromIntegers (scale : ℕ)
    (coefficients : List ℤ) (hscale : scale ≠ 0) :
    Represents (ofIntegers scale coefficients hscale)
      (rationalPowerFromIntegers scale coefficients) := by
  intro x
  rw [eval_ofIntegers,
    rationalPowerEval_fromIntegers scale coefficients x hscale]

lemma represents_add {p q : ScaledIntegerPower}
    {p' q' : RationalPowerPolynomial}
    (hp : Represents p p') (hq : Represents q q') :
    Represents (add p q) (rationalPowerAdd p' q') := by
  intro x
  rw [eval_add, rationalPowerEval_add, hp, hq]

lemma represents_neg {p : ScaledIntegerPower}
    {p' : RationalPowerPolynomial} (hp : Represents p p') :
    Represents (neg p) (rationalPowerNeg p') := by
  intro x
  rw [eval_neg, rationalPowerEval_neg, hp]

lemma represents_sub {p q : ScaledIntegerPower}
    {p' q' : RationalPowerPolynomial}
    (hp : Represents p p') (hq : Represents q q') :
    Represents (sub p q) (rationalPowerSub p' q') := by
  intro x
  rw [eval_sub, rationalPowerEval_sub, hp, hq]

lemma represents_scaleBy (numerator : ℤ) (denominator : ℕ)
    (hdenominator : denominator ≠ 0)
    {p : ScaledIntegerPower} {p' : RationalPowerPolynomial}
    (hp : Represents p p') :
    Represents (scaleBy numerator denominator hdenominator p)
      (rationalPowerScale
        ((numerator : ℚ) / denominator) p') := by
  intro x
  rw [eval_scaleBy, rationalPowerEval_scale, hp]
  norm_num

lemma represents_mul {p q : ScaledIntegerPower}
    {p' q' : RationalPowerPolynomial}
    (hp : Represents p p') (hq : Represents q q') :
    Represents (mul p q) (rationalPowerMul p' q') := by
  intro x
  rw [eval_mul, rationalPowerEval_mul, hp, hq]

lemma represents_pow {p : ScaledIntegerPower}
    {p' : RationalPowerPolynomial} (hp : Represents p p')
    (n : ℕ) : Represents (pow p n) (rationalPowerPow p' n) := by
  intro x
  rw [eval_pow, rationalPowerEval_pow, hp]

lemma represents_comp {p q : ScaledIntegerPower}
    {p' q' : RationalPowerPolynomial}
    (hp : Represents p p') (hq : Represents q q') :
    Represents (comp p q) (rationalPowerComp p' q') := by
  intro x
  rw [eval_comp, rationalPowerEval_comp, hp, hq]

end ScaledIntegerPower

lemma evalIntegerPower_affine
    (denominator : ℕ) (left width : ℤ)
    (coefficients : List ℤ) (x : ℝ)
    (hdenominator : denominator ≠ 0) :
    evalIntegerPower
        (integerPowerAffine denominator left width coefficients) x *
        denominator =
      denominator ^ coefficients.length *
        evalIntegerPower coefficients
          (((left : ℝ) + (width : ℝ) * x) / denominator) := by
  induction coefficients with
  | nil =>
      simp [integerPowerAffine, evalIntegerPower]
  | cons coefficient coefficients ih =>
      simp only [integerPowerAffine, evalIntegerPower_add,
        evalIntegerPower_linear, evalIntegerPower,
        List.length_cons]
      rw [pow_succ]
      norm_num at ih ⊢
      field_simp [hdenominator] at ih ⊢
      ring_nf at ih ⊢
      linear_combination
        ((left : ℝ) + (width : ℝ) * x) * ih

set_option maxRecDepth 100000 in
lemma evalIntegerPower_affine_bernstein
    (denominator degree scale : ℕ) (left width : ℤ)
    (coefficients : List ℤ)
    (bernsteinCoefficients : List ℕ) (x : ℝ)
    (hdenominator : denominator ≠ 0)
    (hlength : coefficients.length = degree + 1)
    (hcoefficients :
      integerPowerScale scale
          (integerPowerAffine denominator left width coefficients) =
        integerPowerScale ((denominator : ℤ) ^ degree)
          (integerPowerBernstein degree bernsteinCoefficients)) :
    (scale : ℝ) * evalIntegerPower coefficients
        (((left : ℝ) + width * x) / denominator) =
      ∑ i ∈ Finset.range (degree + 1),
        (bernsteinCoefficients.getD i 0 : ℝ) * x ^ i *
          (1 - x) ^ (degree - i) := by
  have heval := congrArg
    (fun cs => evalIntegerPower cs x) hcoefficients
  rw [evalIntegerPower_scale, evalIntegerPower_scale] at heval
  simp only [Int.cast_natCast, Int.cast_pow] at heval
  have ha := evalIntegerPower_affine denominator left width
    coefficients x hdenominator
  rw [hlength] at ha
  have ha' :
      evalIntegerPower
          (integerPowerAffine denominator left width coefficients) x =
        (denominator : ℝ) ^ degree *
          evalIntegerPower coefficients
            (((left : ℝ) + width * x) / denominator) := by
    apply mul_right_cancel₀
      (Nat.cast_ne_zero.mpr hdenominator :
        (denominator : ℝ) ≠ 0)
    calc
      _ = (denominator : ℝ) ^ (degree + 1) *
          evalIntegerPower coefficients
            (((left : ℝ) + width * x) / denominator) := ha
      _ = _ := by rw [pow_succ]; ring
  rw [← evalIntegerPower_bernstein]
  apply mul_left_cancel₀
    (pow_ne_zero degree
      (Nat.cast_ne_zero.mpr hdenominator :
        (denominator : ℝ) ≠ 0))
  calc
    _ = (scale : ℝ) *
        ((denominator : ℝ) ^ degree *
          evalIntegerPower coefficients
            (((left : ℝ) + width * x) / denominator)) := by ring
    _ = (scale : ℝ) *
        evalIntegerPower
          (integerPowerAffine denominator left width coefficients) x := by
      rw [ha']
    _ = _ := heval

end

end Arxiv2407_19026
