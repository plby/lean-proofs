import ErdosProblems.Erdos1038.OneCutBulkBox

/-!
# A nonsingular expression chart at the q -> 0 end

The variables are `(r, q, q_r, zPlus, zMinus)`, where on the actual branch
`r = -1 / log q` and `q_r = q * (log q)^2`.  Unlike the q-derivative formula,
the resulting r-derivative extends to a compact interval containing `q = 0`.
-/

namespace Erdos1038

noncomputable section

namespace IntervalExpr

def trExpr : IntervalExpr 5 := .var 0
def tqExpr : IntervalExpr 5 := .var 1
def tqrExpr : IntervalExpr 5 := .var 2
def tzpExpr : IntervalExpr 5 := .var 3
def tzmExpr : IntervalExpr 5 := .var 4

def tOne : IntervalExpr 5 := .rat 1
def tTwo : IntervalExpr 5 := .rat 2
def tFour : IntervalExpr 5 := .rat 4
def tOnePlusQ : IntervalExpr 5 := .add tOne tqExpr

def tailDExpr (terms : Nat) : IntervalExpr 5 :=
  .sub (.log terms tTwo) (.mul tTwo (.log terms tOnePlusQ))

def tailAExpr (terms : Nat) : IntervalExpr 5 :=
  .sub tOne (.mul trExpr (tailDExpr terms))

def tailArExpr (terms : Nat) : IntervalExpr 5 :=
  .add (.neg (tailDExpr terms))
    (.div (.mul tTwo (.mul trExpr tqrExpr)) tOnePlusQ)

def tailWExpr (terms : Nat) (z denominator : IntervalExpr 5) : IntervalExpr 5 :=
  .log terms (.div (.sub z (.sq tqExpr)) denominator)

def tailInnerWExpr (terms : Nat) : IntervalExpr 5 :=
  tailWExpr terms tzpExpr (.sub tOne tzpExpr)

def tailOuterWExpr (terms : Nat) : IntervalExpr 5 :=
  tailWExpr terms tzmExpr (.sub tzmExpr tOne)

def tailGExpr (terms : Nat) (z denominator : IntervalExpr 5) : IntervalExpr 5 :=
  .sub
    (.sub (.mul (tailAExpr terms) (tailWExpr terms z denominator))
      (.log terms z))
    (tailDExpr terms)

def tailInnerGExpr (terms : Nat) : IntervalExpr 5 :=
  .sub
    (.sub (.mul (tailAExpr terms) (tailInnerWExpr terms))
      (.log terms tzpExpr))
    (tailDExpr terms)

def tailOuterGExpr (terms : Nat) : IntervalExpr 5 :=
  .sub
    (.sub (.mul (tailAExpr terms) (tailOuterWExpr terms))
      (.log terms tzmExpr))
    (tailDExpr terms)

def tailInnerGzExpr (terms : Nat) : IntervalExpr 5 :=
  .sub
    (.mul (tailAExpr terms)
      (.add (.inv (.sub tzpExpr (.sq tqExpr)))
        (.inv (.sub tOne tzpExpr))))
    (.inv tzpExpr)

def tailOuterGzExpr (terms : Nat) : IntervalExpr 5 :=
  .sub
    (.mul (tailAExpr terms)
      (.sub (.inv (.sub tzmExpr (.sq tqExpr)))
        (.inv (.sub tzmExpr tOne))))
    (.inv tzmExpr)

def tailGrExpr (terms : Nat) (z W : IntervalExpr 5) : IntervalExpr 5 :=
  .add
    (.add (.mul (tailArExpr terms) W)
      (.mul (tailAExpr terms)
        (.neg (.div (.mul tTwo (.mul tqExpr tqrExpr))
          (.sub z (.sq tqExpr))))))
    (.div (.mul tTwo tqrExpr) tOnePlusQ)

def tailInnerGrExpr (terms : Nat) : IntervalExpr 5 :=
  tailGrExpr terms tzpExpr (tailInnerWExpr terms)

def tailOuterGrExpr (terms : Nat) : IntervalExpr 5 :=
  tailGrExpr terms tzmExpr (tailOuterWExpr terms)

def tailZpSlopeExpr (terms : Nat) : IntervalExpr 5 :=
  .neg (.div (tailInnerGrExpr terms) (tailInnerGzExpr terms))

def tailZmSlopeExpr (terms : Nat) : IntervalExpr 5 :=
  .neg (.div (tailOuterGrExpr terms) (tailOuterGzExpr terms))

def tailHExpr : IntervalExpr 5 := .div tTwo (.sq tOnePlusQ)
def tailKExpr : IntervalExpr 5 :=
  .div (.mul tTwo (.sq tqExpr)) (.sq tOnePlusQ)
def tailHrExpr : IntervalExpr 5 :=
  .neg (.div (.mul tFour tqrExpr) (.cube tOnePlusQ))
def tailKrExpr : IntervalExpr 5 :=
  .div (.mul tFour (.mul tqExpr tqrExpr)) (.cube tOnePlusQ)

def tailLambdaRExpr (terms : Nat) : IntervalExpr 5 :=
  .add
    (.add
      (.mul tailHrExpr (.sub tzmExpr tzpExpr))
      (.mul tailHExpr (.sub (tailZmSlopeExpr terms) (tailZpSlopeExpr terms))))
    (.add
      (.mul tailKrExpr (.sub (.inv tzmExpr) (.inv tzpExpr)))
      (.mul tailKExpr
        (.add
          (.neg (.div (tailZmSlopeExpr terms) (.sq tzmExpr)))
          (.div (tailZpSlopeExpr terms) (.sq tzpExpr)))))

def tailDReal (q : ℝ) : ℝ := Real.log 2 - 2 * Real.log (1 + q)
def tailAReal (r q : ℝ) : ℝ := 1 - r * tailDReal q
def tailArReal (r q qr : ℝ) : ℝ :=
  -tailDReal q + 2 * r * qr / (1 + q)

def tailInnerGReal (r q z : ℝ) : ℝ :=
  tailAReal r q * Real.log ((z - q ^ 2) / (1 - z)) -
    Real.log z - tailDReal q

def tailOuterGReal (r q z : ℝ) : ℝ :=
  tailAReal r q * Real.log ((z - q ^ 2) / (z - 1)) -
    Real.log z - tailDReal q

def tailInnerGzReal (r q z : ℝ) : ℝ :=
  tailAReal r q * (1 / (z - q ^ 2) + 1 / (1 - z)) - 1 / z

def tailOuterGzReal (r q z : ℝ) : ℝ :=
  tailAReal r q * (1 / (z - q ^ 2) - 1 / (z - 1)) - 1 / z

def tailInnerGrReal (r q qr z : ℝ) : ℝ :=
  tailArReal r q qr * Real.log ((z - q ^ 2) / (1 - z)) +
    tailAReal r q * (-2 * q * qr / (z - q ^ 2)) +
    2 * qr / (1 + q)

def tailOuterGrReal (r q qr z : ℝ) : ℝ :=
  tailArReal r q qr * Real.log ((z - q ^ 2) / (z - 1)) +
    tailAReal r q * (-2 * q * qr / (z - q ^ 2)) +
    2 * qr / (1 + q)

def tailZpSlopeReal (r q qr zp : ℝ) : ℝ :=
  -tailInnerGrReal r q qr zp / tailInnerGzReal r q zp

def tailZmSlopeReal (r q qr zm : ℝ) : ℝ :=
  -tailOuterGrReal r q qr zm / tailOuterGzReal r q zm

def tailLambdaRReal (r q qr zp zm : ℝ) : ℝ :=
  (-4 * qr / (1 + q) ^ 3) * (zm - zp) +
    (2 / (1 + q) ^ 2) *
      (tailZmSlopeReal r q qr zm - tailZpSlopeReal r q qr zp) +
    (4 * q * qr / (1 + q) ^ 3) * (zm⁻¹ - zp⁻¹) +
    (2 * q ^ 2 / (1 + q) ^ 2) *
      (-tailZmSlopeReal r q qr zm / zm ^ 2 +
        tailZpSlopeReal r q qr zp / zp ^ 2)

@[simp] theorem trExpr_eval (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] trExpr = r := by
  simp [trExpr, evalReal]

@[simp] theorem tqExpr_eval (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] tqExpr = q := by
  simp [tqExpr, evalReal]

@[simp] theorem tqrExpr_eval (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] tqrExpr = qr := by
  simp [tqrExpr, evalReal]

@[simp] theorem tzpExpr_eval (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] tzpExpr = zp := by
  simp [tzpExpr, evalReal]

@[simp] theorem tzmExpr_eval (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] tzmExpr = zm := by
  simp [tzmExpr, evalReal]

@[simp] theorem tOnePlusQ_eval (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] tOnePlusQ = 1 + q := by
  simp [tOnePlusQ, tOne, evalReal]

@[simp] theorem tailDExpr_eval (terms : Nat) (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] (tailDExpr terms) = tailDReal q := by
  simp only [tailDExpr, tailDReal, tTwo, IntervalExpr.sub, evalReal,
    tOnePlusQ_eval, Rat.cast_ofNat]
  ring

@[simp] theorem tailAExpr_eval (terms : Nat) (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] (tailAExpr terms) = tailAReal r q := by
  simp only [tailAExpr, tailAReal, tOne, IntervalExpr.sub, evalReal,
    trExpr_eval, tailDExpr_eval, Rat.cast_one]
  ring

@[simp] theorem tailArExpr_eval (terms : Nat) (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] (tailArExpr terms) =
      tailArReal r q qr := by
  simp only [tailArExpr, tailArReal, tTwo, IntervalExpr.div, evalReal,
    trExpr_eval, tqrExpr_eval, tOnePlusQ_eval, tailDExpr_eval,
    Rat.cast_ofNat]
  ring

@[simp] theorem tailInnerWExpr_eval (terms : Nat) (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] (tailInnerWExpr terms) =
      Real.log ((zp - q ^ 2) / (1 - zp)) := by
  simp only [tailInnerWExpr, tailWExpr, tOne,
    IntervalExpr.sub, IntervalExpr.div, IntervalExpr.sq, evalReal,
    tqExpr_eval, tzpExpr_eval, Rat.cast_one]
  congr 1
  ring

@[simp] theorem tailOuterWExpr_eval (terms : Nat) (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] (tailOuterWExpr terms) =
      Real.log ((zm - q ^ 2) / (zm - 1)) := by
  simp only [tailOuterWExpr, tailWExpr, tOne,
    IntervalExpr.sub, IntervalExpr.div, IntervalExpr.sq, evalReal,
    tqExpr_eval, tzmExpr_eval, Rat.cast_one]
  congr 1
  ring

@[simp] theorem tailInnerGExpr_eval (terms : Nat) (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] (tailInnerGExpr terms) =
      tailInnerGReal r q zp := by
  simp only [tailInnerGExpr, tailInnerGReal, IntervalExpr.sub, evalReal,
    tailAExpr_eval, tailInnerWExpr_eval, tzpExpr_eval, tailDExpr_eval]
  ring

@[simp] theorem tailOuterGExpr_eval (terms : Nat) (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] (tailOuterGExpr terms) =
      tailOuterGReal r q zm := by
  simp only [tailOuterGExpr, tailOuterGReal, IntervalExpr.sub, evalReal,
    tailAExpr_eval, tailOuterWExpr_eval, tzmExpr_eval, tailDExpr_eval]
  ring

@[simp] theorem tailInnerGzExpr_eval (terms : Nat) (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] (tailInnerGzExpr terms) =
      tailInnerGzReal r q zp := by
  simp only [tailInnerGzExpr, tailInnerGzReal, tOne, IntervalExpr.sub,
    IntervalExpr.sq, evalReal, tailAExpr_eval, tqExpr_eval, tzpExpr_eval,
    Rat.cast_one]
  ring

@[simp] theorem tailOuterGzExpr_eval (terms : Nat) (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] (tailOuterGzExpr terms) =
      tailOuterGzReal r q zm := by
  simp only [tailOuterGzExpr, tailOuterGzReal, tOne, IntervalExpr.sub,
    IntervalExpr.sq, evalReal, tailAExpr_eval, tqExpr_eval, tzmExpr_eval,
    Rat.cast_one]
  ring

@[simp] theorem tailInnerGrExpr_eval (terms : Nat) (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] (tailInnerGrExpr terms) =
      tailInnerGrReal r q qr zp := by
  simp only [tailInnerGrExpr, tailGrExpr, tailInnerGrReal, tTwo,
    IntervalExpr.sub, IntervalExpr.div, IntervalExpr.sq, evalReal,
    tailArExpr_eval,
    tailInnerWExpr_eval, tailAExpr_eval, tqExpr_eval, tqrExpr_eval,
    tzpExpr_eval, tOnePlusQ_eval, Rat.cast_ofNat]
  ring

@[simp] theorem tailOuterGrExpr_eval (terms : Nat) (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] (tailOuterGrExpr terms) =
      tailOuterGrReal r q qr zm := by
  simp only [tailOuterGrExpr, tailGrExpr, tailOuterGrReal, tTwo,
    IntervalExpr.sub, IntervalExpr.div, IntervalExpr.sq, evalReal,
    tailArExpr_eval,
    tailOuterWExpr_eval, tailAExpr_eval, tqExpr_eval, tqrExpr_eval,
    tzmExpr_eval, tOnePlusQ_eval, Rat.cast_ofNat]
  ring

@[simp] theorem tailZpSlopeExpr_eval (terms : Nat) (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] (tailZpSlopeExpr terms) =
      tailZpSlopeReal r q qr zp := by
  simp only [tailZpSlopeExpr, IntervalExpr.div, evalReal,
    tailInnerGrExpr_eval, tailInnerGzExpr_eval]
  rw [tailZpSlopeReal]
  simp only [div_eq_mul_inv]
  ring

@[simp] theorem tailZmSlopeExpr_eval (terms : Nat) (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] (tailZmSlopeExpr terms) =
      tailZmSlopeReal r q qr zm := by
  simp only [tailZmSlopeExpr, IntervalExpr.div, evalReal,
    tailOuterGrExpr_eval, tailOuterGzExpr_eval]
  rw [tailZmSlopeReal]
  simp only [div_eq_mul_inv]
  ring

@[simp] theorem tailLambdaRExpr_eval (terms : Nat) (r q qr zp zm : ℝ) :
    evalReal ![r, q, qr, zp, zm] (tailLambdaRExpr terms) =
      tailLambdaRReal r q qr zp zm := by
  simp only [tailLambdaRExpr, tailHExpr, tailKExpr, tailHrExpr,
    tailKrExpr, tailLambdaRReal, tTwo, tFour,
    IntervalExpr.sub, IntervalExpr.div, IntervalExpr.sq,
    IntervalExpr.cube, evalReal, tqExpr_eval, tqrExpr_eval, tzpExpr_eval,
    tzmExpr_eval, tOnePlusQ_eval, tailZpSlopeExpr_eval,
    tailZmSlopeExpr_eval, Rat.cast_ofNat]
  simp only [div_eq_mul_inv, pow_succ]
  ring

end IntervalExpr

end

end Erdos1038
