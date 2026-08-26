import ErdosProblems.Erdos1038.OneCutSoftT
import ErdosProblems.Erdos1038.OneCutTailQBox

/-!
# Interval expressions for the regularized one-cut soft chart

The seven coordinates are `q`, the soft inner coordinate `s`, the scaled
outer root `zm`, and enclosures for `T(s)`, `T'(s)`, `T(w)`, `T'(w)`, where
`w = ((1+q)/(1-q))^2 s`.
-/

namespace Erdos1038

noncomputable section

def softKappa (q : ℝ) : ℝ := (1 + q) / (1 - q)
def softKappaPrime (q : ℝ) : ℝ := 2 / (1 - q) ^ 2
def softW (q s : ℝ) : ℝ := softKappa q ^ 2 * s

def softDividedInnerAt (q ts tw : ℝ) : ℝ :=
  A q * softKappa q * tw - ts

def softDividedInnerPartialQAt (q s tw tpw : ℝ) : ℝ :=
  (Aprime q * softKappa q + A q * softKappaPrime q) * tw +
    A q * softKappa q * tpw *
      (2 * softKappa q * softKappaPrime q * s)

def softDividedInnerPartialSAt (q tps tpw : ℝ) : ℝ :=
  A q * softKappa q ^ 3 * tpw - tps

def softC (s : ℝ) : ℝ := (1 + s) / (1 - s)
def softCPrime (s : ℝ) : ℝ := 2 / (1 - s) ^ 2

def softLengthAt (q s zm : ℝ) : ℝ :=
  scaledH q * zm + scaledK q / zm - 2 * H q * softC s

def softLengthPartialQAt (q s zm : ℝ) : ℝ :=
  scaledHprime q * zm + scaledKprime q / zm -
    2 * Hprime q * softC s

def softLengthPartialSAt (q s : ℝ) : ℝ :=
  -2 * H q * softCPrime s

def softLengthPartialZmAt (q zm : ℝ) : ℝ :=
  scaledH q - scaledK q / zm ^ 2

def softLambdaDerivativeAt (q s zm tps tw tpw : ℝ) : ℝ :=
  softLengthPartialQAt q s zm +
    softLengthPartialSAt q s *
      (-softDividedInnerPartialQAt q s tw tpw /
        softDividedInnerPartialSAt q tps tpw) +
    softLengthPartialZmAt q zm * IntervalExpr.scaledZMinusSlopeAt q zm

namespace IntervalExpr

def powExpr {n : Nat} (x : IntervalExpr n) : Nat → IntervalExpr n
  | 0 => eOne
  | k + 1 => .mul (powExpr x k) x

def softTLowerExpr {n : Nat} : Nat → IntervalExpr n → IntervalExpr n
  | 0, _ => eZero
  | k + 1, x =>
      .add (softTLowerExpr k x)
        (.div (powExpr x k) (.rat (2 * k + 1)))

def softTUpperExpr {n : Nat} (terms : Nat) (x : IntervalExpr n) :
    IntervalExpr n :=
  .add (softTLowerExpr terms x)
    (.div (powExpr x terms) (.sub eOne x))

def softTPrimeUpperExpr {n : Nat} (x : IntervalExpr n) :
    IntervalExpr n :=
  .sub
    (.sub (.sub (.div eOne (.mul eTwo (.sub eOne x))) (.rat (1 / 6)))
      (.div x (.rat 10)))
    (.div (.sq x) (.rat 14))

def softTPrimeLowerExpr {n : Nat} (x : IntervalExpr n) :
    IntervalExpr n :=
  .add (.add (.rat (1 / 3)) (.div (.mul eTwo x) (.rat 5)))
    (.div (.mul (.rat 3) (.sq x)) (.rat 7))

@[simp] theorem powExpr_eval {n : Nat} (x : Fin n → ℝ)
    (e : IntervalExpr n) (k : Nat) :
    evalReal x (powExpr e k) = evalReal x e ^ k := by
  induction k with
  | zero => simp [powExpr, eOne, eRat, evalReal]
  | succ k ih => simp [powExpr, evalReal, ih, pow_succ]

@[simp] theorem softTLowerExpr_eval {n : Nat} (x : Fin n → ℝ)
    (terms : Nat) (e : IntervalExpr n) :
    evalReal x (softTLowerExpr terms e) =
      softTLower terms (evalReal x e) := by
  induction terms with
  | zero => simp [softTLowerExpr, softTLower, eZero, eRat, evalReal]
  | succ k ih =>
      simp only [softTLowerExpr, evalReal, ih, div, powExpr_eval,
        Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
      simp only [softTLower, Finset.sum_range_succ]
      have hkcast : (((k : Rat) : ℝ)) = (k : ℝ) := by norm_num
      rw [hkcast]
      simp [div_eq_mul_inv]

@[simp] theorem softTUpperExpr_eval {n : Nat} (x : Fin n → ℝ)
    (terms : Nat) (e : IntervalExpr n) :
    evalReal x (softTUpperExpr terms e) =
      softTUpper terms (evalReal x e) := by
  simp only [softTUpperExpr, evalReal, softTLowerExpr_eval, softTUpper,
    div, powExpr_eval, sub, eOne, eRat]
  ring_nf

@[simp] theorem softTPrimeUpperExpr_eval {n : Nat} (x : Fin n → ℝ)
    (e : IntervalExpr n) :
    evalReal x (softTPrimeUpperExpr e) =
      1 / (2 * (1 - evalReal x e)) - 1 / 6 - evalReal x e / 10 -
        evalReal x e ^ 2 / 14 := by
  simp [softTPrimeUpperExpr, evalReal, eOne, eTwo, eRat, sub, div, sq]
  ring_nf

@[simp] theorem softTPrimeLowerExpr_eval {n : Nat} (x : Fin n → ℝ)
    (e : IntervalExpr n) :
    evalReal x (softTPrimeLowerExpr e) =
      1 / 3 + 2 * evalReal x e / 5 + 3 * evalReal x e ^ 2 / 7 := by
  simp [softTPrimeLowerExpr, evalReal, eTwo, eRat, div, sq]
  ring_nf

def softQExpr : IntervalExpr 7 := .var 0
def softSExpr : IntervalExpr 7 := .var 1
def softZmExpr : IntervalExpr 7 := .var 2
def softTsExpr : IntervalExpr 7 := .var 3
def softTpsExpr : IntervalExpr 7 := .var 4
def softTwExpr : IntervalExpr 7 := .var 5
def softTpwExpr : IntervalExpr 7 := .var 6

def softOnePlusQExpr : IntervalExpr 7 := .add eOne softQExpr
def softOneMinusQExpr : IntervalExpr 7 := .sub eOne softQExpr
def softHExpr : IntervalExpr 7 :=
  .div (.mul eTwo softQExpr) (.sq softOnePlusQExpr)
def softHprimeExpr : IntervalExpr 7 :=
  .div (.mul eTwo (.sub eOne softQExpr)) (.cube softOnePlusQExpr)
def softLogQExpr (terms shift : Nat) : IntervalExpr 7 :=
  .log2Shift terms shift softQExpr
def softLogHExpr (terms shift : Nat) : IntervalExpr 7 :=
  .log2Shift terms shift softHExpr
def softAExpr (terms shift : Nat) : IntervalExpr 7 :=
  .div (softLogHExpr terms shift) (softLogQExpr terms shift)
def softAprimeExpr (terms shift : Nat) : IntervalExpr 7 :=
  .div
    (.sub
      (.mul (.div softHprimeExpr softHExpr) (softLogQExpr terms shift))
      (.mul (softLogHExpr terms shift) (.inv softQExpr)))
    (.sq (softLogQExpr terms shift))

def softKappaExpr : IntervalExpr 7 :=
  .div softOnePlusQExpr softOneMinusQExpr
def softKappaPrimeExpr : IntervalExpr 7 :=
  .div eTwo (.sq softOneMinusQExpr)
def softWExpr : IntervalExpr 7 := .mul (.sq softKappaExpr) softSExpr

def softDividedInnerExpr (terms shift : Nat) : IntervalExpr 7 :=
  .sub (.mul (.mul (softAExpr terms shift) softKappaExpr) softTwExpr)
    softTsExpr

def softDividedInnerPartialQExpr (terms shift : Nat) : IntervalExpr 7 :=
  .add
    (.mul
      (.add (.mul (softAprimeExpr terms shift) softKappaExpr)
        (.mul (softAExpr terms shift) softKappaPrimeExpr))
      softTwExpr)
    (.mul
      (.mul (.mul (softAExpr terms shift) softKappaExpr) softTpwExpr)
      (.mul (.mul eTwo softKappaExpr)
        (.mul softKappaPrimeExpr softSExpr)))

def softDividedInnerPartialSExpr (terms shift : Nat) : IntervalExpr 7 :=
  .sub
    (.mul (.mul (softAExpr terms shift) (.cube softKappaExpr)) softTpwExpr)
    softTpsExpr

def softScaledDExpr (terms : Nat) : IntervalExpr 7 :=
  .log terms (.div eTwo (.sq softOnePlusQExpr))
def softScaledDprimeExpr : IntervalExpr 7 :=
  .neg (.div eTwo softOnePlusQExpr)
def softOuterLogArgumentExpr : IntervalExpr 7 :=
  .div (.sub softZmExpr (.sq softQExpr)) (.sub softZmExpr eOne)
def softOuterResidualExpr (terms shift : Nat) : IntervalExpr 7 :=
  .sub
    (.sub (.mul (softAExpr terms shift)
      (.log terms softOuterLogArgumentExpr)) (.log terms softZmExpr))
    (softScaledDExpr terms)
def softOuterPartialZmExpr (terms shift : Nat) : IntervalExpr 7 :=
  .sub
    (.mul (softAExpr terms shift)
      (.sub (.inv (.sub softZmExpr (.sq softQExpr)))
        (.inv (.sub softZmExpr eOne))))
    (.inv softZmExpr)
def softOuterPartialQExpr (terms shift : Nat) : IntervalExpr 7 :=
  .sub
    (.sub
      (.mul (softAprimeExpr terms shift)
        (.log terms softOuterLogArgumentExpr))
      (.div (.mul (.mul (softAExpr terms shift) eTwo) softQExpr)
        (.sub softZmExpr (.sq softQExpr))))
    softScaledDprimeExpr
def softZmSlopeExpr (terms shift : Nat) : IntervalExpr 7 :=
  .neg (.div (softOuterPartialQExpr terms shift)
    (softOuterPartialZmExpr terms shift))

def softCExpr : IntervalExpr 7 :=
  .div (.add eOne softSExpr) (.sub eOne softSExpr)
def softCPrimeExpr : IntervalExpr 7 :=
  .div eTwo (.sq (.sub eOne softSExpr))
def softScaledHExpr : IntervalExpr 7 :=
  .div eTwo (.sq softOnePlusQExpr)
def softScaledKExpr : IntervalExpr 7 :=
  .div (.mul eTwo (.sq softQExpr)) (.sq softOnePlusQExpr)
def softScaledHprimeExpr : IntervalExpr 7 :=
  .neg (.div eFour (.cube softOnePlusQExpr))
def softScaledKprimeExpr : IntervalExpr 7 :=
  .div (.mul eFour softQExpr) (.cube softOnePlusQExpr)

def softLengthExpr : IntervalExpr 7 :=
  .sub
    (.add (.mul softScaledHExpr softZmExpr)
      (.div softScaledKExpr softZmExpr))
    (.mul (.mul eTwo softHExpr) softCExpr)
def softLengthPartialQExpr : IntervalExpr 7 :=
  .sub
    (.add (.mul softScaledHprimeExpr softZmExpr)
      (.div softScaledKprimeExpr softZmExpr))
    (.mul (.mul eTwo softHprimeExpr) softCExpr)
def softLengthPartialSExpr : IntervalExpr 7 :=
  .neg (.mul (.mul eTwo softHExpr) softCPrimeExpr)
def softLengthPartialZmExpr : IntervalExpr 7 :=
  .sub softScaledHExpr (.div softScaledKExpr (.sq softZmExpr))

def softLambdaDerivativeExpr (terms shift : Nat) : IntervalExpr 7 :=
  .add
    (.add softLengthPartialQExpr
      (.mul softLengthPartialSExpr
        (.neg (.div (softDividedInnerPartialQExpr terms shift)
          (softDividedInnerPartialSExpr terms shift)))))
    (.mul softLengthPartialZmExpr (softZmSlopeExpr terms shift))

@[simp] theorem softQExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softQExpr = q := by simp [softQExpr, evalReal]
@[simp] theorem softSExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softSExpr = s := by simp [softSExpr, evalReal]
@[simp] theorem softZmExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softZmExpr = zm := by simp [softZmExpr, evalReal]
@[simp] theorem softTsExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softTsExpr = ts := by simp [softTsExpr, evalReal]
@[simp] theorem softTpsExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softTpsExpr = tps := by simp [softTpsExpr, evalReal]
@[simp] theorem softTwExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softTwExpr = tw := by simp [softTwExpr, evalReal]
@[simp] theorem softTpwExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softTpwExpr = tpw := by simp [softTpwExpr, evalReal]

@[simp] theorem softOnePlusQExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softOnePlusQExpr = 1 + q := by
  simp [softOnePlusQExpr, eOne, eRat, evalReal]

@[simp] theorem softOneMinusQExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softOneMinusQExpr = 1 - q := by
  simp [softOneMinusQExpr, eOne, eRat, sub, evalReal]
  ring_nf

@[simp] theorem softHExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softHExpr = H q := by
  simp only [softHExpr, eTwo, eRat, div, sq, evalReal,
    softQExpr_eval, softOnePlusQExpr_eval, Rat.cast_ofNat]
  rw [H]
  ring_nf

@[simp] theorem softHprimeExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softHprimeExpr = Hprime q := by
  simp only [softHprimeExpr, eOne, eTwo, eRat, sub, div, cube, evalReal,
    softQExpr_eval, softOnePlusQExpr_eval, Rat.cast_ofNat]
  rw [Hprime]
  ring_nf

@[simp] theorem softLogQExpr_eval (terms shift : Nat)
    (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw]
      (softLogQExpr terms shift) = Real.log q := by
  simp [softLogQExpr, evalReal]

@[simp] theorem softLogHExpr_eval (terms shift : Nat)
    (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw]
      (softLogHExpr terms shift) = Real.log (H q) := by
  simp [softLogHExpr, evalReal]

@[simp] theorem softAExpr_eval (terms shift : Nat)
    (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw]
      (softAExpr terms shift) = A q := by
  simp [softAExpr, div, evalReal, A]
  ring_nf

@[simp] theorem softAprimeExpr_eval (terms shift : Nat)
    (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw]
      (softAprimeExpr terms shift) = Aprime q := by
  simp only [softAprimeExpr, sub, div, sq, evalReal, softHExpr_eval,
    softHprimeExpr_eval, softLogQExpr_eval, softLogHExpr_eval,
    softQExpr_eval]
  rw [Aprime]
  ring_nf

@[simp] theorem softKappaExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softKappaExpr =
      softKappa q := by
  simp [softKappaExpr, softKappa, div, evalReal]
  ring_nf

@[simp] theorem softKappaPrimeExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softKappaPrimeExpr =
      softKappaPrime q := by
  simp [softKappaPrimeExpr, softKappaPrime, div, sq, eTwo, eRat,
    evalReal, pow_two]
  simp [div_eq_mul_inv]

@[simp] theorem softDividedInnerPartialQExpr_eval (terms shift : Nat)
    (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw]
        (softDividedInnerPartialQExpr terms shift) =
      softDividedInnerPartialQAt q s tw tpw := by
  simp only [softDividedInnerPartialQExpr, evalReal, softAprimeExpr_eval,
    softKappaExpr_eval, softAExpr_eval, softKappaPrimeExpr_eval,
    softTwExpr_eval, softTpwExpr_eval, softSExpr_eval, eTwo, eRat,
    Rat.cast_ofNat]
  rw [softDividedInnerPartialQAt]
  ring_nf

@[simp] theorem softDividedInnerPartialSExpr_eval (terms shift : Nat)
    (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw]
        (softDividedInnerPartialSExpr terms shift) =
      softDividedInnerPartialSAt q tps tpw := by
  simp only [softDividedInnerPartialSExpr, cube, sub, evalReal,
    softAExpr_eval, softKappaExpr_eval, softTpwExpr_eval,
    softTpsExpr_eval]
  rw [softDividedInnerPartialSAt]
  ring_nf

@[simp] theorem softOuterPartialZmExpr_eval (terms shift : Nat)
    (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw]
        (softOuterPartialZmExpr terms shift) =
      scaledOuterPartialZ q zm := by
  simp only [softOuterPartialZmExpr, sub, sq, evalReal,
    softAExpr_eval, softZmExpr_eval, softQExpr_eval, eOne, eRat]
  rw [scaledOuterPartialZ]
  ring_nf

@[simp] theorem softOuterPartialQExpr_eval (terms shift : Nat)
    (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw]
        (softOuterPartialQExpr terms shift) =
      scaledOuterPartialQ q zm := by
  simp only [softOuterPartialQExpr, softOuterLogArgumentExpr,
    softScaledDprimeExpr, eTwo, eRat, sub, div, sq, evalReal,
    softAExpr_eval, softAprimeExpr_eval, softQExpr_eval, softZmExpr_eval,
    softOnePlusQExpr_eval, eOne, Rat.cast_ofNat]
  rw [scaledOuterPartialQ, scaledDprime]
  ring_nf

@[simp] theorem softZmSlopeExpr_eval (terms shift : Nat)
    (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw]
        (softZmSlopeExpr terms shift) =
      scaledZMinusSlopeAt q zm := by
  simp only [softZmSlopeExpr, div, evalReal, softOuterPartialQExpr_eval,
    softOuterPartialZmExpr_eval]
  rw [scaledZMinusSlopeAt]
  ring_nf

@[simp] theorem softCExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softCExpr = softC s := by
  simp [softCExpr, softC, eOne, eRat, sub, div, evalReal]
  ring_nf

@[simp] theorem softCPrimeExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softCPrimeExpr =
      softCPrime s := by
  simp [softCPrimeExpr, softCPrime, eOne, eTwo, eRat, sub, div, sq,
    evalReal, pow_two]
  simp [div_eq_mul_inv]
  ring_nf

@[simp] theorem softScaledHExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softScaledHExpr =
      scaledH q := by
  simp [softScaledHExpr, scaledH, eTwo, eRat, div, sq, evalReal, pow_two]
  simp [div_eq_mul_inv]

@[simp] theorem softScaledKExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softScaledKExpr =
      scaledK q := by
  simp [softScaledKExpr, scaledK, eTwo, eRat, div, sq, evalReal, pow_two]
  simp [div_eq_mul_inv]

@[simp] theorem softScaledHprimeExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softScaledHprimeExpr =
      scaledHprime q := by
  simp [softScaledHprimeExpr, scaledHprime, eFour, eRat, div, cube,
    evalReal, pow_succ]
  simp [div_eq_mul_inv]

@[simp] theorem softScaledKprimeExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softScaledKprimeExpr =
      scaledKprime q := by
  simp [softScaledKprimeExpr, scaledKprime, eFour, eRat, div, cube,
    evalReal, pow_succ]
  simp [div_eq_mul_inv]

@[simp] theorem softLengthPartialQExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softLengthPartialQExpr =
      softLengthPartialQAt q s zm := by
  simp only [softLengthPartialQExpr, sub, div, evalReal,
    softScaledHprimeExpr_eval,
    softZmExpr_eval, softScaledKprimeExpr_eval, softHprimeExpr_eval,
    softCExpr_eval, eTwo, eRat, Rat.cast_ofNat]
  rw [softLengthPartialQAt]
  ring_nf

@[simp] theorem softLengthPartialSExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softLengthPartialSExpr =
      softLengthPartialSAt q s := by
  simp only [softLengthPartialSExpr, evalReal, softHExpr_eval,
    softCPrimeExpr_eval, eTwo, eRat, Rat.cast_ofNat]
  rw [softLengthPartialSAt]
  ring_nf

@[simp] theorem softLengthPartialZmExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softLengthPartialZmExpr =
      softLengthPartialZmAt q zm := by
  simp only [softLengthPartialZmExpr, sub, div, evalReal,
    softScaledHExpr_eval, softScaledKExpr_eval, softZmExpr_eval, sq]
  rw [softLengthPartialZmAt]
  ring_nf

@[simp] theorem softCoreExprs_eval (terms shift : Nat)
    (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw]
        (softLambdaDerivativeExpr terms shift) =
      softLambdaDerivativeAt q s zm tps tw tpw := by
  simp only [softLambdaDerivativeExpr, div, evalReal,
    softLengthPartialQExpr_eval,
    softLengthPartialSExpr_eval, softDividedInnerPartialQExpr_eval,
    softDividedInnerPartialSExpr_eval, softLengthPartialZmExpr_eval,
    softZmSlopeExpr_eval]
  rw [softLambdaDerivativeAt]
  ring_nf

end IntervalExpr

end

end Erdos1038
