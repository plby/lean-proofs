import ErdosProblems.Erdos1038.OneCutScaledRootBounds
import ErdosProblems.Erdos1038.RationalInterval

/-!
# A proved interval-expression evaluator for the one-cut certificate

Certificate data are merely rational boxes.  This evaluator interprets a
small arithmetic/logarithm expression language both over `ℝ` and over
`RatInterval`; `intervalEval_sound` proves that every successful interval
evaluation encloses the real value.  Thus later kernel reductions check only
exact rational arithmetic.
-/

namespace Erdos1038

noncomputable section

inductive IntervalExpr (n : Nat) where
  | rat (r : Rat)
  | var (i : Fin n)
  | add (a b : IntervalExpr n)
  | neg (a : IntervalExpr n)
  | mul (a b : IntervalExpr n)
  | inv (a : IntervalExpr n)
  | log (terms : Nat) (a : IntervalExpr n)
  | log2Shift (terms shift : Nat) (a : IntervalExpr n)
deriving DecidableEq, Repr

namespace IntervalExpr

def sub {n : Nat} (a b : IntervalExpr n) : IntervalExpr n := add a (neg b)

def div {n : Nat} (a b : IntervalExpr n) : IntervalExpr n := mul a (inv b)

def sq {n : Nat} (a : IntervalExpr n) : IntervalExpr n := mul a a

def cube {n : Nat} (a : IntervalExpr n) : IntervalExpr n := mul (mul a a) a

def evalReal {n : Nat} (x : Fin n → ℝ) : IntervalExpr n → ℝ
  | .rat r => (r : ℝ)
  | .var i => x i
  | .add a b => evalReal x a + evalReal x b
  | .neg a => -evalReal x a
  | .mul a b => evalReal x a * evalReal x b
  | .inv a => (evalReal x a)⁻¹
  | .log _ a => Real.log (evalReal x a)
  | .log2Shift _ _ a => Real.log (evalReal x a)

def log2ShiftInterval (terms shift : Nat) (A : RatInterval) :
    Option RatInterval := do
  let scaled := RatInterval.mul (RatInterval.point ((2 : Rat) ^ shift)) A
  let logScaled ← RatInterval.log? terms scaled
  let logTwo ← RatInterval.log? terms (RatInterval.point 2)
  pure (RatInterval.sub logScaled
    (RatInterval.mul (RatInterval.point (shift : Rat)) logTwo))

def evalInterval {n : Nat} (X : Fin n → RatInterval) :
    IntervalExpr n → Option RatInterval
  | .rat r => some (RatInterval.point r)
  | .var i => some (X i)
  | .add a b => do
      let A ← evalInterval X a
      let B ← evalInterval X b
      pure (RatInterval.add A B)
  | .neg a => do
      let A ← evalInterval X a
      pure (RatInterval.neg A)
  | .mul a b => do
      let A ← evalInterval X a
      let B ← evalInterval X b
      pure (RatInterval.mul A B)
  | .inv a => do
      let A ← evalInterval X a
      RatInterval.inv? A
  | .log terms a => do
      let A ← evalInterval X a
      RatInterval.log? terms A
  | .log2Shift terms shift a => do
      let A ← evalInterval X a
      log2ShiftInterval terms shift A

theorem log2ShiftInterval_sound {terms shift : Nat} {A I : RatInterval}
    {x : ℝ} (hAord : A.Ordered) (hAx : A.Contains x)
    (hI : log2ShiftInterval terms shift A = some I) :
    I.Ordered ∧ I.Contains (Real.log x) := by
  let p : Rat := (2 : Rat) ^ shift
  let scaled := RatInterval.mul (RatInterval.point p) A
  cases hscaled : RatInterval.log? terms scaled with
  | none => simp [log2ShiftInterval, p, scaled, hscaled] at hI
  | some L =>
      cases htwo : RatInterval.log? terms (RatInterval.point 2) with
      | none => simp [log2ShiftInterval, p, scaled, hscaled, htwo] at hI
      | some T =>
          have hEq : RatInterval.sub L
              (RatInterval.mul (RatInterval.point (shift : Rat)) T) = I := by
            simpa [log2ShiftInterval, p, scaled, hscaled, htwo] using! hI
          symm at hEq
          subst I
          have hpord := RatInterval.point_ordered p
          have hpcontains := RatInterval.point_contains p
          have hscaledOrd : scaled.Ordered :=
            RatInterval.mul_ordered hpord hAord
          have hscaledContains : scaled.Contains ((p : ℝ) * x) :=
            RatInterval.mul_contains hpcontains hAx
          have hLord := RatInterval.log_ordered hscaledOrd hscaled
          have hLcontains := RatInterval.log_contains hscaledContains hscaled
          have hTord := RatInterval.log_ordered
            (RatInterval.point_ordered (2 : Rat)) htwo
          have hTcontains := RatInterval.log_contains
            (RatInterval.point_contains (2 : Rat)) htwo
          have hkord := RatInterval.point_ordered (shift : Rat)
          have hkcontains := RatInterval.point_contains (shift : Rat)
          have hmulOrd := RatInterval.mul_ordered hkord hTord
          have hmulContains := RatInterval.mul_contains hkcontains hTcontains
          have hsubOrd := RatInterval.sub_ordered hLord hmulOrd
          have hsubContains := RatInterval.sub_contains hLcontains hmulContains
          have hscaledLo : (0 : Rat) < scaled.lo := by
            by_cases hlo : (0 : Rat) < scaled.lo
            · exact hlo
            · simp [RatInterval.log?, hlo] at hscaled
          have hprodpos : 0 < (p : ℝ) * x := by
            have hlo : (0 : ℝ) < (scaled.lo : ℝ) := by exact_mod_cast hscaledLo
            exact hlo.trans_le hscaledContains.1
          have hp : 0 < (p : ℝ) := by
            dsimp [p]
            positivity
          have hx : 0 < x := by
            rcases (mul_pos_iff.mp hprodpos) with h | h
            · exact h.2
            · exact False.elim ((not_lt_of_ge hp.le) h.1)
          have hpcast : (p : ℝ) = (2 : ℝ) ^ shift := by
            simp [p]
          have hkcast : (((shift : Rat) : ℝ)) = (shift : ℝ) := by
            norm_num
          have hid : Real.log ((p : ℝ) * x) -
              ((shift : Rat) : ℝ) * Real.log (2 : ℝ) = Real.log x := by
            rw [Real.log_mul hp.ne' hx.ne', hpcast, Real.log_pow, hkcast]
            ring
          exact ⟨hsubOrd, hid ▸ hsubContains⟩

theorem evalInterval_sound {n : Nat} {X : Fin n → RatInterval}
    {x : Fin n → ℝ}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i)) :
    ∀ (e : IntervalExpr n) (I : RatInterval),
      evalInterval X e = some I →
        I.Ordered ∧ I.Contains (evalReal x e) := by
  intro e
  induction e with
  | rat r =>
      intro I hI
      simp only [evalInterval, Option.some.injEq] at hI
      subst I
      exact ⟨RatInterval.point_ordered r, RatInterval.point_contains r⟩
  | var i =>
      intro I hI
      simp only [evalInterval, Option.some.injEq] at hI
      subst I
      exact ⟨hordered i, hcontains i⟩
  | add a b iha ihb =>
      intro I hI
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at hI
      | some A =>
          cases hb : evalInterval X b with
          | none => simp [evalInterval, ha, hb] at hI
          | some B =>
              have hEq : RatInterval.add A B = I := by
                simpa [evalInterval, ha, hb] using! hI
              symm at hEq
              subst I
              exact ⟨RatInterval.add_ordered (iha A ha).1 (ihb B hb).1,
                RatInterval.add_contains (iha A ha).2 (ihb B hb).2⟩
  | neg a ih =>
      intro I hI
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at hI
      | some A =>
          have hEq : RatInterval.neg A = I := by
            simpa [evalInterval, ha] using! hI
          symm at hEq
          subst I
          exact ⟨RatInterval.neg_ordered (ih A ha).1,
            RatInterval.neg_contains (ih A ha).2⟩
  | mul a b iha ihb =>
      intro I hI
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at hI
      | some A =>
          cases hb : evalInterval X b with
          | none => simp [evalInterval, ha, hb] at hI
          | some B =>
              have hEq : RatInterval.mul A B = I := by
                simpa [evalInterval, ha, hb] using! hI
              symm at hEq
              subst I
              exact ⟨RatInterval.mul_ordered (iha A ha).1 (ihb B hb).1,
                RatInterval.mul_contains (iha A ha).2 (ihb B hb).2⟩
  | inv a ih =>
      intro I hI
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at hI
      | some A =>
          have hA := ih A ha
          have hI' : RatInterval.inv? A = some I := by
            simpa [evalInterval, ha] using! hI
          exact ⟨RatInterval.inv_ordered hA.1 hI',
            RatInterval.inv_contains hA.2 hI'⟩
  | log terms a ih =>
      intro I hI
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at hI
      | some A =>
          have hA := ih A ha
          have hI' : RatInterval.log? terms A = some I := by
            simpa [evalInterval, ha] using! hI
          exact ⟨RatInterval.log_ordered hA.1 hI',
            RatInterval.log_contains hA.2 hI'⟩
  | log2Shift terms shift a ih =>
      intro I hI
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at hI
      | some A =>
          have hA := ih A ha
          have hI' : log2ShiftInterval terms shift A = some I := by
            simpa [evalInterval, ha] using! hI
          exact log2ShiftInterval_sound hA.1 hA.2 hI'

theorem evalInterval_lt_zero {n : Nat} {X : Fin n → RatInterval}
    {x : Fin n → ℝ} {e : IntervalExpr n} {I : RatInterval}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i))
    (heval : evalInterval X e = some I) (hneg : I.hi < 0) :
    evalReal x e < 0 := by
  have hsound := (evalInterval_sound hordered hcontains e I heval).2.2
  have hcast : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
  exact hsound.trans_lt hcast

theorem evalInterval_pos {n : Nat} {X : Fin n → RatInterval}
    {x : Fin n → ℝ} {e : IntervalExpr n} {I : RatInterval}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i))
    (heval : evalInterval X e = some I) (hpos : 0 < I.lo) :
    0 < evalReal x e := by
  have hsound := (evalInterval_sound hordered hcontains e I heval).2.1
  have hcast : 0 < (I.lo : ℝ) := by exact_mod_cast hpos
  exact hcast.trans_le hsound

/-! ## The concrete stable expressions -/

def eRat {n : Nat} (r : Rat) : IntervalExpr n := .rat r

def eZero {n : Nat} : IntervalExpr n := eRat 0
def eOne {n : Nat} : IntervalExpr n := eRat 1
def eTwo {n : Nat} : IntervalExpr n := eRat 2
def eFour {n : Nat} : IntervalExpr n := eRat 4

def qExpr : IntervalExpr 3 := .var 0
def zpExpr : IntervalExpr 3 := .var 1
def zmExpr : IntervalExpr 3 := .var 2

def onePlusQExpr : IntervalExpr 3 := .add eOne qExpr
def HExpr : IntervalExpr 3 := .div (.mul eTwo qExpr) (.sq onePlusQExpr)
def HprimeExpr : IntervalExpr 3 :=
  .div (.mul eTwo (.sub eOne qExpr)) (.cube onePlusQExpr)
def logQExpr (terms shift : Nat) : IntervalExpr 3 :=
  .log2Shift terms shift qExpr
def logHExpr (terms shift : Nat) : IntervalExpr 3 :=
  .log2Shift terms shift HExpr
def AExpr (terms shift : Nat) : IntervalExpr 3 :=
  .div (logHExpr terms shift) (logQExpr terms shift)
def AprimeExpr (terms shift : Nat) : IntervalExpr 3 :=
  .div
    (.sub (.mul (.div HprimeExpr HExpr) (logQExpr terms shift))
      (.mul (logHExpr terms shift) (.inv qExpr)))
    (.sq (logQExpr terms shift))

def scaledDprimeExpr : IntervalExpr 3 := .neg (.div eTwo onePlusQExpr)

def scaledDExpr (terms : Nat) : IntervalExpr 3 :=
  .log terms (.div eTwo (.sq onePlusQExpr))

def innerLogArgumentExpr : IntervalExpr 3 :=
  .div (.sub zpExpr (.sq qExpr)) (.sub eOne zpExpr)

def outerLogArgumentExpr : IntervalExpr 3 :=
  .div (.sub zmExpr (.sq qExpr)) (.sub zmExpr eOne)

def innerResidualExpr (terms shift : Nat) : IntervalExpr 3 :=
  .sub (.sub (.mul (AExpr terms shift) (.log terms innerLogArgumentExpr))
    (.log terms zpExpr))
    (scaledDExpr terms)

def outerResidualExpr (terms shift : Nat) : IntervalExpr 3 :=
  .sub (.sub (.mul (AExpr terms shift) (.log terms outerLogArgumentExpr))
    (.log terms zmExpr))
    (scaledDExpr terms)

def innerPartialZExpr (terms shift : Nat) : IntervalExpr 3 :=
  .sub
    (.mul (AExpr terms shift)
      (.add (.inv (.sub zpExpr (.sq qExpr)))
        (.inv (.sub eOne zpExpr))))
    (.inv zpExpr)

def outerPartialZExpr (terms shift : Nat) : IntervalExpr 3 :=
  .sub
    (.mul (AExpr terms shift)
      (.sub (.inv (.sub zmExpr (.sq qExpr)))
        (.inv (.sub zmExpr eOne))))
    (.inv zmExpr)

def innerPartialQExpr (terms shift : Nat) : IntervalExpr 3 :=
  .sub
    (.sub
      (.mul (AprimeExpr terms shift) (.log terms innerLogArgumentExpr))
      (.div (.mul (.mul (AExpr terms shift) eTwo) qExpr)
        (.sub zpExpr (.sq qExpr))))
    scaledDprimeExpr

def outerPartialQExpr (terms shift : Nat) : IntervalExpr 3 :=
  .sub
    (.sub
      (.mul (AprimeExpr terms shift) (.log terms outerLogArgumentExpr))
      (.div (.mul (.mul (AExpr terms shift) eTwo) qExpr)
        (.sub zmExpr (.sq qExpr))))
    scaledDprimeExpr

def zpSlopeExpr (terms shift : Nat) : IntervalExpr 3 :=
  .neg (.div (innerPartialQExpr terms shift) (innerPartialZExpr terms shift))

def zmSlopeExpr (terms shift : Nat) : IntervalExpr 3 :=
  .neg (.div (outerPartialQExpr terms shift) (outerPartialZExpr terms shift))

def scaledHExpr : IntervalExpr 3 := .div eTwo (.sq onePlusQExpr)
def scaledKExpr : IntervalExpr 3 :=
  .div (.mul eTwo (.sq qExpr)) (.sq onePlusQExpr)
def scaledHprimeExpr : IntervalExpr 3 := .neg (.div eFour (.cube onePlusQExpr))
def scaledKprimeExpr : IntervalExpr 3 :=
  .div (.mul eFour qExpr) (.cube onePlusQExpr)

def lambdaDerivativeExpr (terms shift : Nat) : IntervalExpr 3 :=
  .add
    (.add
      (.mul scaledHprimeExpr (.sub zmExpr zpExpr))
      (.mul scaledHExpr
        (.sub (zmSlopeExpr terms shift) (zpSlopeExpr terms shift))))
    (.add
      (.mul scaledKprimeExpr (.sub (.inv zmExpr) (.inv zpExpr)))
      (.mul scaledKExpr
        (.add
          (.neg (.div (zmSlopeExpr terms shift) (.sq zmExpr)))
          (.div (zpSlopeExpr terms shift) (.sq zpExpr)))))

def lambdaExpr : IntervalExpr 3 :=
  .add
    (.mul scaledHExpr (.sub zmExpr zpExpr))
    (.mul scaledKExpr (.sub (.inv zmExpr) (.inv zpExpr)))

def scaledZPlusSlopeAt (q zp : ℝ) : ℝ :=
  -scaledInnerPartialQ q zp / scaledInnerPartialZ q zp

def scaledZMinusSlopeAt (q zm : ℝ) : ℝ :=
  -scaledOuterPartialQ q zm / scaledOuterPartialZ q zm

def scaledLambdaDerivativeAt (q zp zm : ℝ) : ℝ :=
  scaledHprime q * (zm - zp) +
    scaledH q * (scaledZMinusSlopeAt q zm - scaledZPlusSlopeAt q zp) +
    scaledKprime q * (zm⁻¹ - zp⁻¹) +
    scaledK q *
      (-scaledZMinusSlopeAt q zm / zm ^ 2 +
        scaledZPlusSlopeAt q zp / zp ^ 2)

theorem scaledLambdaDerivativeFormula_eq_at (q : ℝ) :
    scaledLambdaDerivativeFormula q =
      scaledLambdaDerivativeAt q (zPlus q) (zMinus q) := by
  rfl

@[simp] theorem qExpr_eval (q zp zm : ℝ) :
    evalReal ![q, zp, zm] qExpr = q := by
  simp [qExpr, evalReal]

@[simp] theorem zpExpr_eval (q zp zm : ℝ) :
    evalReal ![q, zp, zm] zpExpr = zp := by
  simp [zpExpr, evalReal]

@[simp] theorem zmExpr_eval (q zp zm : ℝ) :
    evalReal ![q, zp, zm] zmExpr = zm := by
  simp [zmExpr, evalReal]

@[simp] theorem onePlusQExpr_eval (q zp zm : ℝ) :
    evalReal ![q, zp, zm] onePlusQExpr = 1 + q := by
  simp [onePlusQExpr, eOne, eRat, evalReal]

@[simp] theorem HExpr_eval (q zp zm : ℝ) :
    evalReal ![q, zp, zm] HExpr = H q := by
  simp only [HExpr, eTwo, eRat, div, sq, evalReal, qExpr_eval,
    onePlusQExpr_eval, Rat.cast_ofNat]
  rw [H]
  ring

@[simp] theorem HprimeExpr_eval (q zp zm : ℝ) :
    evalReal ![q, zp, zm] HprimeExpr = Hprime q := by
  simp only [HprimeExpr, eOne, eTwo, eRat, sub, div, cube, evalReal,
    qExpr_eval, onePlusQExpr_eval, Rat.cast_ofNat]
  rw [Hprime]
  ring

@[simp] theorem logQExpr_eval (terms shift : Nat) (q zp zm : ℝ) :
    evalReal ![q, zp, zm] (logQExpr terms shift) = Real.log q := by
  simp [logQExpr, evalReal]

@[simp] theorem logHExpr_eval (terms shift : Nat) (q zp zm : ℝ) :
    evalReal ![q, zp, zm] (logHExpr terms shift) = Real.log (H q) := by
  simp [logHExpr, evalReal]

@[simp] theorem AExpr_eval (terms shift : Nat) (q zp zm : ℝ) :
    evalReal ![q, zp, zm] (AExpr terms shift) = A q := by
  simp only [AExpr, div, evalReal, logHExpr_eval, logQExpr_eval]
  rw [A]
  rfl

@[simp] theorem AprimeExpr_eval (terms shift : Nat) (q zp zm : ℝ) :
    evalReal ![q, zp, zm] (AprimeExpr terms shift) = Aprime q := by
  simp only [AprimeExpr, sub, div, sq, evalReal, HprimeExpr_eval,
    HExpr_eval, logQExpr_eval, logHExpr_eval, qExpr_eval]
  rw [Aprime]
  ring

@[simp] theorem scaledDprimeExpr_eval (q zp zm : ℝ) :
    evalReal ![q, zp, zm] scaledDprimeExpr = scaledDprime q := by
  simp only [scaledDprimeExpr, eTwo, eRat, div, evalReal,
    onePlusQExpr_eval, Rat.cast_ofNat]
  rw [scaledDprime]
  ring

@[simp] theorem scaledDExpr_eval (terms : Nat) (q zp zm : ℝ) :
    evalReal ![q, zp, zm] (scaledDExpr terms) = scaledD q := by
  simp only [scaledDExpr, eTwo, eRat, div, sq, evalReal,
    onePlusQExpr_eval, Rat.cast_ofNat]
  rw [scaledD]
  congr 1
  ring

@[simp] theorem innerLogArgumentExpr_eval (q zp zm : ℝ) :
    evalReal ![q, zp, zm] innerLogArgumentExpr =
      (zp - q ^ 2) / (1 - zp) := by
  simp only [innerLogArgumentExpr, eOne, eRat, sub, div, sq, evalReal,
    qExpr_eval, zpExpr_eval, Rat.cast_one]
  ring

@[simp] theorem outerLogArgumentExpr_eval (q zp zm : ℝ) :
    evalReal ![q, zp, zm] outerLogArgumentExpr =
      (zm - q ^ 2) / (zm - 1) := by
  simp only [outerLogArgumentExpr, eOne, eRat, sub, div, sq, evalReal,
    qExpr_eval, zmExpr_eval, Rat.cast_one]
  ring

theorem innerResidualExpr_eval (terms shift : Nat) (q zp zm : ℝ) :
    evalReal ![q, zp, zm] (innerResidualExpr terms shift) =
      scaledInnerResidual (q, zp) := by
  simp only [innerResidualExpr, sub, evalReal, AExpr_eval,
    innerLogArgumentExpr_eval, zpExpr_eval, scaledDExpr_eval]
  rfl

theorem outerResidualExpr_eval (terms shift : Nat) (q zp zm : ℝ) :
    evalReal ![q, zp, zm] (outerResidualExpr terms shift) =
      scaledOuterResidual (q, zm) := by
  simp only [outerResidualExpr, sub, evalReal, AExpr_eval,
    outerLogArgumentExpr_eval, zmExpr_eval, scaledDExpr_eval]
  rfl

@[simp] theorem innerPartialZExpr_eval (terms shift : Nat) (q zp zm : ℝ) :
    evalReal ![q, zp, zm] (innerPartialZExpr terms shift) =
      scaledInnerPartialZ q zp := by
  simp only [innerPartialZExpr, eOne, eRat, sub, sq, evalReal,
    AExpr_eval, qExpr_eval, zpExpr_eval, Rat.cast_one]
  rw [scaledInnerPartialZ]
  ring

@[simp] theorem outerPartialZExpr_eval (terms shift : Nat) (q zp zm : ℝ) :
    evalReal ![q, zp, zm] (outerPartialZExpr terms shift) =
      scaledOuterPartialZ q zm := by
  simp only [outerPartialZExpr, eOne, eRat, sub, sq, evalReal,
    AExpr_eval, qExpr_eval, zmExpr_eval, Rat.cast_one]
  rw [scaledOuterPartialZ]
  ring

@[simp] theorem innerPartialQExpr_eval (terms shift : Nat) (q zp zm : ℝ) :
    evalReal ![q, zp, zm] (innerPartialQExpr terms shift) =
      scaledInnerPartialQ q zp := by
  simp only [innerPartialQExpr, eTwo, eRat, sub, div, sq, evalReal,
    AprimeExpr_eval, innerLogArgumentExpr_eval, AExpr_eval, qExpr_eval,
    zpExpr_eval, scaledDprimeExpr_eval, Rat.cast_ofNat]
  rw [scaledInnerPartialQ]
  ring

@[simp] theorem outerPartialQExpr_eval (terms shift : Nat) (q zp zm : ℝ) :
    evalReal ![q, zp, zm] (outerPartialQExpr terms shift) =
      scaledOuterPartialQ q zm := by
  simp only [outerPartialQExpr, eTwo, eRat, sub, div, sq, evalReal,
    AprimeExpr_eval, outerLogArgumentExpr_eval, AExpr_eval, qExpr_eval,
    zmExpr_eval, scaledDprimeExpr_eval, Rat.cast_ofNat]
  rw [scaledOuterPartialQ]
  ring

@[simp] theorem zpSlopeExpr_eval (terms shift : Nat) (q zp zm : ℝ) :
    evalReal ![q, zp, zm] (zpSlopeExpr terms shift) =
      scaledZPlusSlopeAt q zp := by
  simp only [zpSlopeExpr, div, evalReal, innerPartialQExpr_eval,
    innerPartialZExpr_eval]
  rw [scaledZPlusSlopeAt]
  ring

@[simp] theorem zmSlopeExpr_eval (terms shift : Nat) (q zp zm : ℝ) :
    evalReal ![q, zp, zm] (zmSlopeExpr terms shift) =
      scaledZMinusSlopeAt q zm := by
  simp only [zmSlopeExpr, div, evalReal, outerPartialQExpr_eval,
    outerPartialZExpr_eval]
  rw [scaledZMinusSlopeAt]
  ring

@[simp] theorem scaledHExpr_eval (q zp zm : ℝ) :
    evalReal ![q, zp, zm] scaledHExpr = scaledH q := by
  simp only [scaledHExpr, eTwo, eRat, div, sq, evalReal,
    onePlusQExpr_eval, Rat.cast_ofNat]
  rw [scaledH]
  ring

@[simp] theorem scaledKExpr_eval (q zp zm : ℝ) :
    evalReal ![q, zp, zm] scaledKExpr = scaledK q := by
  simp only [scaledKExpr, eTwo, eRat, div, sq, evalReal,
    qExpr_eval, onePlusQExpr_eval, Rat.cast_ofNat]
  rw [scaledK]
  ring

@[simp] theorem scaledHprimeExpr_eval (q zp zm : ℝ) :
    evalReal ![q, zp, zm] scaledHprimeExpr = scaledHprime q := by
  simp only [scaledHprimeExpr, eFour, eRat, div, cube, evalReal,
    onePlusQExpr_eval, Rat.cast_ofNat]
  rw [scaledHprime]
  ring

@[simp] theorem scaledKprimeExpr_eval (q zp zm : ℝ) :
    evalReal ![q, zp, zm] scaledKprimeExpr = scaledKprime q := by
  simp only [scaledKprimeExpr, eFour, eRat, div, cube, evalReal,
    qExpr_eval, onePlusQExpr_eval, Rat.cast_ofNat]
  rw [scaledKprime]
  ring

theorem lambdaDerivativeExpr_eval (terms shift : Nat) (q zp zm : ℝ) :
    evalReal ![q, zp, zm] (lambdaDerivativeExpr terms shift) =
      scaledLambdaDerivativeAt q zp zm := by
  simp only [lambdaDerivativeExpr, sub, div, sq, evalReal,
    scaledHprimeExpr_eval, scaledHExpr_eval, scaledKprimeExpr_eval,
    scaledKExpr_eval, zpExpr_eval, zmExpr_eval, zpSlopeExpr_eval,
    zmSlopeExpr_eval]
  rw [scaledLambdaDerivativeAt]
  ring

theorem lambdaExpr_eval (q zp zm : ℝ) :
    evalReal ![q, zp, zm] lambdaExpr = scaledLambdaExpression q zp zm := by
  simp only [lambdaExpr, sub, evalReal, scaledHExpr_eval,
    scaledKExpr_eval, zpExpr_eval, zmExpr_eval]
  rw [scaledLambdaExpression, scaledH, scaledK]
  ring

end IntervalExpr

end

end Erdos1038
