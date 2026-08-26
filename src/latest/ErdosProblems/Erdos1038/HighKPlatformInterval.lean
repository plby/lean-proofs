import ErdosProblems.Erdos1038.HighKScalarCalibration
import ErdosProblems.Erdos1038.TrigInterval

/-!
# Exact interval expressions for the high-ratio platform certificate

This is a separate expression language for the high-`k` computation.  In
addition to rational arithmetic and logarithms it has square-root, sine, and
cosine nodes.  Trigonometric nodes are evaluated by `TrigInterval`, hence a
successful evaluation is reduced entirely to exact rational arithmetic.
-/

set_option warningAsError false

namespace Erdos1038

noncomputable section

open RatInterval

/-- Arithmetic/transcendental expressions needed by the platform verifier. -/
inductive HighKIntervalExpr (n : Nat) where
  | rat (r : Rat)
  | var (i : Fin n)
  | add (a b : HighKIntervalExpr n)
  | neg (a : HighKIntervalExpr n)
  | mul (a b : HighKIntervalExpr n)
  | inv (a : HighKIntervalExpr n)
  | log (terms : Nat) (a : HighKIntervalExpr n)
  | sqrt (steps : Nat) (a : HighKIntervalExpr n)
  | sin (doubles : Nat) (a : HighKIntervalExpr n)
  | cos (doubles : Nat) (a : HighKIntervalExpr n)
deriving DecidableEq, Repr

namespace HighKIntervalExpr

def sub {n : Nat} (a b : HighKIntervalExpr n) : HighKIntervalExpr n :=
  .add a (.neg b)

def div {n : Nat} (a b : HighKIntervalExpr n) : HighKIntervalExpr n :=
  .mul a (.inv b)

def sq {n : Nat} (a : HighKIntervalExpr n) : HighKIntervalExpr n :=
  .mul a a

def cube {n : Nat} (a : HighKIntervalExpr n) : HighKIntervalExpr n :=
  .mul (.mul a a) a

def evalReal {n : Nat} (x : Fin n → ℝ) : HighKIntervalExpr n → ℝ
  | .rat r => (r : ℝ)
  | .var i => x i
  | .add a b => evalReal x a + evalReal x b
  | .neg a => -evalReal x a
  | .mul a b => evalReal x a * evalReal x b
  | .inv a => (evalReal x a)⁻¹
  | .log _ a => Real.log (evalReal x a)
  | .sqrt _ a => Real.sqrt (evalReal x a)
  | .sin _ a => Real.sin (evalReal x a)
  | .cos _ a => Real.cos (evalReal x a)

/-- A sine enclosure can fail only if the scaled seed interval is not
contained in `[-1,1]`. -/
def evalSin? (doubles : Nat) (I : RatInterval) : Option RatInterval :=
  if (scaleDownPowTwo doubles I).maxAbs ≤ 1 then
    some (sinCosBox doubles I).sin
  else none

/-- Cosine companion to `evalSin?`. -/
def evalCos? (doubles : Nat) (I : RatInterval) : Option RatInterval :=
  if (scaleDownPowTwo doubles I).maxAbs ≤ 1 then
    some (sinCosBox doubles I).cos
  else none

def evalInterval {n : Nat} (X : Fin n → RatInterval) :
    HighKIntervalExpr n → Option RatInterval
  | .rat r => some (point r)
  | .var i => some (X i)
  | .add a b => do
      let A ← evalInterval X a
      let B ← evalInterval X b
      pure (A.add B)
  | .neg a => do
      let A ← evalInterval X a
      pure A.neg
  | .mul a b => do
      let A ← evalInterval X a
      let B ← evalInterval X b
      pure (A.mul B)
  | .inv a => do
      let A ← evalInterval X a
      A.inv?
  | .log terms a => do
      let A ← evalInterval X a
      A.log? terms
  | .sqrt steps a => do
      let A ← evalInterval X a
      A.sqrt? steps
  | .sin doubles a => do
      let A ← evalInterval X a
      evalSin? doubles A
  | .cos doubles a => do
      let A ← evalInterval X a
      evalCos? doubles A

theorem evalSin_sound {doubles : Nat} {I J : RatInterval} {x : ℝ}
    (hI : I.Ordered) (hx : I.Contains x)
    (heval : evalSin? doubles I = some J) :
    J.Ordered ∧ J.Contains (Real.sin x) := by
  by_cases hunit : (scaleDownPowTwo doubles I).maxAbs ≤ 1
  · rw [evalSin?, if_pos hunit] at heval
    cases heval
    exact ⟨(sinCosBox_ordered doubles hI).1,
      (sinCosBox_contains doubles hx hunit).1⟩
  · simp [evalSin?, hunit] at heval

theorem evalCos_sound {doubles : Nat} {I J : RatInterval} {x : ℝ}
    (hI : I.Ordered) (hx : I.Contains x)
    (heval : evalCos? doubles I = some J) :
    J.Ordered ∧ J.Contains (Real.cos x) := by
  by_cases hunit : (scaleDownPowTwo doubles I).maxAbs ≤ 1
  · rw [evalCos?, if_pos hunit] at heval
    cases heval
    exact ⟨(sinCosBox_ordered doubles hI).2,
      (sinCosBox_contains doubles hx hunit).2⟩
  · simp [evalCos?, hunit] at heval

/-- Semantic soundness of every successful high-`k` interval expression. -/
theorem evalInterval_sound {n : Nat} {X : Fin n → RatInterval}
    {x : Fin n → ℝ}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i)) :
    ∀ (e : HighKIntervalExpr n) (I : RatInterval),
      evalInterval X e = some I →
        I.Ordered ∧ I.Contains (evalReal x e) := by
  intro e
  induction e with
  | rat r =>
      intro I hI
      simp only [evalInterval, Option.some.injEq] at hI
      subst I
      exact ⟨point_ordered r, point_contains r⟩
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
              have hEq : A.add B = I := by
                simpa [evalInterval, ha, hb] using! hI
              symm at hEq
              subst I
              exact ⟨add_ordered (iha A ha).1 (ihb B hb).1,
                add_contains (iha A ha).2 (ihb B hb).2⟩
  | neg a ih =>
      intro I hI
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at hI
      | some A =>
          have hEq : A.neg = I := by simpa [evalInterval, ha] using! hI
          symm at hEq
          subst I
          exact ⟨neg_ordered (ih A ha).1, neg_contains (ih A ha).2⟩
  | mul a b iha ihb =>
      intro I hI
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at hI
      | some A =>
          cases hb : evalInterval X b with
          | none => simp [evalInterval, ha, hb] at hI
          | some B =>
              have hEq : A.mul B = I := by
                simpa [evalInterval, ha, hb] using! hI
              symm at hEq
              subst I
              exact ⟨mul_ordered (iha A ha).1 (ihb B hb).1,
                mul_contains (iha A ha).2 (ihb B hb).2⟩
  | inv a ih =>
      intro I hI
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at hI
      | some A =>
          have hA := ih A ha
          have hI' : A.inv? = some I := by
            simpa [evalInterval, ha] using! hI
          exact ⟨inv_ordered hA.1 hI', inv_contains hA.2 hI'⟩
  | log terms a ih =>
      intro I hI
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at hI
      | some A =>
          have hA := ih A ha
          have hI' : A.log? terms = some I := by
            simpa [evalInterval, ha] using! hI
          exact ⟨log_ordered hA.1 hI', log_contains hA.2 hI'⟩
  | sqrt steps a ih =>
      intro I hI
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at hI
      | some A =>
          have hA := ih A ha
          have hI' : A.sqrt? steps = some I := by
            simpa [evalInterval, ha] using! hI
          exact ⟨sqrt_ordered hA.1 hI', sqrt_contains hA.2 hI'⟩
  | sin doubles a ih =>
      intro I hI
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at hI
      | some A =>
          have hA := ih A ha
          have hI' : evalSin? doubles A = some I := by
            simpa [evalInterval, ha] using! hI
          exact evalSin_sound hA.1 hA.2 hI'
  | cos doubles a ih =>
      intro I hI
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at hI
      | some A =>
          have hA := ih A ha
          have hI' : evalCos? doubles A = some I := by
            simpa [evalInterval, ha] using! hI
          exact evalCos_sound hA.1 hA.2 hI'

def EvalPositive {n : Nat} (X : Fin n → RatInterval)
    (e : HighKIntervalExpr n) : Prop :=
  ∃ I, evalInterval X e = some I ∧ 0 < I.lo

def EvalNegative {n : Nat} (X : Fin n → RatInterval)
    (e : HighKIntervalExpr n) : Prop :=
  ∃ I, evalInterval X e = some I ∧ I.hi < 0

theorem evalPositive_sound {n : Nat} {X : Fin n → RatInterval}
    {x : Fin n → ℝ} {e : HighKIntervalExpr n}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i))
    (hpositive : EvalPositive X e) : 0 < evalReal x e := by
  obtain ⟨I, hI, hpos⟩ := hpositive
  have hsound := (evalInterval_sound hordered hcontains e I hI).2.1
  have hcast : 0 < (I.lo : ℝ) := by exact_mod_cast hpos
  exact hcast.trans_le hsound

theorem evalNegative_sound {n : Nat} {X : Fin n → RatInterval}
    {x : Fin n → ℝ} {e : HighKIntervalExpr n}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i))
    (hnegative : EvalNegative X e) : evalReal x e < 0 := by
  obtain ⟨I, hI, hneg⟩ := hnegative
  have hsound := (evalInterval_sound hordered hcontains e I hI).2.2
  have hcast : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
  exact hsound.trans_lt hcast

end HighKIntervalExpr

end

end Erdos1038
