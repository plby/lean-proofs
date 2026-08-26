import ErdosProblems.Erdos1038.OneCutSoftExpr

/-!
# Exact rational boxes in the regularized soft chart
-/

namespace Erdos1038

noncomputable section

open IntervalExpr

def EvalLowerBound {n : Nat} (X : Fin n → RatInterval)
    (e : IntervalExpr n) (target : RatInterval) : Prop :=
  match evalInterval X e with
  | none => False
  | some I => target.lo ≤ I.lo

def EvalUpperBound {n : Nat} (X : Fin n → RatInterval)
    (e : IntervalExpr n) (target : RatInterval) : Prop :=
  match evalInterval X e with
  | none => False
  | some I => I.hi ≤ target.hi

instance instDecidableEvalLowerBound {n : Nat} (X : Fin n → RatInterval)
    (e : IntervalExpr n) (target : RatInterval) :
    Decidable (EvalLowerBound X e target) := by
  unfold EvalLowerBound
  split <;> infer_instance

instance instDecidableEvalUpperBound {n : Nat} (X : Fin n → RatInterval)
    (e : IntervalExpr n) (target : RatInterval) :
    Decidable (EvalUpperBound X e target) := by
  unfold EvalUpperBound
  split <;> infer_instance

def oneVars (I : RatInterval) : Fin 1 → RatInterval := ![I]
def oneExpr : IntervalExpr 1 := .var 0

def SoftTEnclosed (terms : Nat) (I target : RatInterval) : Prop :=
  EvalLowerBound (oneVars I) (softTLowerExpr terms oneExpr) target ∧
    EvalUpperBound (oneVars I) (softTUpperExpr terms oneExpr) target

def SoftTPrimeEnclosed (I target : RatInterval) : Prop :=
  EvalLowerBound (oneVars I) (softTPrimeLowerExpr oneExpr) target ∧
    EvalUpperBound (oneVars I) (softTPrimeUpperExpr oneExpr) target

instance instDecidableSoftTEnclosed (terms : Nat) (I target : RatInterval) :
    Decidable (SoftTEnclosed terms I target) := by
  unfold SoftTEnclosed
  infer_instance

instance instDecidableSoftTPrimeEnclosed (I target : RatInterval) :
    Decidable (SoftTPrimeEnclosed I target) := by
  unfold SoftTPrimeEnclosed
  infer_instance

theorem evalLowerBound_sound {n : Nat} {X : Fin n → RatInterval}
    {x : Fin n → ℝ} {e : IntervalExpr n} {target : RatInterval}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i))
    (hcert : EvalLowerBound X e target) :
    (target.lo : ℝ) ≤ evalReal x e := by
  cases h : evalInterval X e with
  | none => simp [EvalLowerBound, h] at hcert
  | some I =>
      have hle : target.lo ≤ I.lo := by
        simpa [EvalLowerBound, h] using! hcert
      have hs := (evalInterval_sound hordered hcontains e I h).2.1
      exact (by exact_mod_cast hle : (target.lo : ℝ) ≤ (I.lo : ℝ)).trans hs

theorem evalUpperBound_sound {n : Nat} {X : Fin n → RatInterval}
    {x : Fin n → ℝ} {e : IntervalExpr n} {target : RatInterval}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i))
    (hcert : EvalUpperBound X e target) :
    evalReal x e ≤ (target.hi : ℝ) := by
  cases h : evalInterval X e with
  | none => simp [EvalUpperBound, h] at hcert
  | some I =>
      have hle : I.hi ≤ target.hi := by
        simpa [EvalUpperBound, h] using! hcert
      have hs := (evalInterval_sound hordered hcontains e I h).2.2
      exact hs.trans (by exact_mod_cast hle : (I.hi : ℝ) ≤ (target.hi : ℝ))

theorem oneVars_ordered {I : RatInterval} (hI : I.Ordered) :
    ∀ i, (oneVars I i).Ordered := by
  intro i
  fin_cases i
  exact hI

theorem oneVars_contains {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    ∀ i, (oneVars I i).Contains (![x] i) := by
  intro i
  fin_cases i
  exact hx

@[simp] theorem oneExpr_eval (x : ℝ) : evalReal ![x] oneExpr = x := by
  simp [oneExpr, evalReal]

theorem softT_mem_of_enclosed {terms : Nat} {I target : RatInterval}
    (hI : I.Ordered) {x : ℝ} (hxI : I.Contains x)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hcert : SoftTEnclosed terms I target) (hterms : 0 < terms) :
    target.Contains (softT x) := by
  have hlo := evalLowerBound_sound (oneVars_ordered hI)
    (oneVars_contains hxI) hcert.1
  have hhi := evalUpperBound_sound (oneVars_ordered hI)
    (oneVars_contains hxI) hcert.2
  rw [softTLowerExpr_eval, oneExpr_eval] at hlo
  rw [softTUpperExpr_eval, oneExpr_eval] at hhi
  have hb := softT_bounds hterms hx0 hx1
  exact ⟨hlo.trans hb.1, hb.2.trans hhi⟩

theorem softTPrime_mem_of_enclosed {I target : RatInterval}
    (hI : I.Ordered) {x : ℝ} (hxI : I.Contains x)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hcert : SoftTPrimeEnclosed I target) :
    target.Contains (softTPrime x) := by
  have hlo := evalLowerBound_sound (oneVars_ordered hI)
    (oneVars_contains hxI) hcert.1
  have hhi := evalUpperBound_sound (oneVars_ordered hI)
    (oneVars_contains hxI) hcert.2
  rw [softTPrimeLowerExpr_eval, oneExpr_eval] at hlo
  rw [softTPrimeUpperExpr_eval, oneExpr_eval] at hhi
  have hb := softTPrime_bounds hx0 hx1
  exact ⟨hlo.trans hb.1, hb.2.trans hhi⟩

namespace IntervalExpr

def softDividedInnerLowerExpr (terms shift : Nat) : IntervalExpr 7 :=
  .sub
    (.mul (.mul (softAExpr terms shift) softKappaExpr)
      (softTLowerExpr terms softWExpr))
    (softTUpperExpr terms softSExpr)

def softDividedInnerUpperExpr (terms shift : Nat) : IntervalExpr 7 :=
  .sub
    (.mul (.mul (softAExpr terms shift) softKappaExpr)
      (softTUpperExpr terms softWExpr))
    (softTLowerExpr terms softSExpr)

@[simp] theorem softWExpr_eval (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw] softWExpr = softW q s := by
  simp only [softWExpr, sq, evalReal, softKappaExpr_eval, softSExpr_eval]
  rw [softW]
  ring_nf

@[simp] theorem softDividedInnerLowerExpr_eval (terms shift : Nat)
    (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw]
        (softDividedInnerLowerExpr terms shift) =
      A q * softKappa q * softTLower terms (softW q s) -
        softTUpper terms s := by
  simp [softDividedInnerLowerExpr, sub, evalReal]
  ring_nf

@[simp] theorem softDividedInnerUpperExpr_eval (terms shift : Nat)
    (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw]
        (softDividedInnerUpperExpr terms shift) =
      A q * softKappa q * softTUpper terms (softW q s) -
        softTLower terms s := by
  simp [softDividedInnerUpperExpr, sub, evalReal]
  ring_nf

end IntervalExpr

structure SoftBox where
  shift : Nat
  q : RatInterval
  s : RatInterval
  zm : RatInterval
  w : RatInterval
  ts : RatInterval
  tps : RatInterval
  tw : RatInterval
  tpw : RatInterval
deriving DecidableEq, Repr

namespace SoftBox

def vars (B : SoftBox) : Fin 7 → RatInterval :=
  ![B.q, B.s, B.zm, B.ts, B.tps, B.tw, B.tpw]

def innerLowerVars (B : SoftBox) : Fin 7 → RatInterval :=
  ![B.q, RatInterval.point B.s.lo, B.zm, B.ts, B.tps, B.tw, B.tpw]

def innerUpperVars (B : SoftBox) : Fin 7 → RatInterval :=
  ![B.q, RatInterval.point B.s.hi, B.zm, B.ts, B.tps, B.tw, B.tpw]

def outerLowerVars (B : SoftBox) : Fin 7 → RatInterval :=
  ![B.q, B.s, RatInterval.point B.zm.lo, B.ts, B.tps, B.tw, B.tpw]

def outerUpperVars (B : SoftBox) : Fin 7 → RatInterval :=
  ![B.q, B.s, RatInterval.point B.zm.hi, B.ts, B.tps, B.tw, B.tpw]

def GeometryCertified (B : SoftBox) : Prop :=
  B.q.Ordered ∧ B.s.Ordered ∧ B.zm.Ordered ∧ B.w.Ordered ∧
    B.ts.Ordered ∧ B.tps.Ordered ∧ B.tw.Ordered ∧ B.tpw.Ordered ∧
    0 < B.q.lo ∧ B.q.hi < 1 ∧
    0 ≤ B.s.lo ∧ 0 < B.s.hi ∧ B.s.hi < 1 ∧
    0 ≤ B.w.lo ∧ B.w.hi < 1 ∧ 1 < B.zm.lo

def FunctionCertified (terms : Nat) (B : SoftBox) : Prop :=
  OneCutTailCertificate.EvalInside B.vars softWExpr B.w ∧
    SoftTEnclosed terms B.s B.ts ∧
    SoftTPrimeEnclosed B.s B.tps ∧
    SoftTEnclosed terms B.w B.tw ∧
    SoftTPrimeEnclosed B.w B.tpw

def RootsCertified (terms : Nat) (B : SoftBox) : Prop :=
  (B.s.lo = 0 ∨
      EvalNegative B.innerLowerVars
        (softDividedInnerUpperExpr terms B.shift)) ∧
    EvalPositive B.innerUpperVars
      (softDividedInnerLowerExpr terms B.shift) ∧
    EvalPositive B.vars
      (softDividedInnerPartialSExpr terms B.shift) ∧
    EvalPositive B.outerLowerVars
      (softOuterResidualExpr terms B.shift) ∧
    EvalNegative B.outerUpperVars
      (softOuterResidualExpr terms B.shift)

def BaseCertified (terms : Nat) (B : SoftBox) : Prop :=
  GeometryCertified B ∧ FunctionCertified terms B ∧ RootsCertified terms B

def PositiveCertified (terms : Nat) (B : SoftBox) : Prop :=
  BaseCertified terms B ∧
    EvalPositive B.vars (softLambdaDerivativeExpr terms B.shift)

instance instDecidableGeometryCertified (B : SoftBox) :
    Decidable (GeometryCertified B) := by
  unfold GeometryCertified RatInterval.Ordered
  infer_instance

instance instDecidableFunctionCertified (terms : Nat) (B : SoftBox) :
    Decidable (FunctionCertified terms B) := by
  unfold FunctionCertified
  infer_instance

instance instDecidableRootsCertified (terms : Nat) (B : SoftBox) :
    Decidable (RootsCertified terms B) := by
  unfold RootsCertified
  infer_instance

instance instDecidableBaseCertified (terms : Nat) (B : SoftBox) :
    Decidable (BaseCertified terms B) := by
  unfold BaseCertified
  infer_instance

instance instDecidablePositiveCertified (terms : Nat) (B : SoftBox) :
    Decidable (PositiveCertified terms B) := by
  unfold PositiveCertified
  infer_instance

end SoftBox

end

end Erdos1038
