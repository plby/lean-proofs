import ErdosProblems.Erdos1038.OneCutIntervalExpr

/-!
# Kernel-checked bulk boxes for the one-cut certificate

A `BulkBox` contains a rational parameter interval and rational enclosures of
the two scaled roots.  `NegativeCertified` and `PositiveCertified` are fully
decidable propositions: they evaluate four residual signs and the stable
length derivative using exact rational interval arithmetic.
-/

open Set

namespace Erdos1038

noncomputable section

open IntervalExpr

def EvalNegative {n : Nat} (X : Fin n → RatInterval)
    (e : IntervalExpr n) : Prop :=
  match evalInterval X e with
  | none => False
  | some I => I.hi < 0

def EvalPositive {n : Nat} (X : Fin n → RatInterval)
    (e : IntervalExpr n) : Prop :=
  match evalInterval X e with
  | none => False
  | some I => 0 < I.lo

instance instDecidableEvalNegative {n : Nat} (X : Fin n → RatInterval)
    (e : IntervalExpr n) : Decidable (EvalNegative X e) := by
  unfold EvalNegative
  cases evalInterval X e with
  | none => exact isFalse id
  | some I => exact inferInstance

instance instDecidableEvalPositive {n : Nat} (X : Fin n → RatInterval)
    (e : IntervalExpr n) : Decidable (EvalPositive X e) := by
  unfold EvalPositive
  cases evalInterval X e with
  | none => exact isFalse id
  | some I => exact inferInstance

theorem evalNegative_sound {n : Nat} {X : Fin n → RatInterval}
    {x : Fin n → ℝ} {e : IntervalExpr n}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i))
    (hcert : EvalNegative X e) :
    evalReal x e < 0 := by
  cases h : evalInterval X e with
  | none => simp [EvalNegative, h] at hcert
  | some I =>
      have hhi : I.hi < 0 := by simpa [EvalNegative, h] using! hcert
      exact evalInterval_lt_zero hordered hcontains h hhi

theorem evalPositive_sound {n : Nat} {X : Fin n → RatInterval}
    {x : Fin n → ℝ} {e : IntervalExpr n}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i))
    (hcert : EvalPositive X e) :
    0 < evalReal x e := by
  cases h : evalInterval X e with
  | none => simp [EvalPositive, h] at hcert
  | some I =>
      have hlo : 0 < I.lo := by simpa [EvalPositive, h] using! hcert
      exact evalInterval_pos hordered hcontains h hlo

structure BulkBox where
  q : RatInterval
  zp : RatInterval
  zm : RatInterval
deriving DecidableEq, Repr

namespace BulkBox

def vars (B : BulkBox) : Fin 3 → RatInterval := ![B.q, B.zp, B.zm]

def innerLowerVars (B : BulkBox) : Fin 3 → RatInterval :=
  ![B.q, RatInterval.point B.zp.lo, RatInterval.point 2]

def innerUpperVars (B : BulkBox) : Fin 3 → RatInterval :=
  ![B.q, RatInterval.point B.zp.hi, RatInterval.point 2]

def outerLowerVars (B : BulkBox) : Fin 3 → RatInterval :=
  ![B.q, RatInterval.point 1, RatInterval.point B.zm.lo]

def outerUpperVars (B : BulkBox) : Fin 3 → RatInterval :=
  ![B.q, RatInterval.point 1, RatInterval.point B.zm.hi]

def BaseCertified (terms shift : Nat) (B : BulkBox) : Prop :=
  B.q.Ordered ∧ B.zp.Ordered ∧ B.zm.Ordered ∧
  0 < B.q.lo ∧ B.q.hi < qSoftLowerRat ∧
  B.q.hi < B.zp.lo ∧ B.zp.lo < B.zp.hi ∧ B.zp.hi < 1 ∧
  1 < B.zm.lo ∧ B.zm.lo < B.zm.hi ∧
  EvalNegative B.innerLowerVars (innerResidualExpr terms shift) ∧
  EvalPositive B.innerUpperVars (innerResidualExpr terms shift) ∧
  EvalPositive B.outerLowerVars (outerResidualExpr terms shift) ∧
  EvalNegative B.outerUpperVars (outerResidualExpr terms shift)

def NegativeCertified (terms shift : Nat) (B : BulkBox) : Prop :=
  B.BaseCertified terms shift ∧
    EvalNegative B.vars (lambdaDerivativeExpr terms shift)

def PositiveCertified (terms shift : Nat) (B : BulkBox) : Prop :=
  B.BaseCertified terms shift ∧
    EvalPositive B.vars (lambdaDerivativeExpr terms shift)

instance instDecidableBaseCertified (terms shift : Nat) (B : BulkBox) :
    Decidable (B.BaseCertified terms shift) := by
  unfold BaseCertified RatInterval.Ordered
  infer_instance

instance instDecidableNegativeCertified (terms shift : Nat) (B : BulkBox) :
    Decidable (B.NegativeCertified terms shift) := by
  unfold NegativeCertified
  infer_instance

instance instDecidablePositiveCertified (terms shift : Nat) (B : BulkBox) :
    Decidable (B.PositiveCertified terms shift) := by
  unfold PositiveCertified
  infer_instance

theorem vars_ordered {terms shift : Nat} {B : BulkBox}
    (hB : B.BaseCertified terms shift) :
    ∀ i, (B.vars i).Ordered := by
  intro i
  fin_cases i
  · exact hB.1
  · exact hB.2.1
  · exact hB.2.2.1

private theorem endpointVars_ordered
    {B : BulkBox} (hq : B.q.Ordered) :
    (∀ i, (B.innerLowerVars i).Ordered) ∧
      (∀ i, (B.innerUpperVars i).Ordered) ∧
      (∀ i, (B.outerLowerVars i).Ordered) ∧
      (∀ i, (B.outerUpperVars i).Ordered) := by
  constructor
  · intro i
    fin_cases i
    · exact hq
    · exact RatInterval.point_ordered _
    · exact RatInterval.point_ordered _
  constructor
  · intro i
    fin_cases i
    · exact hq
    · exact RatInterval.point_ordered _
    · exact RatInterval.point_ordered _
  constructor
  · intro i
    fin_cases i
    · exact hq
    · exact RatInterval.point_ordered _
    · exact RatInterval.point_ordered _
  · intro i
    fin_cases i
    · exact hq
    · exact RatInterval.point_ordered _
    · exact RatInterval.point_ordered _

private theorem innerLowerVars_contains {B : BulkBox} {q : ℝ}
    (hq : B.q.Contains q) :
    ∀ i, (B.innerLowerVars i).Contains (![q, (B.zp.lo : ℝ), 2] i) := by
  intro i
  fin_cases i
  · exact hq
  · simpa [innerLowerVars] using! RatInterval.point_contains B.zp.lo
  · simpa [innerLowerVars] using! RatInterval.point_contains (2 : Rat)

private theorem innerUpperVars_contains {B : BulkBox} {q : ℝ}
    (hq : B.q.Contains q) :
    ∀ i, (B.innerUpperVars i).Contains (![q, (B.zp.hi : ℝ), 2] i) := by
  intro i
  fin_cases i
  · exact hq
  · simpa [innerUpperVars] using! RatInterval.point_contains B.zp.hi
  · simpa [innerUpperVars] using! RatInterval.point_contains (2 : Rat)

private theorem outerLowerVars_contains {B : BulkBox} {q : ℝ}
    (hq : B.q.Contains q) :
    ∀ i, (B.outerLowerVars i).Contains (![q, 1, (B.zm.lo : ℝ)] i) := by
  intro i
  fin_cases i
  · exact hq
  · simpa [outerLowerVars] using! RatInterval.point_contains (1 : Rat)
  · simpa [outerLowerVars] using! RatInterval.point_contains B.zm.lo

private theorem outerUpperVars_contains {B : BulkBox} {q : ℝ}
    (hq : B.q.Contains q) :
    ∀ i, (B.outerUpperVars i).Contains (![q, 1, (B.zm.hi : ℝ)] i) := by
  intro i
  fin_cases i
  · exact hq
  · simpa [outerUpperVars] using! RatInterval.point_contains (1 : Rat)
  · simpa [outerUpperVars] using! RatInterval.point_contains B.zm.hi

theorem roots_mem {terms shift : Nat} {B : BulkBox}
    (hB : B.BaseCertified terms shift)
    {q : ℝ} (hqB : B.q.Contains q) :
    zPlus q ∈ Ioo (B.zp.lo : ℝ) (B.zp.hi : ℝ) ∧
      zMinus q ∈ Ioo (B.zm.lo : ℝ) (B.zm.hi : ℝ) := by
  have hqlo : (0 : ℝ) < (B.q.lo : ℝ) := by exact_mod_cast hB.2.2.2.1
  have hq : 0 < q := hqlo.trans_le hqB.1
  have hqhiSoft : (B.q.hi : ℝ) < qSoft := by
    have hrat : (B.q.hi : ℝ) < (qSoftLowerRat : ℝ) := by
      exact_mod_cast hB.2.2.2.2.1
    exact hrat.trans qSoftLower_lt_qSoft
  have hqs : q < qSoft := hqB.2.trans_lt hqhiSoft
  have horders := endpointVars_ordered hB.1
  have hpLo : scaledInnerResidual (q, (B.zp.lo : ℝ)) < 0 := by
    have h := evalNegative_sound horders.1 (innerLowerVars_contains hqB)
      hB.2.2.2.2.2.2.2.2.2.2.1
    rwa [innerResidualExpr_eval] at h
  have hpHi : 0 < scaledInnerResidual (q, (B.zp.hi : ℝ)) := by
    have h := evalPositive_sound horders.2.1 (innerUpperVars_contains hqB)
      hB.2.2.2.2.2.2.2.2.2.2.2.1
    rwa [innerResidualExpr_eval] at h
  have hmLo : 0 < scaledOuterResidual (q, (B.zm.lo : ℝ)) := by
    have h := evalPositive_sound horders.2.2.1 (outerLowerVars_contains hqB)
      hB.2.2.2.2.2.2.2.2.2.2.2.2.1
    rwa [outerResidualExpr_eval] at h
  have hmHi : scaledOuterResidual (q, (B.zm.hi : ℝ)) < 0 := by
    have h := evalNegative_sound horders.2.2.2 (outerUpperVars_contains hqB)
      hB.2.2.2.2.2.2.2.2.2.2.2.2.2
    rwa [outerResidualExpr_eval] at h
  have hqzp : q < (B.zp.lo : ℝ) := by
    have hcast : (B.q.hi : ℝ) < (B.zp.lo : ℝ) := by
      exact_mod_cast hB.2.2.2.2.2.1
    exact hqB.2.trans_lt hcast
  have hzp : (B.zp.lo : ℝ) < (B.zp.hi : ℝ) := by
    exact_mod_cast hB.2.2.2.2.2.2.1
  have hzp1 : (B.zp.hi : ℝ) < 1 := by
    exact_mod_cast hB.2.2.2.2.2.2.2.1
  have h1zm : (1 : ℝ) < (B.zm.lo : ℝ) := by
    exact_mod_cast hB.2.2.2.2.2.2.2.2.1
  have hzm : (B.zm.lo : ℝ) < (B.zm.hi : ℝ) := by
    exact_mod_cast hB.2.2.2.2.2.2.2.2.2.1
  exact scaledRoots_mem_Ioo_of_endpoint_signs hq hqs hqzp hzp hzp1
    h1zm hzm hpLo hpHi hmLo hmHi

theorem vars_contains_roots {terms shift : Nat} {B : BulkBox}
    (hB : B.BaseCertified terms shift) {q : ℝ} (hqB : B.q.Contains q) :
    ∀ i, (B.vars i).Contains (![q, zPlus q, zMinus q] i) := by
  have hr := B.roots_mem hB hqB
  intro i
  fin_cases i
  · exact hqB
  · exact ⟨hr.1.1.le, hr.1.2.le⟩
  · exact ⟨hr.2.1.le, hr.2.2.le⟩

theorem lambdaDerivativeFormula_neg_of_certified {terms shift : Nat} {B : BulkBox}
    (hB : B.NegativeCertified terms shift) {q : ℝ}
    (hqB : B.q.Contains q) :
    LambdaDerivativeFormula q < 0 := by
  have hqlo : (0 : ℝ) < (B.q.lo : ℝ) := by exact_mod_cast hB.1.2.2.2.1
  have hq : 0 < q := hqlo.trans_le hqB.1
  have hrat : (B.q.hi : ℝ) < (qSoftLowerRat : ℝ) := by
    exact_mod_cast hB.1.2.2.2.2.1
  have hqs : q < qSoft := hqB.2.trans_lt (hrat.trans qSoftLower_lt_qSoft)
  have h := evalNegative_sound (B.vars_ordered hB.1)
    (B.vars_contains_roots hB.1 hqB) hB.2
  rw [lambdaDerivativeExpr_eval] at h
  rw [LambdaDerivativeFormula_eq_scaled hq hqs,
    scaledLambdaDerivativeFormula_eq_at]
  exact h

theorem lambdaDerivativeFormula_pos_of_certified {terms shift : Nat} {B : BulkBox}
    (hB : B.PositiveCertified terms shift) {q : ℝ}
    (hqB : B.q.Contains q) :
    0 < LambdaDerivativeFormula q := by
  have hqlo : (0 : ℝ) < (B.q.lo : ℝ) := by exact_mod_cast hB.1.2.2.2.1
  have hq : 0 < q := hqlo.trans_le hqB.1
  have hrat : (B.q.hi : ℝ) < (qSoftLowerRat : ℝ) := by
    exact_mod_cast hB.1.2.2.2.2.1
  have hqs : q < qSoft := hqB.2.trans_lt (hrat.trans qSoftLower_lt_qSoft)
  have h := evalPositive_sound (B.vars_ordered hB.1)
    (B.vars_contains_roots hB.1 hqB) hB.2
  rw [lambdaDerivativeExpr_eval] at h
  rw [LambdaDerivativeFormula_eq_scaled hq hqs,
    scaledLambdaDerivativeFormula_eq_at]
  exact h

end BulkBox

end

end Erdos1038
