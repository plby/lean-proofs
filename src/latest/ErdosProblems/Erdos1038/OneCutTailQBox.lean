import ErdosProblems.Erdos1038.OneCutTailSign
import ErdosProblems.Erdos1038.OneCutNewtonBox

/-!
# Stable q-indexed boxes using the nonsingular tail chart

Each box stores enclosures for `r = -1 / log q` and
`q_r = q * (log q)^2`.  Those two enclosures are themselves checked by the
generic interval evaluator, so the executable certificate remains entirely
exact-rational while allowing a different logarithm shift in every box.
-/

open Set

namespace Erdos1038

noncomputable section

open IntervalExpr

namespace OneCutTailCertificate

def EvalInside {n : Nat} (X : Fin n → RatInterval)
    (e : IntervalExpr n) (target : RatInterval) : Prop :=
  match evalInterval X e with
  | none => False
  | some I => target.lo ≤ I.lo ∧ I.hi ≤ target.hi

instance instDecidableEvalInside {n : Nat} (X : Fin n → RatInterval)
    (e : IntervalExpr n) (target : RatInterval) :
    Decidable (EvalInside X e target) := by
  unfold EvalInside
  split <;> infer_instance

theorem evalInside_sound {n : Nat} {X : Fin n → RatInterval}
    {x : Fin n → ℝ} {e : IntervalExpr n} {target : RatInterval}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i))
    (hcert : EvalInside X e target) :
    target.Contains (evalReal x e) := by
  cases h : evalInterval X e with
  | none => simp [EvalInside, h] at hcert
  | some I =>
      have hinside : target.lo ≤ I.lo ∧ I.hi ≤ target.hi := by
        simpa [EvalInside, h] using! hcert
      have hsound := (evalInterval_sound hordered hcontains e I h).2
      have hlo : (target.lo : ℝ) ≤ (I.lo : ℝ) := by
        exact_mod_cast hinside.1
      have hhi : (I.hi : ℝ) ≤ (target.hi : ℝ) := by
        exact_mod_cast hinside.2
      exact ⟨hlo.trans hsound.1, hsound.2.trans hhi⟩

def tailQOnlyExpr : IntervalExpr 1 := .var 0

def tailRFromQExpr (terms shift : Nat) : IntervalExpr 1 :=
  .neg (.inv (.log2Shift terms shift tailQOnlyExpr))

def tailQrFromQExpr (terms shift : Nat) : IntervalExpr 1 :=
  .mul tailQOnlyExpr
    (.sq (.log2Shift terms shift tailQOnlyExpr))

@[simp] theorem tailQOnlyExpr_eval (q : ℝ) :
    evalReal ![q] tailQOnlyExpr = q := by
  simp [tailQOnlyExpr, evalReal]

@[simp] theorem tailRFromQExpr_eval (terms shift : Nat) (q : ℝ) :
    evalReal ![q] (tailRFromQExpr terms shift) = tailRReal q := by
  simp only [tailRFromQExpr, evalReal, tailQOnlyExpr_eval]
  rw [tailRReal]
  ring

@[simp] theorem tailQrFromQExpr_eval (terms shift : Nat) (q : ℝ) :
    evalReal ![q] (tailQrFromQExpr terms shift) = tailQrReal q := by
  simp only [tailQrFromQExpr, IntervalExpr.sq, evalReal,
    tailQOnlyExpr_eval]
  rw [tailQrReal]
  ring

structure TailQBox where
  shift : Nat
  q : RatInterval
  r : RatInterval
  qr : RatInterval
  zp : RatInterval
  zm : RatInterval
deriving DecidableEq, Repr

namespace TailQBox

def qVars (B : TailQBox) : Fin 1 → RatInterval := ![B.q]

def vars (B : TailQBox) : Fin 5 → RatInterval :=
  ![B.r, B.q, B.qr, B.zp, B.zm]

def innerLowerVars (B : TailQBox) : Fin 5 → RatInterval :=
  ![B.r, B.q, B.qr, RatInterval.point B.zp.lo, B.zm]

def innerUpperVars (B : TailQBox) : Fin 5 → RatInterval :=
  ![B.r, B.q, B.qr, RatInterval.point B.zp.hi, B.zm]

def outerLowerVars (B : TailQBox) : Fin 5 → RatInterval :=
  ![B.r, B.q, B.qr, B.zp, RatInterval.point B.zm.lo]

def outerUpperVars (B : TailQBox) : Fin 5 → RatInterval :=
  ![B.r, B.q, B.qr, B.zp, RatInterval.point B.zm.hi]

def BaseCertified (terms : Nat) (B : TailQBox) : Prop :=
  B.q.Ordered ∧ B.r.Ordered ∧ B.qr.Ordered ∧
  B.zp.Ordered ∧ B.zm.Ordered ∧
  0 < B.q.lo ∧ B.q.hi < qSoftLowerRat ∧
  B.q.hi < B.zp.lo ∧ B.zp.lo < B.zp.hi ∧ B.zp.hi < 1 ∧
  1 < B.zm.lo ∧ B.zm.lo < B.zm.hi ∧
  EvalInside B.qVars (tailRFromQExpr terms B.shift) B.r ∧
  EvalInside B.qVars (tailQrFromQExpr terms B.shift) B.qr ∧
  EvalNegative B.innerLowerVars (tailInnerGExpr terms) ∧
  EvalPositive B.innerUpperVars (tailInnerGExpr terms) ∧
  EvalPositive B.outerLowerVars (tailOuterGExpr terms) ∧
  EvalNegative B.outerUpperVars (tailOuterGExpr terms)

def NegativeCertified (terms : Nat) (B : TailQBox) : Prop :=
  B.BaseCertified terms ∧ EvalNegative B.vars (tailLambdaRExpr terms)

def PositiveCertified (terms : Nat) (B : TailQBox) : Prop :=
  B.BaseCertified terms ∧ EvalPositive B.vars (tailLambdaRExpr terms)

instance instDecidableBaseCertified (terms : Nat) (B : TailQBox) :
    Decidable (B.BaseCertified terms) := by
  unfold BaseCertified RatInterval.Ordered
  infer_instance

instance instDecidableNegativeCertified (terms : Nat) (B : TailQBox) :
    Decidable (B.NegativeCertified terms) := by
  unfold NegativeCertified
  infer_instance

instance instDecidablePositiveCertified (terms : Nat) (B : TailQBox) :
    Decidable (B.PositiveCertified terms) := by
  unfold PositiveCertified
  infer_instance

private theorem base_parts {terms : Nat} {B : TailQBox}
    (hB : B.BaseCertified terms) :
    B.q.Ordered ∧ B.r.Ordered ∧ B.qr.Ordered ∧
      B.zp.Ordered ∧ B.zm.Ordered ∧
      0 < B.q.lo ∧ B.q.hi < qSoftLowerRat ∧
      B.q.hi < B.zp.lo ∧ B.zp.lo < B.zp.hi ∧ B.zp.hi < 1 ∧
      1 < B.zm.lo ∧ B.zm.lo < B.zm.hi ∧
      EvalInside B.qVars (tailRFromQExpr terms B.shift) B.r ∧
      EvalInside B.qVars (tailQrFromQExpr terms B.shift) B.qr ∧
      EvalNegative B.innerLowerVars (tailInnerGExpr terms) ∧
      EvalPositive B.innerUpperVars (tailInnerGExpr terms) ∧
      EvalPositive B.outerLowerVars (tailOuterGExpr terms) ∧
      EvalNegative B.outerUpperVars (tailOuterGExpr terms) := hB

theorem qVars_ordered {terms : Nat} {B : TailQBox}
    (hB : B.BaseCertified terms) : ∀ i, (B.qVars i).Ordered := by
  intro i
  fin_cases i
  exact hB.1

theorem qVars_contains {B : TailQBox} {q : ℝ}
    (hqB : B.q.Contains q) :
    ∀ i, (B.qVars i).Contains (![q] i) := by
  intro i
  fin_cases i
  exact hqB

theorem derived_contains {terms : Nat} {B : TailQBox}
    (hB : B.BaseCertified terms) {q : ℝ} (hqB : B.q.Contains q) :
    B.r.Contains (tailRReal q) ∧ B.qr.Contains (tailQrReal q) := by
  have hr := evalInside_sound (B.qVars_ordered hB)
    (B.qVars_contains hqB) (base_parts hB).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hqr := evalInside_sound (B.qVars_ordered hB)
    (B.qVars_contains hqB) (base_parts hB).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [tailRFromQExpr_eval] at hr
  rw [tailQrFromQExpr_eval] at hqr
  exact ⟨hr, hqr⟩

theorem vars_ordered {terms : Nat} {B : TailQBox}
    (hB : B.BaseCertified terms) : ∀ i, (B.vars i).Ordered := by
  intro i
  fin_cases i
  · exact hB.2.1
  · exact hB.1
  · exact hB.2.2.1
  · exact hB.2.2.2.1
  · exact hB.2.2.2.2.1

private theorem endpointVars_ordered {terms : Nat} {B : TailQBox}
    (hB : B.BaseCertified terms) :
    (∀ i, (B.innerLowerVars i).Ordered) ∧
      (∀ i, (B.innerUpperVars i).Ordered) ∧
      (∀ i, (B.outerLowerVars i).Ordered) ∧
      (∀ i, (B.outerUpperVars i).Ordered) := by
  constructor
  · intro i
    fin_cases i
    · exact hB.2.1
    · exact hB.1
    · exact hB.2.2.1
    · exact RatInterval.point_ordered _
    · exact hB.2.2.2.2.1
  constructor
  · intro i
    fin_cases i
    · exact hB.2.1
    · exact hB.1
    · exact hB.2.2.1
    · exact RatInterval.point_ordered _
    · exact hB.2.2.2.2.1
  constructor
  · intro i
    fin_cases i
    · exact hB.2.1
    · exact hB.1
    · exact hB.2.2.1
    · exact hB.2.2.2.1
    · exact RatInterval.point_ordered _
  · intro i
    fin_cases i
    · exact hB.2.1
    · exact hB.1
    · exact hB.2.2.1
    · exact hB.2.2.2.1
    · exact RatInterval.point_ordered _

private theorem innerLowerVars_contains {terms : Nat} {B : TailQBox}
    (hB : B.BaseCertified terms) {q : ℝ} (hqB : B.q.Contains q) :
    ∀ i, (B.innerLowerVars i).Contains
      (![tailRReal q, q, tailQrReal q, (B.zp.lo : ℝ),
        (B.zm.lo : ℝ)] i) := by
  have hd := B.derived_contains hB hqB
  intro i
  fin_cases i
  · exact hd.1
  · exact hqB
  · exact hd.2
  · simpa [innerLowerVars] using! RatInterval.point_contains B.zp.lo
  · have hz : B.zm.Contains (B.zm.lo : ℝ) :=
      ⟨le_rfl, by
        exact_mod_cast (hB.2.2.2.2.2.2.2.2.2.2.2.1).le⟩
    simpa [innerLowerVars] using! hz

private theorem innerUpperVars_contains {terms : Nat} {B : TailQBox}
    (hB : B.BaseCertified terms) {q : ℝ} (hqB : B.q.Contains q) :
    ∀ i, (B.innerUpperVars i).Contains
      (![tailRReal q, q, tailQrReal q, (B.zp.hi : ℝ),
        (B.zm.lo : ℝ)] i) := by
  have hd := B.derived_contains hB hqB
  intro i
  fin_cases i
  · exact hd.1
  · exact hqB
  · exact hd.2
  · simpa [innerUpperVars] using! RatInterval.point_contains B.zp.hi
  · have hz : B.zm.Contains (B.zm.lo : ℝ) :=
      ⟨le_rfl, by
        exact_mod_cast (hB.2.2.2.2.2.2.2.2.2.2.2.1).le⟩
    simpa [innerUpperVars] using! hz

private theorem outerLowerVars_contains {terms : Nat} {B : TailQBox}
    (hB : B.BaseCertified terms) {q : ℝ} (hqB : B.q.Contains q) :
    ∀ i, (B.outerLowerVars i).Contains
      (![tailRReal q, q, tailQrReal q, (B.zp.lo : ℝ),
        (B.zm.lo : ℝ)] i) := by
  have hd := B.derived_contains hB hqB
  intro i
  fin_cases i
  · exact hd.1
  · exact hqB
  · exact hd.2
  · have hz : B.zp.Contains (B.zp.lo : ℝ) :=
      ⟨le_rfl, by exact_mod_cast (hB.2.2.2.2.2.2.2.2.1).le⟩
    simpa [outerLowerVars] using! hz
  · simpa [outerLowerVars] using! RatInterval.point_contains B.zm.lo

private theorem outerUpperVars_contains {terms : Nat} {B : TailQBox}
    (hB : B.BaseCertified terms) {q : ℝ} (hqB : B.q.Contains q) :
    ∀ i, (B.outerUpperVars i).Contains
      (![tailRReal q, q, tailQrReal q, (B.zp.lo : ℝ),
        (B.zm.hi : ℝ)] i) := by
  have hd := B.derived_contains hB hqB
  intro i
  fin_cases i
  · exact hd.1
  · exact hqB
  · exact hd.2
  · have hz : B.zp.Contains (B.zp.lo : ℝ) :=
      ⟨le_rfl, by exact_mod_cast (hB.2.2.2.2.2.2.2.2.1).le⟩
    simpa [outerUpperVars] using! hz
  · simpa [outerUpperVars] using! RatInterval.point_contains B.zm.hi

theorem roots_mem {terms : Nat} {B : TailQBox}
    (hB : B.BaseCertified terms) {q : ℝ} (hqB : B.q.Contains q) :
    zPlus q ∈ Ioo (B.zp.lo : ℝ) (B.zp.hi : ℝ) ∧
      zMinus q ∈ Ioo (B.zm.lo : ℝ) (B.zm.hi : ℝ) := by
  have hqlo : (0 : ℝ) < (B.q.lo : ℝ) := by
    exact_mod_cast hB.2.2.2.2.2.1
  have hq : 0 < q := hqlo.trans_le hqB.1
  have hqsoftRat : (B.q.hi : ℝ) < (qSoftLowerRat : ℝ) := by
    exact_mod_cast hB.2.2.2.2.2.2.1
  have hqs : q < qSoft := hqB.2.trans_lt
    (hqsoftRat.trans qSoftLower_lt_qSoft)
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have horders := endpointVars_ordered hB
  have hpLoTail := evalNegative_sound horders.1
    (innerLowerVars_contains hB hqB)
    (base_parts hB).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpHiTail := evalPositive_sound horders.2.1
    (innerUpperVars_contains hB hqB)
    (base_parts hB).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmLoTail := evalPositive_sound horders.2.2.1
    (outerLowerVars_contains hB hqB)
    (base_parts hB).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmHiTail := evalNegative_sound horders.2.2.2
    (outerUpperVars_contains hB hqB)
    (base_parts hB).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [tailInnerGExpr_eval,
    tailInnerGReal_eq_scaledInnerResidual hq hq1] at hpLoTail hpHiTail
  rw [tailOuterGExpr_eval,
    tailOuterGReal_eq_scaledOuterResidual hq hq1] at hmLoTail hmHiTail
  have hqzp : q < (B.zp.lo : ℝ) := hqB.2.trans_lt (by
    exact_mod_cast hB.2.2.2.2.2.2.2.1)
  have hzp : (B.zp.lo : ℝ) < (B.zp.hi : ℝ) := by
    exact_mod_cast hB.2.2.2.2.2.2.2.2.1
  have hzp1 : (B.zp.hi : ℝ) < 1 := by
    exact_mod_cast hB.2.2.2.2.2.2.2.2.2.1
  have h1zm : (1 : ℝ) < (B.zm.lo : ℝ) := by
    exact_mod_cast hB.2.2.2.2.2.2.2.2.2.2.1
  have hzm : (B.zm.lo : ℝ) < (B.zm.hi : ℝ) := by
    exact_mod_cast hB.2.2.2.2.2.2.2.2.2.2.2.1
  exact scaledRoots_mem_Ioo_of_endpoint_signs hq hqs hqzp hzp hzp1
    h1zm hzm hpLoTail hpHiTail hmLoTail hmHiTail

theorem vars_contains_roots {terms : Nat} {B : TailQBox}
    (hB : B.BaseCertified terms) {q : ℝ} (hqB : B.q.Contains q) :
    ∀ i, (B.vars i).Contains
      (![tailRReal q, q, tailQrReal q, zPlus q, zMinus q] i) := by
  have hd := B.derived_contains hB hqB
  have hr := B.roots_mem hB hqB
  intro i
  fin_cases i
  · exact hd.1
  · exact hqB
  · exact hd.2
  · exact ⟨hr.1.1.le, hr.1.2.le⟩
  · exact ⟨hr.2.1.le, hr.2.2.le⟩

theorem lambdaDerivativeFormula_neg_of_certified {terms : Nat}
    {B : TailQBox} (hB : B.NegativeCertified terms) {q : ℝ}
    (hqB : B.q.Contains q) : LambdaDerivativeFormula q < 0 := by
  have hqlo : (0 : ℝ) < (B.q.lo : ℝ) := by
    exact_mod_cast hB.1.2.2.2.2.2.1
  have hq : 0 < q := hqlo.trans_le hqB.1
  have hqsoftRat : (B.q.hi : ℝ) < (qSoftLowerRat : ℝ) := by
    exact_mod_cast hB.1.2.2.2.2.2.2.1
  have hqs : q < qSoft := hqB.2.trans_lt
    (hqsoftRat.trans qSoftLower_lt_qSoft)
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have htail := evalNegative_sound (B.vars_ordered hB.1)
    (B.vars_contains_roots hB.1 hqB) hB.2
  rw [tailLambdaRExpr_eval,
    tailLambdaRReal_eq_scaled_mul hq hq1] at htail
  have hspeed : 0 < tailQrReal q := by
    rw [tailQrReal]
    exact mul_pos hq (sq_pos_of_ne_zero (log_q_ne_zero hq hq1))
  have hscaled : scaledLambdaDerivativeAt q (zPlus q) (zMinus q) < 0 := by
    by_contra hn
    have := mul_nonneg (le_of_not_gt hn) hspeed.le
    linarith
  rw [LambdaDerivativeFormula_eq_scaled hq hqs,
    scaledLambdaDerivativeFormula_eq_at]
  exact hscaled

theorem lambdaDerivativeFormula_pos_of_certified {terms : Nat}
    {B : TailQBox} (hB : B.PositiveCertified terms) {q : ℝ}
    (hqB : B.q.Contains q) : 0 < LambdaDerivativeFormula q := by
  have hqlo : (0 : ℝ) < (B.q.lo : ℝ) := by
    exact_mod_cast hB.1.2.2.2.2.2.1
  have hq : 0 < q := hqlo.trans_le hqB.1
  have hqsoftRat : (B.q.hi : ℝ) < (qSoftLowerRat : ℝ) := by
    exact_mod_cast hB.1.2.2.2.2.2.2.1
  have hqs : q < qSoft := hqB.2.trans_lt
    (hqsoftRat.trans qSoftLower_lt_qSoft)
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have htail := evalPositive_sound (B.vars_ordered hB.1)
    (B.vars_contains_roots hB.1 hqB) hB.2
  rw [tailLambdaRExpr_eval,
    tailLambdaRReal_eq_scaled_mul hq hq1] at htail
  have hspeed : 0 < tailQrReal q := by
    rw [tailQrReal]
    exact mul_pos hq (sq_pos_of_ne_zero (log_q_ne_zero hq hq1))
  have hscaled : 0 < scaledLambdaDerivativeAt q (zPlus q) (zMinus q) := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hspeed.le
    linarith
  rw [LambdaDerivativeFormula_eq_scaled hq hqs,
    scaledLambdaDerivativeFormula_eq_at]
  exact hscaled

end TailQBox

end OneCutTailCertificate

end

end Erdos1038
