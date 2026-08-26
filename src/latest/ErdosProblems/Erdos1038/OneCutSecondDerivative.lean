import ErdosProblems.Erdos1038.IntervalExprDerivative
import ErdosProblems.Erdos1038.OneCutNewtonBox

/-!
# A checked second derivative for the one-cut length

The first derivative is already represented by `lambdaDerivativeExpr`.  Its
directional derivative along `(q, zPlus q, zMinus q)` gives a stable expression
for the second derivative, including both implicit-root slopes.
-/

open Filter Set
open scoped Topology

namespace Erdos1038

noncomputable section

open IntervalExpr

namespace NewtonBulkBox

def rootDirectionExpr (terms shift : Nat) : Fin 3 → IntervalExpr 3 :=
  ![.rat 1, zpSlopeExpr terms shift, zmSlopeExpr terms shift]

def lambdaSecondExpr (terms shift : Nat) : IntervalExpr 3 :=
  directional (rootDirectionExpr terms shift)
    (lambdaDerivativeExpr terms shift)

def EvalDefined {n : Nat} (X : Fin n → RatInterval)
    (e : IntervalExpr n) : Prop :=
  match evalInterval X e with
  | none => False
  | some _ => True

instance instDecidableEvalDefined {n : Nat} (X : Fin n → RatInterval)
    (e : IntervalExpr n) : Decidable (EvalDefined X e) := by
  unfold EvalDefined
  cases evalInterval X e <;> infer_instance

theorem evalDefined_iff_exists {n : Nat} {X : Fin n → RatInterval}
    {e : IntervalExpr n} :
    EvalDefined X e ↔ ∃ I, evalInterval X e = some I := by
  unfold EvalDefined
  cases h : evalInterval X e with
  | none => simp
  | some I => simp only [true_iff]
              exact ⟨I, rfl⟩

def SecondPositiveCertified (terms shift : Nat) (N : NewtonBulkBox) : Prop :=
  N.Certified terms shift ∧
    EvalDefined N.tightVars (lambdaDerivativeExpr terms shift) ∧
    EvalPositive N.tightVars (lambdaSecondExpr terms shift)

instance instDecidableSecondPositiveCertified (terms shift : Nat)
    (N : NewtonBulkBox) : Decidable (N.SecondPositiveCertified terms shift) := by
  unfold SecondPositiveCertified
  infer_instance

private theorem rootDirection_hasDerivAt {terms shift : Nat} {q : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) :
    ∀ i, HasDerivAt
      (fun r ↦ (![r, zPlus r, zMinus r] : Fin 3 → ℝ) i)
      (evalReal ![q, zPlus q, zMinus q]
        (rootDirectionExpr terms shift i)) q := by
  intro i
  fin_cases i
  · simpa [rootDirectionExpr, evalReal] using! hasDerivAt_id q
  · simpa [rootDirectionExpr, scaledZPlusSlopeAt, scaledZPlusSlope] using!
      hasDerivAt_zPlus hq hqs
  · simpa [rootDirectionExpr, scaledZMinusSlopeAt, scaledZMinusSlope] using!
      hasDerivAt_zMinus hq hqs

theorem hasDerivAt_lambdaDerivativeFormula_of_certified
    {terms shift : Nat} {N : NewtonBulkBox}
    (hN : N.SecondPositiveCertified terms shift)
    {q : ℝ} (hqB : N.broad.q.Contains q) :
    HasDerivAt LambdaDerivativeFormula
      (evalReal ![q, zPlus q, zMinus q]
        (lambdaSecondExpr terms shift)) q := by
  have hbase := hN.1.1.1
  have hqlo : (0 : ℝ) < (N.broad.q.lo : ℝ) := by
    exact_mod_cast hbase.2.2.2.1
  have hq : 0 < q := hqlo.trans_le hqB.1
  have hrat : (N.broad.q.hi : ℝ) < (qSoftLowerRat : ℝ) := by
    exact_mod_cast hbase.2.2.2.2.1
  have hqs : q < qSoft :=
    hqB.2.trans_lt (hrat.trans qSoftLower_lt_qSoft)
  obtain ⟨I, hEval⟩ := evalDefined_iff_exists.mp hN.2.1
  have hreg : RegularAt ![q, zPlus q, zMinus q]
      (lambdaDerivativeExpr terms shift) :=
    regularAt_of_evalInterval (N.tightVars_ordered hN.1)
      (N.tightVars_contains_roots hN.1 hqB) hEval
  have hscaled := hasDerivAt_evalReal_directional
    (rootDirectionExpr terms shift) (lambdaDerivativeExpr terms shift)
    (rootDirection_hasDerivAt hq hqs) rfl hreg
  have hevent : LambdaDerivativeFormula =ᶠ[nhds q]
      fun r ↦ evalReal ![r, zPlus r, zMinus r]
        (lambdaDerivativeExpr terms shift) := by
    filter_upwards [Ioi_mem_nhds hq, Iio_mem_nhds hqs] with r hr0 hrs
    rw [LambdaDerivativeFormula_eq_scaled hr0 hrs,
      scaledLambdaDerivativeFormula_eq_at, lambdaDerivativeExpr_eval]
  exact hscaled.congr_of_eventuallyEq hevent

theorem lambdaDerivativeFormula_deriv_pos_of_certified
    {terms shift : Nat} {N : NewtonBulkBox}
    (hN : N.SecondPositiveCertified terms shift)
    {q : ℝ} (hqB : N.broad.q.Contains q) :
    0 < deriv LambdaDerivativeFormula q := by
  have hpos := evalPositive_sound (N.tightVars_ordered hN.1)
    (N.tightVars_contains_roots hN.1 hqB) hN.2.2
  exact (hasDerivAt_lambdaDerivativeFormula_of_certified hN hqB).deriv ▸ hpos

theorem lambdaDerivativeFormula_continuousAt_of_certified
    {terms shift : Nat} {N : NewtonBulkBox}
    (hN : N.SecondPositiveCertified terms shift)
    {q : ℝ} (hqB : N.broad.q.Contains q) :
    ContinuousAt LambdaDerivativeFormula q :=
  (hasDerivAt_lambdaDerivativeFormula_of_certified hN hqB).continuousAt

def SecondPositiveCoverCertified (terms shift : Nat) (finish : Rat) :
    Rat → List NewtonBulkBox → Prop
  | _, [] => False
  | start, [N] =>
      N.broad.q.lo ≤ start ∧ N.SecondPositiveCertified terms shift ∧
        finish ≤ N.broad.q.hi
  | start, N :: N' :: Ns =>
      N.broad.q.lo ≤ start ∧ N.SecondPositiveCertified terms shift ∧
        SecondPositiveCoverCertified terms shift finish N.broad.q.hi (N' :: Ns)

instance instDecidableSecondPositiveCoverCertified (terms shift : Nat)
    (finish start : Rat) (boxes : List NewtonBulkBox) :
    Decidable (SecondPositiveCoverCertified terms shift finish start boxes) := by
  induction boxes generalizing start with
  | nil => unfold SecondPositiveCoverCertified; infer_instance
  | cons N Ns ih =>
      cases Ns with
      | nil => unfold SecondPositiveCoverCertified; infer_instance
      | cons N' Ns =>
          unfold SecondPositiveCoverCertified
          letI := ih N.broad.q.hi
          infer_instance

theorem lambdaDerivativeFormula_data_of_cover {terms shift : Nat}
    {finish start : Rat} {boxes : List NewtonBulkBox}
    (hcover : SecondPositiveCoverCertified terms shift finish start boxes)
    {q : ℝ} (hq : (start : ℝ) ≤ q ∧ q ≤ (finish : ℝ)) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt LambdaDerivativeFormula d q := by
  induction boxes generalizing start with
  | nil =>
      simp only [SecondPositiveCoverCertified] at hcover
  | cons N Ns ih =>
      cases Ns with
      | nil =>
        simp only [SecondPositiveCoverCertified] at hcover
        have hqN : N.broad.q.Contains q := by
          constructor
          · have hlo : (N.broad.q.lo : ℝ) ≤ (start : ℝ) := by
              exact_mod_cast hcover.1
            exact hlo.trans hq.1
          · exact hq.2.trans (by exact_mod_cast hcover.2.2)
        let d := evalReal ![q, zPlus q, zMinus q]
          (lambdaSecondExpr terms shift)
        refine ⟨d, ?_, hasDerivAt_lambdaDerivativeFormula_of_certified
          hcover.2.1 hqN⟩
        exact evalPositive_sound (N.tightVars_ordered hcover.2.1.1)
          (N.tightVars_contains_roots hcover.2.1.1 hqN) hcover.2.1.2.2
      | cons N' Ns =>
        simp only [SecondPositiveCoverCertified] at hcover
        by_cases hqhi : q ≤ (N.broad.q.hi : ℝ)
        · have hqN : N.broad.q.Contains q := by
            constructor
            · have hlo : (N.broad.q.lo : ℝ) ≤ (start : ℝ) := by
                exact_mod_cast hcover.1
              exact hlo.trans hq.1
            · exact hqhi
          let d := evalReal ![q, zPlus q, zMinus q]
            (lambdaSecondExpr terms shift)
          refine ⟨d, ?_, hasDerivAt_lambdaDerivativeFormula_of_certified
            hcover.2.1 hqN⟩
          exact evalPositive_sound (N.tightVars_ordered hcover.2.1.1)
            (N.tightVars_contains_roots hcover.2.1.1 hqN) hcover.2.1.2.2
        · exact ih hcover.2.2 ⟨(lt_of_not_ge hqhi).le, hq.2⟩

theorem lambdaDerivativeFormula_deriv_pos_of_cover {terms shift : Nat}
    {finish start : Rat} {boxes : List NewtonBulkBox}
    (hcover : SecondPositiveCoverCertified terms shift finish start boxes)
    {q : ℝ} (hq : (start : ℝ) ≤ q ∧ q ≤ (finish : ℝ)) :
    0 < deriv LambdaDerivativeFormula q := by
  obtain ⟨d, hd, hderiv⟩ := lambdaDerivativeFormula_data_of_cover hcover hq
  rwa [hderiv.deriv]

theorem lambdaDerivativeFormula_continuousAt_of_cover {terms shift : Nat}
    {finish start : Rat} {boxes : List NewtonBulkBox}
    (hcover : SecondPositiveCoverCertified terms shift finish start boxes)
    {q : ℝ} (hq : (start : ℝ) ≤ q ∧ q ≤ (finish : ℝ)) :
    ContinuousAt LambdaDerivativeFormula q := by
  obtain ⟨d, hd, hderiv⟩ := lambdaDerivativeFormula_data_of_cover hcover hq
  exact hderiv.continuousAt

end NewtonBulkBox

end

end Erdos1038
