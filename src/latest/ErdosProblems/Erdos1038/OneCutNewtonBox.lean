import ErdosProblems.Erdos1038.IntervalNewton
import ErdosProblems.Erdos1038.OneCutBulkBox

/-!
# Parametric Newton contraction for one-cut bulk boxes

The broad root intervals in a `BulkBox` are obtained from endpoint signs.
This file verifies the interval-Newton contraction used by the numerical
certificate and yields much tighter root intervals for derivative and value
evaluation.
-/

open Set

namespace Erdos1038

noncomputable section

open IntervalExpr

structure RootNewtonData where
  center : Rat
  tight : RatInterval
deriving DecidableEq, Repr

structure NewtonBulkBox where
  broad : BulkBox
  plus : RootNewtonData
  minus : RootNewtonData
deriving DecidableEq, Repr

namespace NewtonBulkBox

def innerCenterVars (N : NewtonBulkBox) : Fin 3 → RatInterval :=
  ![N.broad.q, RatInterval.point N.plus.center, RatInterval.point 2]

def outerCenterVars (N : NewtonBulkBox) : Fin 3 → RatInterval :=
  ![N.broad.q, RatInterval.point 1, RatInterval.point N.minus.center]

def innerNewtonImage? (terms shift : Nat) (N : NewtonBulkBox) :
    Option RatInterval := do
  let R ← evalInterval N.innerCenterVars (innerResidualExpr terms shift)
  let D ← evalInterval N.broad.vars (innerPartialZExpr terms shift)
  let Q ← R.div? D
  pure (RatInterval.sub (RatInterval.point N.plus.center) Q)

def outerNewtonImage? (terms shift : Nat) (N : NewtonBulkBox) :
    Option RatInterval := do
  let R ← evalInterval N.outerCenterVars (outerResidualExpr terms shift)
  let D ← evalInterval N.broad.vars (outerPartialZExpr terms shift)
  let Q ← R.div? D
  pure (RatInterval.sub (RatInterval.point N.minus.center) Q)

def IntervalContained (I J : RatInterval) : Prop :=
  J.lo ≤ I.lo ∧ I.hi ≤ J.hi

def InnerNewtonCertified (terms shift : Nat) (N : NewtonBulkBox) : Prop :=
  N.broad.BaseCertified terms shift ∧ N.plus.tight.Ordered ∧
    N.broad.zp.lo ≤ N.plus.center ∧ N.plus.center ≤ N.broad.zp.hi ∧
    match N.innerNewtonImage? terms shift with
    | none => False
    | some I => IntervalContained I N.plus.tight

def OuterNewtonCertified (terms shift : Nat) (N : NewtonBulkBox) : Prop :=
  N.broad.BaseCertified terms shift ∧ N.minus.tight.Ordered ∧
    N.broad.zm.lo ≤ N.minus.center ∧ N.minus.center ≤ N.broad.zm.hi ∧
    match N.outerNewtonImage? terms shift with
    | none => False
    | some I => IntervalContained I N.minus.tight

def Certified (terms shift : Nat) (N : NewtonBulkBox) : Prop :=
  N.InnerNewtonCertified terms shift ∧ N.OuterNewtonCertified terms shift

private instance instDecidableIntervalContained (I J : RatInterval) :
    Decidable (IntervalContained I J) := by
  unfold IntervalContained
  infer_instance

instance instDecidableInnerNewtonCertified (terms shift : Nat)
    (N : NewtonBulkBox) : Decidable (N.InnerNewtonCertified terms shift) := by
  unfold InnerNewtonCertified
  letI := BulkBox.instDecidableBaseCertified terms shift N.broad
  letI : Decidable N.plus.tight.Ordered := by
    unfold RatInterval.Ordered
    infer_instance
  cases N.innerNewtonImage? terms shift <;> infer_instance

instance instDecidableOuterNewtonCertified (terms shift : Nat)
    (N : NewtonBulkBox) : Decidable (N.OuterNewtonCertified terms shift) := by
  unfold OuterNewtonCertified
  letI := BulkBox.instDecidableBaseCertified terms shift N.broad
  letI : Decidable N.minus.tight.Ordered := by
    unfold RatInterval.Ordered
    infer_instance
  cases N.outerNewtonImage? terms shift <;> infer_instance

instance instDecidableCertified (terms shift : Nat) (N : NewtonBulkBox) :
    Decidable (N.Certified terms shift) := by
  unfold Certified
  infer_instance

private theorem innerCenterVars_ordered {N : NewtonBulkBox}
    (hq : N.broad.q.Ordered) :
    ∀ i, (N.innerCenterVars i).Ordered := by
  intro i
  fin_cases i
  · exact hq
  · exact RatInterval.point_ordered _
  · exact RatInterval.point_ordered _

private theorem outerCenterVars_ordered {N : NewtonBulkBox}
    (hq : N.broad.q.Ordered) :
    ∀ i, (N.outerCenterVars i).Ordered := by
  intro i
  fin_cases i
  · exact hq
  · exact RatInterval.point_ordered _
  · exact RatInterval.point_ordered _

private theorem innerCenterVars_contains {N : NewtonBulkBox} {q : ℝ}
    (hq : N.broad.q.Contains q) :
    ∀ i, (N.innerCenterVars i).Contains
      (![q, (N.plus.center : ℝ), 2] i) := by
  intro i
  fin_cases i
  · exact hq
  · simpa [innerCenterVars] using! RatInterval.point_contains N.plus.center
  · simpa [innerCenterVars] using! RatInterval.point_contains (2 : Rat)

private theorem outerCenterVars_contains {N : NewtonBulkBox} {q : ℝ}
    (hq : N.broad.q.Contains q) :
    ∀ i, (N.outerCenterVars i).Contains
      (![q, 1, (N.minus.center : ℝ)] i) := by
  intro i
  fin_cases i
  · exact hq
  · simpa [outerCenterVars] using! RatInterval.point_contains (1 : Rat)
  · simpa [outerCenterVars] using! RatInterval.point_contains N.minus.center

private theorem intervalContained_contains {I J : RatInterval} {x : ℝ}
    (hIJ : IntervalContained I J) (hx : I.Contains x) : J.Contains x := by
  have hlo : (J.lo : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hIJ.1
  have hhi : (I.hi : ℝ) ≤ (J.hi : ℝ) := by exact_mod_cast hIJ.2
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

theorem innerNewtonImage_contains_zPlus {terms shift : Nat}
    {N : NewtonBulkBox} (hbase : N.broad.BaseCertified terms shift)
    {q : ℝ} (hqB : N.broad.q.Contains q)
    {I : RatInterval} (himage : N.innerNewtonImage? terms shift = some I)
    (hcenterLo : N.broad.zp.lo ≤ N.plus.center)
    (hcenterHi : N.plus.center ≤ N.broad.zp.hi) :
    I.Contains (zPlus q) := by
  cases hR : evalInterval N.innerCenterVars (innerResidualExpr terms shift) with
  | none => simp [innerNewtonImage?, hR] at himage
  | some R =>
      cases hD : evalInterval N.broad.vars (innerPartialZExpr terms shift) with
      | none => simp [innerNewtonImage?, hR, hD] at himage
      | some D =>
          cases hQ : R.div? D with
          | none => simp [innerNewtonImage?, hR, hD, hQ] at himage
          | some Q =>
              have hEq : RatInterval.sub (RatInterval.point N.plus.center) Q = I := by
                simpa [innerNewtonImage?, hR, hD, hQ] using! himage
              symm at hEq
              subst I
              have hroots := N.broad.roots_mem hbase hqB
              have hqlo : (0 : ℝ) < (N.broad.q.lo : ℝ) := by
                exact_mod_cast hbase.2.2.2.1
              have hq : 0 < q := hqlo.trans_le hqB.1
              have hrat : (N.broad.q.hi : ℝ) < (qSoftLowerRat : ℝ) := by
                exact_mod_cast hbase.2.2.2.2.1
              have hqs : q < qSoft :=
                hqB.2.trans_lt (hrat.trans qSoftLower_lt_qSoft)
              have hRcontains : R.Contains
                  (scaledInnerResidual (q, (N.plus.center : ℝ))) := by
                have hs := (evalInterval_sound
                  (innerCenterVars_ordered hbase.1)
                  (innerCenterVars_contains hqB) _ _ hR).2
                rwa [innerResidualExpr_eval] at hs
              have hDcontains : ∀ y ∈ Icc (N.broad.zp.lo : ℝ)
                  (N.broad.zp.hi : ℝ),
                  D.Contains (scaledInnerPartialZ q y) := by
                intro y hy
                have hvars : ∀ i, (N.broad.vars i).Contains
                    (![q, y, zMinus q] i) := by
                  intro i
                  fin_cases i
                  · exact hqB
                  · exact hy
                  · exact ⟨hroots.2.1.le, hroots.2.2.le⟩
                have hs := (evalInterval_sound
                  (N.broad.vars_ordered hbase) hvars _ _ hD).2
                rwa [innerPartialZExpr_eval] at hs
              have hcenter : (N.plus.center : ℝ) ∈
                  Icc (N.broad.zp.lo : ℝ) (N.broad.zp.hi : ℝ) := by
                constructor
                · exact_mod_cast hcenterLo
                · exact_mod_cast hcenterHi
              have hrootClosed : zPlus q ∈
                  Icc (N.broad.zp.lo : ℝ) (N.broad.zp.hi : ℝ) :=
                ⟨hroots.1.1.le, hroots.1.2.le⟩
              have hroot : scaledInnerResidual (q, zPlus q) = 0 := by
                rw [scaledInnerResidual_eq_scaledResidual (zPlus_lt_one hq hqs),
                  scaledResidual_zPlus hq hqs]
              have hderiv : ∀ y ∈ Icc (N.broad.zp.lo : ℝ)
                  (N.broad.zp.hi : ℝ),
                  HasDerivAt (fun z ↦ scaledInnerResidual (q, z))
                    (scaledInnerPartialZ q y) y := by
                intro y hy
                have hqzp : q < (N.broad.zp.lo : ℝ) := by
                  have hh : (N.broad.q.hi : ℝ) <
                      (N.broad.zp.lo : ℝ) := by
                    exact_mod_cast hbase.2.2.2.2.2.1
                  exact hqB.2.trans_lt hh
                have hy0 : 0 < y := hq.trans (hqzp.trans_le hy.1)
                have hq2y : q ^ 2 < y := by
                  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
                  have hq2q : q ^ 2 < q := by
                    nlinarith [mul_pos hq (sub_pos.mpr hq1)]
                  exact hq2q.trans (hqzp.trans_le hy.1)
                have hy1 : y < 1 := hy.2.trans_lt (by
                  exact_mod_cast hbase.2.2.2.2.2.2.2.1)
                exact hasDerivAt_scaledInnerResidual_right hy0 hq2y hy1
              exact intervalNewton_contains_root hrootClosed hcenter hroot
                hderiv hRcontains hDcontains hQ

theorem outerNewtonImage_contains_zMinus {terms shift : Nat}
    {N : NewtonBulkBox} (hbase : N.broad.BaseCertified terms shift)
    {q : ℝ} (hqB : N.broad.q.Contains q)
    {I : RatInterval} (himage : N.outerNewtonImage? terms shift = some I)
    (hcenterLo : N.broad.zm.lo ≤ N.minus.center)
    (hcenterHi : N.minus.center ≤ N.broad.zm.hi) :
    I.Contains (zMinus q) := by
  cases hR : evalInterval N.outerCenterVars (outerResidualExpr terms shift) with
  | none => simp [outerNewtonImage?, hR] at himage
  | some R =>
      cases hD : evalInterval N.broad.vars (outerPartialZExpr terms shift) with
      | none => simp [outerNewtonImage?, hR, hD] at himage
      | some D =>
          cases hQ : R.div? D with
          | none => simp [outerNewtonImage?, hR, hD, hQ] at himage
          | some Q =>
              have hEq : RatInterval.sub (RatInterval.point N.minus.center) Q = I := by
                simpa [outerNewtonImage?, hR, hD, hQ] using! himage
              symm at hEq
              subst I
              have hroots := N.broad.roots_mem hbase hqB
              have hqlo : (0 : ℝ) < (N.broad.q.lo : ℝ) := by
                exact_mod_cast hbase.2.2.2.1
              have hq : 0 < q := hqlo.trans_le hqB.1
              have hrat : (N.broad.q.hi : ℝ) < (qSoftLowerRat : ℝ) := by
                exact_mod_cast hbase.2.2.2.2.1
              have hqs : q < qSoft :=
                hqB.2.trans_lt (hrat.trans qSoftLower_lt_qSoft)
              have hRcontains : R.Contains
                  (scaledOuterResidual (q, (N.minus.center : ℝ))) := by
                have hs := (evalInterval_sound
                  (outerCenterVars_ordered hbase.1)
                  (outerCenterVars_contains hqB) _ _ hR).2
                rwa [outerResidualExpr_eval] at hs
              have hDcontains : ∀ y ∈ Icc (N.broad.zm.lo : ℝ)
                  (N.broad.zm.hi : ℝ),
                  D.Contains (scaledOuterPartialZ q y) := by
                intro y hy
                have hvars : ∀ i, (N.broad.vars i).Contains
                    (![q, zPlus q, y] i) := by
                  intro i
                  fin_cases i
                  · exact hqB
                  · exact ⟨hroots.1.1.le, hroots.1.2.le⟩
                  · exact hy
                have hs := (evalInterval_sound
                  (N.broad.vars_ordered hbase) hvars _ _ hD).2
                rwa [outerPartialZExpr_eval] at hs
              have hcenter : (N.minus.center : ℝ) ∈
                  Icc (N.broad.zm.lo : ℝ) (N.broad.zm.hi : ℝ) := by
                constructor
                · exact_mod_cast hcenterLo
                · exact_mod_cast hcenterHi
              have hrootClosed : zMinus q ∈
                  Icc (N.broad.zm.lo : ℝ) (N.broad.zm.hi : ℝ) :=
                ⟨hroots.2.1.le, hroots.2.2.le⟩
              have hroot : scaledOuterResidual (q, zMinus q) = 0 := by
                rw [scaledOuterResidual_eq_scaledResidual
                    (one_lt_zMinus hq hqs.le),
                  scaledResidual_zMinus hq hqs.le]
              have hderiv : ∀ y ∈ Icc (N.broad.zm.lo : ℝ)
                  (N.broad.zm.hi : ℝ),
                  HasDerivAt (fun z ↦ scaledOuterResidual (q, z))
                    (scaledOuterPartialZ q y) y := by
                intro y hy
                have hOneLo : (1 : ℝ) < (N.broad.zm.lo : ℝ) := by
                  exact_mod_cast hbase.2.2.2.2.2.2.2.2.1
                have hy1 : 1 < y := hOneLo.trans_le hy.1
                have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
                have hq2y : q ^ 2 < y := by
                  have hq2q : q ^ 2 < q := by
                    nlinarith [mul_pos hq (sub_pos.mpr hq1)]
                  exact hq2q.trans (hq1.trans hy1)
                exact hasDerivAt_scaledOuterResidual_right hq2y hy1
              exact intervalNewton_contains_root hrootClosed hcenter hroot
                hderiv hRcontains hDcontains hQ

theorem tight_roots_mem {terms shift : Nat} {N : NewtonBulkBox}
    (hN : N.Certified terms shift) {q : ℝ}
    (hqB : N.broad.q.Contains q) :
    N.plus.tight.Contains (zPlus q) ∧
      N.minus.tight.Contains (zMinus q) := by
  have hpMatch := hN.1.2.2.2.2
  cases hp : N.innerNewtonImage? terms shift with
  | none => simp [hp] at hpMatch
  | some IP =>
      have hpContain : IntervalContained IP N.plus.tight := by
        simpa [hp] using! hpMatch
      have hpRoot := innerNewtonImage_contains_zPlus hN.1.1 hqB hp
        hN.1.2.2.1 hN.1.2.2.2.1
      have hpTight := intervalContained_contains hpContain hpRoot
      have hmMatch := hN.2.2.2.2.2
      cases hm : N.outerNewtonImage? terms shift with
      | none => simp [hm] at hmMatch
      | some IM =>
          have hmContain : IntervalContained IM N.minus.tight := by
            simpa [hm] using! hmMatch
          have hmRoot := outerNewtonImage_contains_zMinus hN.2.1 hqB hm
            hN.2.2.2.1 hN.2.2.2.2.1
          exact ⟨hpTight, intervalContained_contains hmContain hmRoot⟩

def tightVars (N : NewtonBulkBox) : Fin 3 → RatInterval :=
  ![N.broad.q, N.plus.tight, N.minus.tight]

theorem tightVars_ordered {terms shift : Nat} {N : NewtonBulkBox}
    (hN : N.Certified terms shift) :
    ∀ i, (N.tightVars i).Ordered := by
  intro i
  fin_cases i
  · exact hN.1.1.1
  · exact hN.1.2.1
  · exact hN.2.2.1

theorem tightVars_contains_roots {terms shift : Nat} {N : NewtonBulkBox}
    (hN : N.Certified terms shift) {q : ℝ}
    (hqB : N.broad.q.Contains q) :
    ∀ i, (N.tightVars i).Contains (![q, zPlus q, zMinus q] i) := by
  have hroots := N.tight_roots_mem hN hqB
  intro i
  fin_cases i
  · exact hqB
  · exact hroots.1
  · exact hroots.2

def TightNegativeCertified (terms shift : Nat) (N : NewtonBulkBox) : Prop :=
  N.Certified terms shift ∧
    EvalNegative N.tightVars (lambdaDerivativeExpr terms shift)

def TightPositiveCertified (terms shift : Nat) (N : NewtonBulkBox) : Prop :=
  N.Certified terms shift ∧
    EvalPositive N.tightVars (lambdaDerivativeExpr terms shift)

instance instDecidableTightNegativeCertified (terms shift : Nat)
    (N : NewtonBulkBox) : Decidable (N.TightNegativeCertified terms shift) := by
  unfold TightNegativeCertified
  infer_instance

instance instDecidableTightPositiveCertified (terms shift : Nat)
    (N : NewtonBulkBox) : Decidable (N.TightPositiveCertified terms shift) := by
  unfold TightPositiveCertified
  infer_instance

theorem lambdaDerivativeFormula_neg_of_tight_certified {terms shift : Nat}
    {N : NewtonBulkBox} (hN : N.TightNegativeCertified terms shift)
    {q : ℝ} (hqB : N.broad.q.Contains q) :
    LambdaDerivativeFormula q < 0 := by
  have hbase := hN.1.1.1
  have hqlo : (0 : ℝ) < (N.broad.q.lo : ℝ) := by
    exact_mod_cast hbase.2.2.2.1
  have hq : 0 < q := hqlo.trans_le hqB.1
  have hrat : (N.broad.q.hi : ℝ) < (qSoftLowerRat : ℝ) := by
    exact_mod_cast hbase.2.2.2.2.1
  have hqs : q < qSoft :=
    hqB.2.trans_lt (hrat.trans qSoftLower_lt_qSoft)
  have h := evalNegative_sound (N.tightVars_ordered hN.1)
    (N.tightVars_contains_roots hN.1 hqB) hN.2
  rw [lambdaDerivativeExpr_eval] at h
  rw [LambdaDerivativeFormula_eq_scaled hq hqs,
    scaledLambdaDerivativeFormula_eq_at]
  exact h

theorem lambdaDerivativeFormula_pos_of_tight_certified {terms shift : Nat}
    {N : NewtonBulkBox} (hN : N.TightPositiveCertified terms shift)
    {q : ℝ} (hqB : N.broad.q.Contains q) :
    0 < LambdaDerivativeFormula q := by
  have hbase := hN.1.1.1
  have hqlo : (0 : ℝ) < (N.broad.q.lo : ℝ) := by
    exact_mod_cast hbase.2.2.2.1
  have hq : 0 < q := hqlo.trans_le hqB.1
  have hrat : (N.broad.q.hi : ℝ) < (qSoftLowerRat : ℝ) := by
    exact_mod_cast hbase.2.2.2.2.1
  have hqs : q < qSoft :=
    hqB.2.trans_lt (hrat.trans qSoftLower_lt_qSoft)
  have h := evalPositive_sound (N.tightVars_ordered hN.1)
    (N.tightVars_contains_roots hN.1 hqB) hN.2
  rw [lambdaDerivativeExpr_eval] at h
  rw [LambdaDerivativeFormula_eq_scaled hq hqs,
    scaledLambdaDerivativeFormula_eq_at]
  exact h

def EvalBetween {n : Nat} (lo hi : Rat) (X : Fin n → RatInterval)
    (e : IntervalExpr n) : Prop :=
  match evalInterval X e with
  | none => False
  | some I => lo < I.lo ∧ I.hi < hi

instance instDecidableEvalBetween {n : Nat} (lo hi : Rat)
    (X : Fin n → RatInterval) (e : IntervalExpr n) :
    Decidable (EvalBetween lo hi X e) := by
  unfold EvalBetween
  cases evalInterval X e <;> infer_instance

theorem evalBetween_sound {n : Nat} {lo hi : Rat}
    {X : Fin n → RatInterval} {x : Fin n → ℝ} {e : IntervalExpr n}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i))
    (hcert : EvalBetween lo hi X e) :
    (lo : ℝ) < evalReal x e ∧ evalReal x e < (hi : ℝ) := by
  cases h : evalInterval X e with
  | none => simp [EvalBetween, h] at hcert
  | some I =>
      have hcert' : lo < I.lo ∧ I.hi < hi := by
        simpa [EvalBetween, h] using! hcert
      have hbounds := (evalInterval_sound hordered hcontains _ _ h).2
      have hlo : (lo : ℝ) < (I.lo : ℝ) := by
        exact_mod_cast hcert'.1
      have hhi : (I.hi : ℝ) < (hi : ℝ) := by
        exact_mod_cast hcert'.2
      exact ⟨hlo.trans_le hbounds.1, hbounds.2.trans_lt hhi⟩

def LambdaBetweenCertified (terms shift : Nat) (lo hi : Rat)
    (N : NewtonBulkBox) : Prop :=
  N.Certified terms shift ∧ EvalBetween lo hi N.tightVars lambdaExpr

instance instDecidableLambdaBetweenCertified (terms shift : Nat)
    (lo hi : Rat) (N : NewtonBulkBox) :
    Decidable (N.LambdaBetweenCertified terms shift lo hi) := by
  unfold LambdaBetweenCertified
  infer_instance

theorem lambda_between_of_certified {terms shift : Nat} {lo hi : Rat}
    {N : NewtonBulkBox} (hN : N.LambdaBetweenCertified terms shift lo hi)
    {q : ℝ} (hqB : N.broad.q.Contains q) :
    (lo : ℝ) < Lambda q ∧ Lambda q < (hi : ℝ) := by
  have hbase := hN.1.1.1
  have hqlo : (0 : ℝ) < (N.broad.q.lo : ℝ) := by
    exact_mod_cast hbase.2.2.2.1
  have hq : 0 < q := hqlo.trans_le hqB.1
  have hrat : (N.broad.q.hi : ℝ) < (qSoftLowerRat : ℝ) := by
    exact_mod_cast hbase.2.2.2.2.1
  have hqs : q < qSoft :=
    hqB.2.trans_lt (hrat.trans qSoftLower_lt_qSoft)
  have h := evalBetween_sound (N.tightVars_ordered hN.1)
    (N.tightVars_contains_roots hN.1 hqB) hN.2
  rw [lambdaExpr_eval] at h
  rwa [Lambda_eq_scaledLambdaExpression hq hqs]

end NewtonBulkBox

end

end Erdos1038
