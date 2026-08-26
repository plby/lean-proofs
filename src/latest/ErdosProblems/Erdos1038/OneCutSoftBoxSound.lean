import ErdosProblems.Erdos1038.OneCutSoftBox
import ErdosProblems.Erdos1038.OneCutSoftChart
import ErdosProblems.Erdos1038.OneCutScaledRootBounds

/-!
# Soundness of the exact soft-chart boxes
-/

open Set

namespace Erdos1038

noncomputable section

open IntervalExpr

namespace IntervalExpr

@[simp] theorem softOuterResidualExpr_eval (terms shift : Nat)
    (q s zm ts tps tw tpw : ℝ) :
    evalReal ![q, s, zm, ts, tps, tw, tpw]
        (softOuterResidualExpr terms shift) =
      scaledOuterResidual (q, zm) := by
  simp only [softOuterResidualExpr, softOuterLogArgumentExpr,
    softScaledDExpr, sub, div, sq, evalReal, softAExpr_eval,
    softQExpr_eval, softZmExpr_eval, softOnePlusQExpr_eval,
    eOne, eTwo, eRat, Rat.cast_ofNat]
  rw [scaledOuterResidual, scaledD]
  ring_nf

end IntervalExpr

namespace SoftBox

private theorem geometry_of_base {terms : Nat} {B : SoftBox}
    (hB : B.BaseCertified terms) : B.GeometryCertified := hB.1

private theorem function_of_base {terms : Nat} {B : SoftBox}
    (hB : B.BaseCertified terms) : B.FunctionCertified terms := hB.2.1

private theorem roots_of_base {terms : Nat} {B : SoftBox}
    (hB : B.BaseCertified terms) : B.RootsCertified terms := hB.2.2

theorem vars_ordered {terms : Nat} {B : SoftBox}
    (hB : B.BaseCertified terms) : ∀ i, (B.vars i).Ordered := by
  rcases geometry_of_base hB with
    ⟨hq, hs, hzm, hw, hts, htps, htw, htpw, _⟩
  intro i
  fin_cases i <;> assumption

private theorem interval_lo_contains {I : RatInterval} (hI : I.Ordered) :
    I.Contains (I.lo : ℝ) := by
  constructor
  · exact le_rfl
  · exact_mod_cast hI

private theorem interval_hi_contains {I : RatInterval} (hI : I.Ordered) :
    I.Contains (I.hi : ℝ) := by
  constructor
  · exact_mod_cast hI
  · exact le_rfl

private theorem lowerVars_ordered {terms : Nat} {B : SoftBox}
    (hB : B.BaseCertified terms) :
    (∀ i, (B.innerLowerVars i).Ordered) ∧
      (∀ i, (B.outerLowerVars i).Ordered) := by
  rcases geometry_of_base hB with
    ⟨hq, hs, hzm, hw, hts, htps, htw, htpw, _⟩
  constructor <;> intro i <;> fin_cases i <;>
    simp only [innerLowerVars, outerLowerVars] <;>
    first | assumption | exact RatInterval.point_ordered _

private theorem upperVars_ordered {terms : Nat} {B : SoftBox}
    (hB : B.BaseCertified terms) :
    (∀ i, (B.innerUpperVars i).Ordered) ∧
      (∀ i, (B.outerUpperVars i).Ordered) := by
  rcases geometry_of_base hB with
    ⟨hq, hs, hzm, hw, hts, htps, htw, htpw, _⟩
  constructor <;> intro i <;> fin_cases i <;>
    simp only [innerUpperVars, outerUpperVars] <;>
    first | assumption | exact RatInterval.point_ordered _

private theorem vars_contains_qs_lows {terms : Nat} {B : SoftBox}
    (hB : B.BaseCertified terms) {q x : ℝ}
    (hqB : B.q.Contains q) (hxB : B.s.Contains x) :
    ∀ i, (B.vars i).Contains
      (![q, x, (B.zm.lo : ℝ), (B.ts.lo : ℝ), (B.tps.lo : ℝ),
        (B.tw.lo : ℝ), (B.tpw.lo : ℝ)] i) := by
  rcases geometry_of_base hB with
    ⟨hq, hs, hzm, hw, hts, htps, htw, htpw, _⟩
  intro i
  fin_cases i
  · exact hqB
  · exact hxB
  · exact interval_lo_contains hzm
  · exact interval_lo_contains hts
  · exact interval_lo_contains htps
  · exact interval_lo_contains htw
  · exact interval_lo_contains htpw

private theorem innerLowerVars_contains {terms : Nat} {B : SoftBox}
    (hB : B.BaseCertified terms) {q : ℝ} (hqB : B.q.Contains q) :
    ∀ i, (B.innerLowerVars i).Contains
      (![q, (B.s.lo : ℝ), (B.zm.lo : ℝ), (B.ts.lo : ℝ),
        (B.tps.lo : ℝ), (B.tw.lo : ℝ), (B.tpw.lo : ℝ)] i) := by
  rcases geometry_of_base hB with
    ⟨hq, hs, hzm, hw, hts, htps, htw, htpw, _⟩
  intro i
  fin_cases i
  · exact hqB
  · simpa [innerLowerVars] using! RatInterval.point_contains B.s.lo
  · exact interval_lo_contains hzm
  · exact interval_lo_contains hts
  · exact interval_lo_contains htps
  · exact interval_lo_contains htw
  · exact interval_lo_contains htpw

private theorem innerUpperVars_contains {terms : Nat} {B : SoftBox}
    (hB : B.BaseCertified terms) {q : ℝ} (hqB : B.q.Contains q) :
    ∀ i, (B.innerUpperVars i).Contains
      (![q, (B.s.hi : ℝ), (B.zm.lo : ℝ), (B.ts.lo : ℝ),
        (B.tps.lo : ℝ), (B.tw.lo : ℝ), (B.tpw.lo : ℝ)] i) := by
  rcases geometry_of_base hB with
    ⟨hq, hs, hzm, hw, hts, htps, htw, htpw, _⟩
  intro i
  fin_cases i
  · exact hqB
  · simpa [innerUpperVars] using! RatInterval.point_contains B.s.hi
  · exact interval_lo_contains hzm
  · exact interval_lo_contains hts
  · exact interval_lo_contains htps
  · exact interval_lo_contains htw
  · exact interval_lo_contains htpw

theorem softW_mem {terms : Nat} {B : SoftBox}
    (hB : B.BaseCertified terms) {q x : ℝ}
    (hqB : B.q.Contains q) (hxB : B.s.Contains x) :
    B.w.Contains (softW q x) := by
  have h := OneCutTailCertificate.evalInside_sound
    (B.vars_ordered hB) (vars_contains_qs_lows hB hqB hxB)
    (function_of_base hB).1
  simpa using! h

private theorem softDividedInner_lo_neg {terms : Nat} {B : SoftBox}
    (hterms : 0 < terms) (hB : B.BaseCertified terms)
    {q : ℝ} (hqB : B.q.Contains q) (hqs : q < qSoft)
    (hlo0 : B.s.lo ≠ 0) :
    softDividedInnerAt q (softT (B.s.lo : ℝ))
        (softT (softW q (B.s.lo : ℝ))) < 0 := by
  rcases geometry_of_base hB with
    ⟨hqOrd, hsOrd, hzmOrd, hwOrd, htsOrd, htpsOrd, htwOrd, htpwOrd,
      hqlo, hqhi, hslo, hshi0, hshi1, hwlo, hwhi, hzmlo⟩
  rcases roots_of_base hB with ⟨hlo, hhi, hslope, hmlo, hmhi⟩
  have hloCert : EvalNegative B.innerLowerVars
      (softDividedInnerUpperExpr terms B.shift) := hlo.resolve_left hlo0
  have hupper := evalNegative_sound (lowerVars_ordered hB).1
    (innerLowerVars_contains hB hqB) hloCert
  rw [softDividedInnerUpperExpr_eval] at hupper
  have hqloReal : (0 : ℝ) < (B.q.lo : ℝ) := by exact_mod_cast hqlo
  have hq : 0 < q := hqloReal.trans_le hqB.1
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hx0 : 0 < (B.s.lo : ℝ) := by
    have hx0' : (0 : Rat) < B.s.lo := lt_of_le_of_ne hslo (Ne.symm hlo0)
    exact_mod_cast hx0'
  have hx1 : (B.s.lo : ℝ) < 1 :=
    (by exact_mod_cast hsOrd : (B.s.lo : ℝ) ≤ (B.s.hi : ℝ)).trans_lt
      (by exact_mod_cast hshi1)
  have hxB := interval_lo_contains hsOrd
  have hwB := B.softW_mem hB hqB hxB
  have hwloReal : (0 : ℝ) ≤ (B.w.lo : ℝ) := by exact_mod_cast hwlo
  have hw0 : 0 ≤ softW q (B.s.lo : ℝ) := hwloReal.trans hwB.1
  have hw1 : softW q (B.s.lo : ℝ) < 1 :=
    hwB.2.trans_lt (by exact_mod_cast hwhi)
  have hsBounds := softT_bounds hterms hx0.le hx1
  have hwBounds := softT_bounds hterms hw0 hw1
  have hAk : 0 ≤ A q * softKappa q := by
    exact (mul_pos (A_pos_of_pos_le_qSoft hq hqs.le)
      (by rw [softKappa]; exact div_pos (by linarith) (by linarith))).le
  rw [softDividedInnerAt]
  exact lt_of_le_of_lt
    (sub_le_sub (mul_le_mul_of_nonneg_left hwBounds.2 hAk) hsBounds.1)
    hupper

private theorem softDividedInner_hi_pos {terms : Nat} {B : SoftBox}
    (hterms : 0 < terms) (hB : B.BaseCertified terms)
    {q : ℝ} (hqB : B.q.Contains q) (hqs : q < qSoft) :
    0 < softDividedInnerAt q (softT (B.s.hi : ℝ))
      (softT (softW q (B.s.hi : ℝ))) := by
  rcases geometry_of_base hB with
    ⟨hqOrd, hsOrd, hzmOrd, hwOrd, htsOrd, htpsOrd, htwOrd, htpwOrd,
      hqlo, hqhi, hslo, hshi0, hshi1, hwlo, hwhi, hzmlo⟩
  rcases roots_of_base hB with ⟨hlo, hhi, hslope, hmlo, hmhi⟩
  have hlower := evalPositive_sound (upperVars_ordered hB).1
    (innerUpperVars_contains hB hqB) hhi
  rw [softDividedInnerLowerExpr_eval] at hlower
  have hqloReal : (0 : ℝ) < (B.q.lo : ℝ) := by exact_mod_cast hqlo
  have hq : 0 < q := hqloReal.trans_le hqB.1
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hx0 : 0 < (B.s.hi : ℝ) := by exact_mod_cast hshi0
  have hx1 : (B.s.hi : ℝ) < 1 := by exact_mod_cast hshi1
  have hxB := interval_hi_contains hsOrd
  have hwB := B.softW_mem hB hqB hxB
  have hwloReal : (0 : ℝ) ≤ (B.w.lo : ℝ) := by exact_mod_cast hwlo
  have hw0 : 0 ≤ softW q (B.s.hi : ℝ) := hwloReal.trans hwB.1
  have hw1 : softW q (B.s.hi : ℝ) < 1 :=
    hwB.2.trans_lt (by exact_mod_cast hwhi)
  have hsBounds := softT_bounds hterms hx0.le hx1
  have hwBounds := softT_bounds hterms hw0 hw1
  have hAk : 0 ≤ A q * softKappa q := by
    exact (mul_pos (A_pos_of_pos_le_qSoft hq hqs.le)
      (by rw [softKappa]; exact div_pos (by linarith) (by linarith))).le
  rw [softDividedInnerAt]
  exact lt_of_lt_of_le hlower
    (sub_le_sub (mul_le_mul_of_nonneg_left hwBounds.1 hAk) hsBounds.2)

theorem innerRoot_mem {terms : Nat} {B : SoftBox}
    (hterms : 0 < terms) (hB : B.BaseCertified terms)
    {q : ℝ} (hqB : B.q.Contains q) (hqs : q < qSoft) :
    oneCutSoftS q ∈ Ioo (B.s.lo : ℝ) (B.s.hi : ℝ) := by
  rcases geometry_of_base hB with
    ⟨hqOrd, hsOrd, hzmOrd, hwOrd, htsOrd, htpsOrd, htwOrd, htpwOrd,
      hqlo, hqhi, hslo, hshi0, hshi1, hwlo, hwhi, hzmlo⟩
  have hqloReal : (0 : ℝ) < (B.q.lo : ℝ) := by exact_mod_cast hqlo
  have hq : 0 < q := hqloReal.trans_le hqB.1
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hactual := oneCutSoftS_mem_Ioo hq hqs
  constructor
  · by_cases hlo0 : B.s.lo = 0
    · rw [hlo0]
      norm_num
      exact hactual.1
    · have hx0 : 0 < (B.s.lo : ℝ) := by
        have hx0' : (0 : Rat) < B.s.lo := lt_of_le_of_ne hslo (Ne.symm hlo0)
        exact_mod_cast hx0'
      have hx1 : (B.s.lo : ℝ) < 1 :=
        (by exact_mod_cast hsOrd : (B.s.lo : ℝ) ≤ (B.s.hi : ℝ)).trans_lt
          (by exact_mod_cast hshi1)
      have hwB := B.softW_mem hB hqB (interval_lo_contains hsOrd)
      have hw1 : softW q (B.s.lo : ℝ) < 1 :=
        hwB.2.trans_lt (by exact_mod_cast hwhi)
      exact softDividedInner_neg_imp_lt_actual hq hqs hx0 hx1 hw1
        (softDividedInner_lo_neg hterms hB hqB hqs hlo0)
  · have hx0 : 0 < (B.s.hi : ℝ) := by exact_mod_cast hshi0
    have hx1 : (B.s.hi : ℝ) < 1 := by exact_mod_cast hshi1
    have hwB := B.softW_mem hB hqB (interval_hi_contains hsOrd)
    have hw1 : softW q (B.s.hi : ℝ) < 1 :=
      hwB.2.trans_lt (by exact_mod_cast hwhi)
    exact softDividedInner_pos_imp_actual_lt hq hqs hx0 hx1 hw1
      (softDividedInner_hi_pos hterms hB hqB hqs)

private theorem outerLowerVars_contains {terms : Nat} {B : SoftBox}
    (hB : B.BaseCertified terms) {q : ℝ} (hqB : B.q.Contains q) :
    ∀ i, (B.outerLowerVars i).Contains
      (![q, (B.s.lo : ℝ), (B.zm.lo : ℝ), (B.ts.lo : ℝ),
        (B.tps.lo : ℝ), (B.tw.lo : ℝ), (B.tpw.lo : ℝ)] i) := by
  rcases geometry_of_base hB with
    ⟨hq, hs, hzm, hw, hts, htps, htw, htpw, _⟩
  intro i
  fin_cases i
  · exact hqB
  · exact interval_lo_contains hs
  · simpa [outerLowerVars] using! RatInterval.point_contains B.zm.lo
  · exact interval_lo_contains hts
  · exact interval_lo_contains htps
  · exact interval_lo_contains htw
  · exact interval_lo_contains htpw

private theorem outerUpperVars_contains {terms : Nat} {B : SoftBox}
    (hB : B.BaseCertified terms) {q : ℝ} (hqB : B.q.Contains q) :
    ∀ i, (B.outerUpperVars i).Contains
      (![q, (B.s.lo : ℝ), (B.zm.hi : ℝ), (B.ts.lo : ℝ),
        (B.tps.lo : ℝ), (B.tw.lo : ℝ), (B.tpw.lo : ℝ)] i) := by
  rcases geometry_of_base hB with
    ⟨hq, hs, hzm, hw, hts, htps, htw, htpw, _⟩
  intro i
  fin_cases i
  · exact hqB
  · exact interval_lo_contains hs
  · simpa [outerUpperVars] using! RatInterval.point_contains B.zm.hi
  · exact interval_lo_contains hts
  · exact interval_lo_contains htps
  · exact interval_lo_contains htw
  · exact interval_lo_contains htpw

theorem outerRoot_mem {terms : Nat} {B : SoftBox}
    (hB : B.BaseCertified terms) {q : ℝ}
    (hqB : B.q.Contains q) (hqs : q < qSoft) :
    zMinus q ∈ Ioo (B.zm.lo : ℝ) (B.zm.hi : ℝ) := by
  rcases geometry_of_base hB with
    ⟨hqOrd, hsOrd, hzmOrd, hwOrd, htsOrd, htpsOrd, htwOrd, htpwOrd,
      hqlo, hqhi, hslo, hshi0, hshi1, hwlo, hwhi, hzmlo⟩
  rcases roots_of_base hB with ⟨hlo, hhi, hslope, hmlo, hmhi⟩
  have hqloReal : (0 : ℝ) < (B.q.lo : ℝ) := by exact_mod_cast hqlo
  have hq : 0 < q := hqloReal.trans_le hqB.1
  have hmLo := evalPositive_sound (lowerVars_ordered hB).2
    (outerLowerVars_contains hB hqB) hmlo
  have hmHi := evalNegative_sound (upperVars_ordered hB).2
    (outerUpperVars_contains hB hqB) hmhi
  rw [softOuterResidualExpr_eval] at hmLo hmHi
  have h1lo : (1 : ℝ) < (B.zm.lo : ℝ) := by exact_mod_cast hzmlo
  have h1hi : (1 : ℝ) < (B.zm.hi : ℝ) :=
    h1lo.trans_le (by exact_mod_cast hzmOrd)
  exact ⟨scaledOuterResidual_pos_imp_lt_zMinus hq hqs.le h1lo hmLo,
    scaledOuterResidual_neg_imp_zMinus_lt hq hqs.le
      h1hi hmHi⟩

theorem vars_contains_actual {terms : Nat} {B : SoftBox}
    (hterms : 0 < terms) (hB : B.BaseCertified terms)
    {q : ℝ} (hqB : B.q.Contains q) (hqs : q < qSoft) :
    ∀ i, (B.vars i).Contains
      (![q, oneCutSoftS q, zMinus q, softT (oneCutSoftS q),
        softTPrime (oneCutSoftS q), softT (softW q (oneCutSoftS q)),
        softTPrime (softW q (oneCutSoftS q))] i) := by
  rcases geometry_of_base hB with
    ⟨hqOrd, hsOrd, hzmOrd, hwOrd, htsOrd, htpsOrd, htwOrd, htpwOrd,
      hqlo, hqhi, hslo, hshi0, hshi1, hwlo, hwhi, hzmlo⟩
  rcases function_of_base hB with ⟨hwCert, hTs, hTps, hTw, hTpw⟩
  have hqloReal : (0 : ℝ) < (B.q.lo : ℝ) := by exact_mod_cast hqlo
  have hq : 0 < q := hqloReal.trans_le hqB.1
  have hsRoot := B.innerRoot_mem hterms hB hqB hqs
  have hzmRoot := B.outerRoot_mem hB hqB hqs
  have hsB : B.s.Contains (oneCutSoftS q) :=
    ⟨hsRoot.1.le, hsRoot.2.le⟩
  have hwB := B.softW_mem hB hqB hsB
  have hs0 : 0 ≤ oneCutSoftS q := (oneCutSoftS_mem_Ioo hq hqs).1.le
  have hs1 : oneCutSoftS q < 1 := oneCutSoftS_mem_Ioo hq hqs |>.2
  have hwloReal : (0 : ℝ) ≤ (B.w.lo : ℝ) := by exact_mod_cast hwlo
  have hw0 : 0 ≤ softW q (oneCutSoftS q) := hwloReal.trans hwB.1
  have hw1 : softW q (oneCutSoftS q) < 1 :=
    hwB.2.trans_lt (by exact_mod_cast hwhi)
  have hTsMem := softT_mem_of_enclosed hsOrd hsB hs0 hs1 hTs hterms
  have hTpsMem := softTPrime_mem_of_enclosed hsOrd hsB hs0 hs1 hTps
  have hTwMem := softT_mem_of_enclosed hwOrd hwB hw0 hw1 hTw hterms
  have hTpwMem := softTPrime_mem_of_enclosed hwOrd hwB hw0 hw1 hTpw
  intro i
  fin_cases i
  · exact hqB
  · exact hsB
  · exact ⟨hzmRoot.1.le, hzmRoot.2.le⟩
  · exact hTsMem
  · exact hTpsMem
  · exact hTwMem
  · exact hTpwMem

theorem lambdaDerivativeFormula_pos_of_certified {terms : Nat}
    {B : SoftBox} (hterms : 0 < terms) (hB : B.PositiveCertified terms)
    {q : ℝ} (hqB : B.q.Contains q) (hqs : q < qSoft) :
    0 < LambdaDerivativeFormula q := by
  have hq : 0 < q := by
    rcases geometry_of_base hB.1 with
      ⟨hqOrd, hsOrd, hzmOrd, hwOrd, htsOrd, htpsOrd, htwOrd, htpwOrd,
        hqlo, _⟩
    have hqloReal : (0 : ℝ) < (B.q.lo : ℝ) := by exact_mod_cast hqlo
    exact hqloReal.trans_le hqB.1
  have heval := evalPositive_sound (B.vars_ordered hB.1)
    (B.vars_contains_actual hterms hB.1 hqB hqs) hB.2
  rw [softCoreExprs_eval, softLambdaDerivativeAt_actual_eq hq hqs] at heval
  exact heval

end SoftBox

end

end Erdos1038
