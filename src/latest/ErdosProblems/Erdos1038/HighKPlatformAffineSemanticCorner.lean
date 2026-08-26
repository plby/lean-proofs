import ErdosProblems.Erdos1038.HighKPlatformAffineCornerComponents

/-!
# Shared semantic certificates for the affine scalar corner

The original tree interval evaluator is intentionally simple, but a tree
duplicates common subexpressions.  At the affine corner this is particularly
costly for `Qmax`, `Rmax`, and the square of their sinc difference.  This
module supplies a semantic interface: independently checked component bounds
are combined after interval soundness, so a component may use algebraic
cancellation or explicitly shared intermediate enclosures without weakening
the mathematical conclusion.
-/

set_option warningAsError false

namespace Erdos1038.HighKPlatformAffineSemanticCorner

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCornerComponents

noncomputable section

/-- A lower bound which holds uniformly for every real point in `X`. -/
def UniformLower {n : ℕ} (X : Fin n → RatInterval)
    (e : HighKIntervalExpr n) (lower : Rat) : Prop :=
  ∀ x, (∀ i, (X i).Ordered) → (∀ i, (X i).Contains (x i)) →
    (lower : ℝ) < evalReal x e

/-- Uniform strict positivity over an interval environment. -/
def UniformPositive {n : ℕ} (X : Fin n → RatInterval)
    (e : HighKIntervalExpr n) : Prop :=
  ∀ x, (∀ i, (X i).Ordered) → (∀ i, (X i).Contains (x i)) →
    0 < evalReal x e

theorem uniformLower_of_evalLower {n : ℕ} {X : Fin n → RatInterval}
    {e : HighKIntervalExpr n} {lower : Rat}
    (h : EvalLower X e lower) : UniformLower X e lower := by
  intro x hordered hcontains
  exact evalLower_sound hordered hcontains h

/-- A checked interval evaluation whose result is contained in the explicit
outer box `J`.  Materializing `J` lets later checks reuse the result without
reevaluating the original expression tree. -/
def EvalEnclosed {n : ℕ} (X : Fin n → RatInterval)
    (e : HighKIntervalExpr n) (J : RatInterval) : Prop :=
  ∃ I, evalInterval X e = some I ∧ J.lo ≤ I.lo ∧ I.hi ≤ J.hi

def evalEnclosedCheck {n : ℕ} (X : Fin n → RatInterval)
    (e : HighKIntervalExpr n) (J : RatInterval) : Bool :=
  match evalInterval X e with
  | some I => decide (J.lo ≤ I.lo ∧ I.hi ≤ J.hi)
  | none => false

theorem evalEnclosed_of_check {n : ℕ} {X : Fin n → RatInterval}
    {e : HighKIntervalExpr n} {J : RatInterval}
    (h : evalEnclosedCheck X e J = true) : EvalEnclosed X e J := by
  cases heval : evalInterval X e with
  | none => simp [evalEnclosedCheck, heval] at h
  | some I =>
      simp [evalEnclosedCheck, heval] at h
      exact ⟨I, heval, h.1, h.2⟩

theorem evalEnclosed_sound {n : ℕ} {X : Fin n → RatInterval}
    {x : Fin n → ℝ} {e : HighKIntervalExpr n} {J : RatInterval}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i))
    (h : EvalEnclosed X e J) : J.Contains (evalReal x e) := by
  obtain ⟨I, heval, hlo, hhi⟩ := h
  have hsound := evalInterval_sound hordered hcontains e I heval
  constructor
  · have hlo' : (J.lo : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo
    exact hlo'.trans hsound.2.1
  · have hhi' : (I.hi : ℝ) ≤ (J.hi : ℝ) := by exact_mod_cast hhi
    exact hsound.2.2.trans hhi'

/-- An exact interval evaluation with a deliberately coarse strict upper
cap. -/
def EvalUpper {n : ℕ} (X : Fin n → RatInterval)
    (e : HighKIntervalExpr n) (upper : Rat) : Prop :=
  ∃ I, evalInterval X e = some I ∧ I.hi < upper

def evalUpperCheck {n : ℕ} (X : Fin n → RatInterval)
    (e : HighKIntervalExpr n) (upper : Rat) : Bool :=
  match evalInterval X e with
  | some I => decide (I.hi < upper)
  | none => false

theorem evalUpper_of_check {n : ℕ} {X : Fin n → RatInterval}
    {e : HighKIntervalExpr n} {upper : Rat}
    (h : evalUpperCheck X e upper = true) : EvalUpper X e upper := by
  cases heval : evalInterval X e with
  | none => simp [evalUpperCheck, heval] at h
  | some I =>
      simp [evalUpperCheck, heval] at h
      exact ⟨I, heval, h⟩

theorem evalUpper_sound {n : ℕ} {X : Fin n → RatInterval}
    {x : Fin n → ℝ} {e : HighKIntervalExpr n} {upper : Rat}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i))
    (h : EvalUpper X e upper) : evalReal x e < (upper : ℝ) := by
  obtain ⟨I, heval, hupper⟩ := h
  have hsound := evalInterval_sound hordered hcontains e I heval
  have hupper' : (I.hi : ℝ) < (upper : ℝ) := by
    exact_mod_cast hupper
  exact hsound.2.2.trans_lt hupper'

abbrev E2 := HighKIntervalExpr 2

def qE2 : E2 := .var 0
def rE2 : E2 := .var 1

def sincE2 (trigDoubles : ℕ) (q : E2) : E2 :=
  .div (.sin trigDoubles q) q

/-- The unsquared sinc difference, evaluated only after `Qmax` and `Rmax`
have been enclosed once. -/
def sincGapE2 (trigDoubles : ℕ) : E2 :=
  .sub (sincE2 trigDoubles qE2) (sincE2 trigDoubles rE2)

@[simp] theorem sincGapE2_eval (trigDoubles : ℕ) (q r : ℝ) :
    evalReal ![q, r] (sincGapE2 trigDoubles) =
      Real.sin q / q - Real.sin r / r := by
  simp [sincGapE2, sincE2, qE2, rE2, HighKIntervalExpr.div,
    HighKIntervalExpr.sub, div_eq_mul_inv, sub_eq_add_neg]

/-- A shared `Qmax`/`Rmax` enclosure and one check of the unsquared negative
sinc gap give a lower bound for the square. -/
theorem uniformLower_sincGapSquare_of_enclosures
    {X : Fin 5 → RatInterval} {sqrtSteps trigDoubles : ℕ}
    {edge : HighKPlatformEdge} {qOuter rOuter : RatInterval}
    {gapUpper lower : Rat}
    (hqOuter : qOuter.Ordered) (hrOuter : rOuter.Ordered)
    (hq : EvalEnclosed X (qmaxE sqrtSteps edge) qOuter)
    (hr : EvalEnclosed X (rmaxE sqrtSteps edge) rOuter)
    (hgap : EvalUpper ![qOuter, rOuter] (sincGapE2 trigDoubles) gapUpper)
    (hgapNegative : gapUpper < 0)
    (hlower : lower < gapUpper * gapUpper) :
    UniformLower X (sincGapSquareE sqrtSteps trigDoubles edge) lower := by
  intro x hordered hcontains
  let q : ℝ := evalReal x (qmaxE sqrtSteps edge)
  let r : ℝ := evalReal x (rmaxE sqrtSteps edge)
  have hqContains : qOuter.Contains q :=
    evalEnclosed_sound hordered hcontains hq
  have hrContains : rOuter.Contains r :=
    evalEnclosed_sound hordered hcontains hr
  have hpairOrdered : ∀ i : Fin 2, ((![qOuter, rOuter] :
      Fin 2 → RatInterval) i).Ordered := by
    intro i
    fin_cases i <;> assumption
  have hpairContains : ∀ i : Fin 2, ((![qOuter, rOuter] :
      Fin 2 → RatInterval) i).Contains ((![q, r] : Fin 2 → ℝ) i) := by
    intro i
    fin_cases i <;> assumption
  have hgapReal : Real.sin q / q - Real.sin r / r < (gapUpper : ℝ) := by
    simpa using! evalUpper_sound hpairOrdered hpairContains hgap
  have hgapNegative' : (gapUpper : ℝ) < 0 := by
    exact_mod_cast hgapNegative
  have hlower' : (lower : ℝ) < (gapUpper : ℝ) * (gapUpper : ℝ) := by
    exact_mod_cast hlower
  have htarget :
      evalReal x (sincGapSquareE sqrtSteps trigDoubles edge) =
        (Real.sin q / q - Real.sin r / r) ^ 2 := by
    simp [sincGapSquareE, sincE, HighKIntervalExpr.sq,
      HighKIntervalExpr.sub, HighKIntervalExpr.div, q, r,
      div_eq_mul_inv, sub_eq_add_neg, pow_two]
  rw [htarget]
  nlinarith

/-- Algebraic cancellation of the penalty quotient.  Positivity hypotheses
exclude exactly the two denominators cancelled in the identity. -/
theorem penaltyQuotientE_eval_eq_neg_ceff
    {x : Fin 5 → ℝ}
    {logTerms sqrtSteps : ℕ} {edge : HighKPlatformEdge}
    (hpi : 0 < evalReal x piE)
    (hapi : 0 < evalReal x (apiE sqrtSteps edge)) :
    evalReal x (penaltyQuotientE logTerms sqrtSteps edge) =
      -evalReal x (ceffE logTerms sqrtSteps edge) := by
  simp only [penaltyQuotientE, penaltyE, qmaxE,
    HighKIntervalExpr.evalReal, HighKIntervalExpr.div]
  field_simp [hpi.ne', hapi.ne']

/-- The cheaper interval evaluation of `-C_eff` certifies the original
penalty quotient after the exact algebraic cancellation above. -/
theorem uniformLower_penaltyQuotient_of_negCeff
    {X : Fin 5 → RatInterval} {logTerms sqrtSteps : ℕ}
    {edge : HighKPlatformEdge} {lower : Rat}
    (hpi : EvalPositive X piE)
    (hapi : EvalPositive X (apiE sqrtSteps edge))
    (hnegCeff : EvalLower X (.neg (ceffE logTerms sqrtSteps edge)) lower) :
    UniformLower X (penaltyQuotientE logTerms sqrtSteps edge) lower := by
  intro x hordered hcontains
  have hpiReal := evalPositive_sound hordered hcontains hpi
  have hapiReal := evalPositive_sound hordered hcontains hapi
  have hlower := evalLower_sound hordered hcontains hnegCeff
  rw [penaltyQuotientE_eval_eq_neg_ceff hpiReal hapiReal]
  simpa using! hlower

/-- Combine five uniform lower bounds directly at the level of real
semantics.  Unlike exact tree reconstruction, this retains sharing inside
the cell-dependent components. -/
theorem uniformPositive_affineCorner_of_lower_components
    {X : Fin 5 → RatInterval}
    {logTerms sqrtSteps trigDoubles N : ℕ}
    {edge : HighKPlatformEdge} {qCap rCap : Rat}
    {prefactorLower qCorrectionLower rCorrectionLower penaltyLower
      sincGapLower : Rat}
    (hprefactor : UniformLower X (prefactorE logTerms sqrtSteps edge)
      prefactorLower)
    (hqCorrection : UniformLower X
      (circleCorrectionLowerE logTerms trigDoubles N (.rat qCap) piE)
      qCorrectionLower)
    (hrCorrection : UniformLower X
      (circleCorrectionLowerE logTerms trigDoubles N (.rat rCap) piE)
      rCorrectionLower)
    (hpenalty : UniformLower X
      (penaltyQuotientE logTerms sqrtSteps edge) penaltyLower)
    (hsincGap : UniformLower X
      (sincGapSquareE sqrtSteps trigDoubles edge) sincGapLower)
    (hpositive : 0 < prefactorLower + qCorrectionLower +
      rCorrectionLower + penaltyLower + sincGapLower) :
    UniformPositive X
      (affineCornerLowerE logTerms sqrtSteps trigDoubles N
        edge qCap rCap) := by
  intro x hordered hcontains
  have hp := hprefactor x hordered hcontains
  have hq := hqCorrection x hordered hcontains
  have hr := hrCorrection x hordered hcontains
  have hpen := hpenalty x hordered hcontains
  have hsinc := hsincGap x hordered hcontains
  have hpositive' : (0 : ℝ) <
      (prefactorLower : ℝ) + (qCorrectionLower : ℝ) +
        (rCorrectionLower : ℝ) + (penaltyLower : ℝ) +
        (sincGapLower : ℝ) := by
    exact_mod_cast hpositive
  change 0 <
    evalReal x (prefactorE logTerms sqrtSteps edge) +
      evalReal x
        (circleCorrectionLowerE logTerms trigDoubles N (.rat qCap) piE) +
      evalReal x
        (circleCorrectionLowerE logTerms trigDoubles N (.rat rCap) piE) +
      evalReal x (penaltyQuotientE logTerms sqrtSteps edge) +
      evalReal x (sincGapSquareE sqrtSteps trigDoubles edge)
  linarith

end

end Erdos1038.HighKPlatformAffineSemanticCorner
