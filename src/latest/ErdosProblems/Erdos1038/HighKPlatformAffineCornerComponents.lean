import ErdosProblems.Erdos1038.HighKPlatformIntervalChecker

/-!
# Componentwise exact checks for the affine scalar corner

The direct Boolean evaluation of the affine corner duplicates several large
exact-rational subcomputations in one reduction.  This module gives an
equivalent proof-producing interface: each of the five top-level components
is evaluated independently and exported behind an opaque theorem together
with a coarse rational lower cap.  The final theorem reconstructs the
original `evalInterval` result exactly, so consumers retain the existing
`evalPositiveCheck ... = true` API and its established soundness chain.
-/

set_option warningAsError false

namespace Erdos1038.HighKPlatformAffineCornerComponents

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula

noncomputable section

abbrev E := HighKIntervalExpr 5

/-- The penalty contribution at the affine corner. -/
def penaltyQuotientE (logTerms sqrtSteps : ℕ)
    (edge : HighKPlatformEdge) : E :=
  .div (penaltyE logTerms sqrtSteps edge) (qmaxE sqrtSteps edge)

/-- The retained first Fourier square at the affine corner. -/
def sincGapSquareE (sqrtSteps trigDoubles : ℕ)
    (edge : HighKPlatformEdge) : E :=
  .sq (.sub (sincE trigDoubles (qmaxE sqrtSteps edge))
    (sincE trigDoubles (rmaxE sqrtSteps edge)))

/-- An exact evaluator witness with a deliberately coarse rational lower cap.
The exact interval remains existential, preventing downstream elaboration from
unfolding or printing its potentially very large rational endpoints. -/
def EvalLower {n : ℕ} (X : Fin n → RatInterval)
    (e : HighKIntervalExpr n) (lower : Rat) : Prop :=
  ∃ I, evalInterval X e = some I ∧ lower < I.lo

/-- Closed Boolean checker for `EvalLower`. -/
def evalLowerCheck {n : ℕ} (X : Fin n → RatInterval)
    (e : HighKIntervalExpr n) (lower : Rat) : Bool :=
  match evalInterval X e with
  | some I => decide (lower < I.lo)
  | none => false

theorem evalLower_of_check {n : ℕ} {X : Fin n → RatInterval}
    {e : HighKIntervalExpr n} {lower : Rat}
    (h : evalLowerCheck X e lower = true) : EvalLower X e lower := by
  cases heval : evalInterval X e with
  | none => simp [evalLowerCheck, heval] at h
  | some I =>
      simp [evalLowerCheck, heval] at h
      exact ⟨I, heval, h⟩

/-- Semantic lower-bound consequence of a checked component. -/
theorem evalLower_sound {n : ℕ} {X : Fin n → RatInterval}
    {x : Fin n → ℝ} {e : HighKIntervalExpr n} {lower : Rat}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i))
    (h : EvalLower X e lower) : (lower : ℝ) < evalReal x e := by
  obtain ⟨I, heval, hlower⟩ := h
  have hcontainsEval :=
    (evalInterval_sound hordered hcontains e I heval).2.1
  have hlowerCast : (lower : ℝ) < (I.lo : ℝ) := by
    exact_mod_cast hlower
  exact hlowerCast.trans_le hcontainsEval

/-- Pointwise agreement only at the variables actually read by an expression.
This permits globally cached correction certificates: those expressions read
only the common `pi` box, not the cell-dependent `k`, root, or length boxes. -/
def AgreeOn {n : ℕ} (X Y : Fin n → RatInterval) :
    HighKIntervalExpr n → Prop
  | .rat _ => True
  | .var i => X i = Y i
  | .add p q => AgreeOn X Y p ∧ AgreeOn X Y q
  | .neg p => AgreeOn X Y p
  | .mul p q => AgreeOn X Y p ∧ AgreeOn X Y q
  | .inv p => AgreeOn X Y p
  | .log _ p => AgreeOn X Y p
  | .sqrt _ p => AgreeOn X Y p
  | .sin _ p => AgreeOn X Y p
  | .cos _ p => AgreeOn X Y p

theorem evalInterval_eq_of_agreeOn {n : ℕ}
    {X Y : Fin n → RatInterval} {e : HighKIntervalExpr n}
    (h : AgreeOn X Y e) : evalInterval X e = evalInterval Y e := by
  induction e with
  | rat r => rfl
  | var i =>
      simp only [AgreeOn] at h
      exact congrArg some h
  | add p q ihp ihq =>
      simp only [AgreeOn] at h
      simp only [HighKIntervalExpr.evalInterval]
      rw [ihp h.1, ihq h.2]
  | neg p ih =>
      simp only [AgreeOn] at h
      simp only [HighKIntervalExpr.evalInterval]
      rw [ih h]
  | mul p q ihp ihq =>
      simp only [AgreeOn] at h
      simp only [HighKIntervalExpr.evalInterval]
      rw [ihp h.1, ihq h.2]
  | inv p ih =>
      simp only [AgreeOn] at h
      simp only [HighKIntervalExpr.evalInterval]
      rw [ih h]
  | log terms p ih =>
      simp only [AgreeOn] at h
      simp only [HighKIntervalExpr.evalInterval]
      rw [ih h]
  | sqrt steps p ih =>
      simp only [AgreeOn] at h
      simp only [HighKIntervalExpr.evalInterval]
      rw [ih h]
  | sin doubles p ih =>
      simp only [AgreeOn] at h
      simp only [HighKIntervalExpr.evalInterval]
      rw [ih h]
  | cos doubles p ih =>
      simp only [AgreeOn] at h
      simp only [HighKIntervalExpr.evalInterval]
      rw [ih h]

/-- Exact reconstruction of the original corner evaluator from five cached
component evaluations. -/
theorem evalInterval_affineCorner_of_five_components
    {X : Fin 5 → RatInterval}
    {logTerms sqrtSteps trigDoubles N : ℕ}
    {edge : HighKPlatformEdge} {qCap rCap : Rat}
    {prefactorBox qCorrectionBox rCorrectionBox penaltyBox sincGapBox :
      RatInterval}
    (hprefactor : evalInterval X (prefactorE logTerms sqrtSteps edge) =
      some prefactorBox)
    (hqCorrection : evalInterval X
      (circleCorrectionLowerE logTerms trigDoubles N (.rat qCap) piE) =
      some qCorrectionBox)
    (hrCorrection : evalInterval X
      (circleCorrectionLowerE logTerms trigDoubles N (.rat rCap) piE) =
      some rCorrectionBox)
    (hpenalty : evalInterval X
      (penaltyQuotientE logTerms sqrtSteps edge) = some penaltyBox)
    (hsincGap : evalInterval X
      (sincGapSquareE sqrtSteps trigDoubles edge) = some sincGapBox) :
    evalInterval X
      (affineCornerLowerE logTerms sqrtSteps trigDoubles N
        edge qCap rCap) =
      some (((((prefactorBox.add qCorrectionBox).add rCorrectionBox).add
        penaltyBox).add sincGapBox)) := by
  change evalInterval X
      (.add (.add
        (.add
          (.add (prefactorE logTerms sqrtSteps edge)
            (circleCorrectionLowerE logTerms trigDoubles N
              (.rat qCap) piE))
          (circleCorrectionLowerE logTerms trigDoubles N
            (.rat rCap) piE))
        (penaltyQuotientE logTerms sqrtSteps edge))
        (sincGapSquareE sqrtSteps trigDoubles edge)) = _
  simp only [HighKIntervalExpr.evalInterval]
  rw [hprefactor, hqCorrection, hrCorrection, hpenalty, hsincGap]
  rfl

/-- Reassemble five independently checked lower components into the exact
Boolean expected by `HighKPlatformAffineCell.RawChecks.corner`. -/
theorem evalPositiveCheck_affineCorner_of_lower_components
    {X : Fin 5 → RatInterval}
    {logTerms sqrtSteps trigDoubles N : ℕ}
    {edge : HighKPlatformEdge} {qCap rCap : Rat}
    {prefactorLower qCorrectionLower rCorrectionLower penaltyLower
      sincGapLower : Rat}
    (hprefactor : EvalLower X (prefactorE logTerms sqrtSteps edge)
      prefactorLower)
    (hqCorrection : EvalLower X
      (circleCorrectionLowerE logTerms trigDoubles N (.rat qCap) piE)
      qCorrectionLower)
    (hrCorrection : EvalLower X
      (circleCorrectionLowerE logTerms trigDoubles N (.rat rCap) piE)
      rCorrectionLower)
    (hpenalty : EvalLower X (penaltyQuotientE logTerms sqrtSteps edge)
      penaltyLower)
    (hsincGap : EvalLower X (sincGapSquareE sqrtSteps trigDoubles edge)
      sincGapLower)
    (hpositive : 0 < prefactorLower + qCorrectionLower +
      rCorrectionLower + penaltyLower + sincGapLower) :
    evalPositiveCheck X
      (affineCornerLowerE logTerms sqrtSteps trigDoubles N
        edge qCap rCap) = true := by
  obtain ⟨prefactorBox, hprefactorEval, hprefactorLower⟩ := hprefactor
  obtain ⟨qCorrectionBox, hqCorrectionEval, hqCorrectionLower⟩ :=
    hqCorrection
  obtain ⟨rCorrectionBox, hrCorrectionEval, hrCorrectionLower⟩ :=
    hrCorrection
  obtain ⟨penaltyBox, hpenaltyEval, hpenaltyLower⟩ := hpenalty
  obtain ⟨sincGapBox, hsincGapEval, hsincGapLower⟩ := hsincGap
  have heval := evalInterval_affineCorner_of_five_components
    hprefactorEval hqCorrectionEval hrCorrectionEval hpenaltyEval hsincGapEval
  unfold evalPositiveCheck
  rw [heval]
  have hintervalPositive :
      0 < (((((prefactorBox.add qCorrectionBox).add rCorrectionBox).add
        penaltyBox).add sincGapBox)).lo := by
    dsimp only [RatInterval.add]
    linarith
  simpa using! hintervalPositive

end

end Erdos1038.HighKPlatformAffineCornerComponents
