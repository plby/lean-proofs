import ErdosProblems.Erdos1038.HighKTerminalScalarAlgebra
import ErdosProblems.Erdos1038.HighKPlatformIntervalSmoke

/-!
# Exact interval checker for the terminal scalar

The variables are `(r,q,z₊,z₋,π)`, with `r=-1/log q`.  Every
expression below is regular at `q=0`; in particular, the parameter `A` is
evaluated as `1-r*log(2/(1+q)^2)`.
-/

set_option warningAsError false
set_option maxHeartbeats 4000000

open Set

namespace Erdos1038

noncomputable section

open HighKIntervalExpr
open OneCutTailCertificate

namespace HighKTerminalFormula

abbrev E := HighKIntervalExpr 5

def e0 : E := .rat 0
def e1 : E := .rat 1
def e2 : E := .rat 2

def rE : E := .var 0
def qE : E := .var 1
def zpE : E := .var 2
def zmE : E := .var 3
def piE : E := .var 4

def dE (logTerms : ℕ) : E :=
  .log logTerms (.div e2 (.sq (.add e1 qE)))

def alphaE (logTerms : ℕ) : E :=
  .sub e1 (.mul rE (dE logTerms))

def rawE (logTerms : ℕ) (z : E) : E :=
  .sub e1
    (.div
      (.mul (.mul (alphaE logTerms) (.sub e1 (.sq qE))) z)
      (.mul (.sub e1 z) (.sub z (.sq qE))))

def plusWeightE (logTerms : ℕ) : E :=
  .neg (.inv (rawE logTerms zpE))

def minusWeightE (logTerms : ℕ) : E :=
  .inv (rawE logTerms zmE)

def pE (logTerms : ℕ) : E :=
  .add (.sub e1 (alphaE logTerms))
    (.div (.mul (.mul e2 qE) (alphaE logTerms)) (.add e1 qE))

def denominatorE (logTerms : ℕ) : E :=
  .mul (.mul e2 (pE logTerms))
    (.add (plusWeightE logTerms) (minusWeightE logTerms))

def qmaxE (logTerms : ℕ) : E :=
  .div (.mul piE (.sub e1 (alphaE logTerms))) (pE logTerms)

def rratioE (logTerms : ℕ) : E :=
  .div
    (.add
      (.mul (.add e1 (.div qE zpE)) (plusWeightE logTerms))
      (.mul (.add e1 (.div qE zmE)) (minusWeightE logTerms)))
    (.mul e2 (.add (plusWeightE logTerms) (minusWeightE logTerms)))

def rmaxE (logTerms : ℕ) : E :=
  .mul piE (rratioE logTerms)

def rectangleBaseLowerE (logTerms trigDoubles fourierTerms : ℕ)
    (qCap rCap : Rat) : E :=
  .add
    (.add (.neg (.log logTerms (denominatorE logTerms)))
      (circleCorrectionLowerE logTerms trigDoubles fourierTerms
        (.rat qCap) piE))
    (circleCorrectionLowerE logTerms trigDoubles fourierTerms
      (.rat rCap) piE)

def actualValues (q : ℝ) : Fin 5 → ℝ :=
  ![tailRReal q, q, zPlus q, zMinus q, Real.pi]

@[simp] theorem actualValues_zero (q : ℝ) :
    actualValues q (0 : Fin 5) = tailRReal q := rfl

@[simp] theorem actualValues_one (q : ℝ) :
    actualValues q (1 : Fin 5) = q := rfl

@[simp] theorem actualValues_two (q : ℝ) :
    actualValues q (2 : Fin 5) = zPlus q := rfl

@[simp] theorem actualValues_three (q : ℝ) :
    actualValues q (3 : Fin 5) = zMinus q := rfl

@[simp] theorem actualValues_four (q : ℝ) :
    actualValues q (4 : Fin 5) = Real.pi := rfl

attribute [simp] HighKIntervalExpr.evalReal

@[simp] theorem dE_eval (v : Fin 5 → ℝ) (logTerms : ℕ) :
    evalReal v (dE logTerms) = scaledD (v 1) := by
  simp only [dE, HighKIntervalExpr.div, HighKIntervalExpr.sq,
    HighKIntervalExpr.evalReal, e1, e2, qE, scaledD]
  congr 1
  ring

theorem alphaE_eval_actual {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (logTerms : ℕ) :
    evalReal (actualValues q) (alphaE logTerms) = A q := by
  simp only [alphaE, HighKIntervalExpr.sub, HighKIntervalExpr.evalReal,
    e1, rE, dE_eval, actualValues_zero, actualValues_one]
  norm_num at ⊢
  rw [show 1 + -(tailRReal q * scaledD q) =
    1 - tailRReal q * scaledD q by ring]
  rw [← tailDReal_eq_scaledD hq]
  exact tailAReal_eq_A hq hq1

@[simp] theorem rawE_eval_actual {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (logTerms : ℕ) (z : E) :
    evalReal (actualValues q) (rawE logTerms z) =
      terminalRaw q (evalReal (actualValues q) z) := by
  unfold rawE terminalRaw
  simp only [HighKIntervalExpr.sub, HighKIntervalExpr.div,
    HighKIntervalExpr.sq, HighKIntervalExpr.evalReal, e1, qE]
  rw [alphaE_eval_actual hq hq1 logTerms]
  simp only [actualValues_one]
  ring

@[simp] theorem plusWeightE_eval_actual {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (logTerms : ℕ) :
    evalReal (actualValues q) (plusWeightE logTerms) =
      terminalPlusWeight q (zPlus q) := by
  unfold plusWeightE terminalPlusWeight
  simp only [HighKIntervalExpr.evalReal]
  rw [rawE_eval_actual hq hq1 logTerms]
  simp only [zpE, HighKIntervalExpr.evalReal, actualValues_two]
  ring

@[simp] theorem minusWeightE_eval_actual {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (logTerms : ℕ) :
    evalReal (actualValues q) (minusWeightE logTerms) =
      terminalMinusWeight q (zMinus q) := by
  unfold minusWeightE terminalMinusWeight
  simp only [HighKIntervalExpr.evalReal]
  rw [rawE_eval_actual hq hq1 logTerms]
  simp only [zmE, HighKIntervalExpr.evalReal, actualValues_three]
  rw [one_div]

@[simp] theorem pE_eval_actual {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (logTerms : ℕ) :
    evalReal (actualValues q) (pE logTerms) = terminalP q := by
  unfold pE terminalP
  simp only [HighKIntervalExpr.sub, HighKIntervalExpr.div,
    HighKIntervalExpr.evalReal, e1, e2, qE]
  rw [alphaE_eval_actual hq hq1 logTerms]
  simp only [actualValues_one]
  ring

@[simp] theorem denominatorE_eval_actual {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (logTerms : ℕ) :
    evalReal (actualValues q) (denominatorE logTerms) =
      terminalScalarDenominator q (zPlus q) (zMinus q) := by
  unfold denominatorE terminalScalarDenominator
  simp only [HighKIntervalExpr.evalReal, e2]
  rw [pE_eval_actual hq hq1 logTerms,
    plusWeightE_eval_actual hq hq1 logTerms,
    minusWeightE_eval_actual hq hq1 logTerms]
  norm_num [e2]

@[simp] theorem qmaxE_eval_actual {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (logTerms : ℕ) :
    evalReal (actualValues q) (qmaxE logTerms) = terminalStableQmax q := by
  unfold qmaxE terminalStableQmax
  simp only [HighKIntervalExpr.sub, HighKIntervalExpr.div,
    HighKIntervalExpr.evalReal, e1, piE]
  rw [alphaE_eval_actual hq hq1 logTerms,
    pE_eval_actual hq hq1 logTerms]
  simp only [actualValues_four]
  ring

@[simp] theorem rratioE_eval_actual {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (logTerms : ℕ) :
    evalReal (actualValues q) (rratioE logTerms) =
      terminalStableRratio q (zPlus q) (zMinus q) := by
  unfold rratioE terminalStableRratio
  simp only [HighKIntervalExpr.div, HighKIntervalExpr.evalReal,
    e1, e2, qE, zpE, zmE]
  rw [plusWeightE_eval_actual hq hq1 logTerms,
    minusWeightE_eval_actual hq hq1 logTerms]
  simp only [actualValues_one, actualValues_two, actualValues_three]
  ring

@[simp] theorem rmaxE_eval_actual {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (logTerms : ℕ) :
    evalReal (actualValues q) (rmaxE logTerms) =
      terminalStableRmax q (zPlus q) (zMinus q) := by
  unfold rmaxE terminalStableRmax
  simp only [HighKIntervalExpr.evalReal, piE]
  rw [rratioE_eval_actual hq hq1 logTerms]
  simp only [actualValues_four]

def rootTerms : ℕ := 20
def logTerms : ℕ := 24
def trigDoubles : ℕ := 8
def fourierTerms : ℕ := 8

def boxes (B : TailQBox) : Fin 5 → RatInterval :=
  ![B.r, B.q, B.zp, B.zm,
    HighKPlatformIntervalSmoke.piBox]

theorem boxes_ordered {B : TailQBox} (hB : B.BaseCertified rootTerms) :
    ∀ i, (boxes B i).Ordered := by
  intro i
  fin_cases i
  · exact hB.2.1
  · exact hB.1
  · exact hB.2.2.2.1
  · exact hB.2.2.2.2.1
  · norm_num [boxes, HighKPlatformIntervalSmoke.piBox,
      RatInterval.Ordered]

theorem boxes_contains_actual {B : TailQBox} (hB : B.BaseCertified rootTerms)
    {q : ℝ} (hqB : B.q.Contains q) :
    ∀ i, (boxes B i).Contains (actualValues q i) := by
  have hd := B.derived_contains hB hqB
  have hr := B.roots_mem hB hqB
  intro i
  fin_cases i
  · exact hd.1
  · exact hqB
  · exact ⟨hr.1.1.le, hr.1.2.le⟩
  · exact ⟨hr.2.1.le, hr.2.2.le⟩
  · simpa [boxes, actualValues] using!
      HighKPlatformIntervalSmoke.pi_mem_piBox

def tailBoxes : Fin 5 → RatInterval :=
  ![⟨0, 1 / 50⟩, ⟨0, tailQ⟩,
    ⟨499 / 1000, 501 / 1000⟩,
    ⟨149 / 100, 15001 / 10000⟩,
    HighKPlatformIntervalSmoke.piBox]

theorem tailBoxes_ordered : ∀ i, (tailBoxes i).Ordered := by
  intro i
  fin_cases i <;>
    norm_num [tailBoxes, tailQ, HighKPlatformIntervalSmoke.piBox,
      RatInterval.Ordered]

theorem tailBoxes_contains_actual {q : ℝ}
    (hq : 0 < q) (hqTail : q ≤ (tailQ : ℝ)) :
    ∀ i, (tailBoxes i).Contains (actualValues q i) := by
  have hroots := scaledRoots_mem_tail_box hq hqTail
  intro i
  fin_cases i
  all_goals dsimp [tailBoxes, actualValues, RatInterval.Contains]
  · constructor
    · simpa only [Rat.cast_zero] using! (tailRReal_pos hq hqTail).le
    · exact tailRReal_le_fiftieth hq hqTail
  · constructor
    · simpa only [Rat.cast_zero] using! hq.le
    · exact hqTail
  · exact ⟨hroots.1.1.le, hroots.1.2.le⟩
  · exact ⟨hroots.2.1.le, hroots.2.2.le⟩
  · exact HighKPlatformIntervalSmoke.pi_mem_piBox

def denominatorBelowOneE : E :=
  .sub (denominatorE logTerms) e1

def SimpleCertified (B : TailQBox) : Prop :=
  B.BaseCertified rootTerms ∧
    evalNegativeCheck (boxes B) denominatorBelowOneE = true

instance (B : TailQBox) : Decidable (SimpleCertified B) := by
  unfold SimpleCertified
  infer_instance

def tailSimpleCheck : Bool :=
  evalNegativeCheck tailBoxes denominatorBelowOneE

theorem simpleCertified_base {B : TailQBox} (hB : SimpleCertified B) :
    B.BaseCertified rootTerms := hB.1

theorem denominator_lt_one_of_simpleCertified {B : TailQBox}
    (hB : SimpleCertified B) {q : ℝ} (hqB : B.q.Contains q) :
    terminalScalarDenominator q (zPlus q) (zMinus q) < 1 := by
  have hq : 0 < q := by
    have hlo : (0 : ℝ) < (B.q.lo : ℝ) := by
      exact_mod_cast hB.1.2.2.2.2.2.1
    exact hlo.trans_le hqB.1
  have hqs : q < qSoft := by
    have hhi : (B.q.hi : ℝ) < (qSoftLowerRat : ℝ) := by
      exact_mod_cast hB.1.2.2.2.2.2.2.1
    exact hqB.2.trans_lt (hhi.trans qSoftLower_lt_qSoft)
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hneg := HighKIntervalExpr.evalNegative_sound (boxes_ordered hB.1)
    (boxes_contains_actual hB.1 hqB) (evalNegative_of_check hB.2)
  simp [denominatorBelowOneE, e1,
    denominatorE_eval_actual hq hq1 logTerms] at hneg
  linarith

theorem denominator_lt_one_of_tailCheck
    (hcheck : tailSimpleCheck = true) {q : ℝ}
    (hq : 0 < q) (hqTail : q ≤ (tailQ : ℝ)) :
    terminalScalarDenominator q (zPlus q) (zMinus q) < 1 := by
  have hq1 := hqTail.trans_lt tailQ_lt_one
  have hneg := HighKIntervalExpr.evalNegative_sound tailBoxes_ordered
    (tailBoxes_contains_actual hq hqTail)
    (evalNegative_of_check hcheck)
  simp [denominatorBelowOneE, e1,
    denominatorE_eval_actual hq hq1 logTerms] at hneg
  linarith

structure RefinedData where
  root : TailQBox
  qCap : Rat
  rCap : Rat
deriving DecidableEq, Repr

def RefinedCertified (d : RefinedData) : Prop :=
  d.root.BaseCertified rootTerms ∧
  0 < d.qCap ∧ d.qCap ≤ 3 ∧
  0 < d.rCap ∧ d.rCap ≤ 3 ∧
  evalPositiveCheck (boxes d.root) (qmaxE logTerms) = true ∧
  evalPositiveCheck (boxes d.root) (rmaxE logTerms) = true ∧
  evalNegativeCheck (boxes d.root)
    (.sub (qmaxE logTerms) (.rat d.qCap)) = true ∧
  evalNegativeCheck (boxes d.root)
    (.sub (rmaxE logTerms) (.rat d.rCap)) = true ∧
  evalPositiveCheck (boxes d.root)
    (rectangleBaseLowerE logTerms trigDoubles fourierTerms
      d.qCap d.rCap) = true

instance (d : RefinedData) : Decidable (RefinedCertified d) := by
  unfold RefinedCertified
  infer_instance

def AllSimpleCertified : List TailQBox → Prop
  | [] => True
  | B :: Bs => SimpleCertified B ∧ AllSimpleCertified Bs

instance (Bs : List TailQBox) : Decidable (AllSimpleCertified Bs) := by
  induction Bs with
  | nil => simp [AllSimpleCertified]; infer_instance
  | cons B Bs ih =>
      simp only [AllSimpleCertified]
      exact instDecidableAnd

theorem AllSimpleCertified.append {Bs Cs : List TailQBox}
    (hBs : AllSimpleCertified Bs) (hCs : AllSimpleCertified Cs) :
    AllSimpleCertified (Bs ++ Cs) := by
  induction Bs with
  | nil => simpa [AllSimpleCertified] using! hCs
  | cons B Bs ih =>
      simp only [AllSimpleCertified] at hBs ⊢
      exact ⟨hBs.1, ih hBs.2⟩

theorem AllSimpleCertified.of_mem {Bs : List TailQBox}
    (hall : AllSimpleCertified Bs) {B : TailQBox} (hB : B ∈ Bs) :
    SimpleCertified B := by
  induction Bs with
  | nil => simp at hB
  | cons C Cs ih =>
      simp only [AllSimpleCertified] at hall
      simp only [List.mem_cons] at hB
      rcases hB with rfl | hB
      · exact hall.1
      · exact ih hall.2 hB

def AllRefinedCertified : List RefinedData → Prop
  | [] => True
  | d :: ds => RefinedCertified d ∧ AllRefinedCertified ds

instance (ds : List RefinedData) : Decidable (AllRefinedCertified ds) := by
  induction ds with
  | nil => simp [AllRefinedCertified]; infer_instance
  | cons d ds ih =>
      simp only [AllRefinedCertified]
      exact instDecidableAnd

theorem AllRefinedCertified.append {ds es : List RefinedData}
    (hds : AllRefinedCertified ds) (hes : AllRefinedCertified es) :
    AllRefinedCertified (ds ++ es) := by
  induction ds with
  | nil => simpa [AllRefinedCertified] using! hes
  | cons d ds ih =>
      simp only [AllRefinedCertified] at hds ⊢
      exact ⟨hds.1, ih hds.2⟩

theorem AllRefinedCertified.of_mem {ds : List RefinedData}
    (hall : AllRefinedCertified ds) {d : RefinedData} (hd : d ∈ ds) :
    RefinedCertified d := by
  induction ds with
  | nil => simp at hd
  | cons c cs ih =>
      simp only [AllRefinedCertified] at hall
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact hall.1
      · exact ih hall.2 hd

theorem rectangleBaseLowerE_le
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft)
    {qCap rCap : Rat}
    (hqCapPos : 0 < (qCap : ℝ)) (hqCapPi : (qCap : ℝ) ≤ Real.pi)
    (hrCapPos : 0 < (rCap : ℝ)) (hrCapPi : (rCap : ℝ) ≤ Real.pi)
    (hqCap : terminalStableQmax q ≤ (qCap : ℝ))
    (hrCap : terminalStableRmax q (zPlus q) (zMinus q) ≤ (rCap : ℝ)) :
    evalReal (actualValues q)
        (rectangleBaseLowerE logTerms trigDoubles fourierTerms qCap rCap) ≤
      circleRectangleBase
        (platformCapacity (terminalPlatformEdge q))
        (platformAPi (terminalPlatformRatio q) (terminalPlatformEdge q))
        (platformBPi (terminalPlatformEdge q)
          (terminalPlatformXMinus q) (terminalPlatformXPlus q)
          (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q))
        (platformReferenceCircleRadiusCap
          (terminalPlatformRatio q) (terminalPlatformEdge q))
        (platformAdjointCircleRadiusCap (terminalPlatformEdge q)
          (terminalPlatformXMinus q) (terminalPlatformXPlus q)
          (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q)) := by
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hqmax := terminalStableQmax_mem_Ioc hq hqs
  have hrmax := terminalStableRmax_mem_Ioc hq hqs
  have hqLower : evalReal (actualValues q)
      (circleCorrectionLowerE logTerms trigDoubles fourierTerms
        (.rat qCap) piE) ≤ circleCorrection (qCap : ℝ) := by
    simpa [piE, actualValues] using! circleCorrectionLowerE_le
      (v := actualValues q) (logTerms := logTerms)
      (trigDoubles := trigDoubles) (N := fourierTerms)
      (q := (.rat qCap : E)) (pi := piE)
      hqCapPos hqCapPi (by simp [piE, actualValues])
      (by norm_num [fourierTerms])
  have hrLower : evalReal (actualValues q)
      (circleCorrectionLowerE logTerms trigDoubles fourierTerms
        (.rat rCap) piE) ≤ circleCorrection (rCap : ℝ) := by
    simpa [piE, actualValues] using! circleCorrectionLowerE_le
      (v := actualValues q) (logTerms := logTerms)
      (trigDoubles := trigDoubles) (N := fourierTerms)
      (q := (.rat rCap : E)) (pi := piE)
      hrCapPos hrCapPi (by simp [piE, actualValues])
      (by norm_num [fourierTerms])
  have hqMono : circleCorrection (qCap : ℝ) ≤
      circleCorrection (terminalStableQmax q) :=
    circleCorrection_antitoneOn
      ⟨hqmax.1, hqCap.trans hqCapPi⟩ ⟨hqCapPos, hqCapPi⟩ hqCap
  have hrMono : circleCorrection (rCap : ℝ) ≤
      circleCorrection (terminalStableRmax q (zPlus q) (zMinus q)) :=
    circleCorrection_antitoneOn
      ⟨hrmax.1, hrCap.trans hrCapPi⟩ ⟨hrCapPos, hrCapPi⟩ hrCap
  rw [terminalCircleRectangleBase_eq hq hqs]
  simp only [rectangleBaseLowerE, HighKIntervalExpr.evalReal,
    denominatorE_eval_actual hq hq1 logTerms]
  linarith

theorem base_pos_of_refinedCertified {d : RefinedData}
    (hd : RefinedCertified d) {q : ℝ} (hqB : d.root.q.Contains q) :
    0 < circleRectangleBase
        (platformCapacity (terminalPlatformEdge q))
        (platformAPi (terminalPlatformRatio q) (terminalPlatformEdge q))
        (platformBPi (terminalPlatformEdge q)
          (terminalPlatformXMinus q) (terminalPlatformXPlus q)
          (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q))
        (platformReferenceCircleRadiusCap
          (terminalPlatformRatio q) (terminalPlatformEdge q))
        (platformAdjointCircleRadiusCap (terminalPlatformEdge q)
          (terminalPlatformXMinus q) (terminalPlatformXPlus q)
          (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q)) := by
  have hbase := hd.1
  have hq : 0 < q := by
    have hlo : (0 : ℝ) < (d.root.q.lo : ℝ) := by
      exact_mod_cast hbase.2.2.2.2.2.1
    exact hlo.trans_le hqB.1
  have hqs : q < qSoft := by
    have hhi : (d.root.q.hi : ℝ) < (qSoftLowerRat : ℝ) := by
      exact_mod_cast hbase.2.2.2.2.2.2.1
    exact hqB.2.trans_lt (hhi.trans qSoftLower_lt_qSoft)
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hord := boxes_ordered hbase
  have hcontains := boxes_contains_actual hbase hqB
  have hqpos := HighKIntervalExpr.evalPositive_sound hord hcontains
    (evalPositive_of_check hd.2.2.2.2.2.1)
  have hrpos := HighKIntervalExpr.evalPositive_sound hord hcontains
    (evalPositive_of_check hd.2.2.2.2.2.2.1)
  have hqcap' := HighKIntervalExpr.evalNegative_sound hord hcontains
    (evalNegative_of_check hd.2.2.2.2.2.2.2.1)
  have hrcap' := HighKIntervalExpr.evalNegative_sound hord hcontains
    (evalNegative_of_check hd.2.2.2.2.2.2.2.2.1)
  have hlower := HighKIntervalExpr.evalPositive_sound hord hcontains
    (evalPositive_of_check hd.2.2.2.2.2.2.2.2.2)
  simp [qmaxE_eval_actual hq hq1 logTerms] at hqpos
  simp [rmaxE_eval_actual hq hq1 logTerms] at hrpos
  simp [HighKIntervalExpr.sub,
    qmaxE_eval_actual hq hq1 logTerms] at hqcap'
  simp [HighKIntervalExpr.sub,
    rmaxE_eval_actual hq hq1 logTerms] at hrcap'
  have hqCapPos : 0 < (d.qCap : ℝ) := by exact_mod_cast hd.2.1
  have hrCapPos : 0 < (d.rCap : ℝ) := by exact_mod_cast hd.2.2.2.1
  have hqCapPi : (d.qCap : ℝ) ≤ Real.pi := by
    have hthree : (d.qCap : ℝ) ≤ 3 := by exact_mod_cast hd.2.2.1
    exact hthree.trans Real.pi_gt_three.le
  have hrCapPi : (d.rCap : ℝ) ≤ Real.pi := by
    have hthree : (d.rCap : ℝ) ≤ 3 := by exact_mod_cast hd.2.2.2.2.1
    exact hthree.trans Real.pi_gt_three.le
  have hle := rectangleBaseLowerE_le hq hqs hqCapPos hqCapPi
    hrCapPos hrCapPi (by linarith) (by linarith)
  exact hlower.trans_le hle

/-- Rational chain condition used by generated box lists. -/
def QCover (lo hi : Rat) : List TailQBox → Prop
  | [] => hi ≤ lo
  | B :: Bs => B.q.lo ≤ lo ∧ QCover B.q.hi hi Bs

instance (lo hi : Rat) (Bs : List TailQBox) : Decidable (QCover lo hi Bs) := by
  induction Bs generalizing lo with
  | nil => simp [QCover]; infer_instance
  | cons B Bs ih =>
      simp only [QCover]
      exact instDecidableAnd

theorem QCover.sound {lo hi : Rat} {Bs : List TailQBox}
    (hcover : QCover lo hi Bs) {q : ℝ}
    (hlo : (lo : ℝ) ≤ q) (hhi : q < (hi : ℝ)) :
    ∃ B ∈ Bs, B.q.Contains q := by
  induction Bs generalizing lo with
  | nil =>
      simp only [QCover] at hcover
      have hrat : (hi : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hcover
      linarith
  | cons B Bs ih =>
      simp only [QCover] at hcover
      by_cases hq : q ≤ (B.q.hi : ℝ)
      · refine ⟨B, by simp, ?_⟩
        have hleft : (B.q.lo : ℝ) ≤ (lo : ℝ) := by
          exact_mod_cast hcover.1
        exact ⟨hleft.trans hlo, hq⟩
      · obtain ⟨C, hCBs, hCq⟩ := ih hcover.2
          (show (B.q.hi : ℝ) ≤ q from le_of_not_ge hq)
        exact ⟨C, by simp [hCBs], hCq⟩

end HighKTerminalFormula

end

end Erdos1038
