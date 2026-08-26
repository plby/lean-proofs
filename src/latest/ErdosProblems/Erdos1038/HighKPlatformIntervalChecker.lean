import ErdosProblems.Erdos1038.HighKCircleCorrectionInterval

/-!
# Kernel-checked platform slab checker

This module converts successful exact-rational interval evaluations into the
constant- and affine-edge scalar certificate interfaces.  Fourier correction
terms are evaluated at rational upper caps; antitonicity then transfers those
bounds to every parameter value in the slab.
-/

set_option warningAsError false

open Set

namespace Erdos1038

noncomputable section

open HighKIntervalExpr

attribute [simp] HighKIntervalExpr.evalReal

def evalPositiveCheck {n : ℕ} (X : Fin n → RatInterval)
    (e : HighKIntervalExpr n) : Bool :=
  match evalInterval X e with
  | some I => decide (0 < I.lo)
  | none => false

def evalNegativeCheck {n : ℕ} (X : Fin n → RatInterval)
    (e : HighKIntervalExpr n) : Bool :=
  match evalInterval X e with
  | some I => decide (I.hi < 0)
  | none => false

theorem evalPositive_of_check {n : ℕ} {X : Fin n → RatInterval}
    {e : HighKIntervalExpr n} (h : evalPositiveCheck X e = true) :
    EvalPositive X e := by
  cases heval : evalInterval X e with
  | none => simp [evalPositiveCheck, heval] at h
  | some I =>
      simp [evalPositiveCheck, heval] at h
      exact ⟨I, heval, h⟩

theorem evalNegative_of_check {n : ℕ} {X : Fin n → RatInterval}
    {e : HighKIntervalExpr n} (h : evalNegativeCheck X e = true) :
    EvalNegative X e := by
  cases heval : evalInterval X e with
  | none => simp [evalNegativeCheck, heval] at h
  | some I =>
      simp [evalNegativeCheck, heval] at h
      exact ⟨I, heval, h⟩

def prependFin {n : ℕ} {A : Type} (x : A) (f : Fin n → A) :
    Fin (n + 1) → A :=
  @Fin.cases n (fun _ ↦ A) x f

/-- Rename the variables of an interval expression. -/
def renameExpr {n m : ℕ} (f : Fin n → Fin m) :
    HighKIntervalExpr n → HighKIntervalExpr m
  | .rat r => .rat r
  | .var i => .var (f i)
  | .add p q => .add (renameExpr f p) (renameExpr f q)
  | .neg p => .neg (renameExpr f p)
  | .mul p q => .mul (renameExpr f p) (renameExpr f q)
  | .inv p => .inv (renameExpr f p)
  | .log terms p => .log terms (renameExpr f p)
  | .sqrt steps p => .sqrt steps (renameExpr f p)
  | .sin doubles p => .sin doubles (renameExpr f p)
  | .cos doubles p => .cos doubles (renameExpr f p)

@[simp] theorem evalReal_renameExpr {n m : ℕ} (f : Fin n → Fin m)
    (v : Fin m → ℝ) (e : HighKIntervalExpr n) :
    evalReal v (renameExpr f e) = evalReal (fun i ↦ v (f i)) e := by
  induction e <;> simp [renameExpr, *]

namespace HighKPlatformFormula

abbrev E6 := HighKIntervalExpr 6

def liftE (e : E) : E6 := renameExpr Fin.succ e

def qCellE : E6 := .var 0

def sinc6E (trigDoubles : ℕ) (q : E6) : E6 :=
  .div (.sin trigDoubles q) q

def sincNumerator6E (trigDoubles : ℕ) (q : E6) : E6 :=
  .sub (.sin trigDoubles q) (.mul q (.cos trigDoubles q))

/-- The affine derivative with a sixth independent interval variable for
the `Q` cell. -/
def affineDerivativeCellE (logTerms sqrtSteps trigDoubles : ℕ)
    (edge : HighKPlatformEdge) : E6 :=
  .add
    (.neg (.div (liftE (penaltyE logTerms sqrtSteps edge)) (.sq qCellE)))
    (.mul
      (.mul (.rat 2) (.sub (sinc6E trigDoubles qCellE)
        (sinc6E trigDoubles (liftE (rmaxE sqrtSteps edge)))))
      (.neg (.div (sincNumerator6E trigDoubles qCellE) (.sq qCellE))))

theorem affineDerivativeCellE_eval
    {v : Fin 5 → ℝ} {Q : ℝ}
    (logTerms sqrtSteps trigDoubles : ℕ) (edge : HighKPlatformEdge)
    (hpi : evalReal v piE = Real.pi)
    (hQ : Q ≠ 0) (hr : evalReal v (rmaxE sqrtSteps edge) ≠ 0) :
    evalReal (prependFin Q v)
        (affineDerivativeCellE logTerms sqrtSteps trigDoubles edge) =
      affineCircleScalarDerivative
        (evalReal v (apiE sqrtSteps edge))
        (evalReal v (ceffE logTerms sqrtSteps edge))
        (evalReal v (rmaxE sqrtSteps edge)) Q := by
  have hpenalty : evalReal v (penaltyE logTerms sqrtSteps edge) =
      circleEffectivePenalty (evalReal v (apiE sqrtSteps edge))
        (evalReal v (ceffE logTerms sqrtSteps edge)) := by
    change -(evalReal v piE * evalReal v (ceffE logTerms sqrtSteps edge) /
        evalReal v (apiE sqrtSteps edge)) = _
    rw [hpi]
    unfold circleEffectivePenalty
    ring
  rw [affineCircleScalarDerivative]
  simp [affineDerivativeCellE, liftE, qCellE, sinc6E,
    sincNumerator6E, HighKIntervalExpr.div, HighKIntervalExpr.sq,
    HighKIntervalExpr.sub, HighKIntervalExpr.evalReal, prependFin,
    Real.sinc_of_ne_zero hQ,
    Real.sinc_of_ne_zero hr, sincNumerator, hpenalty,
    div_eq_mul_inv, sub_eq_add_neg]
  ring

/-- A finite family of rational `Q` boxes covering the derivative domain.
The `rBox` and `qBox` fields are the exact interval-evaluator outputs, so the
two rational endpoint comparisons imply coverage for every real point in the
parameter slab. -/
structure AffineDerivativeBoxCertificate
    (X : Fin 5 → RatInterval) (logTerms sqrtSteps trigDoubles : ℕ)
    (edge : HighKPlatformEdge) where
  domain : RatInterval
  cells : List RatInterval
  rBox : RatInterval
  qBox : RatInterval
  domain_ordered : domain.Ordered
  cells_ordered : ∀ I ∈ cells, I.Ordered
  covers : ∀ Q : ℝ, domain.Contains Q →
    ∃ I ∈ cells, I.Contains Q
  r_eval : evalInterval X (rmaxE sqrtSteps edge) = some rBox
  q_eval : evalInterval X (qmaxE sqrtSteps edge) = some qBox
  domain_lo_le : domain.lo ≤ rBox.lo
  q_hi_le : qBox.hi ≤ domain.hi
  checked : ∀ I ∈ cells,
    EvalNegative (prependFin I X)
      (affineDerivativeCellE logTerms sqrtSteps trigDoubles edge)

theorem affineDerivative_neg_of_boxCertificate
    {X : Fin 5 → RatInterval} {v : Fin 5 → ℝ}
    {logTerms sqrtSteps trigDoubles : ℕ} {edge : HighKPlatformEdge}
    (hcert : AffineDerivativeBoxCertificate X
      logTerms sqrtSteps trigDoubles edge)
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (v i))
    (hpi : evalReal v piE = Real.pi)
    (hrpos : 0 < evalReal v (rmaxE sqrtSteps edge)) :
    ∀ Q ∈ Ioo (evalReal v (rmaxE sqrtSteps edge))
        (evalReal v (qmaxE sqrtSteps edge)),
      affineCircleScalarDerivative
        (evalReal v (apiE sqrtSteps edge))
        (evalReal v (ceffE logTerms sqrtSteps edge))
        (evalReal v (rmaxE sqrtSteps edge)) Q < 0 := by
  have hrSound := evalInterval_sound hordered hcontains
    (rmaxE sqrtSteps edge) hcert.rBox hcert.r_eval
  have hqSound := evalInterval_sound hordered hcontains
    (qmaxE sqrtSteps edge) hcert.qBox hcert.q_eval
  intro Q hQ
  have hdomain : hcert.domain.Contains Q := by
    constructor
    · have hlo : (hcert.domain.lo : ℝ) ≤ (hcert.rBox.lo : ℝ) := by
        exact_mod_cast hcert.domain_lo_le
      exact hlo.trans (hrSound.2.1.trans hQ.1.le)
    · have hhi : (hcert.qBox.hi : ℝ) ≤ (hcert.domain.hi : ℝ) := by
        exact_mod_cast hcert.q_hi_le
      exact hQ.2.le.trans (hqSound.2.2.trans hhi)
  obtain ⟨I, hI, hIQ⟩ := hcert.covers Q hdomain
  have hextOrdered : ∀ i : Fin 6, ((prependFin I X) i).Ordered := by
    intro i
    refine Fin.cases (hcert.cells_ordered I hI) (fun j ↦ hordered j) i
  have hextContains : ∀ i : Fin 6,
      ((prependFin I X) i).Contains ((prependFin Q v) i) := by
    intro i
    refine Fin.cases hIQ (fun j ↦ hcontains j) i
  have hneg := evalNegative_sound hextOrdered hextContains
    (hcert.checked I hI)
  rw [affineDerivativeCellE_eval logTerms sqrtSteps trigDoubles edge
    hpi (hrpos.trans hQ.1).ne' hrpos.ne'] at hneg
  exact hneg

def prefactorE (logTerms sqrtSteps : ℕ)
    (edge : HighKPlatformEdge) : E :=
  .log logTerms (.div (.mul e2 (capacityE edge))
    (.mul (apiE sqrtSteps edge) (bpiE sqrtSteps edge)))

def rectangleBaseLowerE (logTerms sqrtSteps trigDoubles N : ℕ)
    (edge : HighKPlatformEdge) (qCap rCap : Rat) : E :=
  .add (.add (prefactorE logTerms sqrtSteps edge)
      (circleCorrectionLowerE logTerms trigDoubles N (.rat qCap) piE))
    (circleCorrectionLowerE logTerms trigDoubles N (.rat rCap) piE)

def constantEndpointLowerE (logTerms sqrtSteps trigDoubles N : ℕ)
    (edge : HighKPlatformEdge) (qCap rCap : Rat) : E :=
  .add (rectangleBaseLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap)
    (.div (penaltyE logTerms sqrtSteps edge) (qmaxE sqrtSteps edge))

def affineLeftLowerE (logTerms sqrtSteps trigDoubles N : ℕ)
    (edge : HighKPlatformEdge) (qCap rCap : Rat) : E :=
  .add (rectangleBaseLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap)
    (.div (penaltyE logTerms sqrtSteps edge) (rmaxE sqrtSteps edge))

def affineCornerLowerE (logTerms sqrtSteps trigDoubles N : ℕ)
    (edge : HighKPlatformEdge) (qCap rCap : Rat) : E :=
  .add
    (.add (rectangleBaseLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap)
      (.div (penaltyE logTerms sqrtSteps edge) (qmaxE sqrtSteps edge)))
    (.sq (.sub (sincE trigDoubles (qmaxE sqrtSteps edge))
      (sincE trigDoubles (rmaxE sqrtSteps edge))))

theorem penaltyE_eval_of_pi {v : Fin 5 → ℝ}
    (logTerms sqrtSteps : ℕ) (edge : HighKPlatformEdge)
    (hpi : evalReal v piE = Real.pi) :
    evalReal v (penaltyE logTerms sqrtSteps edge) =
      circleEffectivePenalty (evalReal v (apiE sqrtSteps edge))
        (evalReal v (ceffE logTerms sqrtSteps edge)) := by
  change -(evalReal v piE * evalReal v (ceffE logTerms sqrtSteps edge) /
      evalReal v (apiE sqrtSteps edge)) = _
  rw [hpi]
  unfold circleEffectivePenalty
  ring

theorem rectangleBaseLowerE_le
    {v : Fin 5 → ℝ} {logTerms sqrtSteps trigDoubles N : ℕ}
    {edge : HighKPlatformEdge} {qCap rCap : Rat}
    (hN : 0 < N)
    (hpi : evalReal v piE = Real.pi)
    (hqCapPos : 0 < (qCap : ℝ)) (hqCapPi : (qCap : ℝ) ≤ Real.pi)
    (hrCapPos : 0 < (rCap : ℝ)) (hrCapPi : (rCap : ℝ) ≤ Real.pi)
    (hqPos : 0 < evalReal v (qmaxE sqrtSteps edge))
    (hrPos : 0 < evalReal v (rmaxE sqrtSteps edge))
    (hqCap : evalReal v (qmaxE sqrtSteps edge) ≤ (qCap : ℝ))
    (hrCap : evalReal v (rmaxE sqrtSteps edge) ≤ (rCap : ℝ)) :
    evalReal v (rectangleBaseLowerE logTerms sqrtSteps trigDoubles N
      edge qCap rCap) ≤
      circleRectangleBase
        (evalReal v (capacityE edge))
        (evalReal v (apiE sqrtSteps edge))
        (evalReal v (bpiE sqrtSteps edge))
        (evalReal v (qmaxE sqrtSteps edge))
        (evalReal v (rmaxE sqrtSteps edge)) := by
  have hqLower : evalReal v
      (circleCorrectionLowerE logTerms trigDoubles N (.rat qCap) piE) ≤
      circleCorrection (qCap : ℝ) := by
    simpa using! circleCorrectionLowerE_le
      (v := v) (logTerms := logTerms) (trigDoubles := trigDoubles)
      (N := N) (q := (.rat qCap : E)) (pi := piE)
      hqCapPos hqCapPi hpi hN
  have hrLower : evalReal v
      (circleCorrectionLowerE logTerms trigDoubles N (.rat rCap) piE) ≤
      circleCorrection (rCap : ℝ) := by
    simpa using! circleCorrectionLowerE_le
      (v := v) (logTerms := logTerms) (trigDoubles := trigDoubles)
      (N := N) (q := (.rat rCap : E)) (pi := piE)
      hrCapPos hrCapPi hpi hN
  have hqMono : circleCorrection (qCap : ℝ) ≤
      circleCorrection (evalReal v (qmaxE sqrtSteps edge)) :=
    circleCorrection_antitoneOn
      ⟨hqPos, hqCap.trans hqCapPi⟩ ⟨hqCapPos, hqCapPi⟩ hqCap
  have hrMono : circleCorrection (rCap : ℝ) ≤
      circleCorrection (evalReal v (rmaxE sqrtSteps edge)) :=
    circleCorrection_antitoneOn
      ⟨hrPos, hrCap.trans hrCapPi⟩ ⟨hrCapPos, hrCapPi⟩ hrCap
  change Real.log (2 * evalReal v (capacityE edge) /
        (evalReal v (apiE sqrtSteps edge) *
          evalReal v (bpiE sqrtSteps edge))) +
      evalReal v (circleCorrectionLowerE logTerms trigDoubles N
        (.rat qCap) piE) +
      evalReal v (circleCorrectionLowerE logTerms trigDoubles N
        (.rat rCap) piE) ≤ _
  unfold circleRectangleBase
  linarith

theorem constantEndpointLowerE_le
    {v : Fin 5 → ℝ} {logTerms sqrtSteps trigDoubles N : ℕ}
    {edge : HighKPlatformEdge} {qCap rCap : Rat}
    (hN : 0 < N)
    (hpi : evalReal v piE = Real.pi)
    (hqCapPos : 0 < (qCap : ℝ)) (hqCapPi : (qCap : ℝ) ≤ Real.pi)
    (hrCapPos : 0 < (rCap : ℝ)) (hrCapPi : (rCap : ℝ) ≤ Real.pi)
    (hqPos : 0 < evalReal v (qmaxE sqrtSteps edge))
    (hrPos : 0 < evalReal v (rmaxE sqrtSteps edge))
    (hqCap : evalReal v (qmaxE sqrtSteps edge) ≤ (qCap : ℝ))
    (hrCap : evalReal v (rmaxE sqrtSteps edge) ≤ (rCap : ℝ)) :
    evalReal v (constantEndpointLowerE logTerms sqrtSteps trigDoubles N
      edge qCap rCap) ≤
      circleRectangleBase
        (evalReal v (capacityE edge))
        (evalReal v (apiE sqrtSteps edge))
        (evalReal v (bpiE sqrtSteps edge))
        (evalReal v (qmaxE sqrtSteps edge))
        (evalReal v (rmaxE sqrtSteps edge)) +
      circleEffectivePenalty (evalReal v (apiE sqrtSteps edge))
        (evalReal v (ceffE logTerms sqrtSteps edge)) /
        evalReal v (qmaxE sqrtSteps edge) := by
  have hbase := rectangleBaseLowerE_le
    (logTerms := logTerms) (trigDoubles := trigDoubles) hN hpi
    hqCapPos hqCapPi hrCapPos hrCapPi hqPos hrPos hqCap hrCap
  have hpenalty := penaltyE_eval_of_pi logTerms sqrtSteps edge hpi
  change evalReal v
      (rectangleBaseLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap) +
        evalReal v (penaltyE logTerms sqrtSteps edge) /
          evalReal v (qmaxE sqrtSteps edge) ≤ _
  rw [hpenalty]
  linarith

theorem affineLeftLowerE_le
    {v : Fin 5 → ℝ} {logTerms sqrtSteps trigDoubles N : ℕ}
    {edge : HighKPlatformEdge} {qCap rCap : Rat}
    (hN : 0 < N)
    (hpi : evalReal v piE = Real.pi)
    (hqCapPos : 0 < (qCap : ℝ)) (hqCapPi : (qCap : ℝ) ≤ Real.pi)
    (hrCapPos : 0 < (rCap : ℝ)) (hrCapPi : (rCap : ℝ) ≤ Real.pi)
    (hqPos : 0 < evalReal v (qmaxE sqrtSteps edge))
    (hrPos : 0 < evalReal v (rmaxE sqrtSteps edge))
    (hqCap : evalReal v (qmaxE sqrtSteps edge) ≤ (qCap : ℝ))
    (hrCap : evalReal v (rmaxE sqrtSteps edge) ≤ (rCap : ℝ)) :
    evalReal v (affineLeftLowerE logTerms sqrtSteps trigDoubles N
      edge qCap rCap) ≤
      circleRectangleBase
        (evalReal v (capacityE edge))
        (evalReal v (apiE sqrtSteps edge))
        (evalReal v (bpiE sqrtSteps edge))
        (evalReal v (qmaxE sqrtSteps edge))
        (evalReal v (rmaxE sqrtSteps edge)) +
      circleEffectivePenalty (evalReal v (apiE sqrtSteps edge))
        (evalReal v (ceffE logTerms sqrtSteps edge)) /
        evalReal v (rmaxE sqrtSteps edge) := by
  have hbase := rectangleBaseLowerE_le
    (logTerms := logTerms) (trigDoubles := trigDoubles) hN hpi
    hqCapPos hqCapPi hrCapPos hrCapPi hqPos hrPos hqCap hrCap
  have hpenalty := penaltyE_eval_of_pi logTerms sqrtSteps edge hpi
  change evalReal v
      (rectangleBaseLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap) +
        evalReal v (penaltyE logTerms sqrtSteps edge) /
          evalReal v (rmaxE sqrtSteps edge) ≤ _
  rw [hpenalty]
  linarith

theorem affineCornerLowerE_le
    {v : Fin 5 → ℝ} {logTerms sqrtSteps trigDoubles N : ℕ}
    {edge : HighKPlatformEdge} {qCap rCap : Rat}
    (hN : 0 < N)
    (hpi : evalReal v piE = Real.pi)
    (hqCapPos : 0 < (qCap : ℝ)) (hqCapPi : (qCap : ℝ) ≤ Real.pi)
    (hrCapPos : 0 < (rCap : ℝ)) (hrCapPi : (rCap : ℝ) ≤ Real.pi)
    (hqPos : 0 < evalReal v (qmaxE sqrtSteps edge))
    (hrPos : 0 < evalReal v (rmaxE sqrtSteps edge))
    (hqCap : evalReal v (qmaxE sqrtSteps edge) ≤ (qCap : ℝ))
    (hrCap : evalReal v (rmaxE sqrtSteps edge) ≤ (rCap : ℝ)) :
    evalReal v (affineCornerLowerE logTerms sqrtSteps trigDoubles N
      edge qCap rCap) ≤
      affineCircleScalar
        (evalReal v (capacityE edge))
        (evalReal v (apiE sqrtSteps edge))
        (evalReal v (bpiE sqrtSteps edge))
        (evalReal v (ceffE logTerms sqrtSteps edge))
        (evalReal v (rmaxE sqrtSteps edge))
        (evalReal v (qmaxE sqrtSteps edge))
        (evalReal v (qmaxE sqrtSteps edge)) := by
  have hbase := rectangleBaseLowerE_le
    (logTerms := logTerms) (trigDoubles := trigDoubles) hN hpi
    hqCapPos hqCapPi hrCapPos hrCapPi hqPos hrPos hqCap hrCap
  have hqne := hqPos.ne'
  have hrne := hrPos.ne'
  have hsqQ := sincE_eval trigDoubles (qmaxE sqrtSteps edge) v hqne
  have hsqR := sincE_eval trigDoubles (rmaxE sqrtSteps edge) v hrne
  have hpenalty := penaltyE_eval_of_pi logTerms sqrtSteps edge hpi
  simp only [affineCornerLowerE, evalReal, evalReal_div,
    evalReal_sq, evalReal_sub]
  rw [hsqQ, hsqR, hpenalty]
  unfold affineCircleScalar
  linarith

/-- Exact interval predicates sufficient for a constant-edge scalar
certificate.  Every predicate is executable on rational data. -/
theorem constantEdgeCertificate_of_interval
    {X : Fin 5 → RatInterval} {v : Fin 5 → ℝ}
    {logTerms sqrtSteps trigDoubles N : ℕ}
    {edge : HighKPlatformEdge} {qCap rCap : Rat}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (v i))
    (hN : 0 < N)
    (hpi : evalReal v piE = Real.pi)
    (hqCapPos : 0 < (qCap : ℝ)) (hqCapPi : (qCap : ℝ) ≤ Real.pi)
    (hrCapPos : 0 < (rCap : ℝ)) (hrCapPi : (rCap : ℝ) ≤ Real.pi)
    (haPi : EvalPositive X (apiE sqrtSteps edge))
    (hQmax : EvalPositive X (qmaxE sqrtSteps edge))
    (hRmax : EvalPositive X (rmaxE sqrtSteps edge))
    (hQcap : EvalNegative X
      (.sub (qmaxE sqrtSteps edge) (.rat qCap)))
    (hRcap : EvalNegative X
      (.sub (rmaxE sqrtSteps edge) (.rat rCap)))
    (hCeff : EvalNegative X (ceffE logTerms sqrtSteps edge))
    (hendpoint : EvalPositive X
      (constantEndpointLowerE logTerms sqrtSteps trigDoubles N
        edge qCap rCap)) :
    ConstantEdgeCircleCertificate
      (evalReal v (capacityE edge))
      (evalReal v (apiE sqrtSteps edge))
      (evalReal v (bpiE sqrtSteps edge))
      (evalReal v (ceffE logTerms sqrtSteps edge))
      (evalReal v (qmaxE sqrtSteps edge))
      (evalReal v (rmaxE sqrtSteps edge)) := by
  have haPi' := evalPositive_sound hordered hcontains haPi
  have hQmax' := evalPositive_sound hordered hcontains hQmax
  have hRmax' := evalPositive_sound hordered hcontains hRmax
  have hQcap' := evalNegative_sound hordered hcontains hQcap
  have hRcap' := evalNegative_sound hordered hcontains hRcap
  have hCeff' := evalNegative_sound hordered hcontains hCeff
  have hendpoint' := evalPositive_sound hordered hcontains hendpoint
  have hQle : evalReal v (qmaxE sqrtSteps edge) ≤ (qCap : ℝ) := by
    simpa [HighKIntervalExpr.sub] using! hQcap'.le
  have hRle : evalReal v (rmaxE sqrtSteps edge) ≤ (rCap : ℝ) := by
    simpa [HighKIntervalExpr.sub] using! hRcap'.le
  have hlower := constantEndpointLowerE_le
    (logTerms := logTerms) (trigDoubles := trigDoubles) hN hpi
    hqCapPos hqCapPi hrCapPos hrCapPi hQmax' hRmax' hQle hRle
  refine ⟨haPi', hQmax', hQle.trans hqCapPi, hRmax',
    hRle.trans hrCapPi, hCeff'.le, ?_⟩
  exact hendpoint'.trans_le hlower

/-- Exact-rational interval predicates plus a finite `Q`-box cover are
sufficient for the affine scalar certificate. -/
theorem affineEdgeCertificate_of_interval
    {X : Fin 5 → RatInterval} {v : Fin 5 → ℝ}
    {logTerms sqrtSteps trigDoubles N : ℕ}
    {edge : HighKPlatformEdge} {qCap rCap : Rat}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (v i))
    (hN : 0 < N)
    (hpi : evalReal v piE = Real.pi)
    (hqCapPos : 0 < (qCap : ℝ)) (hqCapPi : (qCap : ℝ) ≤ Real.pi)
    (hrCapPos : 0 < (rCap : ℝ)) (hrCapPi : (rCap : ℝ) ≤ Real.pi)
    (haPi : EvalPositive X (apiE sqrtSteps edge))
    (hQmax : EvalPositive X (qmaxE sqrtSteps edge))
    (hRmax : EvalPositive X (rmaxE sqrtSteps edge))
    (hRltQ : EvalNegative X
      (.sub (rmaxE sqrtSteps edge) (qmaxE sqrtSteps edge)))
    (hQcap : EvalNegative X
      (.sub (qmaxE sqrtSteps edge) (.rat qCap)))
    (hRcap : EvalNegative X
      (.sub (rmaxE sqrtSteps edge) (.rat rCap)))
    (hCeff : EvalNegative X (ceffE logTerms sqrtSteps edge))
    (hleft : EvalPositive X
      (affineLeftLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap))
    (hcorner : EvalPositive X
      (affineCornerLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap))
    (hderivative : AffineDerivativeBoxCertificate X
      logTerms sqrtSteps trigDoubles edge) :
    AffineCircleCertificate
      (evalReal v (capacityE edge))
      (evalReal v (apiE sqrtSteps edge))
      (evalReal v (bpiE sqrtSteps edge))
      (evalReal v (ceffE logTerms sqrtSteps edge))
      (evalReal v (qmaxE sqrtSteps edge))
      (evalReal v (rmaxE sqrtSteps edge)) := by
  have haPi' := evalPositive_sound hordered hcontains haPi
  have hQmax' := evalPositive_sound hordered hcontains hQmax
  have hRmax' := evalPositive_sound hordered hcontains hRmax
  have hRltQ' := evalNegative_sound hordered hcontains hRltQ
  have hQcap' := evalNegative_sound hordered hcontains hQcap
  have hRcap' := evalNegative_sound hordered hcontains hRcap
  have hCeff' := evalNegative_sound hordered hcontains hCeff
  have hleft' := evalPositive_sound hordered hcontains hleft
  have hcorner' := evalPositive_sound hordered hcontains hcorner
  have hRQ : evalReal v (rmaxE sqrtSteps edge) <
      evalReal v (qmaxE sqrtSteps edge) := by
    simpa [HighKIntervalExpr.sub] using! hRltQ'
  have hQle : evalReal v (qmaxE sqrtSteps edge) ≤ (qCap : ℝ) := by
    simpa [HighKIntervalExpr.sub] using! hQcap'.le
  have hRle : evalReal v (rmaxE sqrtSteps edge) ≤ (rCap : ℝ) := by
    simpa [HighKIntervalExpr.sub] using! hRcap'.le
  have hleftLower := affineLeftLowerE_le
    (logTerms := logTerms) (trigDoubles := trigDoubles) hN hpi
    hqCapPos hqCapPi hrCapPos hrCapPi hQmax' hRmax' hQle hRle
  have hcornerLower := affineCornerLowerE_le
    (logTerms := logTerms) (trigDoubles := trigDoubles) hN hpi
    hqCapPos hqCapPi hrCapPos hrCapPi hQmax' hRmax' hQle hRle
  refine ⟨haPi', hRmax', hRQ, hQle.trans hqCapPi, hCeff',
    hleft'.trans_le hleftLower, hcorner'.trans_le hcornerLower, ?_⟩
  exact affineDerivative_neg_of_boxCertificate hderivative
    hordered hcontains hpi hRmax'

/-- Platform-specialized affine transfer theorem. -/
theorem platformAffineCalibration_of_interval
    {X : Fin 5 → RatInterval} {k xm xp ell : ℝ}
    {logTerms sqrtSteps trigDoubles N : ℕ}
    {edge : HighKPlatformEdge} {qCap rCap : Rat}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i,
      (X i).Contains (![k, xm, xp, ell, Real.pi] i))
    (hxm : xm < highKPlatformEdge edge k)
    (hxp : xp < highKPlatformEdge edge k)
    (ha2 : highKPlatformEdge edge k < 2)
    (hN : 0 < N)
    (hqCapPos : 0 < (qCap : ℝ)) (hqCapPi : (qCap : ℝ) ≤ Real.pi)
    (hrCapPos : 0 < (rCap : ℝ)) (hrCapPi : (rCap : ℝ) ≤ Real.pi)
    (haPi : EvalPositive X (apiE sqrtSteps edge))
    (hQmax : EvalPositive X (qmaxE sqrtSteps edge))
    (hRmax : EvalPositive X (rmaxE sqrtSteps edge))
    (hRltQ : EvalNegative X
      (.sub (rmaxE sqrtSteps edge) (qmaxE sqrtSteps edge)))
    (hQcap : EvalNegative X
      (.sub (qmaxE sqrtSteps edge) (.rat qCap)))
    (hRcap : EvalNegative X
      (.sub (rmaxE sqrtSteps edge) (.rat rCap)))
    (hCeff : EvalNegative X (ceffE logTerms sqrtSteps edge))
    (hleft : EvalPositive X
      (affineLeftLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap))
    (hcorner : EvalPositive X
      (affineCornerLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap))
    (hderivative : AffineDerivativeBoxCertificate X
      logTerms sqrtSteps trigDoubles edge) :
    PlatformAffineCalibration k (highKPlatformEdge edge k) xm xp
      (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
      (1 / platformExteriorWx k (highKPlatformEdge edge k) xp)
      (platformEffectiveConstant ell k (highKPlatformEdge edge k) xm xp
        (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
        (1 / platformExteriorWx k (highKPlatformEdge edge k) xp)) := by
  have hcert := affineEdgeCertificate_of_interval hordered hcontains hN
    (by simp) hqCapPos hqCapPi hrCapPos hrCapPi haPi hQmax hRmax
      hRltQ hQcap hRcap hCeff hleft hcorner hderivative
  simpa only [PlatformAffineCalibration, capacityE_eval, apiE_eval,
    bpiE_eval sqrtSteps edge hxm hxp ha2,
    ceffE_eval logTerms sqrtSteps edge hxm hxp ha2,
    qmaxE_eval, rmaxE_eval sqrtSteps edge hxm hxp ha2] using! hcert

/-- Platform-specialized form of `constantEdgeCertificate_of_interval`. -/
theorem platformConstantEdgeCalibration_of_interval
    {X : Fin 5 → RatInterval} {k xm xp ell : ℝ}
    {logTerms sqrtSteps trigDoubles N : ℕ}
    {edge : HighKPlatformEdge} {qCap rCap : Rat}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i,
      (X i).Contains (![k, xm, xp, ell, Real.pi] i))
    (hxm : xm < highKPlatformEdge edge k)
    (hxp : xp < highKPlatformEdge edge k)
    (ha2 : highKPlatformEdge edge k < 2)
    (hN : 0 < N)
    (hqCapPos : 0 < (qCap : ℝ)) (hqCapPi : (qCap : ℝ) ≤ Real.pi)
    (hrCapPos : 0 < (rCap : ℝ)) (hrCapPi : (rCap : ℝ) ≤ Real.pi)
    (haPi : EvalPositive X (apiE sqrtSteps edge))
    (hQmax : EvalPositive X (qmaxE sqrtSteps edge))
    (hRmax : EvalPositive X (rmaxE sqrtSteps edge))
    (hQcap : EvalNegative X
      (.sub (qmaxE sqrtSteps edge) (.rat qCap)))
    (hRcap : EvalNegative X
      (.sub (rmaxE sqrtSteps edge) (.rat rCap)))
    (hCeff : EvalNegative X (ceffE logTerms sqrtSteps edge))
    (hendpoint : EvalPositive X
      (constantEndpointLowerE logTerms sqrtSteps trigDoubles N
        edge qCap rCap)) :
    PlatformConstantEdgeCalibration k (highKPlatformEdge edge k) xm xp
      (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
      (1 / platformExteriorWx k (highKPlatformEdge edge k) xp)
      (platformEffectiveConstant ell k (highKPlatformEdge edge k) xm xp
        (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
        (1 / platformExteriorWx k (highKPlatformEdge edge k) xp)) := by
  have hcert := constantEdgeCertificate_of_interval hordered hcontains hN
    (by simp) hqCapPos hqCapPi hrCapPos hrCapPi haPi hQmax hRmax
      hQcap hRcap hCeff hendpoint
  simpa only [PlatformConstantEdgeCalibration, capacityE_eval, apiE_eval,
    bpiE_eval sqrtSteps edge hxm hxp ha2,
    ceffE_eval logTerms sqrtSteps edge hxm hxp ha2,
    qmaxE_eval, rmaxE_eval sqrtSteps edge hxm hxp ha2] using! hcert

/-! ## Explicit crossing-branch certificate data -/

inductive PlatformCrossingSide where
  | minus
  | plus
deriving DecidableEq, Repr

inductive PlatformSlopeOrientation where
  | decreasing
  | increasing
deriving DecidableEq, Repr

def crossingWE (logTerms sqrtSteps : ℕ) (edge : HighKPlatformEdge) :
    PlatformCrossingSide → E
  | .minus => exteriorWE logTerms sqrtSteps edge true xmE
  | .plus => exteriorWE logTerms sqrtSteps edge false xpE

def crossingWxE (sqrtSteps : ℕ) (edge : HighKPlatformEdge) :
    PlatformCrossingSide → E
  | .minus => exteriorWxE sqrtSteps edge xmE
  | .plus => exteriorWxE sqrtSteps edge xpE

/-- Formal symbolic differentiation.  The crossing expressions use only the
first six cases; sine and cosine are included so the operation is reusable by
the scalar checker. -/
def diffExpr {n : ℕ} (i : Fin n) :
    HighKIntervalExpr n → HighKIntervalExpr n
  | .rat _ => .rat 0
  | .var j => if j = i then .rat 1 else .rat 0
  | .add p q => .add (diffExpr i p) (diffExpr i q)
  | .neg p => .neg (diffExpr i p)
  | .mul p q => .add (.mul (diffExpr i p) q) (.mul p (diffExpr i q))
  | .inv p => .neg (.div (diffExpr i p) (.sq p))
  | .log _ p => .div (diffExpr i p) p
  | .sqrt steps p => .div (diffExpr i p)
      (.mul (.rat 2) (.sqrt steps p))
  | .sin doubles p => .mul (.cos doubles p) (diffExpr i p)
  | .cos doubles p => .neg (.mul (.sin doubles p) (diffExpr i p))

/-- The implicit slope `-W_k/W_x`, with `x` held fixed in the symbolic
derivative and the dependence `a=a(k)` already present in `crossingWE`. -/
def crossingSlopeE (logTerms sqrtSteps : ℕ)
    (edge : HighKPlatformEdge) (side : PlatformCrossingSide) : E :=
  .neg (.div (diffExpr 0 (crossingWE logTerms sqrtSteps edge side))
    (crossingWxE sqrtSteps edge side))

def crossingBracketSigns (side : PlatformCrossingSide)
    (left right : Fin 5 → RatInterval) (w : E) : Prop :=
  match side with
  | .minus => EvalPositive left w ∧ EvalNegative right w
  | .plus => EvalNegative left w ∧ EvalPositive right w

def crossingWxSign (side : PlatformCrossingSide)
    (X : Fin 5 → RatInterval) (wx : E) : Prop :=
  match side with
  | .minus => EvalNegative X wx
  | .plus => EvalPositive X wx

def slopeBoxSign (orientation : PlatformSlopeOrientation)
    (I : RatInterval) : Prop :=
  match orientation with
  | .decreasing => I.hi < 0
  | .increasing => 0 < I.lo

/-- The exact finite data used by the external verifier to transport its two
crossing roots across a parameter slab.  Endpoint sign brackets, the uniform
`W_x` sign, and the implicit-slope enclosure are separate fields so none can
be silently inferred from floating-point root finding. -/
structure PlatformCrossingBranchCertificate
    (logTerms sqrtSteps : ℕ) (edge : HighKPlatformEdge)
    (side : PlatformCrossingSide) where
  atLoLeft : Fin 5 → RatInterval
  atLoRight : Fin 5 → RatInterval
  atHiLeft : Fin 5 → RatInterval
  atHiRight : Fin 5 → RatInterval
  envelope : Fin 5 → RatInterval
  orientation : PlatformSlopeOrientation
  slopeBox : RatInterval
  atLoLeft_ordered : ∀ i, (atLoLeft i).Ordered
  atLoRight_ordered : ∀ i, (atLoRight i).Ordered
  atHiLeft_ordered : ∀ i, (atHiLeft i).Ordered
  atHiRight_ordered : ∀ i, (atHiRight i).Ordered
  envelope_ordered : ∀ i, (envelope i).Ordered
  atLo_signs : crossingBracketSigns side atLoLeft atLoRight
    (crossingWE logTerms sqrtSteps edge side)
  atHi_signs : crossingBracketSigns side atHiLeft atHiRight
    (crossingWE logTerms sqrtSteps edge side)
  wx_sign : crossingWxSign side envelope
    (crossingWxE sqrtSteps edge side)
  slope_eval : evalInterval envelope
    (crossingSlopeE logTerms sqrtSteps edge side) = some slopeBox
  slope_ordered : slopeBox.Ordered
  slope_sign : slopeBoxSign orientation slopeBox

end HighKPlatformFormula

end

end Erdos1038
