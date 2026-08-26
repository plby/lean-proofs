import ErdosProblems.Erdos1038.HighKPlatformGlobalCrossingRestriction

/-!
# Reusable exact certificates for constant-edge parameter cells

The constant part of the high-`k` cover consists of 840 adjacent cells of
width `1 / 400`.  This module isolates all analytic and bookkeeping work that
is common to those cells.  A concrete cell supplies only four rational
endpoints, two rational scalar caps, and the finite interval-check results.
-/

set_option warningAsError false
set_option maxHeartbeats 4000000

namespace Erdos1038.HighKPlatformConstantCell

open Erdos1038 Set RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformCrossingCertificates
open Erdos1038.HighKPlatformGlobalCrossingProbes
open Erdos1038.HighKPlatformGlobalCrossingCertificates
open Erdos1038.HighKPlatformGlobalCrossingRestriction

/-- Uniform approximation depths used by the constant-edge grid. -/
def logTerms : ℕ := 80
def sqrtSteps : ℕ := 64

/-- Independent, shallower depths suffice for the scalar lower bound.  The
exact-real semantics are independent of these approximation parameters. -/
def scalarLogTerms : ℕ := 24
def scalarSqrtSteps : ℕ := 16
def scalarTrigDoubles : ℕ := 8
def scalarFourierTerms : ℕ := 16

def zeroBox : RatInterval := point 0

/-- The rigorous target-length enclosure available from the closed one-cut
certificate.  Using this (slightly wider) box makes the generated scalar
certificate directly applicable to the exact constant `L`. -/
def ellBox : RatInterval :=
  ⟨1834430475762661 / 10 ^ 15, 1834430475762662 / 10 ^ 15⟩

theorem ellBox_ordered : ellBox.Ordered := by
  norm_num [ellBox, RatInterval.Ordered]

/-- Exact indexing data for the constant regime. -/
def cellCount : ℕ := 840
def chunkSize : ℕ := 20
def chunkCount : ℕ := 42
def gridStart : Rat := 21 / 10
def gridStep : Rat := 1 / 400
def gridEnd : Rat := 21 / 5

def gridKLo (i : Fin cellCount) : Rat :=
  gridStart + (i.val : Rat) * gridStep

def gridKHi (i : Fin cellCount) : Rat :=
  gridStart + ((i.val + 1 : ℕ) : Rat) * gridStep

/-- Row-major indexing used by the deterministic 42-by-20 build split. -/
def chunkIndex (q : Fin chunkCount) (r : Fin chunkSize) : Fin cellCount :=
  ⟨q.val * chunkSize + r.val, by
    have hq := q.isLt
    have hr := r.isLt
    norm_num [chunkCount, chunkSize, cellCount] at hq hr ⊢
    omega⟩

def chunkOf (i : Fin cellCount) : Fin chunkCount :=
  ⟨i.val / chunkSize, by
    have hi := i.isLt
    norm_num [cellCount, chunkSize, chunkCount] at hi ⊢
    omega⟩

def localOf (i : Fin cellCount) : Fin chunkSize :=
  ⟨i.val % chunkSize, Nat.mod_lt _ (by norm_num [chunkSize])⟩

@[simp] theorem chunkIndex_chunkOf_localOf (i : Fin cellCount) :
    chunkIndex (chunkOf i) (localOf i) = i := by
  apply Fin.ext
  simpa [chunkIndex, chunkOf, localOf, chunkSize] using!
    Nat.div_add_mod' i.val 20

/-- The 840 closed cells cover the complete constant-edge parameter range. -/
theorem exists_gridCell {k : ℝ}
    (hk : k ∈ Icc (gridStart : ℝ) (gridEnd : ℝ)) :
    ∃ i : Fin cellCount,
      k ∈ Icc (gridKLo i : ℝ) (gridKHi i : ℝ) := by
  have htop : (gridStart : ℝ) + cellCount * (gridStep : ℝ) =
      (gridEnd : ℝ) := by
    norm_num [gridStart, gridEnd, gridStep, cellCount]
  have hk' : k ∈ Icc (gridStart : ℝ)
      ((gridStart : ℝ) + cellCount * (gridStep : ℝ)) := by
    rwa [htop]
  obtain ⟨i, hi⟩ := exists_uniformGrid_cell
    (start := (gridStart : ℝ)) (step := (gridStep : ℝ))
    (N := cellCount) (by norm_num [gridStep])
      (by norm_num [cellCount]) hk'
  refine ⟨i, ?_⟩
  simpa [gridKLo, gridKHi] using! hi

/-- The six rational inputs that vary from one constant-edge cell to another. -/
structure Data where
  kLo : Rat
  kHi : Rat
  xmBox : RatInterval
  xpBox : RatInterval
  qCap : Rat
  rCap : Rat
deriving Repr

namespace Data

def kBox (d : Data) : RatInterval := ⟨d.kLo, d.kHi⟩

/-- A point environment for one side of an endpoint bracket. -/
def endpoint (_d : Data) (side : PlatformCrossingSide)
    (k x : Rat) : Fin 5 → RatInterval :=
  match side with
  | .minus => ![point k, point x, zeroBox, zeroBox, zeroBox]
  | .plus => ![point k, zeroBox, point x, zeroBox, zeroBox]

/-- The complete `(k,x)` rectangle for a crossing branch. -/
def envelope (d : Data) (side : PlatformCrossingSide) :
    Fin 5 → RatInterval :=
  match side with
  | .minus => ![d.kBox, d.xmBox, zeroBox, zeroBox, zeroBox]
  | .plus => ![d.kBox, zeroBox, d.xpBox, zeroBox, zeroBox]

def slopeBox (d : Data) (side : PlatformCrossingSide) : RatInterval :=
  (evalInterval (d.envelope side)
    (crossingSlopeE logTerms sqrtSteps .constant side)).getD zeroBox

def correctionE (side : PlatformCrossingSide) : HighKIntervalExpr 5 :=
  match side with
  | .minus =>
      .sub e1 (.mul (rhoZeroE sqrtSteps .constant)
        (rhoE sqrtSteps .constant xmE))
  | .plus =>
      .sub e1 (.mul (rhoZeroE sqrtSteps .constant)
        (rhoE sqrtSteps .constant xpE))

/-- The scalar box uses the common exact target-length and `pi` enclosures. -/
def boxes (d : Data) : Fin 5 → RatInterval :=
  ![d.kBox, d.xmBox, d.xpBox,
    ellBox,
    Erdos1038.HighKPlatformIntervalSmoke.piBox]

end Data

/-- Elementary rational geometry needed by the analytic crossing theorem. -/
structure Geometry (d : Data) : Prop where
  k_lt : d.kLo < d.kHi
  xm_lt : d.xmBox.lo < d.xmBox.hi
  xp_lt : d.xpBox.lo < d.xpBox.hi
  xm_negative : d.xmBox.hi < 0
  xp_positive : 0 < d.xpBox.lo
  xm_lt_edge : d.xmBox.hi < 9 / 5
  xp_lt_edge : d.xpBox.hi < 9 / 5
  k_global_lo : constantKBox.lo ≤ d.kLo
  k_global_hi : d.kHi ≤ constantKBox.hi
  xm_global_lo : constantXmBox.lo ≤ d.xmBox.lo
  xm_global_hi : d.xmBox.hi ≤ constantXmBox.hi
  xp_global_lo : constantXpBox.lo ≤ d.xpBox.lo
  xp_global_hi : d.xpBox.hi ≤ constantXpBox.hi

/-- The finite crossing checks for one cell.  Both constant-edge roots move
to the left as `k` increases, hence both slope boxes have the decreasing
orientation. -/
structure CrossingChecks (d : Data) : Prop where
  minusAtLo_signs : crossingBracketSigns .minus
    (d.endpoint .minus d.kLo d.xmBox.lo)
    (d.endpoint .minus d.kLo d.xmBox.hi)
    (crossingWE logTerms sqrtSteps .constant .minus)
  minusAtHi_signs : crossingBracketSigns .minus
    (d.endpoint .minus d.kHi d.xmBox.lo)
    (d.endpoint .minus d.kHi d.xmBox.hi)
    (crossingWE logTerms sqrtSteps .constant .minus)
  plusAtLo_signs : crossingBracketSigns .plus
    (d.endpoint .plus d.kLo d.xpBox.lo)
    (d.endpoint .plus d.kLo d.xpBox.hi)
    (crossingWE logTerms sqrtSteps .constant .plus)
  plusAtHi_signs : crossingBracketSigns .plus
    (d.endpoint .plus d.kHi d.xpBox.lo)
    (d.endpoint .plus d.kHi d.xpBox.hi)
    (crossingWE logTerms sqrtSteps .constant .plus)
  minusWx_sign : crossingWxSign .minus (d.envelope .minus)
    (crossingWxE sqrtSteps .constant .minus)
  plusWx_sign : crossingWxSign .plus (d.envelope .plus)
    (crossingWxE sqrtSteps .constant .plus)
  minusSlope_eval : evalInterval (d.envelope .minus)
    (crossingSlopeE logTerms sqrtSteps .constant .minus) =
      some (d.slopeBox .minus)
  plusSlope_eval : evalInterval (d.envelope .plus)
    (crossingSlopeE logTerms sqrtSteps .constant .plus) =
      some (d.slopeBox .plus)
  minusSlope_ordered : (d.slopeBox .minus).Ordered
  plusSlope_ordered : (d.slopeBox .plus).Ordered
  minusSlope_negative : slopeBoxSign .decreasing (d.slopeBox .minus)
  plusSlope_negative : slopeBoxSign .decreasing (d.slopeBox .plus)
  minusDiffDomain_check : diffDomainCheck (d.envelope .minus)
    (crossingWE logTerms sqrtSteps .constant .minus) = true
  plusDiffDomain_check : diffDomainCheck (d.envelope .plus)
    (crossingWE logTerms sqrtSteps .constant .plus) = true
  minusCorrection_check : evalNonzeroCheck (d.envelope .minus)
    (Data.correctionE .minus) = true
  plusCorrection_check : evalNonzeroCheck (d.envelope .plus)
    (Data.correctionE .plus) = true

/-- The seven semantic scalar checks plus elementary cap bounds. -/
structure ScalarChecks (d : Data) : Prop where
  qCap_positive : 0 < d.qCap
  qCap_le_three : d.qCap ≤ 3
  rCap_positive : 0 < d.rCap
  rCap_le_three : d.rCap ≤ 3
  api : EvalPositive d.boxes (apiE scalarSqrtSteps .constant)
  qmax : EvalPositive d.boxes (qmaxE scalarSqrtSteps .constant)
  rmax : EvalPositive d.boxes (rmaxE scalarSqrtSteps .constant)
  qcap : EvalNegative d.boxes
    (.sub (qmaxE scalarSqrtSteps .constant) (.rat d.qCap))
  rcap : EvalNegative d.boxes
    (.sub (rmaxE scalarSqrtSteps .constant) (.rat d.rCap))
  ceff : EvalNegative d.boxes
    (ceffE scalarLogTerms scalarSqrtSteps .constant)
  endpoint : EvalPositive d.boxes
    (constantEndpointLowerE scalarLogTerms scalarSqrtSteps
      scalarTrigDoubles scalarFourierTerms .constant d.qCap d.rCap)

/-- Complete proof object for a constant-edge cell. -/
structure Certificate (d : Data) : Prop where
  geometry : Geometry d
  crossing : CrossingChecks d
  scalar : ScalarChecks d

/-! ## Single-Boolean executable interface

Generated chunks prove one finite universal Boolean statement.  The lemmas
below turn that computation into the semantic certificate structure, avoiding
thousands of repeated proof declarations in generated source.
-/

def geometryCheck (d : Data) : Bool := decide
  (d.kLo < d.kHi ∧ d.xmBox.lo < d.xmBox.hi ∧
    d.xpBox.lo < d.xpBox.hi ∧ d.xmBox.hi < 0 ∧
    0 < d.xpBox.lo ∧ d.xmBox.hi < 9 / 5 ∧
    d.xpBox.hi < 9 / 5 ∧
    constantKBox.lo ≤ d.kLo ∧ d.kHi ≤ constantKBox.hi ∧
    constantXmBox.lo ≤ d.xmBox.lo ∧ d.xmBox.hi ≤ constantXmBox.hi ∧
    constantXpBox.lo ≤ d.xpBox.lo ∧ d.xpBox.hi ≤ constantXpBox.hi)

def slopeCheck (d : Data) (side : PlatformCrossingSide) : Bool :=
  match evalInterval (d.envelope side)
      (crossingSlopeE logTerms sqrtSteps .constant side) with
  | none => false
  | some I => decide (I.lo ≤ I.hi ∧ I.hi < 0)

def crossingCheck (d : Data) : Bool := decide
  (evalPositiveCheck (d.endpoint .minus d.kLo d.xmBox.lo)
      (crossingWE logTerms sqrtSteps .constant .minus) = true ∧
    evalNegativeCheck (d.endpoint .minus d.kLo d.xmBox.hi)
      (crossingWE logTerms sqrtSteps .constant .minus) = true ∧
    evalPositiveCheck (d.endpoint .minus d.kHi d.xmBox.lo)
      (crossingWE logTerms sqrtSteps .constant .minus) = true ∧
    evalNegativeCheck (d.endpoint .minus d.kHi d.xmBox.hi)
      (crossingWE logTerms sqrtSteps .constant .minus) = true ∧
    evalNegativeCheck (d.endpoint .plus d.kLo d.xpBox.lo)
      (crossingWE logTerms sqrtSteps .constant .plus) = true ∧
    evalPositiveCheck (d.endpoint .plus d.kLo d.xpBox.hi)
      (crossingWE logTerms sqrtSteps .constant .plus) = true ∧
    evalNegativeCheck (d.endpoint .plus d.kHi d.xpBox.lo)
      (crossingWE logTerms sqrtSteps .constant .plus) = true ∧
    evalPositiveCheck (d.endpoint .plus d.kHi d.xpBox.hi)
      (crossingWE logTerms sqrtSteps .constant .plus) = true ∧
    evalNegativeCheck (d.envelope .minus)
      (crossingWxE sqrtSteps .constant .minus) = true ∧
    evalPositiveCheck (d.envelope .plus)
      (crossingWxE sqrtSteps .constant .plus) = true ∧
    slopeCheck d .minus = true ∧ slopeCheck d .plus = true ∧
    diffDomainCheck (d.envelope .minus)
      (crossingWE logTerms sqrtSteps .constant .minus) = true ∧
    diffDomainCheck (d.envelope .plus)
      (crossingWE logTerms sqrtSteps .constant .plus) = true ∧
    evalNonzeroCheck (d.envelope .minus) (Data.correctionE .minus) = true ∧
    evalNonzeroCheck (d.envelope .plus) (Data.correctionE .plus) = true)

def scalarCheck (d : Data) : Bool := decide
  (0 < d.qCap ∧ d.qCap ≤ 3 ∧ 0 < d.rCap ∧ d.rCap ≤ 3 ∧
    evalPositiveCheck d.boxes (apiE scalarSqrtSteps .constant) = true ∧
    evalPositiveCheck d.boxes (qmaxE scalarSqrtSteps .constant) = true ∧
    evalPositiveCheck d.boxes (rmaxE scalarSqrtSteps .constant) = true ∧
    evalNegativeCheck d.boxes
      (.sub (qmaxE scalarSqrtSteps .constant) (.rat d.qCap)) = true ∧
    evalNegativeCheck d.boxes
      (.sub (rmaxE scalarSqrtSteps .constant) (.rat d.rCap)) = true ∧
    evalNegativeCheck d.boxes
      (ceffE scalarLogTerms scalarSqrtSteps .constant) = true ∧
    evalPositiveCheck d.boxes
      (constantEndpointLowerE scalarLogTerms scalarSqrtSteps
        scalarTrigDoubles scalarFourierTerms .constant d.qCap d.rCap) = true)

def certificateCheck (d : Data) : Bool :=
  geometryCheck d && crossingCheck d && scalarCheck d

theorem geometry_of_check {d : Data} (h : geometryCheck d = true) :
    Geometry d := by
  have hp : d.kLo < d.kHi ∧ d.xmBox.lo < d.xmBox.hi ∧
      d.xpBox.lo < d.xpBox.hi ∧ d.xmBox.hi < 0 ∧
      0 < d.xpBox.lo ∧ d.xmBox.hi < 9 / 5 ∧
      d.xpBox.hi < 9 / 5 ∧
      constantKBox.lo ≤ d.kLo ∧ d.kHi ≤ constantKBox.hi ∧
      constantXmBox.lo ≤ d.xmBox.lo ∧ d.xmBox.hi ≤ constantXmBox.hi ∧
      constantXpBox.lo ≤ d.xpBox.lo ∧ d.xpBox.hi ≤ constantXpBox.hi := by
    simpa [geometryCheck] using! h
  rcases hp with ⟨hk, hxm, hxp, hxm0, hxp0, hxma, hxpa,
    hklo, hkhi, hxmlo, hxmhi, hxplo, hxphi⟩
  exact ⟨hk, hxm, hxp, hxm0, hxp0, hxma, hxpa,
    hklo, hkhi, hxmlo, hxmhi, hxplo, hxphi⟩

theorem slopeFacts_of_check {d : Data} {side : PlatformCrossingSide}
    (h : slopeCheck d side = true) :
    evalInterval (d.envelope side)
        (crossingSlopeE logTerms sqrtSteps .constant side) =
        some (d.slopeBox side) ∧
      (d.slopeBox side).Ordered ∧ (d.slopeBox side).hi < 0 := by
  cases heval : evalInterval (d.envelope side)
      (crossingSlopeE logTerms sqrtSteps .constant side) with
  | none => simp [slopeCheck, heval] at h
  | some I =>
      have hI : I.lo ≤ I.hi ∧ I.hi < 0 := by
        simpa [slopeCheck, heval] using! h
      refine ⟨?_, ?_, ?_⟩
      · simp [Data.slopeBox, heval]
      · simpa [Data.slopeBox, heval, RatInterval.Ordered] using! hI.1
      · simpa [Data.slopeBox, heval] using! hI.2

theorem crossing_of_check {d : Data} (h : crossingCheck d = true) :
    CrossingChecks d := by
  have hp := of_decide_eq_true h
  rcases hp with ⟨hmll, hmlr, hmhl, hmhr, hpll, hplr, hphl, hphr,
    hmwx, hpwx, hms, hps, hmd, hpd, hmc, hpc⟩
  have hmSlope := slopeFacts_of_check hms
  have hpSlope := slopeFacts_of_check hps
  exact {
    minusAtLo_signs := ⟨evalPositive_of_check hmll,
      evalNegative_of_check hmlr⟩
    minusAtHi_signs := ⟨evalPositive_of_check hmhl,
      evalNegative_of_check hmhr⟩
    plusAtLo_signs := ⟨evalNegative_of_check hpll,
      evalPositive_of_check hplr⟩
    plusAtHi_signs := ⟨evalNegative_of_check hphl,
      evalPositive_of_check hphr⟩
    minusWx_sign := evalNegative_of_check hmwx
    plusWx_sign := evalPositive_of_check hpwx
    minusSlope_eval := hmSlope.1
    plusSlope_eval := hpSlope.1
    minusSlope_ordered := hmSlope.2.1
    plusSlope_ordered := hpSlope.2.1
    minusSlope_negative := hmSlope.2.2
    plusSlope_negative := hpSlope.2.2
    minusDiffDomain_check := hmd
    plusDiffDomain_check := hpd
    minusCorrection_check := hmc
    plusCorrection_check := hpc
  }

theorem scalar_of_check {d : Data} (h : scalarCheck d = true) :
    ScalarChecks d := by
  have hp := of_decide_eq_true h
  rcases hp with ⟨hq0, hq3, hr0, hr3, ha, hq, hr, hqc, hrc, hc, he⟩
  exact {
    qCap_positive := hq0
    qCap_le_three := hq3
    rCap_positive := hr0
    rCap_le_three := hr3
    api := evalPositive_of_check ha
    qmax := evalPositive_of_check hq
    rmax := evalPositive_of_check hr
    qcap := evalNegative_of_check hqc
    rcap := evalNegative_of_check hrc
    ceff := evalNegative_of_check hc
    endpoint := evalPositive_of_check he
  }

theorem certificate_of_check {d : Data} (h : certificateCheck d = true) :
    Certificate d := by
  have hp : (geometryCheck d = true ∧ crossingCheck d = true) ∧
      scalarCheck d = true := by
    simpa [certificateCheck] using! h
  exact ⟨geometry_of_check hp.1.1, crossing_of_check hp.1.2,
    scalar_of_check hp.2⟩

/-- Raw per-cell table.  A generated 840-cell certificate file needs to list
only these four interval/cap arrays; parameter endpoints come from the exact
uniform grid above. -/
structure Table where
  xmBox : Fin cellCount → RatInterval
  xpBox : Fin cellCount → RatInterval
  qCap : Fin cellCount → Rat
  rCap : Fin cellCount → Rat

namespace Table

def cell (t : Table) (i : Fin cellCount) : Data where
  kLo := gridKLo i
  kHi := gridKHi i
  xmBox := t.xmBox i
  xpBox := t.xpBox i
  qCap := t.qCap i
  rCap := t.rCap i

end Table

/-- A single indexed family of proofs is the complete 840-cell certificate. -/
structure TableCertificate (t : Table) : Prop where
  cell : ∀ i : Fin cellCount, Certificate (t.cell i)

namespace Data

theorem endpoint_ordered (d : Data) (side : PlatformCrossingSide)
    (k x : Rat) : ∀ i, (d.endpoint side k x i).Ordered := by
  intro i
  cases side <;> fin_cases i <;>
    simp [endpoint, zeroBox, point, RatInterval.Ordered]

theorem envelope_ordered (d : Data) (h : Geometry d)
    (side : PlatformCrossingSide) :
    ∀ i, (d.envelope side i).Ordered := by
  intro i
  cases side <;> fin_cases i <;>
    simp [envelope, kBox, zeroBox, point, RatInterval.Ordered,
      h.k_lt.le, h.xm_lt.le, h.xp_lt.le]

theorem boxes_ordered (d : Data) (h : Geometry d) :
    ∀ i, (d.boxes i).Ordered := by
  intro i
  fin_cases i
  · simpa [boxes, kBox, RatInterval.Ordered] using! h.k_lt.le
  · simpa [boxes, RatInterval.Ordered] using! h.xm_lt.le
  · simpa [boxes, RatInterval.Ordered] using! h.xp_lt.le
  · simpa [boxes] using!
      ellBox_ordered
  · simpa [boxes] using!
      Erdos1038.HighKPlatformIntervalSmoke.boxes_ordered 4

theorem endpoint_contains (d : Data) (side : PlatformCrossingSide)
    (k x : Rat) : ∀ i,
    (d.endpoint side k x i).Contains
      (crossingEnvironment side (k : ℝ) (x : ℝ) 0 0 0 i) := by
  intro i
  cases side <;> fin_cases i <;>
    norm_num [endpoint, crossingEnvironment, zeroBox, point,
      RatInterval.Contains]

theorem envelope_contains (d : Data) (side : PlatformCrossingSide)
    {k x : ℝ}
    (hk : k ∈ Icc (d.kLo : ℝ) (d.kHi : ℝ))
    (hx : x ∈ match side with
      | .minus => Icc (d.xmBox.lo : ℝ) (d.xmBox.hi : ℝ)
      | .plus => Icc (d.xpBox.lo : ℝ) (d.xpBox.hi : ℝ)) : ∀ i,
    (d.envelope side i).Contains
      (crossingEnvironment side k x 0 0 0 i) := by
  cases side
  · intro i
    fin_cases i
    · simpa [envelope, kBox, RatInterval.Contains] using! hk
    · simpa [envelope, RatInterval.Contains] using! hx
    · norm_num [envelope, crossingEnvironment, zeroBox, point,
        RatInterval.Contains]
    · norm_num [envelope, crossingEnvironment, zeroBox, point,
        RatInterval.Contains]
    · norm_num [envelope, crossingEnvironment, zeroBox, point,
        RatInterval.Contains]
  · intro i
    fin_cases i
    · simpa [envelope, kBox, RatInterval.Contains] using! hk
    · norm_num [envelope, crossingEnvironment, zeroBox, point,
        RatInterval.Contains]
    · simpa [envelope, RatInterval.Contains] using! hx
    · norm_num [envelope, crossingEnvironment, zeroBox, point,
        RatInterval.Contains]
    · norm_num [envelope, crossingEnvironment, zeroBox, point,
        RatInterval.Contains]

def minusCertificate (d : Data) (h : Geometry d)
    (checks : CrossingChecks d) : PlatformCrossingBranchCertificate
    logTerms sqrtSteps .constant .minus where
  atLoLeft := d.endpoint .minus d.kLo d.xmBox.lo
  atLoRight := d.endpoint .minus d.kLo d.xmBox.hi
  atHiLeft := d.endpoint .minus d.kHi d.xmBox.lo
  atHiRight := d.endpoint .minus d.kHi d.xmBox.hi
  envelope := d.envelope .minus
  orientation := .decreasing
  slopeBox := d.slopeBox .minus
  atLoLeft_ordered := d.endpoint_ordered .minus _ _
  atLoRight_ordered := d.endpoint_ordered .minus _ _
  atHiLeft_ordered := d.endpoint_ordered .minus _ _
  atHiRight_ordered := d.endpoint_ordered .minus _ _
  envelope_ordered := d.envelope_ordered h .minus
  atLo_signs := checks.minusAtLo_signs
  atHi_signs := checks.minusAtHi_signs
  wx_sign := checks.minusWx_sign
  slope_eval := checks.minusSlope_eval
  slope_ordered := checks.minusSlope_ordered
  slope_sign := checks.minusSlope_negative

def plusCertificate (d : Data) (h : Geometry d)
    (checks : CrossingChecks d) : PlatformCrossingBranchCertificate
    logTerms sqrtSteps .constant .plus where
  atLoLeft := d.endpoint .plus d.kLo d.xpBox.lo
  atLoRight := d.endpoint .plus d.kLo d.xpBox.hi
  atHiLeft := d.endpoint .plus d.kHi d.xpBox.lo
  atHiRight := d.endpoint .plus d.kHi d.xpBox.hi
  envelope := d.envelope .plus
  orientation := .decreasing
  slopeBox := d.slopeBox .plus
  atLoLeft_ordered := d.endpoint_ordered .plus _ _
  atLoRight_ordered := d.endpoint_ordered .plus _ _
  atHiLeft_ordered := d.endpoint_ordered .plus _ _
  atHiRight_ordered := d.endpoint_ordered .plus _ _
  envelope_ordered := d.envelope_ordered h .plus
  atLo_signs := checks.plusAtLo_signs
  atHi_signs := checks.plusAtHi_signs
  wx_sign := checks.plusWx_sign
  slope_eval := checks.plusSlope_eval
  slope_ordered := checks.plusSlope_ordered
  slope_sign := checks.plusSlope_negative

theorem existsUnique_minusBranch (d : Data) (h : Geometry d)
    (checks : CrossingChecks d) :
    ∃! root : Icc (d.kLo : ℝ) (d.kHi : ℝ) → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc (d.xmBox.lo : ℝ) (d.xmBox.hi : ℝ) ∧
          platformExteriorW k (highKPlatformEdge .constant k) (root k) = 0 := by
  apply (d.minusCertificate h checks).existsUnique_continuous_crossing
      (other := 0) (ell := 0) (pi := 0)
  · exact_mod_cast h.k_lt.le
  · exact_mod_cast h.xm_lt.le
  · simpa [minusCertificate] using!
      d.endpoint_contains .minus d.kLo d.xmBox.lo
  · simpa [minusCertificate] using!
      d.endpoint_contains .minus d.kLo d.xmBox.hi
  · simpa [minusCertificate] using!
      d.endpoint_contains .minus d.kHi d.xmBox.lo
  · simpa [minusCertificate] using!
      d.endpoint_contains .minus d.kHi d.xmBox.hi
  · intro k hk x hx
    simpa [minusCertificate] using! d.envelope_contains .minus hk hx
  · intro x hx
    change x < 0
    have hnegative : (d.xmBox.hi : ℝ) < 0 := by
      exact_mod_cast h.xm_negative
    exact hx.2.trans_lt hnegative
  · intro k hk
    norm_num [highKPlatformEdge]
  · intro k hk x hx
    have hedge : (d.xmBox.hi : ℝ) < ((9 / 5 : Rat) : ℝ) := by
      exact_mod_cast h.xm_lt_edge
    simpa [highKPlatformEdge] using! hx.2.trans_lt hedge
  · intro k hk
    norm_num [highKPlatformEdge]
  · intro k hk x hx
    have hne := evalReal_ne_zero_of_check
      (d.minusCertificate h checks).envelope_ordered
      (d.envelope_contains .minus hk hx)
      checks.minusCorrection_check
    simpa [Data.correctionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  · intro k hk x hx
    exact diffDomain_of_check
      (d.minusCertificate h checks).envelope_ordered
      (d.envelope_contains .minus hk hx)
      (crossingWE logTerms sqrtSteps .constant .minus)
      checks.minusDiffDomain_check

theorem existsUnique_plusBranch (d : Data) (h : Geometry d)
    (checks : CrossingChecks d) :
    ∃! root : Icc (d.kLo : ℝ) (d.kHi : ℝ) → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc (d.xpBox.lo : ℝ) (d.xpBox.hi : ℝ) ∧
          platformExteriorW k (highKPlatformEdge .constant k) (root k) = 0 := by
  apply (d.plusCertificate h checks).existsUnique_continuous_crossing
      (other := 0) (ell := 0) (pi := 0)
  · exact_mod_cast h.k_lt.le
  · exact_mod_cast h.xp_lt.le
  · simpa [plusCertificate] using!
      d.endpoint_contains .plus d.kLo d.xpBox.lo
  · simpa [plusCertificate] using!
      d.endpoint_contains .plus d.kLo d.xpBox.hi
  · simpa [plusCertificate] using!
      d.endpoint_contains .plus d.kHi d.xpBox.lo
  · simpa [plusCertificate] using!
      d.endpoint_contains .plus d.kHi d.xpBox.hi
  · intro k hk x hx
    simpa [plusCertificate] using! d.envelope_contains .plus hk hx
  · intro x hx
    change 0 < x
    have hpositive : 0 < (d.xpBox.lo : ℝ) := by
      exact_mod_cast h.xp_positive
    exact hpositive.trans_le hx.1
  · intro k hk
    norm_num [highKPlatformEdge]
  · intro k hk x hx
    have hedge : (d.xpBox.hi : ℝ) < ((9 / 5 : Rat) : ℝ) := by
      exact_mod_cast h.xp_lt_edge
    simpa [highKPlatformEdge] using! hx.2.trans_lt hedge
  · intro k hk
    norm_num [highKPlatformEdge]
  · intro k hk x hx
    have hne := evalReal_ne_zero_of_check
      (d.plusCertificate h checks).envelope_ordered
      (d.envelope_contains .plus hk hx)
      checks.plusCorrection_check
    simpa [Data.correctionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  · intro k hk x hx
    exact diffDomain_of_check
      (d.plusCertificate h checks).envelope_ordered
      (d.envelope_contains .plus hk hx)
      (crossingWE logTerms sqrtSteps .constant .plus)
      checks.plusDiffDomain_check

theorem nonempty_crossingPair (d : Data) (h : Geometry d)
    (checks : CrossingChecks d) :
    Nonempty (ContinuousPlatformCrossingPair .constant
      (d.kLo : ℝ) (d.kHi : ℝ)
      (d.xmBox.lo : ℝ) (d.xmBox.hi : ℝ)
      (d.xpBox.lo : ℝ) (d.xpBox.hi : ℝ)) :=
  exists_crossingPair_of_uniqueBranches
    (d.existsUnique_minusBranch h checks)
    (d.existsUnique_plusBranch h checks)

end Data

/-- The locally tight crossing pair selected by a complete cell certificate. -/
noncomputable def crossingPair (d : Data) (cert : Certificate d) :
    ContinuousPlatformCrossingPair .constant
      (d.kLo : ℝ) (d.kHi : ℝ)
      (d.xmBox.lo : ℝ) (d.xmBox.hi : ℝ)
      (d.xpBox.lo : ℝ) (d.xpBox.hi : ℝ) :=
  Classical.choice (d.nonempty_crossingPair cert.geometry cert.crossing)

theorem parameter_mem_global (d : Data) (h : Geometry d)
    (k : Icc (d.kLo : ℝ) (d.kHi : ℝ)) :
    (k : ℝ) ∈ Icc (constantKBox.lo : ℝ) (constantKBox.hi : ℝ) := by
  have hlo : (constantKBox.lo : ℝ) ≤ (d.kLo : ℝ) := by
    exact_mod_cast h.k_global_lo
  have hhi : (d.kHi : ℝ) ≤ (constantKBox.hi : ℝ) := by
    exact_mod_cast h.k_global_hi
  exact ⟨hlo.trans k.property.1, k.property.2.trans hhi⟩

theorem minusBox_subset_global (d : Data) (h : Geometry d) :
    Icc (d.xmBox.lo : ℝ) (d.xmBox.hi : ℝ) ⊆
      Icc (constantXmBox.lo : ℝ) (constantXmBox.hi : ℝ) := by
  intro x hx
  have hlo : (constantXmBox.lo : ℝ) ≤ (d.xmBox.lo : ℝ) := by
    exact_mod_cast h.xm_global_lo
  have hhi : (d.xmBox.hi : ℝ) ≤ (constantXmBox.hi : ℝ) := by
    exact_mod_cast h.xm_global_hi
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

theorem plusBox_subset_global (d : Data) (h : Geometry d) :
    Icc (d.xpBox.lo : ℝ) (d.xpBox.hi : ℝ) ⊆
      Icc (constantXpBox.lo : ℝ) (constantXpBox.hi : ℝ) := by
  intro x hx
  have hlo : (constantXpBox.lo : ℝ) ≤ (d.xpBox.lo : ℝ) := by
    exact_mod_cast h.xp_global_lo
  have hhi : (d.xpBox.hi : ℝ) ≤ (constantXpBox.hi : ℝ) := by
    exact_mod_cast h.xp_global_hi
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

theorem globalCrossingPair_eq_crossingPair (d : Data)
    (cert : Certificate d) :
    (∀ k : Icc (d.kLo : ℝ) (d.kHi : ℝ),
      constantCrossingPair.xMinus
          ⟨k, parameter_mem_global d cert.geometry k⟩ =
        (crossingPair d cert).xMinus k) ∧
    (∀ k : Icc (d.kLo : ℝ) (d.kHi : ℝ),
      constantCrossingPair.xPlus
          ⟨k, parameter_mem_global d cert.geometry k⟩ =
        (crossingPair d cert).xPlus k) := by
  exact constantCrossingPair_eq_tightPair (crossingPair d cert)
    (parameter_mem_global d cert.geometry)
    (minusBox_subset_global d cert.geometry)
    (plusBox_subset_global d cert.geometry)

/-- Every certified cell supplies the exact constant-edge scalar calibration
along its locally tight pair. -/
theorem constantCalibration_along_crossingPair
    (d : Data) (cert : Certificate d) {ell : ℝ}
    (hell : ellBox.Contains ell) :
    ∀ k : Icc (d.kLo : ℝ) (d.kHi : ℝ),
      PlatformConstantEdgeCalibration k (highKPlatformEdge .constant k)
        ((crossingPair d cert).xMinus k)
        ((crossingPair d cert).xPlus k)
        (-1 / platformExteriorWx k (highKPlatformEdge .constant k)
          ((crossingPair d cert).xMinus k))
        (1 / platformExteriorWx k (highKPlatformEdge .constant k)
          ((crossingPair d cert).xPlus k))
        (platformEffectiveConstant ell k (highKPlatformEdge .constant k)
          ((crossingPair d cert).xMinus k)
          ((crossingPair d cert).xPlus k)
          (-1 / platformExteriorWx k (highKPlatformEdge .constant k)
            ((crossingPair d cert).xMinus k))
          (1 / platformExteriorWx k (highKPlatformEdge .constant k)
            ((crossingPair d cert).xPlus k))) := by
  apply platformConstantEdgeCalibration_along_crossingPair_of_interval
    (X := d.boxes) (qCap := d.qCap) (rCap := d.rCap)
    (logTerms := scalarLogTerms) (sqrtSteps := scalarSqrtSteps)
    (trigDoubles := scalarTrigDoubles) (N := scalarFourierTerms)
    (crossingPair d cert)
  · exact d.boxes_ordered cert.geometry
  · intro k
    change (d.kLo : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ (d.kHi : ℝ)
    exact k.property
  · intro x hx
    simpa [Data.boxes, RatInterval.Contains] using! hx
  · intro x hx
    simpa [Data.boxes, RatInterval.Contains] using! hx
  · simpa [Data.boxes] using! hell
  · simpa [Data.boxes] using!
      Erdos1038.HighKPlatformIntervalSmoke.pi_mem_piBox
  · intro k
    have hupper := ((crossingPair d cert).xMinus_mem k).2
    have hedge : (d.xmBox.hi : ℝ) < ((9 / 5 : Rat) : ℝ) := by
      exact_mod_cast cert.geometry.xm_lt_edge
    simpa [highKPlatformEdge] using! hupper.trans_lt hedge
  · intro k
    have hupper := ((crossingPair d cert).xPlus_mem k).2
    have hedge : (d.xpBox.hi : ℝ) < ((9 / 5 : Rat) : ℝ) := by
      exact_mod_cast cert.geometry.xp_lt_edge
    simpa [highKPlatformEdge] using! hupper.trans_lt hedge
  · intro k
    norm_num [highKPlatformEdge]
  · norm_num [scalarFourierTerms]
  · exact_mod_cast cert.scalar.qCap_positive
  · have hcap : (d.qCap : ℝ) ≤ 3 := by
      exact_mod_cast cert.scalar.qCap_le_three
    exact hcap.trans Real.pi_gt_three.le
  · exact_mod_cast cert.scalar.rCap_positive
  · have hcap : (d.rCap : ℝ) ≤ 3 := by
      exact_mod_cast cert.scalar.rCap_le_three
    exact hcap.trans Real.pi_gt_three.le
  · exact cert.scalar.api
  · exact cert.scalar.qmax
  · exact cert.scalar.rmax
  · exact cert.scalar.qcap
  · exact cert.scalar.rcap
  · exact cert.scalar.ceff
  · exact cert.scalar.endpoint

/-- Cell calibration transferred to the single globally selected constant
crossing pair. -/
theorem constantCalibration_along_globalCrossingPair
    (d : Data) (cert : Certificate d) {ell : ℝ}
    (hell : ellBox.Contains ell) :
    ∀ k : Icc (d.kLo : ℝ) (d.kHi : ℝ),
      PlatformConstantEdgeCalibration k (highKPlatformEdge .constant k)
        (constantCrossingPair.xMinus
          ⟨k, parameter_mem_global d cert.geometry k⟩)
        (constantCrossingPair.xPlus
          ⟨k, parameter_mem_global d cert.geometry k⟩)
        (-1 / platformExteriorWx k (highKPlatformEdge .constant k)
          (constantCrossingPair.xMinus
            ⟨k, parameter_mem_global d cert.geometry k⟩))
        (1 / platformExteriorWx k (highKPlatformEdge .constant k)
          (constantCrossingPair.xPlus
            ⟨k, parameter_mem_global d cert.geometry k⟩))
        (platformEffectiveConstant ell k (highKPlatformEdge .constant k)
          (constantCrossingPair.xMinus
            ⟨k, parameter_mem_global d cert.geometry k⟩)
          (constantCrossingPair.xPlus
            ⟨k, parameter_mem_global d cert.geometry k⟩)
          (-1 / platformExteriorWx k (highKPlatformEdge .constant k)
            (constantCrossingPair.xMinus
              ⟨k, parameter_mem_global d cert.geometry k⟩))
          (1 / platformExteriorWx k (highKPlatformEdge .constant k)
            (constantCrossingPair.xPlus
              ⟨k, parameter_mem_global d cert.geometry k⟩))) := by
  intro k
  exact platformConstantEdgeCalibration_transfer_crossingPair
    constantCrossingPair (crossingPair d cert)
      (parameter_mem_global d cert.geometry) k
      ((globalCrossingPair_eq_crossingPair d cert).1 k)
      ((globalCrossingPair_eq_crossingPair d cert).2 k)
      (constantCalibration_along_crossingPair d cert hell k)

end Erdos1038.HighKPlatformConstantCell
