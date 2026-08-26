import ErdosProblems.Erdos1038.HighKPlatformAffineCrossingSmoke
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCalibration
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerComponents
import ErdosProblems.Erdos1038.HighKPlatformGlobalCrossingRestriction
import ErdosProblems.Erdos1038.HighKPlatformAffinePrecision

/-!
# Reusable exact certificates for affine-edge parameter cells

The affine part of the high-`k` cover consists of 264 adjacent cells of width
`1 / 400`.  This module contains the common crossing, scalar, derivative-grid,
and global-branch bookkeeping.  Generated modules need only provide the two
root boxes, two scalar caps, and the finite Boolean checks for each cell.
-/

set_option warningAsError false
set_option maxHeartbeats 4000000

namespace Erdos1038.HighKPlatformAffineCell

open Erdos1038 Set RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformCrossingCertificates
open Erdos1038.HighKPlatformGlobalCrossingProbes
open Erdos1038.HighKPlatformGlobalCrossingCertificates
open Erdos1038.HighKPlatformGlobalCrossingRestriction
open Erdos1038.HighKPlatformAffinePrecision
open Erdos1038.HighKPlatformAffineSemanticCorner

/-- Precision used only for the crossing branches. -/
def logTerms : ℕ := 80
def sqrtSteps : ℕ := 64

/-- Scalar precision is independent of the crossing precision so the costly
corner enclosure can be tuned without weakening the root certificates. -/
def scalarLogTerms : ℕ := scalarPrecision.logTerms
def scalarSqrtSteps : ℕ := scalarPrecision.sqrtSteps
def scalarTrigDoubles : ℕ := scalarPrecision.trigDoubles
def scalarFourierTerms : ℕ := scalarPrecision.fourierTerms

def derivativeLogTerms : ℕ := 16
def derivativeSqrtSteps : ℕ := 20
def derivativeTrigDoubles : ℕ := 8

def zeroBox : RatInterval := point 0

/-- The target-length enclosure supplied by the closed one-cut certificate.
The affine checks use this directly so the completed table applies to `L`
without a stronger decimal hypothesis. -/
def ellBox : RatInterval :=
  ⟨1834430475762661 / 10 ^ 15, 1834430475762662 / 10 ^ 15⟩

def cellCount : ℕ := 264
def gridStart : Rat := 36 / 25
def gridStep : Rat := 1 / 400
def gridEnd : Rat := 21 / 10

def gridKLo (i : Fin cellCount) : Rat :=
  gridStart + (i.val : Rat) * gridStep

def gridKHi (i : Fin cellCount) : Rat :=
  gridStart + ((i.val + 1 : ℕ) : Rat) * gridStep

def affineEdgeRat (k : Rat) : Rat := 1153 / 500 - k / 4

/-- The uniform grid covers the complete affine parameter range. -/
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

/-- The rational data that vary from cell to cell. -/
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

def endpoint (_d : Data) (side : PlatformCrossingSide)
    (k x : Rat) : Fin 5 → RatInterval :=
  match side with
  | .minus => ![point k, point x, zeroBox, zeroBox, zeroBox]
  | .plus => ![point k, zeroBox, point x, zeroBox, zeroBox]

def envelope (d : Data) (side : PlatformCrossingSide) :
    Fin 5 → RatInterval :=
  match side with
  | .minus => ![d.kBox, d.xmBox, zeroBox, zeroBox, zeroBox]
  | .plus => ![d.kBox, zeroBox, d.xpBox, zeroBox, zeroBox]

def slopeBox (d : Data) (side : PlatformCrossingSide) : RatInterval :=
  (evalInterval (d.envelope side)
    (crossingSlopeE logTerms sqrtSteps .affine side)).getD zeroBox

def correctionE (side : PlatformCrossingSide) : HighKIntervalExpr 5 :=
  match side with
  | .minus =>
      .sub e1 (.mul (rhoZeroE sqrtSteps .affine)
        (rhoE sqrtSteps .affine xmE))
  | .plus =>
      .sub e1 (.mul (rhoZeroE sqrtSteps .affine)
        (rhoE sqrtSteps .affine xpE))

def boxes (d : Data) : Fin 5 → RatInterval :=
  ![d.kBox, d.xmBox, d.xpBox,
    ellBox,
    Erdos1038.HighKPlatformIntervalSmoke.piBox]

def rBox (d : Data) : RatInterval :=
  (evalInterval d.boxes (rmaxE derivativeSqrtSteps .affine)).getD zeroBox

def qBox (d : Data) : RatInterval :=
  (evalInterval d.boxes (qmaxE derivativeSqrtSteps .affine)).getD zeroBox

end Data

def derivativeDomain (d : Data) : RatInterval := ⟨3 / 2, d.qCap⟩

def derivativeStep (d : Data) : Rat := (d.qCap - 3 / 2) / 8

def derivativeCell (d : Data) (i : Fin 8) : RatInterval :=
  ⟨3 / 2 + i * derivativeStep d,
    3 / 2 + (i + 1) * derivativeStep d⟩

def derivativeCells (d : Data) : List RatInterval :=
  List.ofFn (derivativeCell d)

/-- Rational geometry used both by the local crossing theorem and by the
identification with the broad global crossing pair. -/
structure Geometry (d : Data) : Prop where
  k_lt : d.kLo < d.kHi
  xm_lt : d.xmBox.lo < d.xmBox.hi
  xp_lt : d.xpBox.lo < d.xpBox.hi
  xm_negative : d.xmBox.hi < 0
  xp_positive : 0 < d.xpBox.lo
  edge_hi_positive : 0 < affineEdgeRat d.kHi
  xm_lt_edge_hi : d.xmBox.hi < affineEdgeRat d.kHi
  xp_lt_edge_hi : d.xpBox.hi < affineEdgeRat d.kHi
  edge_lo_lt_two : affineEdgeRat d.kLo < 2
  global_k_lo : affineKBox.lo ≤ d.kLo
  global_k_hi : d.kHi ≤ affineKBox.hi
  global_xm_lo : affineXmBox.lo ≤ d.xmBox.lo
  global_xm_hi : d.xmBox.hi ≤ affineXmBox.hi
  global_xp_lo : affineXpBox.lo ≤ d.xpBox.lo
  global_xp_hi : d.xpBox.hi ≤ affineXpBox.hi

/-- Executable form of every per-cell obligation. -/
structure RawChecks (d : Data) : Prop extends Geometry d where
  minusAtLoLeft : evalPositiveCheck
    (d.endpoint .minus d.kLo d.xmBox.lo)
    (crossingWE logTerms sqrtSteps .affine .minus) = true
  minusAtLoRight : evalNegativeCheck
    (d.endpoint .minus d.kLo d.xmBox.hi)
    (crossingWE logTerms sqrtSteps .affine .minus) = true
  minusAtHiLeft : evalPositiveCheck
    (d.endpoint .minus d.kHi d.xmBox.lo)
    (crossingWE logTerms sqrtSteps .affine .minus) = true
  minusAtHiRight : evalNegativeCheck
    (d.endpoint .minus d.kHi d.xmBox.hi)
    (crossingWE logTerms sqrtSteps .affine .minus) = true
  plusAtLoLeft : evalNegativeCheck
    (d.endpoint .plus d.kLo d.xpBox.lo)
    (crossingWE logTerms sqrtSteps .affine .plus) = true
  plusAtLoRight : evalPositiveCheck
    (d.endpoint .plus d.kLo d.xpBox.hi)
    (crossingWE logTerms sqrtSteps .affine .plus) = true
  plusAtHiLeft : evalNegativeCheck
    (d.endpoint .plus d.kHi d.xpBox.lo)
    (crossingWE logTerms sqrtSteps .affine .plus) = true
  plusAtHiRight : evalPositiveCheck
    (d.endpoint .plus d.kHi d.xpBox.hi)
    (crossingWE logTerms sqrtSteps .affine .plus) = true
  minusWx : evalNegativeCheck (d.envelope .minus)
    (crossingWxE sqrtSteps .affine .minus) = true
  plusWx : evalPositiveCheck (d.envelope .plus)
    (crossingWxE sqrtSteps .affine .plus) = true
  minusSlope_eval : evalInterval (d.envelope .minus)
    (crossingSlopeE logTerms sqrtSteps .affine .minus) =
      some (d.slopeBox .minus)
  plusSlope_eval : evalInterval (d.envelope .plus)
    (crossingSlopeE logTerms sqrtSteps .affine .plus) =
      some (d.slopeBox .plus)
  minusSlope_ordered : (d.slopeBox .minus).Ordered
  plusSlope_ordered : (d.slopeBox .plus).Ordered
  minusSlope_negative : (d.slopeBox .minus).hi < 0
  plusSlope_positive : 0 < (d.slopeBox .plus).lo
  minusDiffDomain : diffDomainCheck (d.envelope .minus)
    (crossingWE logTerms sqrtSteps .affine .minus) = true
  plusDiffDomain : diffDomainCheck (d.envelope .plus)
    (crossingWE logTerms sqrtSteps .affine .plus) = true
  minusCorrection : evalNonzeroCheck (d.envelope .minus)
    (Data.correctionE .minus) = true
  plusCorrection : evalNonzeroCheck (d.envelope .plus)
    (Data.correctionE .plus) = true
  qCap_positive : 0 < d.qCap
  qCap_derivative_lower : 3 / 2 < d.qCap
  qCap_le_domain : d.qCap ≤ 309 / 100
  rCap_positive : 0 < d.rCap
  rCap_le_three : d.rCap ≤ 3
  api : evalPositiveCheck d.boxes (apiE scalarSqrtSteps .affine) = true
  qmax : evalPositiveCheck d.boxes (qmaxE scalarSqrtSteps .affine) = true
  rmax : evalPositiveCheck d.boxes (rmaxE scalarSqrtSteps .affine) = true
  rltq : evalNegativeCheck d.boxes
    (.sub (rmaxE scalarSqrtSteps .affine)
      (qmaxE scalarSqrtSteps .affine)) = true
  qcap : evalNegativeCheck d.boxes
    (.sub (qmaxE scalarSqrtSteps .affine) (.rat d.qCap)) = true
  rcap : evalNegativeCheck d.boxes
    (.sub (rmaxE scalarSqrtSteps .affine) (.rat d.rCap)) = true
  ceff : evalNegativeCheck d.boxes
    (ceffE scalarLogTerms scalarSqrtSteps .affine) = true
  corner : UniformPositive d.boxes
    (affineCornerLowerE scalarLogTerms scalarSqrtSteps scalarTrigDoubles
      scalarFourierTerms .affine d.qCap d.rCap)
  r_eval : evalInterval d.boxes (rmaxE derivativeSqrtSteps .affine) =
    some d.rBox
  q_eval : evalInterval d.boxes (qmaxE derivativeSqrtSteps .affine) =
    some d.qBox
  domain_lo_le : (derivativeDomain d).lo ≤ d.rBox.lo
  q_hi_le : d.qBox.hi ≤ (derivativeDomain d).hi
  derivative : ∀ i : Fin 8,
    evalNegativeCheck (prependFin (derivativeCell d i) d.boxes)
      (affineDerivativeCellE derivativeLogTerms derivativeSqrtSteps
        derivativeTrigDoubles .affine) = true

/-- Conjunction form of `RawChecks`.  Generated concrete cells split this at
every conjunction and discharge each closed leaf independently with
proof-producing `kernel_decide`. -/
def RawCheckTuple (d : Data) : Prop :=
  d.kLo < d.kHi ∧
  d.xmBox.lo < d.xmBox.hi ∧
  d.xpBox.lo < d.xpBox.hi ∧
  d.xmBox.hi < 0 ∧
  0 < d.xpBox.lo ∧
  0 < affineEdgeRat d.kHi ∧
  d.xmBox.hi < affineEdgeRat d.kHi ∧
  d.xpBox.hi < affineEdgeRat d.kHi ∧
  affineEdgeRat d.kLo < 2 ∧
  affineKBox.lo ≤ d.kLo ∧
  d.kHi ≤ affineKBox.hi ∧
  affineXmBox.lo ≤ d.xmBox.lo ∧
  d.xmBox.hi ≤ affineXmBox.hi ∧
  affineXpBox.lo ≤ d.xpBox.lo ∧
  d.xpBox.hi ≤ affineXpBox.hi ∧
  evalPositiveCheck (d.endpoint .minus d.kLo d.xmBox.lo)
    (crossingWE logTerms sqrtSteps .affine .minus) = true ∧
  evalNegativeCheck (d.endpoint .minus d.kLo d.xmBox.hi)
    (crossingWE logTerms sqrtSteps .affine .minus) = true ∧
  evalPositiveCheck (d.endpoint .minus d.kHi d.xmBox.lo)
    (crossingWE logTerms sqrtSteps .affine .minus) = true ∧
  evalNegativeCheck (d.endpoint .minus d.kHi d.xmBox.hi)
    (crossingWE logTerms sqrtSteps .affine .minus) = true ∧
  evalNegativeCheck (d.endpoint .plus d.kLo d.xpBox.lo)
    (crossingWE logTerms sqrtSteps .affine .plus) = true ∧
  evalPositiveCheck (d.endpoint .plus d.kLo d.xpBox.hi)
    (crossingWE logTerms sqrtSteps .affine .plus) = true ∧
  evalNegativeCheck (d.endpoint .plus d.kHi d.xpBox.lo)
    (crossingWE logTerms sqrtSteps .affine .plus) = true ∧
  evalPositiveCheck (d.endpoint .plus d.kHi d.xpBox.hi)
    (crossingWE logTerms sqrtSteps .affine .plus) = true ∧
  evalNegativeCheck (d.envelope .minus)
    (crossingWxE sqrtSteps .affine .minus) = true ∧
  evalPositiveCheck (d.envelope .plus)
    (crossingWxE sqrtSteps .affine .plus) = true ∧
  evalInterval (d.envelope .minus)
    (crossingSlopeE logTerms sqrtSteps .affine .minus) =
      some (d.slopeBox .minus) ∧
  evalInterval (d.envelope .plus)
    (crossingSlopeE logTerms sqrtSteps .affine .plus) =
      some (d.slopeBox .plus) ∧
  (d.slopeBox .minus).lo ≤ (d.slopeBox .minus).hi ∧
  (d.slopeBox .plus).lo ≤ (d.slopeBox .plus).hi ∧
  (d.slopeBox .minus).hi < 0 ∧
  0 < (d.slopeBox .plus).lo ∧
  diffDomainCheck (d.envelope .minus)
    (crossingWE logTerms sqrtSteps .affine .minus) = true ∧
  diffDomainCheck (d.envelope .plus)
    (crossingWE logTerms sqrtSteps .affine .plus) = true ∧
  evalNonzeroCheck (d.envelope .minus) (Data.correctionE .minus) = true ∧
  evalNonzeroCheck (d.envelope .plus) (Data.correctionE .plus) = true ∧
  0 < d.qCap ∧ 3 / 2 < d.qCap ∧ d.qCap ≤ 309 / 100 ∧
  0 < d.rCap ∧ d.rCap ≤ 3 ∧
  evalPositiveCheck d.boxes (apiE scalarSqrtSteps .affine) = true ∧
  evalPositiveCheck d.boxes (qmaxE scalarSqrtSteps .affine) = true ∧
  evalPositiveCheck d.boxes (rmaxE scalarSqrtSteps .affine) = true ∧
  evalNegativeCheck d.boxes
    (.sub (rmaxE scalarSqrtSteps .affine)
      (qmaxE scalarSqrtSteps .affine)) = true ∧
  evalNegativeCheck d.boxes
    (.sub (qmaxE scalarSqrtSteps .affine) (.rat d.qCap)) = true ∧
  evalNegativeCheck d.boxes
    (.sub (rmaxE scalarSqrtSteps .affine) (.rat d.rCap)) = true ∧
  evalNegativeCheck d.boxes
    (ceffE scalarLogTerms scalarSqrtSteps .affine) = true ∧
  UniformPositive d.boxes
    (affineCornerLowerE scalarLogTerms scalarSqrtSteps scalarTrigDoubles
      scalarFourierTerms .affine d.qCap d.rCap) ∧
  evalInterval d.boxes (rmaxE derivativeSqrtSteps .affine) = some d.rBox ∧
  evalInterval d.boxes (qmaxE derivativeSqrtSteps .affine) = some d.qBox ∧
  (derivativeDomain d).lo ≤ d.rBox.lo ∧
  d.qBox.hi ≤ (derivativeDomain d).hi ∧
  ∀ i : Fin 8,
    evalNegativeCheck (prependFin (derivativeCell d i) d.boxes)
      (affineDerivativeCellE derivativeLogTerms derivativeSqrtSteps
        derivativeTrigDoubles .affine) = true

theorem rawChecks_iff_tuple (d : Data) :
    RawChecks d ↔ RawCheckTuple d := by
  constructor <;> intro h
  · exact ⟨h.k_lt, h.xm_lt, h.xp_lt, h.xm_negative, h.xp_positive,
      h.edge_hi_positive, h.xm_lt_edge_hi, h.xp_lt_edge_hi,
      h.edge_lo_lt_two, h.global_k_lo, h.global_k_hi,
      h.global_xm_lo, h.global_xm_hi, h.global_xp_lo, h.global_xp_hi,
      h.minusAtLoLeft, h.minusAtLoRight, h.minusAtHiLeft,
      h.minusAtHiRight, h.plusAtLoLeft, h.plusAtLoRight,
      h.plusAtHiLeft, h.plusAtHiRight, h.minusWx, h.plusWx,
      h.minusSlope_eval, h.plusSlope_eval, h.minusSlope_ordered,
      h.plusSlope_ordered, h.minusSlope_negative, h.plusSlope_positive,
      h.minusDiffDomain, h.plusDiffDomain, h.minusCorrection,
      h.plusCorrection, h.qCap_positive, h.qCap_derivative_lower,
      h.qCap_le_domain,
      h.rCap_positive, h.rCap_le_three, h.api, h.qmax, h.rmax,
      h.rltq, h.qcap, h.rcap, h.ceff, h.corner, h.r_eval, h.q_eval,
      h.domain_lo_le, h.q_hi_le, h.derivative⟩
  · simp only [RawCheckTuple] at h
    rcases h with
      ⟨hk, hxm, hxp, hxmneg, hxppos, hepos, hxme, hxpe, he2,
        hgklo, hgkhi, hgxmlo, hgxmhi, hgxplo, hgxphi,
        hmll, hmlr, hmhl, hmhr, hpll, hplr, hphl, hphr,
        hmwx, hpwx, hmse, hpse, hmso, hpso, hms, hps,
        hmdd, hpdd, hmc, hpc, hqpos, hqlo, hq3, hrpos, hr3,
        hapi, hqmax, hrmax, hrltq, hqcap, hrcap, hceff,
        hcorner, hre, hqe, hdomain, hqhi, hderiv⟩
    exact {
      k_lt := hk, xm_lt := hxm, xp_lt := hxp,
      xm_negative := hxmneg, xp_positive := hxppos,
      edge_hi_positive := hepos, xm_lt_edge_hi := hxme,
      xp_lt_edge_hi := hxpe, edge_lo_lt_two := he2,
      global_k_lo := hgklo, global_k_hi := hgkhi,
      global_xm_lo := hgxmlo, global_xm_hi := hgxmhi,
      global_xp_lo := hgxplo, global_xp_hi := hgxphi,
      minusAtLoLeft := hmll, minusAtLoRight := hmlr,
      minusAtHiLeft := hmhl, minusAtHiRight := hmhr,
      plusAtLoLeft := hpll, plusAtLoRight := hplr,
      plusAtHiLeft := hphl, plusAtHiRight := hphr,
      minusWx := hmwx, plusWx := hpwx,
      minusSlope_eval := hmse, plusSlope_eval := hpse,
      minusSlope_ordered := hmso, plusSlope_ordered := hpso,
      minusSlope_negative := hms, plusSlope_positive := hps,
      minusDiffDomain := hmdd, plusDiffDomain := hpdd,
      minusCorrection := hmc, plusCorrection := hpc,
      qCap_positive := hqpos, qCap_derivative_lower := hqlo,
      qCap_le_domain := hq3,
      rCap_positive := hrpos, rCap_le_three := hr3,
      api := hapi, qmax := hqmax, rmax := hrmax, rltq := hrltq,
      qcap := hqcap, rcap := hrcap, ceff := hceff, corner := hcorner,
      r_eval := hre, q_eval := hqe, domain_lo_le := hdomain,
      q_hi_le := hqhi, derivative := hderiv }

/-! ## Composite executable interface

These Boolean groupings remain useful for diagnostics and compatibility.
Production generated modules use the finer `RawCheckTuple` leaves above so
each proof is checked by kernel reduction in isolation. -/

def geometryCheck (d : Data) : Bool := decide
  (d.kLo < d.kHi ∧
    d.xmBox.lo < d.xmBox.hi ∧
    d.xpBox.lo < d.xpBox.hi ∧
    d.xmBox.hi < 0 ∧
    0 < d.xpBox.lo ∧
    0 < affineEdgeRat d.kHi ∧
    d.xmBox.hi < affineEdgeRat d.kHi ∧
    d.xpBox.hi < affineEdgeRat d.kHi ∧
    affineEdgeRat d.kLo < 2 ∧
    affineKBox.lo ≤ d.kLo ∧
    d.kHi ≤ affineKBox.hi ∧
    affineXmBox.lo ≤ d.xmBox.lo ∧
    d.xmBox.hi ≤ affineXmBox.hi ∧
    affineXpBox.lo ≤ d.xpBox.lo ∧
    d.xpBox.hi ≤ affineXpBox.hi)

def crossingCheck (d : Data) : Bool := decide
  (evalPositiveCheck (d.endpoint .minus d.kLo d.xmBox.lo)
      (crossingWE logTerms sqrtSteps .affine .minus) = true ∧
    evalNegativeCheck (d.endpoint .minus d.kLo d.xmBox.hi)
      (crossingWE logTerms sqrtSteps .affine .minus) = true ∧
    evalPositiveCheck (d.endpoint .minus d.kHi d.xmBox.lo)
      (crossingWE logTerms sqrtSteps .affine .minus) = true ∧
    evalNegativeCheck (d.endpoint .minus d.kHi d.xmBox.hi)
      (crossingWE logTerms sqrtSteps .affine .minus) = true ∧
    evalNegativeCheck (d.endpoint .plus d.kLo d.xpBox.lo)
      (crossingWE logTerms sqrtSteps .affine .plus) = true ∧
    evalPositiveCheck (d.endpoint .plus d.kLo d.xpBox.hi)
      (crossingWE logTerms sqrtSteps .affine .plus) = true ∧
    evalNegativeCheck (d.endpoint .plus d.kHi d.xpBox.lo)
      (crossingWE logTerms sqrtSteps .affine .plus) = true ∧
    evalPositiveCheck (d.endpoint .plus d.kHi d.xpBox.hi)
      (crossingWE logTerms sqrtSteps .affine .plus) = true ∧
    evalNegativeCheck (d.envelope .minus)
      (crossingWxE sqrtSteps .affine .minus) = true ∧
    evalPositiveCheck (d.envelope .plus)
      (crossingWxE sqrtSteps .affine .plus) = true ∧
    evalInterval (d.envelope .minus)
      (crossingSlopeE logTerms sqrtSteps .affine .minus) =
        some (d.slopeBox .minus) ∧
    evalInterval (d.envelope .plus)
      (crossingSlopeE logTerms sqrtSteps .affine .plus) =
        some (d.slopeBox .plus) ∧
    (d.slopeBox .minus).lo ≤ (d.slopeBox .minus).hi ∧
    (d.slopeBox .plus).lo ≤ (d.slopeBox .plus).hi ∧
    (d.slopeBox .minus).hi < 0 ∧
    0 < (d.slopeBox .plus).lo ∧
    diffDomainCheck (d.envelope .minus)
      (crossingWE logTerms sqrtSteps .affine .minus) = true ∧
    diffDomainCheck (d.envelope .plus)
      (crossingWE logTerms sqrtSteps .affine .plus) = true ∧
    evalNonzeroCheck (d.envelope .minus) (Data.correctionE .minus) = true ∧
    evalNonzeroCheck (d.envelope .plus) (Data.correctionE .plus) = true)

def scalarCheck (d : Data) : Bool := decide
  (0 < d.qCap ∧ 3 / 2 < d.qCap ∧ d.qCap ≤ 309 / 100 ∧
    0 < d.rCap ∧ d.rCap ≤ 3 ∧
    evalPositiveCheck d.boxes (apiE scalarSqrtSteps .affine) = true ∧
    evalPositiveCheck d.boxes (qmaxE scalarSqrtSteps .affine) = true ∧
    evalPositiveCheck d.boxes (rmaxE scalarSqrtSteps .affine) = true ∧
    evalNegativeCheck d.boxes
      (.sub (rmaxE scalarSqrtSteps .affine)
        (qmaxE scalarSqrtSteps .affine)) = true ∧
    evalNegativeCheck d.boxes
      (.sub (qmaxE scalarSqrtSteps .affine) (.rat d.qCap)) = true ∧
    evalNegativeCheck d.boxes
      (.sub (rmaxE scalarSqrtSteps .affine) (.rat d.rCap)) = true ∧
    evalNegativeCheck d.boxes
      (ceffE scalarLogTerms scalarSqrtSteps .affine) = true ∧
    evalPositiveCheck d.boxes
      (affineCornerLowerE scalarLogTerms scalarSqrtSteps scalarTrigDoubles
        scalarFourierTerms .affine d.qCap d.rCap) = true ∧
    evalInterval d.boxes (rmaxE derivativeSqrtSteps .affine) = some d.rBox ∧
    evalInterval d.boxes (qmaxE derivativeSqrtSteps .affine) = some d.qBox ∧
    (derivativeDomain d).lo ≤ d.rBox.lo ∧
    d.qBox.hi ≤ (derivativeDomain d).hi)

def derivativeCheck (d : Data) : Bool := decide
  (∀ i : Fin 8,
    evalNegativeCheck (prependFin (derivativeCell d i) d.boxes)
      (affineDerivativeCellE derivativeLogTerms derivativeSqrtSteps
        derivativeTrigDoubles .affine) = true)

/-- Single Boolean consumed by generated chunk modules. -/
def rawCheck (d : Data) : Bool :=
  geometryCheck d && crossingCheck d && scalarCheck d && derivativeCheck d

theorem rawChecks_of_check {d : Data} (h : rawCheck d = true) : RawChecks d := by
  have hp : ((geometryCheck d = true ∧ crossingCheck d = true) ∧
      scalarCheck d = true) ∧ derivativeCheck d = true := by
    simpa [rawCheck] using! h
  have hg := of_decide_eq_true hp.1.1.1
  have hc := of_decide_eq_true hp.1.1.2
  have hs := of_decide_eq_true hp.1.2
  have hd := of_decide_eq_true hp.2
  rcases hg with
    ⟨hk, hxm, hxp, hxmneg, hxppos, hepos, hxme, hxpe, he2,
      hgklo, hgkhi, hgxmlo, hgxmhi, hgxplo, hgxphi⟩
  rcases hc with
    ⟨hmll, hmlr, hmhl, hmhr, hpll, hplr, hphl, hphr,
      hmwx, hpwx, hmse, hpse, hmso, hpso, hms, hps,
      hmdd, hpdd, hmc, hpc⟩
  rcases hs with
    ⟨hqpos, hqlo, hq3, hrpos, hr3, hapi, hqmax, hrmax, hrltq,
      hqcap, hrcap, hceff, hcorner, hre, hqe, hdomain, hqhi⟩
  have hcornerUniform : UniformPositive d.boxes
      (affineCornerLowerE scalarLogTerms scalarSqrtSteps scalarTrigDoubles
        scalarFourierTerms .affine d.qCap d.rCap) := by
    intro x hordered hcontains
    exact evalPositive_sound hordered hcontains
      (evalPositive_of_check hcorner)
  exact (rawChecks_iff_tuple d).2
    ⟨hk, hxm, hxp, hxmneg, hxppos, hepos, hxme, hxpe, he2,
      hgklo, hgkhi, hgxmlo, hgxmhi, hgxplo, hgxphi,
      hmll, hmlr, hmhl, hmhr, hpll, hplr, hphl, hphr,
      hmwx, hpwx, hmse, hpse, hmso, hpso, hms, hps,
      hmdd, hpdd, hmc, hpc, hqpos, hqlo, hq3, hrpos, hr3,
      hapi, hqmax, hrmax, hrltq, hqcap, hrcap, hceff,
      hcornerUniform, hre, hqe, hdomain, hqhi, hd⟩

namespace Data

theorem endpoint_ordered (d : Data) (side : PlatformCrossingSide)
    (k x : Rat) : ∀ i, (d.endpoint side k x i).Ordered := by
  intro i
  cases side <;> fin_cases i <;>
    simp [endpoint, zeroBox, point, RatInterval.Ordered]

theorem envelope_ordered (d : Data) (h : Geometry d)
    (side : PlatformCrossingSide) : ∀ i, (d.envelope side i).Ordered := by
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
  · norm_num [boxes, ellBox, RatInterval.Ordered]
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

end Data

/-- The eight-cell derivative grid ends at this slab's checked `qCap`.
Using the old global Fourier endpoint would ask late parameter slabs to prove
derivative negativity far beyond their actual `Qmax` range. -/
def derivativeCertificate (d : Data) (raw : RawChecks d) :
    AffineDerivativeBoxCertificate d.boxes derivativeLogTerms
      derivativeSqrtSteps derivativeTrigDoubles .affine where
  domain := derivativeDomain d
  cells := derivativeCells d
  rBox := d.rBox
  qBox := d.qBox
  domain_ordered := by
    exact raw.qCap_derivative_lower.le
  cells_ordered := by
    intro I hI
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hI
    have hstep : 0 < derivativeStep d := by
      dsimp [derivativeStep]
      linarith [raw.qCap_derivative_lower]
    dsimp [derivativeCell, RatInterval.Ordered]
    nlinarith [hstep.le]
  covers := by
    intro Q hQ
    have hstepRat : 0 < derivativeStep d := by
      dsimp [derivativeStep]
      linarith [raw.qCap_derivative_lower]
    have hstep : 0 < ((derivativeStep d : Rat) : ℝ) := by
      exact_mod_cast hstepRat
    have htop :
        ((3 / 2 : ℝ) + 8 * ((derivativeStep d : Rat) : ℝ)) =
          (d.qCap : ℝ) := by
      norm_num [derivativeStep]
      ring
    have hQ' : Q ∈ Icc (3 / 2 : ℝ)
        ((3 / 2 : ℝ) + 8 * ((derivativeStep d : Rat) : ℝ)) := by
      rw [htop]
      simpa [derivativeDomain, RatInterval.Contains] using! hQ
    obtain ⟨i, hi⟩ := exists_uniformGrid_cell
      (start := (3 / 2 : ℝ))
      (step := ((derivativeStep d : Rat) : ℝ))
      (N := 8) hstep (by norm_num) hQ'
    refine ⟨derivativeCell d i, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
    simpa [derivativeCell, RatInterval.Contains, div_eq_mul_inv] using! hi
  r_eval := raw.r_eval
  q_eval := raw.q_eval
  domain_lo_le := raw.domain_lo_le
  q_hi_le := raw.q_hi_le
  checked := by
    intro I hI
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hI
    exact evalNegative_of_check (raw.derivative i)

namespace Data

theorem edge_pos (d : Data) (h : Geometry d) {k : ℝ}
    (hk : k ∈ Icc (d.kLo : ℝ) (d.kHi : ℝ)) :
    0 < highKPlatformEdge .affine k := by
  have hedgeHi : 0 < ((affineEdgeRat d.kHi : Rat) : ℝ) := by
    exact_mod_cast h.edge_hi_positive
  norm_num [affineEdgeRat, highKPlatformEdge] at hedgeHi ⊢
  linarith [hk.2]

theorem edge_lt_two (d : Data) (h : Geometry d) {k : ℝ}
    (hk : k ∈ Icc (d.kLo : ℝ) (d.kHi : ℝ)) :
    highKPlatformEdge .affine k < 2 := by
  have hedgeLo : ((affineEdgeRat d.kLo : Rat) : ℝ) < 2 := by
    exact_mod_cast h.edge_lo_lt_two
  norm_num [affineEdgeRat, highKPlatformEdge] at hedgeLo ⊢
  linarith [hk.1]

theorem minus_lt_edge (d : Data) (h : Geometry d) {k x : ℝ}
    (hk : k ∈ Icc (d.kLo : ℝ) (d.kHi : ℝ))
    (hx : x ∈ Icc (d.xmBox.lo : ℝ) (d.xmBox.hi : ℝ)) :
    x < highKPlatformEdge .affine k := by
  have hedge : (d.xmBox.hi : ℝ) <
      ((affineEdgeRat d.kHi : Rat) : ℝ) := by
    exact_mod_cast h.xm_lt_edge_hi
  norm_num [affineEdgeRat, highKPlatformEdge] at hedge ⊢
  linarith [hk.2, hx.2]

theorem plus_lt_edge (d : Data) (h : Geometry d) {k x : ℝ}
    (hk : k ∈ Icc (d.kLo : ℝ) (d.kHi : ℝ))
    (hx : x ∈ Icc (d.xpBox.lo : ℝ) (d.xpBox.hi : ℝ)) :
    x < highKPlatformEdge .affine k := by
  have hedge : (d.xpBox.hi : ℝ) <
      ((affineEdgeRat d.kHi : Rat) : ℝ) := by
    exact_mod_cast h.xp_lt_edge_hi
  norm_num [affineEdgeRat, highKPlatformEdge] at hedge ⊢
  linarith [hk.2, hx.2]

def minusCertificate (d : Data) (raw : RawChecks d) :
    PlatformCrossingBranchCertificate
      logTerms sqrtSteps .affine .minus where
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
  envelope_ordered := d.envelope_ordered raw.toGeometry .minus
  atLo_signs := ⟨evalPositive_of_check raw.minusAtLoLeft,
    evalNegative_of_check raw.minusAtLoRight⟩
  atHi_signs := ⟨evalPositive_of_check raw.minusAtHiLeft,
    evalNegative_of_check raw.minusAtHiRight⟩
  wx_sign := evalNegative_of_check raw.minusWx
  slope_eval := raw.minusSlope_eval
  slope_ordered := raw.minusSlope_ordered
  slope_sign := raw.minusSlope_negative

def plusCertificate (d : Data) (raw : RawChecks d) :
    PlatformCrossingBranchCertificate
      logTerms sqrtSteps .affine .plus where
  atLoLeft := d.endpoint .plus d.kLo d.xpBox.lo
  atLoRight := d.endpoint .plus d.kLo d.xpBox.hi
  atHiLeft := d.endpoint .plus d.kHi d.xpBox.lo
  atHiRight := d.endpoint .plus d.kHi d.xpBox.hi
  envelope := d.envelope .plus
  orientation := .increasing
  slopeBox := d.slopeBox .plus
  atLoLeft_ordered := d.endpoint_ordered .plus _ _
  atLoRight_ordered := d.endpoint_ordered .plus _ _
  atHiLeft_ordered := d.endpoint_ordered .plus _ _
  atHiRight_ordered := d.endpoint_ordered .plus _ _
  envelope_ordered := d.envelope_ordered raw.toGeometry .plus
  atLo_signs := ⟨evalNegative_of_check raw.plusAtLoLeft,
    evalPositive_of_check raw.plusAtLoRight⟩
  atHi_signs := ⟨evalNegative_of_check raw.plusAtHiLeft,
    evalPositive_of_check raw.plusAtHiRight⟩
  wx_sign := evalPositive_of_check raw.plusWx
  slope_eval := raw.plusSlope_eval
  slope_ordered := raw.plusSlope_ordered
  slope_sign := raw.plusSlope_positive

theorem existsUnique_minusBranch (d : Data) (raw : RawChecks d) :
    ∃! root : Icc (d.kLo : ℝ) (d.kHi : ℝ) → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc (d.xmBox.lo : ℝ) (d.xmBox.hi : ℝ) ∧
          platformExteriorW k (highKPlatformEdge .affine k) (root k) = 0 := by
  apply (d.minusCertificate raw).existsUnique_continuous_crossing
      (other := 0) (ell := 0) (pi := 0)
  · exact_mod_cast raw.k_lt.le
  · exact_mod_cast raw.xm_lt.le
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
      exact_mod_cast raw.xm_negative
    exact hx.2.trans_lt hnegative
  · intro k hk
    exact d.edge_pos raw.toGeometry hk
  · intro k hk x hx
    exact d.minus_lt_edge raw.toGeometry hk hx
  · intro k hk
    exact d.edge_lt_two raw.toGeometry hk
  · intro k hk x hx
    have hne := evalReal_ne_zero_of_check
      (d.minusCertificate raw).envelope_ordered
      (d.envelope_contains .minus hk hx) raw.minusCorrection
    simpa [Data.correctionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  · intro k hk x hx
    exact diffDomain_of_check
      (d.minusCertificate raw).envelope_ordered
      (d.envelope_contains .minus hk hx)
      (crossingWE logTerms sqrtSteps .affine .minus)
      raw.minusDiffDomain

theorem existsUnique_plusBranch (d : Data) (raw : RawChecks d) :
    ∃! root : Icc (d.kLo : ℝ) (d.kHi : ℝ) → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc (d.xpBox.lo : ℝ) (d.xpBox.hi : ℝ) ∧
          platformExteriorW k (highKPlatformEdge .affine k) (root k) = 0 := by
  apply (d.plusCertificate raw).existsUnique_continuous_crossing
      (other := 0) (ell := 0) (pi := 0)
  · exact_mod_cast raw.k_lt.le
  · exact_mod_cast raw.xp_lt.le
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
      exact_mod_cast raw.xp_positive
    exact hpositive.trans_le hx.1
  · intro k hk
    exact d.edge_pos raw.toGeometry hk
  · intro k hk x hx
    exact d.plus_lt_edge raw.toGeometry hk hx
  · intro k hk
    exact d.edge_lt_two raw.toGeometry hk
  · intro k hk x hx
    have hne := evalReal_ne_zero_of_check
      (d.plusCertificate raw).envelope_ordered
      (d.envelope_contains .plus hk hx) raw.plusCorrection
    simpa [Data.correctionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  · intro k hk x hx
    exact diffDomain_of_check
      (d.plusCertificate raw).envelope_ordered
      (d.envelope_contains .plus hk hx)
      (crossingWE logTerms sqrtSteps .affine .plus)
      raw.plusDiffDomain

theorem nonempty_crossingPair (d : Data) (raw : RawChecks d) :
    Nonempty (ContinuousPlatformCrossingPair .affine
      (d.kLo : ℝ) (d.kHi : ℝ)
      (d.xmBox.lo : ℝ) (d.xmBox.hi : ℝ)
      (d.xpBox.lo : ℝ) (d.xpBox.hi : ℝ)) :=
  exists_crossingPair_of_uniqueBranches
    (d.existsUnique_minusBranch raw) (d.existsUnique_plusBranch raw)

end Data

/-- The locally tight pair selected by one complete executable cell. -/
noncomputable def crossingPair (d : Data) (raw : RawChecks d) :
    ContinuousPlatformCrossingPair .affine
      (d.kLo : ℝ) (d.kHi : ℝ)
      (d.xmBox.lo : ℝ) (d.xmBox.hi : ℝ)
      (d.xpBox.lo : ℝ) (d.xpBox.hi : ℝ) :=
  Classical.choice (d.nonempty_crossingPair raw)

/-- Every executable affine cell supplies the scalar calibration along its
locally tight crossing pair. -/
theorem affineCalibration_along_crossingPair
    (d : Data) (raw : RawChecks d) {ell : ℝ}
    (hell : ellBox.Contains ell) :
    ∀ k : Icc (d.kLo : ℝ) (d.kHi : ℝ),
      PlatformAffineCalibration k (highKPlatformEdge .affine k)
        ((crossingPair d raw).xMinus k)
        ((crossingPair d raw).xPlus k)
        (-1 / platformExteriorWx k (highKPlatformEdge .affine k)
          ((crossingPair d raw).xMinus k))
        (1 / platformExteriorWx k (highKPlatformEdge .affine k)
          ((crossingPair d raw).xPlus k))
        (platformEffectiveConstant ell k (highKPlatformEdge .affine k)
          ((crossingPair d raw).xMinus k)
          ((crossingPair d raw).xPlus k)
          (-1 / platformExteriorWx k (highKPlatformEdge .affine k)
            ((crossingPair d raw).xMinus k))
          (1 / platformExteriorWx k (highKPlatformEdge .affine k)
            ((crossingPair d raw).xPlus k))) := by
  intro k
  apply
    Erdos1038.HighKPlatformAffineSemanticCalibration.platformAffineCalibration_of_uniformCorner_mixedDerivative
      (X := d.boxes) (qCap := d.qCap) (rCap := d.rCap)
      (logTerms := scalarLogTerms) (sqrtSteps := scalarSqrtSteps)
      (trigDoubles := scalarTrigDoubles) (N := scalarFourierTerms)
      (derivativeLogTerms := derivativeLogTerms)
      (derivativeSqrtSteps := derivativeSqrtSteps)
      (derivativeTrigDoubles := derivativeTrigDoubles)
  · exact d.boxes_ordered raw.toGeometry
  · intro i
    fin_cases i
    · change (d.kLo : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ (d.kHi : ℝ)
      exact k.property
    · simpa [Data.boxes, RatInterval.Contains] using!
        (crossingPair d raw).xMinus_mem k
    · simpa [Data.boxes, RatInterval.Contains] using!
        (crossingPair d raw).xPlus_mem k
    · simpa [Data.boxes] using! hell
    · simpa [Data.boxes] using!
        Erdos1038.HighKPlatformIntervalSmoke.pi_mem_piBox
  · exact d.minus_lt_edge raw.toGeometry k.property
      ((crossingPair d raw).xMinus_mem k)
  · exact d.plus_lt_edge raw.toGeometry k.property
      ((crossingPair d raw).xPlus_mem k)
  · exact d.edge_lt_two raw.toGeometry k.property
  · norm_num [scalarFourierTerms, scalarPrecision]
  · exact_mod_cast raw.qCap_positive
  · have hcap : (d.qCap : ℝ) ≤ ((309 / 100 : Rat) : ℝ) := by
      exact_mod_cast raw.qCap_le_domain
    have hpi := Real.pi_gt_d20
    norm_num at hpi ⊢
    linarith
  · exact_mod_cast raw.rCap_positive
  · have hcap : (d.rCap : ℝ) ≤ 3 := by
      exact_mod_cast raw.rCap_le_three
    exact hcap.trans Real.pi_gt_three.le
  · exact evalPositive_of_check raw.api
  · exact evalPositive_of_check raw.qmax
  · exact evalPositive_of_check raw.rmax
  · exact evalNegative_of_check raw.rltq
  · exact evalNegative_of_check raw.qcap
  · exact evalNegative_of_check raw.rcap
  · exact evalNegative_of_check raw.ceff
  · exact raw.corner
  · exact derivativeCertificate d raw

namespace Data

theorem parameter_mem_global (d : Data) (h : Geometry d)
    (k : Icc (d.kLo : ℝ) (d.kHi : ℝ)) :
    (k : ℝ) ∈ Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ) := by
  have hlo : (affineKBox.lo : ℝ) ≤ (d.kLo : ℝ) := by
    exact_mod_cast h.global_k_lo
  have hhi : (d.kHi : ℝ) ≤ (affineKBox.hi : ℝ) := by
    exact_mod_cast h.global_k_hi
  exact ⟨hlo.trans k.property.1, k.property.2.trans hhi⟩

theorem minusBox_subset_global (d : Data) (h : Geometry d) :
    Icc (d.xmBox.lo : ℝ) (d.xmBox.hi : ℝ) ⊆
      Icc (affineXmBox.lo : ℝ) (affineXmBox.hi : ℝ) := by
  intro x hx
  have hlo : (affineXmBox.lo : ℝ) ≤ (d.xmBox.lo : ℝ) := by
    exact_mod_cast h.global_xm_lo
  have hhi : (d.xmBox.hi : ℝ) ≤ (affineXmBox.hi : ℝ) := by
    exact_mod_cast h.global_xm_hi
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

theorem plusBox_subset_global (d : Data) (h : Geometry d) :
    Icc (d.xpBox.lo : ℝ) (d.xpBox.hi : ℝ) ⊆
      Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ) := by
  intro x hx
  have hlo : (affineXpBox.lo : ℝ) ≤ (d.xpBox.lo : ℝ) := by
    exact_mod_cast h.global_xp_lo
  have hhi : (d.xpBox.hi : ℝ) ≤ (affineXpBox.hi : ℝ) := by
    exact_mod_cast h.global_xp_hi
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

end Data

/-- The local pair is the restriction of the whole-range affine pair. -/
theorem globalCrossingPair_eq_localPair (d : Data) (raw : RawChecks d) :
    (∀ k : Icc (d.kLo : ℝ) (d.kHi : ℝ),
      affineCrossingPair.xMinus
          ⟨k, d.parameter_mem_global raw.toGeometry k⟩ =
        (crossingPair d raw).xMinus k) ∧
    (∀ k : Icc (d.kLo : ℝ) (d.kHi : ℝ),
      affineCrossingPair.xPlus
          ⟨k, d.parameter_mem_global raw.toGeometry k⟩ =
        (crossingPair d raw).xPlus k) := by
  exact affineCrossingPair_eq_tightPair (crossingPair d raw)
    (d.parameter_mem_global raw.toGeometry)
    (d.minusBox_subset_global raw.toGeometry)
    (d.plusBox_subset_global raw.toGeometry)

/-- Per-cell affine calibration, stated directly on the globally selected
crossings used by the final table assembly. -/
theorem affineCalibration_along_globalCrossingPair
    (d : Data) (raw : RawChecks d) {ell : ℝ}
    (hell : ellBox.Contains ell) :
    ∀ k : Icc (d.kLo : ℝ) (d.kHi : ℝ),
      PlatformAffineCalibration k (highKPlatformEdge .affine k)
        (affineCrossingPair.xMinus
          ⟨k, d.parameter_mem_global raw.toGeometry k⟩)
        (affineCrossingPair.xPlus
          ⟨k, d.parameter_mem_global raw.toGeometry k⟩)
        (-1 / platformExteriorWx k (highKPlatformEdge .affine k)
          (affineCrossingPair.xMinus
            ⟨k, d.parameter_mem_global raw.toGeometry k⟩))
        (1 / platformExteriorWx k (highKPlatformEdge .affine k)
          (affineCrossingPair.xPlus
            ⟨k, d.parameter_mem_global raw.toGeometry k⟩))
        (platformEffectiveConstant ell k (highKPlatformEdge .affine k)
          (affineCrossingPair.xMinus
            ⟨k, d.parameter_mem_global raw.toGeometry k⟩)
          (affineCrossingPair.xPlus
            ⟨k, d.parameter_mem_global raw.toGeometry k⟩)
          (-1 / platformExteriorWx k (highKPlatformEdge .affine k)
            (affineCrossingPair.xMinus
              ⟨k, d.parameter_mem_global raw.toGeometry k⟩))
          (1 / platformExteriorWx k (highKPlatformEdge .affine k)
            (affineCrossingPair.xPlus
              ⟨k, d.parameter_mem_global raw.toGeometry k⟩))) := by
  intro k
  exact platformAffineCalibration_transfer_crossingPair
    affineCrossingPair (crossingPair d raw)
    (d.parameter_mem_global raw.toGeometry) k
    ((globalCrossingPair_eq_localPair d raw).1 k)
    ((globalCrossingPair_eq_localPair d raw).2 k)
    (affineCalibration_along_crossingPair d raw hell k)

end Erdos1038.HighKPlatformAffineCell
