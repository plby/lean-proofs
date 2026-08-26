import ErdosProblems.Erdos1038.HighKPlatformCrossingCertificates
import ErdosProblems.Erdos1038.KernelDecision

/-!
# Concrete affine-edge crossing certificate on the first calibration cell
-/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCrossingSmoke

open Erdos1038 Set RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformCrossingCertificates

def logTerms : ℕ := 80
def sqrtSteps : ℕ := 64

def kLo : Rat := 36 / 25
def kHi : Rat := 577 / 400

def kBox : RatInterval := ⟨kLo, kHi⟩

def xmBox : RatInterval :=
  ⟨-529477216924859 / 1000000000000000,
    -528928450561710 / 1000000000000000⟩

def xpBox : RatInterval :=
  ⟨1091428751156203 / 1000000000000000,
    1092148409502913 / 1000000000000000⟩

def zeroBox : RatInterval := point 0

def minusEnvelope : Fin 5 → RatInterval :=
  ![kBox, xmBox, zeroBox, zeroBox, zeroBox]

def plusEnvelope : Fin 5 → RatInterval :=
  ![kBox, zeroBox, xpBox, zeroBox, zeroBox]

def minusAtLoLeft : Fin 5 → RatInterval :=
  ![point kLo, point xmBox.lo, zeroBox, zeroBox, zeroBox]

def minusAtLoRight : Fin 5 → RatInterval :=
  ![point kLo, point xmBox.hi, zeroBox, zeroBox, zeroBox]

def minusAtHiLeft : Fin 5 → RatInterval :=
  ![point kHi, point xmBox.lo, zeroBox, zeroBox, zeroBox]

def minusAtHiRight : Fin 5 → RatInterval :=
  ![point kHi, point xmBox.hi, zeroBox, zeroBox, zeroBox]

def plusAtLoLeft : Fin 5 → RatInterval :=
  ![point kLo, zeroBox, point xpBox.lo, zeroBox, zeroBox]

def plusAtLoRight : Fin 5 → RatInterval :=
  ![point kLo, zeroBox, point xpBox.hi, zeroBox, zeroBox]

def plusAtHiLeft : Fin 5 → RatInterval :=
  ![point kHi, zeroBox, point xpBox.lo, zeroBox, zeroBox]

def plusAtHiRight : Fin 5 → RatInterval :=
  ![point kHi, zeroBox, point xpBox.hi, zeroBox, zeroBox]

def minusSlopeBox : RatInterval :=
  (evalInterval minusEnvelope
    (crossingSlopeE logTerms sqrtSteps .affine .minus)).getD zeroBox

def plusSlopeBox : RatInterval :=
  (evalInterval plusEnvelope
    (crossingSlopeE logTerms sqrtSteps .affine .plus)).getD zeroBox

theorem minusAtLo_signs :
    crossingBracketSigns .minus minusAtLoLeft minusAtLoRight
      (crossingWE logTerms sqrtSteps .affine .minus) := by
  change EvalPositive minusAtLoLeft _ ∧ EvalNegative minusAtLoRight _
  exact ⟨evalPositive_of_check (by kernel_decide),
    evalNegative_of_check (by kernel_decide)⟩

theorem minusAtHi_signs :
    crossingBracketSigns .minus minusAtHiLeft minusAtHiRight
      (crossingWE logTerms sqrtSteps .affine .minus) := by
  change EvalPositive minusAtHiLeft _ ∧ EvalNegative minusAtHiRight _
  exact ⟨evalPositive_of_check (by kernel_decide),
    evalNegative_of_check (by kernel_decide)⟩

theorem plusAtLo_signs :
    crossingBracketSigns .plus plusAtLoLeft plusAtLoRight
      (crossingWE logTerms sqrtSteps .affine .plus) := by
  change EvalNegative plusAtLoLeft _ ∧ EvalPositive plusAtLoRight _
  exact ⟨evalNegative_of_check (by kernel_decide),
    evalPositive_of_check (by kernel_decide)⟩

theorem plusAtHi_signs :
    crossingBracketSigns .plus plusAtHiLeft plusAtHiRight
      (crossingWE logTerms sqrtSteps .affine .plus) := by
  change EvalNegative plusAtHiLeft _ ∧ EvalPositive plusAtHiRight _
  exact ⟨evalNegative_of_check (by kernel_decide),
    evalPositive_of_check (by kernel_decide)⟩

theorem minusWx_sign : crossingWxSign .minus minusEnvelope
    (crossingWxE sqrtSteps .affine .minus) := by
  change EvalNegative minusEnvelope _
  exact evalNegative_of_check (by kernel_decide)

theorem plusWx_sign : crossingWxSign .plus plusEnvelope
    (crossingWxE sqrtSteps .affine .plus) := by
  change EvalPositive plusEnvelope _
  exact evalPositive_of_check (by kernel_decide)

theorem minusSlope_eval :
    evalInterval minusEnvelope
      (crossingSlopeE logTerms sqrtSteps .affine .minus) =
        some minusSlopeBox := by
  kernel_decide

theorem plusSlope_eval :
    evalInterval plusEnvelope
      (crossingSlopeE logTerms sqrtSteps .affine .plus) =
        some plusSlopeBox := by
  kernel_decide

theorem minusSlope_ordered : minusSlopeBox.Ordered := by
  change minusSlopeBox.lo ≤ minusSlopeBox.hi
  kernel_decide

theorem plusSlope_ordered : plusSlopeBox.Ordered := by
  change plusSlopeBox.lo ≤ plusSlopeBox.hi
  kernel_decide

theorem minusSlope_negative :
    slopeBoxSign .decreasing minusSlopeBox := by
  change minusSlopeBox.hi < 0
  kernel_decide

theorem plusSlope_positive :
    slopeBoxSign .increasing plusSlopeBox := by
  change 0 < plusSlopeBox.lo
  kernel_decide

private theorem ordered_boxes
    (X : Fin 5 → RatInterval)
    (h : ∀ i, (X i).Ordered) : ∀ i, (X i).Ordered := h

def minusCertificate : PlatformCrossingBranchCertificate
    logTerms sqrtSteps .affine .minus where
  atLoLeft := minusAtLoLeft
  atLoRight := minusAtLoRight
  atHiLeft := minusAtHiLeft
  atHiRight := minusAtHiRight
  envelope := minusEnvelope
  orientation := .decreasing
  slopeBox := minusSlopeBox
  atLoLeft_ordered := ordered_boxes _ (by
    intro i
    fin_cases i <;>
      norm_num [minusAtLoLeft, kLo, xmBox, zeroBox, point,
        RatInterval.Ordered])
  atLoRight_ordered := ordered_boxes _ (by
    intro i
    fin_cases i <;>
      norm_num [minusAtLoRight, kLo, xmBox, zeroBox, point,
        RatInterval.Ordered])
  atHiLeft_ordered := ordered_boxes _ (by
    intro i
    fin_cases i <;>
      norm_num [minusAtHiLeft, kHi, xmBox, zeroBox, point,
        RatInterval.Ordered])
  atHiRight_ordered := ordered_boxes _ (by
    intro i
    fin_cases i <;>
      norm_num [minusAtHiRight, kHi, xmBox, zeroBox, point,
        RatInterval.Ordered])
  envelope_ordered := ordered_boxes _ (by
    intro i
    fin_cases i <;>
      norm_num [minusEnvelope, kBox, kLo, kHi, xmBox, zeroBox, point,
        RatInterval.Ordered])
  atLo_signs := minusAtLo_signs
  atHi_signs := minusAtHi_signs
  wx_sign := minusWx_sign
  slope_eval := minusSlope_eval
  slope_ordered := minusSlope_ordered
  slope_sign := minusSlope_negative

def plusCertificate : PlatformCrossingBranchCertificate
    logTerms sqrtSteps .affine .plus where
  atLoLeft := plusAtLoLeft
  atLoRight := plusAtLoRight
  atHiLeft := plusAtHiLeft
  atHiRight := plusAtHiRight
  envelope := plusEnvelope
  orientation := .increasing
  slopeBox := plusSlopeBox
  atLoLeft_ordered := ordered_boxes _ (by
    intro i
    fin_cases i <;>
      norm_num [plusAtLoLeft, kLo, xpBox, zeroBox, point,
        RatInterval.Ordered])
  atLoRight_ordered := ordered_boxes _ (by
    intro i
    fin_cases i <;>
      norm_num [plusAtLoRight, kLo, xpBox, zeroBox, point,
        RatInterval.Ordered])
  atHiLeft_ordered := ordered_boxes _ (by
    intro i
    fin_cases i <;>
      norm_num [plusAtHiLeft, kHi, xpBox, zeroBox, point,
        RatInterval.Ordered])
  atHiRight_ordered := ordered_boxes _ (by
    intro i
    fin_cases i <;>
      norm_num [plusAtHiRight, kHi, xpBox, zeroBox, point,
        RatInterval.Ordered])
  envelope_ordered := ordered_boxes _ (by
    intro i
    fin_cases i <;>
      norm_num [plusEnvelope, kBox, kLo, kHi, xpBox, zeroBox, point,
        RatInterval.Ordered])
  atLo_signs := plusAtLo_signs
  atHi_signs := plusAtHi_signs
  wx_sign := plusWx_sign
  slope_eval := plusSlope_eval
  slope_ordered := plusSlope_ordered
  slope_sign := plusSlope_positive

def minusCorrectionE : HighKIntervalExpr 5 :=
  .sub e1 (.mul (rhoZeroE sqrtSteps .affine)
    (rhoE sqrtSteps .affine xmE))

def plusCorrectionE : HighKIntervalExpr 5 :=
  .sub e1 (.mul (rhoZeroE sqrtSteps .affine)
    (rhoE sqrtSteps .affine xpE))

theorem minusDiffDomain_check :
    diffDomainCheck minusEnvelope
      (crossingWE logTerms sqrtSteps .affine .minus) = true := by
  kernel_decide

theorem plusDiffDomain_check :
    diffDomainCheck plusEnvelope
      (crossingWE logTerms sqrtSteps .affine .plus) = true := by
  kernel_decide

theorem minusCorrection_check :
    evalNonzeroCheck minusEnvelope minusCorrectionE = true := by
  kernel_decide

theorem plusCorrection_check :
    evalNonzeroCheck plusEnvelope plusCorrectionE = true := by
  kernel_decide

private theorem minusAtLoLeft_contains : ∀ i,
    (minusAtLoLeft i).Contains
      (crossingEnvironment .minus (kLo : ℝ) (xmBox.lo : ℝ)
        0 0 0 i) := by
  intro i
  fin_cases i <;>
    norm_num [minusAtLoLeft, crossingEnvironment, kLo, xmBox, zeroBox,
      point, RatInterval.Contains]

private theorem minusAtLoRight_contains : ∀ i,
    (minusAtLoRight i).Contains
      (crossingEnvironment .minus (kLo : ℝ) (xmBox.hi : ℝ)
        0 0 0 i) := by
  intro i
  fin_cases i <;>
    norm_num [minusAtLoRight, crossingEnvironment, kLo, xmBox, zeroBox,
      point, RatInterval.Contains]

private theorem minusAtHiLeft_contains : ∀ i,
    (minusAtHiLeft i).Contains
      (crossingEnvironment .minus (kHi : ℝ) (xmBox.lo : ℝ)
        0 0 0 i) := by
  intro i
  fin_cases i <;>
    norm_num [minusAtHiLeft, crossingEnvironment, kHi, xmBox, zeroBox,
      point, RatInterval.Contains]

private theorem minusAtHiRight_contains : ∀ i,
    (minusAtHiRight i).Contains
      (crossingEnvironment .minus (kHi : ℝ) (xmBox.hi : ℝ)
        0 0 0 i) := by
  intro i
  fin_cases i <;>
    norm_num [minusAtHiRight, crossingEnvironment, kHi, xmBox, zeroBox,
      point, RatInterval.Contains]

private theorem plusAtLoLeft_contains : ∀ i,
    (plusAtLoLeft i).Contains
      (crossingEnvironment .plus (kLo : ℝ) (xpBox.lo : ℝ)
        0 0 0 i) := by
  intro i
  fin_cases i <;>
    norm_num [plusAtLoLeft, crossingEnvironment, kLo, xpBox, zeroBox,
      point, RatInterval.Contains]

private theorem plusAtLoRight_contains : ∀ i,
    (plusAtLoRight i).Contains
      (crossingEnvironment .plus (kLo : ℝ) (xpBox.hi : ℝ)
        0 0 0 i) := by
  intro i
  fin_cases i <;>
    norm_num [plusAtLoRight, crossingEnvironment, kLo, xpBox, zeroBox,
      point, RatInterval.Contains]

private theorem plusAtHiLeft_contains : ∀ i,
    (plusAtHiLeft i).Contains
      (crossingEnvironment .plus (kHi : ℝ) (xpBox.lo : ℝ)
        0 0 0 i) := by
  intro i
  fin_cases i <;>
    norm_num [plusAtHiLeft, crossingEnvironment, kHi, xpBox, zeroBox,
      point, RatInterval.Contains]

private theorem plusAtHiRight_contains : ∀ i,
    (plusAtHiRight i).Contains
      (crossingEnvironment .plus (kHi : ℝ) (xpBox.hi : ℝ)
        0 0 0 i) := by
  intro i
  fin_cases i <;>
    norm_num [plusAtHiRight, crossingEnvironment, kHi, xpBox, zeroBox,
      point, RatInterval.Contains]

private theorem minusEnvelope_contains {k x : ℝ}
    (hk : k ∈ Icc (kLo : ℝ) (kHi : ℝ))
    (hx : x ∈ Icc (xmBox.lo : ℝ) (xmBox.hi : ℝ)) : ∀ i,
    (minusEnvelope i).Contains
      (crossingEnvironment .minus k x 0 0 0 i) := by
  intro i
  fin_cases i
  · simpa [minusEnvelope, kBox, RatInterval.Contains] using! hk
  · simpa [minusEnvelope, RatInterval.Contains] using! hx
  · norm_num [minusEnvelope, crossingEnvironment, zeroBox, point,
      RatInterval.Contains]
  · norm_num [minusEnvelope, crossingEnvironment, zeroBox, point,
      RatInterval.Contains]
  · norm_num [minusEnvelope, crossingEnvironment, zeroBox, point,
      RatInterval.Contains]

private theorem plusEnvelope_contains {k x : ℝ}
    (hk : k ∈ Icc (kLo : ℝ) (kHi : ℝ))
    (hx : x ∈ Icc (xpBox.lo : ℝ) (xpBox.hi : ℝ)) : ∀ i,
    (plusEnvelope i).Contains
      (crossingEnvironment .plus k x 0 0 0 i) := by
  intro i
  fin_cases i
  · simpa [plusEnvelope, kBox, RatInterval.Contains] using! hk
  · norm_num [plusEnvelope, crossingEnvironment, zeroBox, point,
      RatInterval.Contains]
  · simpa [plusEnvelope, RatInterval.Contains] using! hx
  · norm_num [plusEnvelope, crossingEnvironment, zeroBox, point,
      RatInterval.Contains]
  · norm_num [plusEnvelope, crossingEnvironment, zeroBox, point,
      RatInterval.Contains]

theorem existsUnique_minusBranch :
    ∃! root : Icc (kLo : ℝ) (kHi : ℝ) → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc (xmBox.lo : ℝ) (xmBox.hi : ℝ) ∧
          platformExteriorW k (highKPlatformEdge .affine k) (root k) = 0 := by
  apply minusCertificate.existsUnique_continuous_crossing
      (other := 0) (ell := 0) (pi := 0)
  · norm_num [kLo, kHi]
  · norm_num [xmBox]
  · simpa [minusCertificate] using! minusAtLoLeft_contains
  · simpa [minusCertificate] using! minusAtLoRight_contains
  · simpa [minusCertificate] using! minusAtHiLeft_contains
  · simpa [minusCertificate] using! minusAtHiRight_contains
  · intro k hk x hx
    simpa [minusCertificate] using! minusEnvelope_contains hk hx
  · intro x hx
    change x < 0
    have hupper := hx.2
    norm_num [xmBox] at hupper
    linarith
  · intro k hk
    norm_num [highKPlatformEdge, kLo, kHi] at hk ⊢
    linarith
  · intro k hk x hx
    have hkUpper := hk.2
    have hxUpper := hx.2
    norm_num [kHi, xmBox, highKPlatformEdge] at hkUpper hxUpper ⊢
    linarith
  · intro k hk
    have hkLower := hk.1
    norm_num [kLo, highKPlatformEdge] at hkLower ⊢
    linarith
  · intro k hk x hx
    have hne := evalReal_ne_zero_of_check
      minusCertificate.envelope_ordered (minusEnvelope_contains hk hx)
      minusCorrection_check
    simpa [minusCorrectionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  · intro k hk x hx
    exact diffDomain_of_check minusCertificate.envelope_ordered
      (minusEnvelope_contains hk hx)
      (crossingWE logTerms sqrtSteps .affine .minus)
      minusDiffDomain_check

theorem existsUnique_plusBranch :
    ∃! root : Icc (kLo : ℝ) (kHi : ℝ) → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc (xpBox.lo : ℝ) (xpBox.hi : ℝ) ∧
          platformExteriorW k (highKPlatformEdge .affine k) (root k) = 0 := by
  apply plusCertificate.existsUnique_continuous_crossing
      (other := 0) (ell := 0) (pi := 0)
  · norm_num [kLo, kHi]
  · norm_num [xpBox]
  · simpa [plusCertificate] using! plusAtLoLeft_contains
  · simpa [plusCertificate] using! plusAtLoRight_contains
  · simpa [plusCertificate] using! plusAtHiLeft_contains
  · simpa [plusCertificate] using! plusAtHiRight_contains
  · intro k hk x hx
    simpa [plusCertificate] using! plusEnvelope_contains hk hx
  · intro x hx
    change 0 < x
    have hlower := hx.1
    norm_num [xpBox] at hlower
    linarith
  · intro k hk
    norm_num [highKPlatformEdge, kLo, kHi] at hk ⊢
    linarith
  · intro k hk x hx
    have hkUpper := hk.2
    have hxUpper := hx.2
    norm_num [kHi, xpBox, highKPlatformEdge] at hkUpper hxUpper ⊢
    linarith
  · intro k hk
    have hkLower := hk.1
    norm_num [kLo, highKPlatformEdge] at hkLower ⊢
    linarith
  · intro k hk x hx
    have hne := evalReal_ne_zero_of_check
      plusCertificate.envelope_ordered (plusEnvelope_contains hk hx)
      plusCorrection_check
    simpa [plusCorrectionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  · intro k hk x hx
    exact diffDomain_of_check plusCertificate.envelope_ordered
      (plusEnvelope_contains hk hx)
      (crossingWE logTerms sqrtSteps .affine .plus)
      plusDiffDomain_check

theorem nonempty_crossingPair :
    Nonempty (ContinuousPlatformCrossingPair .affine
      (kLo : ℝ) (kHi : ℝ)
      (xmBox.lo : ℝ) (xmBox.hi : ℝ)
      (xpBox.lo : ℝ) (xpBox.hi : ℝ)) :=
  exists_crossingPair_of_uniqueBranches
    existsUnique_minusBranch existsUnique_plusBranch

noncomputable def crossingPair :
    ContinuousPlatformCrossingPair .affine
      (kLo : ℝ) (kHi : ℝ)
      (xmBox.lo : ℝ) (xmBox.hi : ℝ)
      (xpBox.lo : ℝ) (xpBox.hi : ℝ) :=
  Classical.choice nonempty_crossingPair

def boxes : Fin 5 → RatInterval :=
  ![kBox, xmBox, xpBox,
    Erdos1038.HighKPlatformIntervalSmoke.ellBox,
    Erdos1038.HighKPlatformIntervalSmoke.piBox]

def trigDoubles : ℕ := 12
def fourierTerms : ℕ := 56
def derivativeLogTerms : ℕ := 16
def derivativeSqrtSteps : ℕ := 20
def derivativeTrigDoubles : ℕ := 8
def qCap : Rat := 309 / 100
def rCap : Rat := 5 / 3

def rBox : RatInterval :=
  (evalInterval boxes (rmaxE derivativeSqrtSteps .affine)).getD zeroBox

def qBox : RatInterval :=
  (evalInterval boxes (qmaxE derivativeSqrtSteps .affine)).getD zeroBox

def derivativeDomain : RatInterval := ⟨3 / 2, 309 / 100⟩

def derivativeCell (i : Fin 8) : RatInterval :=
  ⟨3 / 2 + i * (159 / 800),
    3 / 2 + (i + 1) * (159 / 800)⟩

def derivativeCells : List RatInterval := List.ofFn derivativeCell

theorem boxes_ordered : ∀ i, (boxes i).Ordered := by
  intro i
  fin_cases i
  · norm_num [boxes, kBox, kLo, kHi, RatInterval.Ordered]
  · norm_num [boxes, xmBox, RatInterval.Ordered]
  · norm_num [boxes, xpBox, RatInterval.Ordered]
  · simpa [boxes] using!
      Erdos1038.HighKPlatformIntervalSmoke.boxes_ordered 3
  · simpa [boxes] using!
      Erdos1038.HighKPlatformIntervalSmoke.boxes_ordered 4

theorem api_check : EvalPositive boxes (apiE sqrtSteps .affine) :=
  evalPositive_of_check (by kernel_decide)

theorem qmax_check : EvalPositive boxes (qmaxE sqrtSteps .affine) :=
  evalPositive_of_check (by kernel_decide)

theorem rmax_check : EvalPositive boxes (rmaxE sqrtSteps .affine) :=
  evalPositive_of_check (by kernel_decide)

theorem rltq_check : EvalNegative boxes
    (.sub (rmaxE sqrtSteps .affine) (qmaxE sqrtSteps .affine)) :=
  evalNegative_of_check (by kernel_decide)

theorem qcap_check : EvalNegative boxes
    (.sub (qmaxE sqrtSteps .affine) (.rat qCap)) :=
  evalNegative_of_check (by kernel_decide)

theorem rcap_check : EvalNegative boxes
    (.sub (rmaxE sqrtSteps .affine) (.rat rCap)) :=
  evalNegative_of_check (by kernel_decide)

theorem ceff_check : EvalNegative boxes
    (ceffE logTerms sqrtSteps .affine) :=
  evalNegative_of_check (by kernel_decide)

theorem r_eval :
    evalInterval boxes (rmaxE derivativeSqrtSteps .affine) = some rBox := by
  kernel_decide

theorem q_eval :
    evalInterval boxes (qmaxE derivativeSqrtSteps .affine) = some qBox := by
  kernel_decide

/-- The affine left-end check is redundant once the corner is positive and
the scalar derivative is negative on the complete interval: antitonicity
transports the positive value at `Qmax` back to `Rmax`.  This version of the
interval checker therefore needs only the corner certificate. -/
theorem affineEdgeCertificate_of_interval_without_left_of_derivative
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
    (hcorner : EvalPositive X
      (affineCornerLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap))
    (hderivativeNeg : ∀ Q ∈
      Ioo (evalReal v (rmaxE sqrtSteps edge))
        (evalReal v (qmaxE sqrtSteps edge)),
      affineCircleScalarDerivative
        (evalReal v (apiE sqrtSteps edge))
        (evalReal v (ceffE logTerms sqrtSteps edge))
        (evalReal v (rmaxE sqrtSteps edge)) Q < 0) :
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
  have hcorner' := evalPositive_sound hordered hcontains hcorner
  have hRQ : evalReal v (rmaxE sqrtSteps edge) <
      evalReal v (qmaxE sqrtSteps edge) := by
    simpa [HighKIntervalExpr.sub] using! hRltQ'
  have hQle : evalReal v (qmaxE sqrtSteps edge) ≤ (qCap : ℝ) := by
    simpa [HighKIntervalExpr.sub] using! hQcap'.le
  have hRle : evalReal v (rmaxE sqrtSteps edge) ≤ (rCap : ℝ) := by
    simpa [HighKIntervalExpr.sub] using! hRcap'.le
  have hcornerLower := affineCornerLowerE_le
    (logTerms := logTerms) (trigDoubles := trigDoubles) hN hpi
    hqCapPos hqCapPi hrCapPos hrCapPi hQmax' hRmax' hQle hRle
  have hcornerPos : 0 < affineCircleScalar
      (evalReal v (capacityE edge))
      (evalReal v (apiE sqrtSteps edge))
      (evalReal v (bpiE sqrtSteps edge))
      (evalReal v (ceffE logTerms sqrtSteps edge))
      (evalReal v (rmaxE sqrtSteps edge))
      (evalReal v (qmaxE sqrtSteps edge))
      (evalReal v (qmaxE sqrtSteps edge)) :=
    hcorner'.trans_le hcornerLower
  have hanti : AntitoneOn
      (affineCircleScalar
        (evalReal v (capacityE edge))
        (evalReal v (apiE sqrtSteps edge))
        (evalReal v (bpiE sqrtSteps edge))
        (evalReal v (ceffE logTerms sqrtSteps edge))
        (evalReal v (rmaxE sqrtSteps edge))
        (evalReal v (qmaxE sqrtSteps edge)))
      (Icc (evalReal v (rmaxE sqrtSteps edge))
        (evalReal v (qmaxE sqrtSteps edge))) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    · intro Q hQ
      exact (hasDerivAt_affineCircleScalar
        (hRmax'.trans_le hQ.1)).continuousAt.continuousWithinAt
    · intro Q hQ
      rw [interior_Icc] at hQ
      exact (hasDerivAt_affineCircleScalar
        (hRmax'.trans hQ.1)).hasDerivWithinAt
    · intro Q hQ
      rw [interior_Icc] at hQ
      exact (hderivativeNeg Q hQ).le
  have hleftScalar : 0 < affineCircleScalar
      (evalReal v (capacityE edge))
      (evalReal v (apiE sqrtSteps edge))
      (evalReal v (bpiE sqrtSteps edge))
      (evalReal v (ceffE logTerms sqrtSteps edge))
      (evalReal v (rmaxE sqrtSteps edge))
      (evalReal v (qmaxE sqrtSteps edge))
      (evalReal v (rmaxE sqrtSteps edge)) :=
    hcornerPos.trans_le
      (hanti ⟨le_rfl, hRQ.le⟩ ⟨hRQ.le, le_rfl⟩ hRQ.le)
  refine ⟨haPi', hRmax', hRQ, hQle.trans hqCapPi, hCeff', ?_,
    hcornerPos, hderivativeNeg⟩
  simpa [affineCircleScalar] using! hleftScalar

theorem affineEdgeCertificate_of_interval_without_left
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
  apply affineEdgeCertificate_of_interval_without_left_of_derivative
    hordered hcontains hN hpi hqCapPos hqCapPi hrCapPos hrCapPi
    haPi hQmax hRmax hRltQ hQcap hRcap hCeff hcorner
  exact affineDerivative_neg_of_boxCertificate hderivative
    hordered hcontains hpi (evalPositive_sound hordered hcontains hRmax)

/-- Platform specialization of
`affineEdgeCertificate_of_interval_without_left`. -/
theorem platformAffineCalibration_of_interval_without_left
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
  have hcert := affineEdgeCertificate_of_interval_without_left
    hordered hcontains hN (by simp) hqCapPos hqCapPi hrCapPos hrCapPi
    haPi hQmax hRmax hRltQ hQcap hRcap hCeff hcorner hderivative
  simpa only [PlatformAffineCalibration, capacityE_eval, apiE_eval,
    bpiE_eval sqrtSteps edge hxm hxp ha2,
    ceffE_eval logTerms sqrtSteps edge hxm hxp ha2,
    qmaxE_eval, rmaxE_eval sqrtSteps edge hxm hxp ha2] using! hcert

/-- The derivative enclosure may use independent approximation depths:
all choices evaluate to the same exact platform derivative, while smaller
depths can make the executable certificate substantially cheaper. -/
theorem platformAffineCalibration_of_interval_without_left_mixedDerivative
    {X : Fin 5 → RatInterval} {k xm xp ell : ℝ}
    {logTerms sqrtSteps trigDoubles N : ℕ}
    {derivativeLogTerms derivativeSqrtSteps derivativeTrigDoubles : ℕ}
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
    (hcorner : EvalPositive X
      (affineCornerLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap))
    (hderivative : AffineDerivativeBoxCertificate X
      derivativeLogTerms derivativeSqrtSteps derivativeTrigDoubles edge) :
    PlatformAffineCalibration k (highKPlatformEdge edge k) xm xp
      (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
      (1 / platformExteriorWx k (highKPlatformEdge edge k) xp)
      (platformEffectiveConstant ell k (highKPlatformEdge edge k) xm xp
        (-1 / platformExteriorWx k (highKPlatformEdge edge k) xm)
        (1 / platformExteriorWx k (highKPlatformEdge edge k) xp)) := by
  let v : Fin 5 → ℝ := ![k, xm, xp, ell, Real.pi]
  have hcontains' : ∀ i, (X i).Contains (v i) := by
    simpa only [v] using! hcontains
  have hRmaxMain : 0 < evalReal v (rmaxE sqrtSteps edge) :=
    evalPositive_sound hordered hcontains' hRmax
  have hRmaxDerivative :
      0 < evalReal v (rmaxE derivativeSqrtSteps edge) := by
    rw [rmaxE_eval derivativeSqrtSteps edge hxm hxp ha2]
    rw [rmaxE_eval sqrtSteps edge hxm hxp ha2] at hRmaxMain
    exact hRmaxMain
  have hderivativeNeg : ∀ Q ∈
      Ioo (evalReal v (rmaxE sqrtSteps edge))
        (evalReal v (qmaxE sqrtSteps edge)),
      affineCircleScalarDerivative
        (evalReal v (apiE sqrtSteps edge))
        (evalReal v (ceffE logTerms sqrtSteps edge))
        (evalReal v (rmaxE sqrtSteps edge)) Q < 0 := by
    intro Q hQ
    have hQ' : Q ∈ Ioo
        (evalReal v (rmaxE derivativeSqrtSteps edge))
        (evalReal v (qmaxE derivativeSqrtSteps edge)) := by
      simpa only [apiE_eval, qmaxE_eval,
        rmaxE_eval derivativeSqrtSteps edge hxm hxp ha2,
        rmaxE_eval sqrtSteps edge hxm hxp ha2] using! hQ
    have hd := affineDerivative_neg_of_boxCertificate hderivative
      hordered hcontains' (by simp [v]) hRmaxDerivative Q hQ'
    simpa only [apiE_eval,
      ceffE_eval derivativeLogTerms derivativeSqrtSteps edge hxm hxp ha2,
      ceffE_eval logTerms sqrtSteps edge hxm hxp ha2,
      rmaxE_eval derivativeSqrtSteps edge hxm hxp ha2,
      rmaxE_eval sqrtSteps edge hxm hxp ha2] using! hd
  have hcert := affineEdgeCertificate_of_interval_without_left_of_derivative
    hordered hcontains' hN (by simp [v]) hqCapPos hqCapPi
    hrCapPos hrCapPi haPi hQmax hRmax hRltQ hQcap hRcap hCeff hcorner
    hderivativeNeg
  simpa only [v, PlatformAffineCalibration, capacityE_eval, apiE_eval,
    bpiE_eval sqrtSteps edge hxm hxp ha2,
    ceffE_eval logTerms sqrtSteps edge hxm hxp ha2,
    qmaxE_eval, rmaxE_eval sqrtSteps edge hxm hxp ha2] using! hcert

/-- Fast semantic wrapper around the corner-only affine checker.  Keeping
the executable certificates as arguments lets the ordinary calibration
plumbing compile independently of their expensive exact evaluation. -/
theorem affineCalibration_along_crossingPair_of_certificates
    (hcorner : EvalPositive boxes
      (affineCornerLowerE logTerms sqrtSteps trigDoubles fourierTerms
        .affine qCap rCap))
    (hderivative : AffineDerivativeBoxCertificate boxes
      derivativeLogTerms derivativeSqrtSteps derivativeTrigDoubles .affine)
    {ell : ℝ}
    (hell : Erdos1038.HighKPlatformIntervalSmoke.ellBox.Contains ell) :
    ∀ k : Icc (kLo : ℝ) (kHi : ℝ),
      PlatformAffineCalibration k (highKPlatformEdge .affine k)
        (crossingPair.xMinus k) (crossingPair.xPlus k)
        (-1 / platformExteriorWx k (highKPlatformEdge .affine k)
          (crossingPair.xMinus k))
        (1 / platformExteriorWx k (highKPlatformEdge .affine k)
          (crossingPair.xPlus k))
        (platformEffectiveConstant ell k (highKPlatformEdge .affine k)
          (crossingPair.xMinus k) (crossingPair.xPlus k)
          (-1 / platformExteriorWx k (highKPlatformEdge .affine k)
            (crossingPair.xMinus k))
          (1 / platformExteriorWx k (highKPlatformEdge .affine k)
            (crossingPair.xPlus k))) := by
  intro k
  apply platformAffineCalibration_of_interval_without_left_mixedDerivative
    (X := boxes) (qCap := qCap) (rCap := rCap)
    (logTerms := logTerms) (sqrtSteps := sqrtSteps)
    (trigDoubles := trigDoubles) (N := fourierTerms)
    (derivativeLogTerms := derivativeLogTerms)
    (derivativeSqrtSteps := derivativeSqrtSteps)
    (derivativeTrigDoubles := derivativeTrigDoubles)
  · exact boxes_ordered
  · intro i
    fin_cases i
    · change (kLo : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ (kHi : ℝ)
      exact k.property
    · simpa [boxes, RatInterval.Contains] using! crossingPair.xMinus_mem k
    · simpa [boxes, RatInterval.Contains] using! crossingPair.xPlus_mem k
    · simpa [boxes] using! hell
    · simpa [boxes] using!
        Erdos1038.HighKPlatformIntervalSmoke.pi_mem_piBox
  ·
    have hkUpper := k.property.2
    have hxUpper := (crossingPair.xMinus_mem k).2
    norm_num [kHi, xmBox, highKPlatformEdge] at hkUpper hxUpper ⊢
    linarith
  ·
    have hkUpper := k.property.2
    have hxUpper := (crossingPair.xPlus_mem k).2
    norm_num [kHi, xpBox, highKPlatformEdge] at hkUpper hxUpper ⊢
    linarith
  ·
    have hkLower := k.property.1
    norm_num [kLo, highKPlatformEdge] at hkLower ⊢
    linarith
  · norm_num [fourierTerms]
  · norm_num [qCap]
  · have hpi := Real.pi_gt_d20
    norm_num [qCap] at hpi ⊢
    linarith
  · norm_num [rCap]
  · norm_num [rCap]
    linarith [Real.pi_gt_three]
  · exact api_check
  · exact qmax_check
  · exact rmax_check
  · exact rltq_check
  · exact qcap_check
  · exact rcap_check
  · exact ceff_check
  · exact hcorner
  · exact hderivative

/-! The two executable objects are deliberately last: all semantic plumbing
above is checked before either exact rational computation is started. -/

theorem corner_check : EvalPositive boxes
    (affineCornerLowerE logTerms sqrtSteps trigDoubles fourierTerms
      .affine qCap rCap) :=
  evalPositive_of_check (by kernel_decide)

theorem derivativeCells_checked : ∀ i : Fin 8,
    evalNegativeCheck (prependFin (derivativeCell i) boxes)
      (affineDerivativeCellE derivativeLogTerms derivativeSqrtSteps
        derivativeTrigDoubles .affine) = true := by
  kernel_decide

def derivativeCertificate : AffineDerivativeBoxCertificate boxes
    derivativeLogTerms derivativeSqrtSteps derivativeTrigDoubles .affine where
  domain := derivativeDomain
  cells := derivativeCells
  rBox := rBox
  qBox := qBox
  domain_ordered := by
    norm_num [derivativeDomain, RatInterval.Ordered]
  cells_ordered := by
    intro I hI
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hI
    norm_num [derivativeCell, RatInterval.Ordered]
  covers := by
    intro Q hQ
    have htop :
        ((3 / 2 : ℝ) + 8 * (159 / 800 : ℝ)) = 309 / 100 := by
      norm_num
    have hQ' : Q ∈ Icc (3 / 2 : ℝ)
        ((3 / 2 : ℝ) + 8 * (159 / 800 : ℝ)) := by
      rw [htop]
      simpa [derivativeDomain, RatInterval.Contains] using! hQ
    obtain ⟨i, hi⟩ := exists_uniformGrid_cell
      (start := (3 / 2 : ℝ)) (step := (159 / 800 : ℝ))
      (N := 8) (by norm_num) (by norm_num) hQ'
    refine ⟨derivativeCell i, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
    simpa [derivativeCell, RatInterval.Contains, div_eq_mul_inv] using! hi
  r_eval := r_eval
  q_eval := q_eval
  domain_lo_le := by
    kernel_decide
  q_hi_le := by
    kernel_decide
  checked := by
    intro I hI
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hI
    exact evalNegative_of_check (derivativeCells_checked i)

/-- End-to-end affine calibration on the first exact `1/400` grid cell,
with both exterior zeroes supplied by the checked continuous branches. -/
theorem affineCalibration_along_crossingPair
    {ell : ℝ}
    (hell : Erdos1038.HighKPlatformIntervalSmoke.ellBox.Contains ell) :
    ∀ k : Icc (kLo : ℝ) (kHi : ℝ),
      PlatformAffineCalibration k (highKPlatformEdge .affine k)
        (crossingPair.xMinus k) (crossingPair.xPlus k)
        (-1 / platformExteriorWx k (highKPlatformEdge .affine k)
          (crossingPair.xMinus k))
        (1 / platformExteriorWx k (highKPlatformEdge .affine k)
          (crossingPair.xPlus k))
        (platformEffectiveConstant ell k (highKPlatformEdge .affine k)
          (crossingPair.xMinus k) (crossingPair.xPlus k)
          (-1 / platformExteriorWx k (highKPlatformEdge .affine k)
            (crossingPair.xMinus k))
          (1 / platformExteriorWx k (highKPlatformEdge .affine k)
            (crossingPair.xPlus k))) :=
  affineCalibration_along_crossingPair_of_certificates
    corner_check derivativeCertificate hell

end Erdos1038.HighKPlatformAffineCrossingSmoke
