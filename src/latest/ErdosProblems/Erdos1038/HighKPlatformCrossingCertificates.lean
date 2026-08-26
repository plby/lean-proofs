import ErdosProblems.Erdos1038.HighKPlatformCrossing
import ErdosProblems.Erdos1038.HighKPlatformIntervalSmoke
import ErdosProblems.Erdos1038.KernelDecision

/-!
# Concrete exact crossing certificates for the first constant-edge smoke slab

This file turns the exact rational root enclosures already used by the
high-`k` interval smoke test into checked endpoint, transverse-derivative,
and implicit-slope certificates.
-/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformCrossingCertificates

open Erdos1038 Set RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula

def logTerms : ℕ := 80
def sqrtSteps : ℕ := 64

def kLo : Rat := 5 / 2
def kHi : Rat := 250001 / 100000

def kBox : RatInterval := ⟨kLo, kHi⟩

def xmBox : RatInterval :=
  ⟨-683501275752737 / 1000000000000000,
    -683500337311906 / 1000000000000000⟩

def xpBox : RatInterval :=
  ⟨1081574488993373 / 1000000000000000,
    1081575237859631 / 1000000000000000⟩

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
    (crossingSlopeE logTerms sqrtSteps .constant .minus)).getD zeroBox

def plusSlopeBox : RatInterval :=
  (evalInterval plusEnvelope
    (crossingSlopeE logTerms sqrtSteps .constant .plus)).getD zeroBox

/-! ## Executable differentiability-domain checking -/

/-- Check that a successfully evaluated rational interval stays away from
zero. -/
def evalNonzeroCheck {n : ℕ} (X : Fin n → RatInterval)
    (e : HighKIntervalExpr n) : Bool :=
  match evalInterval X e with
  | some I => decide (I.hi < 0 ∨ 0 < I.lo)
  | none => false

theorem evalReal_ne_zero_of_check {n : ℕ}
    {X : Fin n → RatInterval} {v : Fin n → ℝ}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (v i))
    {e : HighKIntervalExpr n} (hcheck : evalNonzeroCheck X e = true) :
    evalReal v e ≠ 0 := by
  cases heval : evalInterval X e with
  | none => simp [evalNonzeroCheck, heval] at hcheck
  | some I =>
      have hsound := (evalInterval_sound hordered hcontains e I heval).2
      have haway : I.hi < 0 ∨ 0 < I.lo := by
        simpa [evalNonzeroCheck, heval] using! hcheck
      rcases haway with hneg | hpos
      · have hnegReal : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
        exact ne_of_lt (hsound.2.trans_lt hnegReal)
      · have hposReal : 0 < (I.lo : ℝ) := by exact_mod_cast hpos
        exact ne_of_gt (hposReal.trans_le hsound.1)

/-- Recursively check every denominator and every logarithm/square-root
argument required by symbolic differentiation. -/
def diffDomainCheck {n : ℕ} (X : Fin n → RatInterval) :
    HighKIntervalExpr n → Bool
  | .rat _ => true
  | .var _ => true
  | .add p q => diffDomainCheck X p && diffDomainCheck X q
  | .neg p => diffDomainCheck X p
  | .mul p q => diffDomainCheck X p && diffDomainCheck X q
  | .inv p => diffDomainCheck X p && evalNonzeroCheck X p
  | .log _ p => diffDomainCheck X p && evalNonzeroCheck X p
  | .sqrt _ p => diffDomainCheck X p && evalNonzeroCheck X p
  | .sin _ p => diffDomainCheck X p
  | .cos _ p => diffDomainCheck X p

theorem diffDomain_of_check {n : ℕ}
    {X : Fin n → RatInterval} {v : Fin n → ℝ}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (v i)) :
    ∀ e : HighKIntervalExpr n,
      diffDomainCheck X e = true → DiffDomain v e := by
  intro e
  induction e with
  | rat r => simp [diffDomainCheck, DiffDomain]
  | var i => simp [diffDomainCheck, DiffDomain]
  | add p q ihp ihq =>
      intro h
      have hpq : diffDomainCheck X p = true ∧
          diffDomainCheck X q = true := by
        simpa [diffDomainCheck] using! h
      exact ⟨ihp hpq.1, ihq hpq.2⟩
  | neg p ih =>
      intro h
      exact ih h
  | mul p q ihp ihq =>
      intro h
      have hpq : diffDomainCheck X p = true ∧
          diffDomainCheck X q = true := by
        simpa [diffDomainCheck] using! h
      exact ⟨ihp hpq.1, ihq hpq.2⟩
  | inv p ih =>
      intro h
      have hp : diffDomainCheck X p = true ∧
          evalNonzeroCheck X p = true := by
        simpa [diffDomainCheck] using! h
      exact ⟨ih hp.1,
        evalReal_ne_zero_of_check hordered hcontains hp.2⟩
  | log terms p ih =>
      intro h
      have hp : diffDomainCheck X p = true ∧
          evalNonzeroCheck X p = true := by
        simpa [diffDomainCheck] using! h
      exact ⟨ih hp.1,
        evalReal_ne_zero_of_check hordered hcontains hp.2⟩
  | sqrt steps p ih =>
      intro h
      have hp : diffDomainCheck X p = true ∧
          evalNonzeroCheck X p = true := by
        simpa [diffDomainCheck] using! h
      exact ⟨ih hp.1,
        evalReal_ne_zero_of_check hordered hcontains hp.2⟩
  | sin doubles p ih =>
      intro h
      exact ih h
  | cos doubles p ih =>
      intro h
      exact ih h

theorem minusAtLo_signs :
    crossingBracketSigns .minus minusAtLoLeft minusAtLoRight
      (crossingWE logTerms sqrtSteps .constant .minus) := by
  change EvalPositive minusAtLoLeft _ ∧ EvalNegative minusAtLoRight _
  exact ⟨evalPositive_of_check (by kernel_decide),
    evalNegative_of_check (by kernel_decide)⟩

theorem minusAtHi_signs :
    crossingBracketSigns .minus minusAtHiLeft minusAtHiRight
      (crossingWE logTerms sqrtSteps .constant .minus) := by
  change EvalPositive minusAtHiLeft _ ∧ EvalNegative minusAtHiRight _
  exact ⟨evalPositive_of_check (by kernel_decide),
    evalNegative_of_check (by kernel_decide)⟩

theorem plusAtLo_signs :
    crossingBracketSigns .plus plusAtLoLeft plusAtLoRight
      (crossingWE logTerms sqrtSteps .constant .plus) := by
  change EvalNegative plusAtLoLeft _ ∧ EvalPositive plusAtLoRight _
  exact ⟨evalNegative_of_check (by kernel_decide),
    evalPositive_of_check (by kernel_decide)⟩

theorem plusAtHi_signs :
    crossingBracketSigns .plus plusAtHiLeft plusAtHiRight
      (crossingWE logTerms sqrtSteps .constant .plus) := by
  change EvalNegative plusAtHiLeft _ ∧ EvalPositive plusAtHiRight _
  exact ⟨evalNegative_of_check (by kernel_decide),
    evalPositive_of_check (by kernel_decide)⟩

theorem minusWx_sign : crossingWxSign .minus minusEnvelope
    (crossingWxE sqrtSteps .constant .minus) := by
  change EvalNegative minusEnvelope _
  exact evalNegative_of_check (by kernel_decide)

theorem plusWx_sign : crossingWxSign .plus plusEnvelope
    (crossingWxE sqrtSteps .constant .plus) := by
  change EvalPositive plusEnvelope _
  exact evalPositive_of_check (by kernel_decide)

theorem minusSlope_eval :
    evalInterval minusEnvelope
      (crossingSlopeE logTerms sqrtSteps .constant .minus) =
        some minusSlopeBox := by
  kernel_decide

theorem plusSlope_eval :
    evalInterval plusEnvelope
      (crossingSlopeE logTerms sqrtSteps .constant .plus) =
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

theorem plusSlope_negative :
    slopeBoxSign .decreasing plusSlopeBox := by
  change plusSlopeBox.hi < 0
  kernel_decide

private theorem ordered_boxes
    (X : Fin 5 → RatInterval)
    (h : ∀ i, (X i).Ordered) : ∀ i, (X i).Ordered := h

def minusCertificate : PlatformCrossingBranchCertificate
    logTerms sqrtSteps .constant .minus where
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
    logTerms sqrtSteps .constant .plus where
  atLoLeft := plusAtLoLeft
  atLoRight := plusAtLoRight
  atHiLeft := plusAtHiLeft
  atHiRight := plusAtHiRight
  envelope := plusEnvelope
  orientation := .decreasing
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
  slope_sign := plusSlope_negative

def minusCorrectionE : HighKIntervalExpr 5 :=
  .sub e1 (.mul (rhoZeroE sqrtSteps .constant)
    (rhoE sqrtSteps .constant xmE))

def plusCorrectionE : HighKIntervalExpr 5 :=
  .sub e1 (.mul (rhoZeroE sqrtSteps .constant)
    (rhoE sqrtSteps .constant xpE))

theorem minusDiffDomain_check :
    diffDomainCheck minusEnvelope
      (crossingWE logTerms sqrtSteps .constant .minus) = true := by
  kernel_decide

theorem plusDiffDomain_check :
    diffDomainCheck plusEnvelope
      (crossingWE logTerms sqrtSteps .constant .plus) = true := by
  kernel_decide

theorem minusCorrection_check :
    evalNonzeroCheck minusEnvelope minusCorrectionE = true := by
  kernel_decide

theorem plusCorrection_check :
    evalNonzeroCheck plusEnvelope plusCorrectionE = true := by
  kernel_decide

/-! ## Box containment and the two stitched branches -/

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
          platformExteriorW k (highKPlatformEdge .constant k) (root k) = 0 := by
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
    norm_num [highKPlatformEdge]
  · intro k hk x hx
    have hupper := hx.2
    norm_num [xmBox, highKPlatformEdge] at hupper ⊢
    linarith
  · intro k hk
    norm_num [highKPlatformEdge]
  · intro k hk x hx
    have hne := evalReal_ne_zero_of_check
      minusCertificate.envelope_ordered (minusEnvelope_contains hk hx)
      minusCorrection_check
    simpa [minusCorrectionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  · intro k hk x hx
    exact diffDomain_of_check minusCertificate.envelope_ordered
      (minusEnvelope_contains hk hx)
      (crossingWE logTerms sqrtSteps .constant .minus)
      minusDiffDomain_check

theorem existsUnique_plusBranch :
    ∃! root : Icc (kLo : ℝ) (kHi : ℝ) → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc (xpBox.lo : ℝ) (xpBox.hi : ℝ) ∧
          platformExteriorW k (highKPlatformEdge .constant k) (root k) = 0 := by
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
    norm_num [highKPlatformEdge]
  · intro k hk x hx
    have hupper := hx.2
    norm_num [xpBox, highKPlatformEdge] at hupper ⊢
    linarith
  · intro k hk
    norm_num [highKPlatformEdge]
  · intro k hk x hx
    have hne := evalReal_ne_zero_of_check
      plusCertificate.envelope_ordered (plusEnvelope_contains hk hx)
      plusCorrection_check
    simpa [plusCorrectionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  · intro k hk x hx
    exact diffDomain_of_check plusCertificate.envelope_ordered
      (plusEnvelope_contains hk hx)
      (crossingWE logTerms sqrtSteps .constant .plus)
      plusDiffDomain_check

theorem nonempty_constantSmokeCrossingPair :
    Nonempty (ContinuousPlatformCrossingPair .constant
      (kLo : ℝ) (kHi : ℝ)
      (xmBox.lo : ℝ) (xmBox.hi : ℝ)
      (xpBox.lo : ℝ) (xpBox.hi : ℝ)) :=
  exists_crossingPair_of_uniqueBranches
    existsUnique_minusBranch existsUnique_plusBranch

noncomputable def constantSmokeCrossingPair :
    ContinuousPlatformCrossingPair .constant
      (kLo : ℝ) (kHi : ℝ)
      (xmBox.lo : ℝ) (xmBox.hi : ℝ)
      (xpBox.lo : ℝ) (xpBox.hi : ℝ) :=
  Classical.choice nonempty_constantSmokeCrossingPair

/-- End-to-end connection from the two checked crossing branches to the
constant-edge scalar calibration on the smoke slab. -/
theorem constantCalibration_along_crossingPair
    {ell : ℝ}
    (hell : HighKPlatformIntervalSmoke.ellBox.Contains ell) :
    ∀ k : Icc (kLo : ℝ) (kHi : ℝ),
      PlatformConstantEdgeCalibration k (highKPlatformEdge .constant k)
        (constantSmokeCrossingPair.xMinus k)
        (constantSmokeCrossingPair.xPlus k)
        (-1 / platformExteriorWx k (highKPlatformEdge .constant k)
          (constantSmokeCrossingPair.xMinus k))
        (1 / platformExteriorWx k (highKPlatformEdge .constant k)
          (constantSmokeCrossingPair.xPlus k))
        (platformEffectiveConstant ell k (highKPlatformEdge .constant k)
          (constantSmokeCrossingPair.xMinus k)
          (constantSmokeCrossingPair.xPlus k)
          (-1 / platformExteriorWx k (highKPlatformEdge .constant k)
            (constantSmokeCrossingPair.xMinus k))
          (1 / platformExteriorWx k (highKPlatformEdge .constant k)
            (constantSmokeCrossingPair.xPlus k))) := by
  apply platformConstantEdgeCalibration_along_crossingPair_of_interval
    (X := HighKPlatformIntervalSmoke.boxes)
    (qCap := HighKPlatformIntervalSmoke.qCap)
    (rCap := HighKPlatformIntervalSmoke.rCap)
    (logTerms := HighKPlatformIntervalSmoke.logTerms)
    (sqrtSteps := HighKPlatformIntervalSmoke.sqrtSteps)
    (trigDoubles := HighKPlatformIntervalSmoke.trigDoubles)
    (N := HighKPlatformIntervalSmoke.fourierTerms)
    constantSmokeCrossingPair
  · exact HighKPlatformIntervalSmoke.boxes_ordered
  · intro k
    simpa [HighKPlatformIntervalSmoke.boxes,
      HighKPlatformIntervalSmoke.kBox, kLo, kHi,
      RatInterval.Contains] using! k.property
  · intro x hx
    simpa [HighKPlatformIntervalSmoke.boxes,
      HighKPlatformIntervalSmoke.xmBox, xmBox,
      RatInterval.Contains] using! hx
  · intro x hx
    simpa [HighKPlatformIntervalSmoke.boxes,
      HighKPlatformIntervalSmoke.xpBox, xpBox,
      RatInterval.Contains] using! hx
  · simpa [HighKPlatformIntervalSmoke.boxes] using! hell
  · simpa [HighKPlatformIntervalSmoke.boxes] using!
      HighKPlatformIntervalSmoke.pi_mem_piBox
  · intro k
    have hupper := (constantSmokeCrossingPair.xMinus_mem k).2
    norm_num [xmBox, highKPlatformEdge] at hupper ⊢
    linarith
  · intro k
    have hupper := (constantSmokeCrossingPair.xPlus_mem k).2
    norm_num [xpBox, highKPlatformEdge] at hupper ⊢
    linarith
  · intro k
    norm_num [highKPlatformEdge]
  · norm_num [HighKPlatformIntervalSmoke.fourierTerms]
  · norm_num [HighKPlatformIntervalSmoke.qCap]
  · norm_num [HighKPlatformIntervalSmoke.qCap]
    linarith [Real.pi_gt_three]
  · norm_num [HighKPlatformIntervalSmoke.rCap]
  · norm_num [HighKPlatformIntervalSmoke.rCap]
    linarith [Real.pi_gt_three]
  · exact HighKPlatformIntervalSmoke.api_check
  · exact HighKPlatformIntervalSmoke.qmax_check
  · exact HighKPlatformIntervalSmoke.rmax_check
  · exact HighKPlatformIntervalSmoke.qcap_check
  · exact HighKPlatformIntervalSmoke.rcap_check
  · exact HighKPlatformIntervalSmoke.ceff_check
  · exact HighKPlatformIntervalSmoke.endpoint_check

end Erdos1038.HighKPlatformCrossingCertificates
