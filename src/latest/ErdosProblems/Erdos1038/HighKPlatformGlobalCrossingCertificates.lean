import ErdosProblems.Erdos1038.HighKPlatformGlobalCrossingProbes
import ErdosProblems.Erdos1038.KernelDecision

/-!
# Compressed whole-range crossing certificates

Three branches are certified by one interval envelope each.  The affine
positive branch, whose transverse derivative is smallest at the low-edge
corner, uses an exact `8 × 8` rectangle cover while remaining one global
continuous branch.
-/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformGlobalCrossingCertificates

open Erdos1038 Set RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformGlobalCrossingProbes

theorem endpointBoxes_ordered (side : PlatformCrossingSide) (k x : Rat) :
    ∀ i, (endpointBoxes side k x i).Ordered := by
  cases side <;> intro i <;> fin_cases i <;>
    norm_num [endpointBoxes, zeroBox, point, RatInterval.Ordered]

theorem envelopeBoxes_ordered (side : PlatformCrossingSide)
    {K X : RatInterval} (hK : K.Ordered) (hX : X.Ordered) :
    ∀ i, (envelopeBoxes side K X i).Ordered := by
  cases side <;> intro i <;> fin_cases i <;>
    simp_all [envelopeBoxes, zeroBox, point, RatInterval.Ordered]

theorem endpointBoxes_contains (side : PlatformCrossingSide) (k x : Rat) :
    ∀ i, (endpointBoxes side k x i).Contains
      (crossingEnvironment side (k : ℝ) (x : ℝ) 0 0 0 i) := by
  cases side <;> intro i <;> fin_cases i <;>
    norm_num [endpointBoxes, crossingEnvironment, zeroBox, point,
      RatInterval.Contains]

theorem envelopeBoxes_contains (side : PlatformCrossingSide)
    {K X : RatInterval} {k x : ℝ}
    (hk : K.Contains k) (hx : X.Contains x) :
    ∀ i, (envelopeBoxes side K X i).Contains
      (crossingEnvironment side k x 0 0 0 i) := by
  cases side <;> intro i <;> fin_cases i <;>
    simp_all [envelopeBoxes, crossingEnvironment, zeroBox, point,
      RatInterval.Contains]

private theorem affineK_ordered : affineKBox.Ordered := by
  norm_num [affineKBox, RatInterval.Ordered]

private theorem affineXm_ordered : affineXmBox.Ordered := by
  norm_num [affineXmBox, RatInterval.Ordered]

private theorem affineXp_ordered : affineXpBox.Ordered := by
  norm_num [affineXpBox, RatInterval.Ordered]

private theorem constantK_ordered : constantKBox.Ordered := by
  norm_num [constantKBox, RatInterval.Ordered]

private theorem constantXm_ordered : constantXmBox.Ordered := by
  norm_num [constantXmBox, RatInterval.Ordered]

private theorem constantXp_ordered : constantXpBox.Ordered := by
  norm_num [constantXpBox, RatInterval.Ordered]

/-! ## The three single-envelope branch certificates -/

theorem affineMinusAtLo_signs :
    crossingBracketSigns .minus
      (endpointBoxes .minus affineKBox.lo affineXmBox.lo)
      (endpointBoxes .minus affineKBox.lo affineXmBox.hi)
      (crossingWE logTerms sqrtSteps .affine .minus) := by
  change EvalPositive _ _ ∧ EvalNegative _ _
  exact ⟨evalPositive_of_check (by kernel_decide),
    evalNegative_of_check (by kernel_decide)⟩

theorem affineMinusAtHi_signs :
    crossingBracketSigns .minus
      (endpointBoxes .minus affineKBox.hi affineXmBox.lo)
      (endpointBoxes .minus affineKBox.hi affineXmBox.hi)
      (crossingWE logTerms sqrtSteps .affine .minus) := by
  change EvalPositive _ _ ∧ EvalNegative _ _
  exact ⟨evalPositive_of_check (by kernel_decide),
    evalNegative_of_check (by kernel_decide)⟩

theorem affineMinusWx_sign : crossingWxSign .minus affineMinusEnvelope
    (crossingWxE sqrtSteps .affine .minus) := by
  change EvalNegative affineMinusEnvelope _
  exact evalNegative_of_check (by kernel_decide)

theorem affineMinusSlope_eval :
    evalInterval affineMinusEnvelope
      (crossingSlopeE logTerms sqrtSteps .affine .minus) =
        some affineMinusSlopeBox := by
  kernel_decide

def affineMinusCertificate : PlatformCrossingBranchCertificate
    logTerms sqrtSteps .affine .minus where
  atLoLeft := endpointBoxes .minus affineKBox.lo affineXmBox.lo
  atLoRight := endpointBoxes .minus affineKBox.lo affineXmBox.hi
  atHiLeft := endpointBoxes .minus affineKBox.hi affineXmBox.lo
  atHiRight := endpointBoxes .minus affineKBox.hi affineXmBox.hi
  envelope := affineMinusEnvelope
  orientation := .decreasing
  slopeBox := affineMinusSlopeBox
  atLoLeft_ordered := endpointBoxes_ordered _ _ _
  atLoRight_ordered := endpointBoxes_ordered _ _ _
  atHiLeft_ordered := endpointBoxes_ordered _ _ _
  atHiRight_ordered := endpointBoxes_ordered _ _ _
  envelope_ordered := envelopeBoxes_ordered _ affineK_ordered affineXm_ordered
  atLo_signs := affineMinusAtLo_signs
  atHi_signs := affineMinusAtHi_signs
  wx_sign := affineMinusWx_sign
  slope_eval := affineMinusSlope_eval
  slope_ordered := by
    change affineMinusSlopeBox.lo ≤ affineMinusSlopeBox.hi
    kernel_decide
  slope_sign := by
    change affineMinusSlopeBox.hi < 0
    kernel_decide

theorem constantMinusAtLo_signs :
    crossingBracketSigns .minus
      (endpointBoxes .minus constantKBox.lo constantXmBox.lo)
      (endpointBoxes .minus constantKBox.lo constantXmBox.hi)
      (crossingWE logTerms sqrtSteps .constant .minus) := by
  change EvalPositive _ _ ∧ EvalNegative _ _
  exact ⟨evalPositive_of_check (by kernel_decide),
    evalNegative_of_check (by kernel_decide)⟩

theorem constantMinusAtHi_signs :
    crossingBracketSigns .minus
      (endpointBoxes .minus constantKBox.hi constantXmBox.lo)
      (endpointBoxes .minus constantKBox.hi constantXmBox.hi)
      (crossingWE logTerms sqrtSteps .constant .minus) := by
  change EvalPositive _ _ ∧ EvalNegative _ _
  exact ⟨evalPositive_of_check (by kernel_decide),
    evalNegative_of_check (by kernel_decide)⟩

theorem constantMinusWx_sign : crossingWxSign .minus constantMinusEnvelope
    (crossingWxE sqrtSteps .constant .minus) := by
  change EvalNegative constantMinusEnvelope _
  exact evalNegative_of_check (by kernel_decide)

theorem constantMinusSlope_eval :
    evalInterval constantMinusEnvelope
      (crossingSlopeE logTerms sqrtSteps .constant .minus) =
        some constantMinusSlopeBox := by
  kernel_decide

def constantMinusCertificate : PlatformCrossingBranchCertificate
    logTerms sqrtSteps .constant .minus where
  atLoLeft := endpointBoxes .minus constantKBox.lo constantXmBox.lo
  atLoRight := endpointBoxes .minus constantKBox.lo constantXmBox.hi
  atHiLeft := endpointBoxes .minus constantKBox.hi constantXmBox.lo
  atHiRight := endpointBoxes .minus constantKBox.hi constantXmBox.hi
  envelope := constantMinusEnvelope
  orientation := .decreasing
  slopeBox := constantMinusSlopeBox
  atLoLeft_ordered := endpointBoxes_ordered _ _ _
  atLoRight_ordered := endpointBoxes_ordered _ _ _
  atHiLeft_ordered := endpointBoxes_ordered _ _ _
  atHiRight_ordered := endpointBoxes_ordered _ _ _
  envelope_ordered := envelopeBoxes_ordered _ constantK_ordered constantXm_ordered
  atLo_signs := constantMinusAtLo_signs
  atHi_signs := constantMinusAtHi_signs
  wx_sign := constantMinusWx_sign
  slope_eval := constantMinusSlope_eval
  slope_ordered := by
    change constantMinusSlopeBox.lo ≤ constantMinusSlopeBox.hi
    kernel_decide
  slope_sign := by
    change constantMinusSlopeBox.hi < 0
    kernel_decide

theorem constantPlusAtLo_signs :
    crossingBracketSigns .plus
      (endpointBoxes .plus constantKBox.lo constantXpBox.lo)
      (endpointBoxes .plus constantKBox.lo constantXpBox.hi)
      (crossingWE logTerms sqrtSteps .constant .plus) := by
  change EvalNegative _ _ ∧ EvalPositive _ _
  exact ⟨evalNegative_of_check (by kernel_decide),
    evalPositive_of_check (by kernel_decide)⟩

theorem constantPlusAtHi_signs :
    crossingBracketSigns .plus
      (endpointBoxes .plus constantKBox.hi constantXpBox.lo)
      (endpointBoxes .plus constantKBox.hi constantXpBox.hi)
      (crossingWE logTerms sqrtSteps .constant .plus) := by
  change EvalNegative _ _ ∧ EvalPositive _ _
  exact ⟨evalNegative_of_check (by kernel_decide),
    evalPositive_of_check (by kernel_decide)⟩

theorem constantPlusWx_sign : crossingWxSign .plus constantPlusEnvelope
    (crossingWxE sqrtSteps .constant .plus) := by
  change EvalPositive constantPlusEnvelope _
  exact evalPositive_of_check (by kernel_decide)

theorem constantPlusSlope_eval :
    evalInterval constantPlusEnvelope
      (crossingSlopeE logTerms sqrtSteps .constant .plus) =
        some constantPlusSlopeBox := by
  kernel_decide

def constantPlusCertificate : PlatformCrossingBranchCertificate
    logTerms sqrtSteps .constant .plus where
  atLoLeft := endpointBoxes .plus constantKBox.lo constantXpBox.lo
  atLoRight := endpointBoxes .plus constantKBox.lo constantXpBox.hi
  atHiLeft := endpointBoxes .plus constantKBox.hi constantXpBox.lo
  atHiRight := endpointBoxes .plus constantKBox.hi constantXpBox.hi
  envelope := constantPlusEnvelope
  orientation := .decreasing
  slopeBox := constantPlusSlopeBox
  atLoLeft_ordered := endpointBoxes_ordered _ _ _
  atLoRight_ordered := endpointBoxes_ordered _ _ _
  atHiLeft_ordered := endpointBoxes_ordered _ _ _
  atHiRight_ordered := endpointBoxes_ordered _ _ _
  envelope_ordered := envelopeBoxes_ordered _ constantK_ordered constantXp_ordered
  atLo_signs := constantPlusAtLo_signs
  atHi_signs := constantPlusAtHi_signs
  wx_sign := constantPlusWx_sign
  slope_eval := constantPlusSlope_eval
  slope_ordered := by
    change constantPlusSlopeBox.lo ≤ constantPlusSlopeBox.hi
    kernel_decide
  slope_sign := by
    change constantPlusSlopeBox.hi < 0
    kernel_decide

theorem affineMinusDiffDomain_check :
    HighKPlatformCrossingCertificates.diffDomainCheck affineMinusEnvelope
      (crossingWE logTerms sqrtSteps .affine .minus) = true := by
  kernel_decide

theorem affineMinusCorrection_check :
    HighKPlatformCrossingCertificates.evalNonzeroCheck
      affineMinusEnvelope affineMinusCorrectionE = true := by
  kernel_decide

theorem constantMinusDiffDomain_check :
    HighKPlatformCrossingCertificates.diffDomainCheck constantMinusEnvelope
      (crossingWE logTerms sqrtSteps .constant .minus) = true := by
  kernel_decide

theorem constantMinusCorrection_check :
    HighKPlatformCrossingCertificates.evalNonzeroCheck
      constantMinusEnvelope constantMinusCorrectionE = true := by
  kernel_decide

theorem constantPlusDiffDomain_check :
    HighKPlatformCrossingCertificates.diffDomainCheck constantPlusEnvelope
      (crossingWE logTerms sqrtSteps .constant .plus) = true := by
  kernel_decide

theorem constantPlusCorrection_check :
    HighKPlatformCrossingCertificates.evalNonzeroCheck
      constantPlusEnvelope constantPlusCorrectionE = true := by
  kernel_decide

/-! ## Whole-range branches from the three direct certificates -/

theorem existsUnique_affineMinusBranch :
    ∃! root : Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ) → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc (affineXmBox.lo : ℝ) (affineXmBox.hi : ℝ) ∧
          platformExteriorW k (highKPlatformEdge .affine k) (root k) = 0 := by
  apply affineMinusCertificate.existsUnique_continuous_crossing
      (other := 0) (ell := 0) (pi := 0)
  · exact_mod_cast affineK_ordered
  · exact_mod_cast affineXm_ordered
  · simpa [affineMinusCertificate] using!
      endpointBoxes_contains .minus affineKBox.lo affineXmBox.lo
  · simpa [affineMinusCertificate] using!
      endpointBoxes_contains .minus affineKBox.lo affineXmBox.hi
  · simpa [affineMinusCertificate] using!
      endpointBoxes_contains .minus affineKBox.hi affineXmBox.lo
  · simpa [affineMinusCertificate] using!
      endpointBoxes_contains .minus affineKBox.hi affineXmBox.hi
  · intro k hk x hx
    have hk' : affineKBox.Contains k := by
      simpa [RatInterval.Contains] using! hk
    have hx' : affineXmBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    simpa [affineMinusCertificate, affineMinusEnvelope] using!
      envelopeBoxes_contains .minus hk' hx'
  · intro x hx
    change x < 0
    have hupper := hx.2
    norm_num [affineXmBox] at hupper
    linarith
  · intro k hk
    have hkUpper := hk.2
    norm_num [affineKBox, highKPlatformEdge] at hkUpper ⊢
    linarith
  · intro k hk x hx
    have hkUpper := hk.2
    have hxUpper := hx.2
    norm_num [affineKBox, affineXmBox, highKPlatformEdge]
      at hkUpper hxUpper ⊢
    linarith
  · intro k hk
    have hkLower := hk.1
    norm_num [affineKBox, highKPlatformEdge] at hkLower ⊢
    linarith
  · intro k hk x hx
    have hk' : affineKBox.Contains k := by
      simpa [RatInterval.Contains] using! hk
    have hx' : affineXmBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    have hcontains := envelopeBoxes_contains .minus hk' hx'
    have hne :=
      HighKPlatformCrossingCertificates.evalReal_ne_zero_of_check
        affineMinusCertificate.envelope_ordered
        (by simpa [affineMinusCertificate, affineMinusEnvelope] using! hcontains)
        affineMinusCorrection_check
    simpa [affineMinusCorrectionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  · intro k hk x hx
    have hk' : affineKBox.Contains k := by
      simpa [RatInterval.Contains] using! hk
    have hx' : affineXmBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    apply HighKPlatformCrossingCertificates.diffDomain_of_check
      affineMinusCertificate.envelope_ordered
      (by simpa [affineMinusCertificate, affineMinusEnvelope] using!
        envelopeBoxes_contains .minus hk' hx')
    exact affineMinusDiffDomain_check

theorem existsUnique_constantMinusBranch :
    ∃! root : Icc (constantKBox.lo : ℝ) (constantKBox.hi : ℝ) → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc (constantXmBox.lo : ℝ) (constantXmBox.hi : ℝ) ∧
          platformExteriorW k (highKPlatformEdge .constant k) (root k) = 0 := by
  apply constantMinusCertificate.existsUnique_continuous_crossing
      (other := 0) (ell := 0) (pi := 0)
  · exact_mod_cast constantK_ordered
  · exact_mod_cast constantXm_ordered
  · simpa [constantMinusCertificate] using!
      endpointBoxes_contains .minus constantKBox.lo constantXmBox.lo
  · simpa [constantMinusCertificate] using!
      endpointBoxes_contains .minus constantKBox.lo constantXmBox.hi
  · simpa [constantMinusCertificate] using!
      endpointBoxes_contains .minus constantKBox.hi constantXmBox.lo
  · simpa [constantMinusCertificate] using!
      endpointBoxes_contains .minus constantKBox.hi constantXmBox.hi
  · intro k hk x hx
    have hk' : constantKBox.Contains k := by
      simpa [RatInterval.Contains] using! hk
    have hx' : constantXmBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    simpa [constantMinusCertificate, constantMinusEnvelope] using!
      envelopeBoxes_contains .minus hk' hx'
  · intro x hx
    change x < 0
    have hupper := hx.2
    norm_num [constantXmBox] at hupper
    linarith
  · intro k hk
    norm_num [highKPlatformEdge]
  · intro k hk x hx
    have hxUpper := hx.2
    norm_num [constantXmBox, highKPlatformEdge] at hxUpper ⊢
    linarith
  · intro k hk
    norm_num [highKPlatformEdge]
  · intro k hk x hx
    have hk' : constantKBox.Contains k := by
      simpa [RatInterval.Contains] using! hk
    have hx' : constantXmBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    have hcontains := envelopeBoxes_contains .minus hk' hx'
    have hne :=
      HighKPlatformCrossingCertificates.evalReal_ne_zero_of_check
        constantMinusCertificate.envelope_ordered
        (by simpa [constantMinusCertificate, constantMinusEnvelope] using! hcontains)
        constantMinusCorrection_check
    simpa [constantMinusCorrectionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  · intro k hk x hx
    have hk' : constantKBox.Contains k := by
      simpa [RatInterval.Contains] using! hk
    have hx' : constantXmBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    apply HighKPlatformCrossingCertificates.diffDomain_of_check
      constantMinusCertificate.envelope_ordered
      (by simpa [constantMinusCertificate, constantMinusEnvelope] using!
        envelopeBoxes_contains .minus hk' hx')
    exact constantMinusDiffDomain_check

theorem existsUnique_constantPlusBranch :
    ∃! root : Icc (constantKBox.lo : ℝ) (constantKBox.hi : ℝ) → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc (constantXpBox.lo : ℝ) (constantXpBox.hi : ℝ) ∧
          platformExteriorW k (highKPlatformEdge .constant k) (root k) = 0 := by
  apply constantPlusCertificate.existsUnique_continuous_crossing
      (other := 0) (ell := 0) (pi := 0)
  · exact_mod_cast constantK_ordered
  · exact_mod_cast constantXp_ordered
  · simpa [constantPlusCertificate] using!
      endpointBoxes_contains .plus constantKBox.lo constantXpBox.lo
  · simpa [constantPlusCertificate] using!
      endpointBoxes_contains .plus constantKBox.lo constantXpBox.hi
  · simpa [constantPlusCertificate] using!
      endpointBoxes_contains .plus constantKBox.hi constantXpBox.lo
  · simpa [constantPlusCertificate] using!
      endpointBoxes_contains .plus constantKBox.hi constantXpBox.hi
  · intro k hk x hx
    have hk' : constantKBox.Contains k := by
      simpa [RatInterval.Contains] using! hk
    have hx' : constantXpBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    simpa [constantPlusCertificate, constantPlusEnvelope] using!
      envelopeBoxes_contains .plus hk' hx'
  · intro x hx
    change 0 < x
    have hlower := hx.1
    norm_num [constantXpBox] at hlower
    linarith
  · intro k hk
    norm_num [highKPlatformEdge]
  · intro k hk x hx
    have hxUpper := hx.2
    norm_num [constantXpBox, highKPlatformEdge] at hxUpper ⊢
    linarith
  · intro k hk
    norm_num [highKPlatformEdge]
  · intro k hk x hx
    have hk' : constantKBox.Contains k := by
      simpa [RatInterval.Contains] using! hk
    have hx' : constantXpBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    have hcontains := envelopeBoxes_contains .plus hk' hx'
    have hne :=
      HighKPlatformCrossingCertificates.evalReal_ne_zero_of_check
        constantPlusCertificate.envelope_ordered
        (by simpa [constantPlusCertificate, constantPlusEnvelope] using! hcontains)
        constantPlusCorrection_check
    simpa [constantPlusCorrectionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  · intro k hk x hx
    have hk' : constantKBox.Contains k := by
      simpa [RatInterval.Contains] using! hk
    have hx' : constantXpBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    apply HighKPlatformCrossingCertificates.diffDomain_of_check
      constantPlusCertificate.envelope_ordered
      (by simpa [constantPlusCertificate, constantPlusEnvelope] using!
        envelopeBoxes_contains .plus hk' hx')
    exact constantPlusDiffDomain_check

/-! ## The affine positive branch on an exact `8 × 8` cover -/

theorem affinePlusDiffDomain_check :
    HighKPlatformCrossingCertificates.diffDomainCheck affinePlusEnvelope
      (crossingWE logTerms sqrtSteps .affine .plus) = true := by
  kernel_decide

theorem affinePlusCorrection_check :
    HighKPlatformCrossingCertificates.evalNonzeroCheck
      affinePlusEnvelope affinePlusCorrectionE = true := by
  kernel_decide

theorem affinePlusRect8Wx_check : ∀ i j : Fin 8,
    evalPositiveCheck (affinePlusRect8Envelope i j)
      (crossingWxE sqrtSteps .affine .plus) = true := by
  kernel_decide

theorem affinePlusRect8Slope_check : ∀ i j : Fin 8,
    evalPositiveCheck (affinePlusRect8Envelope i j)
      (crossingSlopeE logTerms sqrtSteps .affine .plus) = true := by
  kernel_decide

theorem affinePlusAtLo_signs :
    crossingBracketSigns .plus
      (endpointBoxes .plus affineKBox.lo affineXpBox.lo)
      (endpointBoxes .plus affineKBox.lo affineXpBox.hi)
      (crossingWE logTerms sqrtSteps .affine .plus) := by
  change EvalNegative _ _ ∧ EvalPositive _ _
  exact ⟨evalNegative_of_check (by kernel_decide),
    evalPositive_of_check (by kernel_decide)⟩

theorem affinePlusAtHi_signs :
    crossingBracketSigns .plus
      (endpointBoxes .plus affineKBox.hi affineXpBox.lo)
      (endpointBoxes .plus affineKBox.hi affineXpBox.hi)
      (crossingWE logTerms sqrtSteps .affine .plus) := by
  change EvalNegative _ _ ∧ EvalPositive _ _
  exact ⟨evalNegative_of_check (by kernel_decide),
    evalPositive_of_check (by kernel_decide)⟩

private theorem affinePlusOctantK_ordered (i : Fin 8) :
    (affinePlusOctantK i).Ordered := by
  change (affinePlusOctantK i).lo ≤ (affinePlusOctantK i).hi
  fin_cases i <;> kernel_decide

private theorem affinePlusRect8X_ordered (j : Fin 8) :
    (affinePlusRect8X j).Ordered := by
  change (affinePlusRect8X j).lo ≤ (affinePlusRect8X j).hi
  fin_cases j <;> kernel_decide

private theorem affinePlusRect8Envelope_ordered (i j : Fin 8) :
    ∀ q, (affinePlusRect8Envelope i j q).Ordered := by
  exact envelopeBoxes_ordered .plus
    (affinePlusOctantK_ordered i) (affinePlusRect8X_ordered j)

private theorem exists_affinePlusOctantK {k : ℝ}
    (hk : k ∈ Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ)) :
    ∃ i : Fin 8, (affinePlusOctantK i).Contains k := by
  have hk' : k ∈ Icc (36 / 25 : ℝ)
      ((36 / 25 : ℝ) + 8 * (33 / 400 : ℝ)) := by
    constructor
    · simpa [affineKBox] using! hk.1
    · have hupper := hk.2
      norm_num [affineKBox] at hupper ⊢
      exact hupper
  obtain ⟨i, hi⟩ := exists_uniformGrid_cell
    (start := (36 / 25 : ℝ)) (step := (33 / 400 : ℝ))
    (N := 8) (by norm_num) (by norm_num) hk'
  refine ⟨i, ?_⟩
  simpa [affinePlusOctantK, affinePlusNodeK, RatInterval.Contains,
    div_eq_mul_inv] using! hi

private theorem exists_affinePlusRect8X {x : ℝ}
    (hx : x ∈ Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ)) :
    ∃ j : Fin 8, (affinePlusRect8X j).Contains x := by
  have hx' : x ∈ Icc (affineXpBox.lo : ℝ)
      ((affineXpBox.lo : ℝ) + 8 *
        (((affineXpBox.hi - affineXpBox.lo) / 8 : Rat) : ℝ)) := by
    constructor
    · exact hx.1
    · have hupper := hx.2
      norm_num [affineXpBox] at hupper ⊢
      exact hupper
  obtain ⟨j, hj⟩ := exists_uniformGrid_cell
    (start := (affineXpBox.lo : ℝ))
    (step := (((affineXpBox.hi - affineXpBox.lo) / 8 : Rat) : ℝ))
    (N := 8) (by norm_num [affineXpBox]) (by norm_num) hx'
  refine ⟨j, ?_⟩
  simpa [affinePlusRect8X, affinePlusRect8XNode,
    RatInterval.Contains] using! hj

private theorem affinePlusWeakBracketAtLo :
    WeakCrossingBracket .plus
      (fun x ↦ platformExteriorW (affineKBox.lo : ℝ)
        (highKPlatformEdge .affine (affineKBox.lo : ℝ)) x)
      (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ) := by
  have hl := evalNegative_sound
    (endpointBoxes_ordered .plus affineKBox.lo affineXpBox.lo)
    (endpointBoxes_contains .plus affineKBox.lo affineXpBox.lo)
    affinePlusAtLo_signs.1
  have hr := evalPositive_sound
    (endpointBoxes_ordered .plus affineKBox.lo affineXpBox.hi)
    (endpointBoxes_contains .plus affineKBox.lo affineXpBox.hi)
    affinePlusAtLo_signs.2
  rw [crossingWE_eval logTerms sqrtSteps .affine .plus
    (by norm_num [CrossingCoordinateHasSide, affineXpBox])] at hl
  rw [crossingWE_eval logTerms sqrtSteps .affine .plus
    (by norm_num [CrossingCoordinateHasSide, affineXpBox])] at hr
  exact ⟨hl.le, hr.le⟩

private theorem affinePlusWeakBracketAtHi :
    WeakCrossingBracket .plus
      (fun x ↦ platformExteriorW (affineKBox.hi : ℝ)
        (highKPlatformEdge .affine (affineKBox.hi : ℝ)) x)
      (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ) := by
  have hl := evalNegative_sound
    (endpointBoxes_ordered .plus affineKBox.hi affineXpBox.lo)
    (endpointBoxes_contains .plus affineKBox.hi affineXpBox.lo)
    affinePlusAtHi_signs.1
  have hr := evalPositive_sound
    (endpointBoxes_ordered .plus affineKBox.hi affineXpBox.hi)
    (endpointBoxes_contains .plus affineKBox.hi affineXpBox.hi)
    affinePlusAtHi_signs.2
  rw [crossingWE_eval logTerms sqrtSteps .affine .plus
    (by norm_num [CrossingCoordinateHasSide, affineXpBox])] at hl
  rw [crossingWE_eval logTerms sqrtSteps .affine .plus
    (by norm_num [CrossingCoordinateHasSide, affineXpBox])] at hr
  exact ⟨hl.le, hr.le⟩

/-- The selected positive zero on the complete affine-edge range.  Unlike the
other three branches, its transverse and slope bounds are certified on an
exact `8 × 8` cover of the full parameter rectangle. -/
theorem existsUnique_affinePlusBranch :
    ∃! root : Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ) → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ) ∧
          platformExteriorW k (highKPlatformEdge .affine k) (root k) = 0 := by
  let F : ℝ → ℝ → ℝ := fun k x ↦
    platformExteriorW k (highKPlatformEdge .affine k) x
  let Fx : ℝ → ℝ → ℝ := fun k x ↦
    platformExteriorWx k (highKPlatformEdge .affine k) x
  let Fk : ℝ → ℝ → ℝ := fun k x ↦
    evalReal (crossingEnvironment .plus k x 0 0 0)
      (diffExpr 0 (crossingWE logTerms sqrtSteps .affine .plus))
  have hkOrder : (affineKBox.lo : ℝ) ≤ (affineKBox.hi : ℝ) := by
    exact_mod_cast affineK_ordered
  have hxOrder : (affineXpBox.lo : ℝ) ≤ (affineXpBox.hi : ℝ) := by
    exact_mod_cast affineXp_ordered
  have hcoordinate : ∀ x ∈
      Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ),
      CrossingCoordinateHasSide .plus x := by
    intro x hx
    change 0 < x
    have hlower := hx.1
    norm_num [affineXpBox] at hlower
    linarith
  have ha0 : ∀ k ∈ Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ),
      0 < highKPlatformEdge .affine k := by
    intro k hk
    have hkUpper := hk.2
    norm_num [affineKBox, highKPlatformEdge] at hkUpper ⊢
    linarith
  have hxa : ∀ k ∈ Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ),
      ∀ x ∈ Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ),
        x < highKPlatformEdge .affine k := by
    intro k hk x hx
    have hkUpper := hk.2
    have hxUpper := hx.2
    norm_num [affineKBox, affineXpBox, highKPlatformEdge]
      at hkUpper hxUpper ⊢
    linarith
  have ha2 : ∀ k ∈ Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ),
      highKPlatformEdge .affine k < 2 := by
    intro k hk
    have hkLower := hk.1
    norm_num [affineKBox, highKPlatformEdge] at hkLower ⊢
    linarith
  have hx0 : ∀ x ∈
      Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ), x ≠ 0 := by
    intro x hx
    exact (hcoordinate x hx).ne'
  have hcorr : ∀ k ∈
      Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ),
      ∀ x ∈ Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ),
        1 - ((Real.sqrt 2 - Real.sqrt (highKPlatformEdge .affine k)) /
          (Real.sqrt 2 + Real.sqrt (highKPlatformEdge .affine k))) *
            platformRho (highKPlatformEdge .affine k) x ≠ 0 := by
    intro k hk x hx
    have hk' : affineKBox.Contains k := by
      simpa [RatInterval.Contains] using! hk
    have hx' : affineXpBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    have hcontains := envelopeBoxes_contains .plus hk' hx'
    have hne :=
      HighKPlatformCrossingCertificates.evalReal_ne_zero_of_check
        (envelopeBoxes_ordered .plus affineK_ordered affineXp_ordered)
        (by simpa [affinePlusEnvelope] using! hcontains)
        affinePlusCorrection_check
    simpa [affinePlusCorrectionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  have hdom : ∀ k ∈
      Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ),
      ∀ x ∈ Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ),
        DiffDomain (crossingEnvironment .plus k x 0 0 0)
          (crossingWE logTerms sqrtSteps .affine .plus) := by
    intro k hk x hx
    have hk' : affineKBox.Contains k := by
      simpa [RatInterval.Contains] using! hk
    have hx' : affineXpBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    apply HighKPlatformCrossingCertificates.diffDomain_of_check
      (envelopeBoxes_ordered .plus affineK_ordered affineXp_ordered)
      (by simpa [affinePlusEnvelope] using!
        envelopeBoxes_contains .plus hk' hx')
    exact affinePlusDiffDomain_check
  have hstitch : ∃! root :
      Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ) → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ) ∧
          F k (root k) = 0 := by
    apply existsUnique_continuous_zeroBranch_of_endpointSlope
      (F := F) (Fx := Fx) (Fk := Fk) .plus .increasing hkOrder hxOrder
    · exact continuousOn_platformExteriorW_edge ha0 hxa ha2 hx0 hcorr
    · intro k hk x hx
      simpa [F, Fx] using! hasDerivAt_platformExteriorW_x
        (hxa k hk x hx) (ha2 k hk) (hx0 x hx) (hcorr k hk x hx)
    · intro x hx k hk
      simpa [F, Fk] using! hasDerivAt_platformExteriorW_alongEdge
        logTerms sqrtSteps .affine .plus (hcoordinate x hx)
          (hdom k hk x hx)
    · intro k hk x hx
      obtain ⟨i, hi⟩ := exists_affinePlusOctantK hk
      obtain ⟨j, hj⟩ := exists_affinePlusRect8X hx
      have hcontains := envelopeBoxes_contains .plus hi hj
      have hpositive := evalPositive_sound
        (affinePlusRect8Envelope_ordered i j)
        (by simpa [affinePlusRect8Envelope] using! hcontains)
        (evalPositive_of_check (affinePlusRect8Wx_check i j))
      simpa [Fx, TransverseHasSide] using! hpositive
    · intro k hk x hx
      obtain ⟨i, hi⟩ := exists_affinePlusOctantK hk
      obtain ⟨j, hj⟩ := exists_affinePlusRect8X hx
      have hcontains := envelopeBoxes_contains .plus hi hj
      have hs := evalPositive_sound
        (affinePlusRect8Envelope_ordered i j)
        (by simpa [affinePlusRect8Envelope] using! hcontains)
        (evalPositive_of_check (affinePlusRect8Slope_check i j))
      have hdom' : DiffDomain ![k, 0, x, 0, 0]
          (crossingWE logTerms sqrtSteps .affine .plus) := by
        simpa [crossingEnvironment] using! hdom k hk x hx
      simp only [crossingEnvironment] at hs
      rw [crossingSlopeE_eval_plus logTerms sqrtSteps .affine
        (hcoordinate x hx) hdom'] at hs
      have hd := hasDerivAt_platformExteriorW_alongEdge
        logTerms sqrtSteps .affine .plus (hcoordinate x hx)
          (hdom k hk x hx)
      rw [hd.deriv] at hs
      simpa [Fk, Fx, SlopeHasOrientation] using! hs
    · simpa [F] using! affinePlusWeakBracketAtLo
    · simpa [F] using! affinePlusWeakBracketAtHi
  simpa [F] using! hstitch

theorem nonempty_affineCrossingPair :
    Nonempty (ContinuousPlatformCrossingPair .affine
      (affineKBox.lo : ℝ) (affineKBox.hi : ℝ)
      (affineXmBox.lo : ℝ) (affineXmBox.hi : ℝ)
      (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ)) :=
  exists_crossingPair_of_uniqueBranches
    existsUnique_affineMinusBranch existsUnique_affinePlusBranch

noncomputable def affineCrossingPair :
    ContinuousPlatformCrossingPair .affine
      (affineKBox.lo : ℝ) (affineKBox.hi : ℝ)
      (affineXmBox.lo : ℝ) (affineXmBox.hi : ℝ)
      (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ) :=
  Classical.choice nonempty_affineCrossingPair

theorem nonempty_constantCrossingPair :
    Nonempty (ContinuousPlatformCrossingPair .constant
      (constantKBox.lo : ℝ) (constantKBox.hi : ℝ)
      (constantXmBox.lo : ℝ) (constantXmBox.hi : ℝ)
      (constantXpBox.lo : ℝ) (constantXpBox.hi : ℝ)) :=
  exists_crossingPair_of_uniqueBranches
    existsUnique_constantMinusBranch existsUnique_constantPlusBranch

noncomputable def constantCrossingPair :
    ContinuousPlatformCrossingPair .constant
      (constantKBox.lo : ℝ) (constantKBox.hi : ℝ)
      (constantXmBox.lo : ℝ) (constantXmBox.hi : ℝ)
      (constantXpBox.lo : ℝ) (constantXpBox.hi : ℝ) :=
  Classical.choice nonempty_constantCrossingPair

end Erdos1038.HighKPlatformGlobalCrossingCertificates
