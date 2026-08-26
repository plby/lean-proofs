import ErdosProblems.Erdos1038.HighKPlatformGlobalCrossingCertificates
import ErdosProblems.Erdos1038.HighKPlatformCrossingRestriction
import ErdosProblems.Erdos1038.PlatformReferenceExteriorCrossingBridge
import ErdosProblems.Erdos1038.KernelDecision

/-!
# Fibrewise uniqueness for the global high-`k` crossing pairs

The whole-range branch certificates have a uniform nonzero transverse
derivative.  We expose the resulting pointwise injectivity on each broad root
box so that narrow slab certificates can be identified with the globally
selected roots.
-/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformGlobalCrossingRestriction

open Erdos1038 Set RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformGlobalCrossingProbes
open Erdos1038.HighKPlatformGlobalCrossingCertificates
open Erdos1038.HighKPlatformCrossingCertificates

theorem affineMinus_exterior_injOn
    (k : Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ)) :
    Set.InjOn
      (fun x ↦ platformExteriorW k (highKPlatformEdge .affine k) x)
      (Icc (affineXmBox.lo : ℝ) (affineXmBox.hi : ℝ)) := by
  apply affineMinusCertificate.exterior_injOn
      (k := (k : ℝ)) (other := 0) (ell := 0) (pi := 0)
  · intro x hx
    change x < 0
    have hupper := hx.2
    norm_num [affineXmBox] at hupper
    linarith
  · intro x hx
    have hkUpper := k.property.2
    have hxUpper := hx.2
    norm_num [affineKBox, affineXmBox, highKPlatformEdge]
      at hkUpper hxUpper ⊢
    linarith
  · have hkLower := k.property.1
    norm_num [affineKBox, highKPlatformEdge] at hkLower ⊢
    linarith
  · intro x hx
    have hk' : affineKBox.Contains (k : ℝ) := by
      exact k.property
    have hx' : affineXmBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    have hcontains := envelopeBoxes_contains .minus hk' hx'
    have hne := evalReal_ne_zero_of_check
      affineMinusCertificate.envelope_ordered
      (by simpa [affineMinusCertificate, affineMinusEnvelope] using! hcontains)
      affineMinusCorrection_check
    simpa [affineMinusCorrectionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  · intro x hx
    have hk' : affineKBox.Contains (k : ℝ) := by
      exact k.property
    have hx' : affineXmBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    simpa [affineMinusCertificate, affineMinusEnvelope] using!
      envelopeBoxes_contains .minus hk' hx'

theorem constantMinus_exterior_injOn
    (k : Icc (constantKBox.lo : ℝ) (constantKBox.hi : ℝ)) :
    Set.InjOn
      (fun x ↦ platformExteriorW k (highKPlatformEdge .constant k) x)
      (Icc (constantXmBox.lo : ℝ) (constantXmBox.hi : ℝ)) := by
  apply constantMinusCertificate.exterior_injOn
      (k := (k : ℝ)) (other := 0) (ell := 0) (pi := 0)
  · intro x hx
    change x < 0
    have hupper := hx.2
    norm_num [constantXmBox] at hupper
    linarith
  · intro x hx
    have hxUpper := hx.2
    norm_num [constantXmBox, highKPlatformEdge] at hxUpper ⊢
    linarith
  · norm_num [highKPlatformEdge]
  · intro x hx
    have hk' : constantKBox.Contains (k : ℝ) := by
      exact k.property
    have hx' : constantXmBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    have hcontains := envelopeBoxes_contains .minus hk' hx'
    have hne := evalReal_ne_zero_of_check
      constantMinusCertificate.envelope_ordered
      (by simpa [constantMinusCertificate, constantMinusEnvelope] using! hcontains)
      constantMinusCorrection_check
    simpa [constantMinusCorrectionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  · intro x hx
    have hk' : constantKBox.Contains (k : ℝ) := by
      exact k.property
    have hx' : constantXmBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    simpa [constantMinusCertificate, constantMinusEnvelope] using!
      envelopeBoxes_contains .minus hk' hx'

theorem constantPlus_exterior_injOn
    (k : Icc (constantKBox.lo : ℝ) (constantKBox.hi : ℝ)) :
    Set.InjOn
      (fun x ↦ platformExteriorW k (highKPlatformEdge .constant k) x)
      (Icc (constantXpBox.lo : ℝ) (constantXpBox.hi : ℝ)) := by
  apply constantPlusCertificate.exterior_injOn
      (k := (k : ℝ)) (other := 0) (ell := 0) (pi := 0)
  · intro x hx
    change 0 < x
    have hlower := hx.1
    norm_num [constantXpBox] at hlower
    linarith
  · intro x hx
    have hxUpper := hx.2
    norm_num [constantXpBox, highKPlatformEdge] at hxUpper ⊢
    linarith
  · norm_num [highKPlatformEdge]
  · intro x hx
    have hk' : constantKBox.Contains (k : ℝ) := by
      exact k.property
    have hx' : constantXpBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    have hcontains := envelopeBoxes_contains .plus hk' hx'
    have hne := evalReal_ne_zero_of_check
      constantPlusCertificate.envelope_ordered
      (by simpa [constantPlusCertificate, constantPlusEnvelope] using! hcontains)
      constantPlusCorrection_check
    simpa [constantPlusCorrectionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  · intro x hx
    have hk' : constantKBox.Contains (k : ℝ) := by
      exact k.property
    have hx' : constantXpBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    simpa [constantPlusCertificate, constantPlusEnvelope] using!
      envelopeBoxes_contains .plus hk' hx'

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

/-- The affine positive branch uses the checked `8 × 8` cover rather than
one broad transverse-derivative enclosure. -/
theorem affinePlus_exterior_injOn
    (k : Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ)) :
    Set.InjOn
      (fun x ↦ platformExteriorW k (highKPlatformEdge .affine k) x)
      (Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ)) := by
  have hcoordinate : ∀ x ∈
      Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ),
      CrossingCoordinateHasSide .plus x := by
    intro x hx
    change 0 < x
    have hlower := hx.1
    norm_num [affineXpBox] at hlower
    linarith
  have hxa : ∀ x ∈
      Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ),
      x < highKPlatformEdge .affine k := by
    intro x hx
    have hkUpper := k.property.2
    have hxUpper := hx.2
    norm_num [affineKBox, affineXpBox, highKPlatformEdge]
      at hkUpper hxUpper ⊢
    linarith
  have ha2 : highKPlatformEdge .affine k < 2 := by
    have hkLower := k.property.1
    norm_num [affineKBox, highKPlatformEdge] at hkLower ⊢
    linarith
  have hx0 : ∀ x ∈
      Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ), x ≠ 0 := by
    intro x hx
    exact (hcoordinate x hx).ne'
  have hcorr : ∀ x ∈
      Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ),
      1 - ((Real.sqrt 2 - Real.sqrt (highKPlatformEdge .affine k)) /
        (Real.sqrt 2 + Real.sqrt (highKPlatformEdge .affine k))) *
          platformRho (highKPlatformEdge .affine k) x ≠ 0 := by
    intro x hx
    have hk' : affineKBox.Contains (k : ℝ) := k.property
    have hx' : affineXpBox.Contains x := by
      simpa [RatInterval.Contains] using! hx
    have hcontains := envelopeBoxes_contains .plus hk' hx'
    have hne := evalReal_ne_zero_of_check
      (envelopeBoxes_ordered .plus (by
        norm_num [affineKBox, RatInterval.Ordered]) (by
        norm_num [affineXpBox, RatInterval.Ordered]))
      (by simpa [affinePlusEnvelope] using! hcontains)
      affinePlusCorrection_check
    simpa [affinePlusCorrectionE, highKPlatformEdge, crossingEnvironment,
      HighKIntervalExpr.sub] using! hne
  have hcontinuous : ContinuousOn
      (fun x ↦ platformExteriorW k (highKPlatformEdge .affine k) x)
      (Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ)) := by
    intro x hx
    exact (hasDerivAt_platformExteriorW_x
      (hxa x hx) ha2 (hx0 x hx) (hcorr x hx)).continuousAt.continuousWithinAt
  apply (strictMonoOn_of_deriv_pos
    (convex_Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ))
    hcontinuous ?_).injOn
  intro x hx
  have hxmem : x ∈
      Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ) :=
    interior_subset hx
  rw [(hasDerivAt_platformExteriorW_x
    (hxa x hxmem) ha2 (hx0 x hxmem) (hcorr x hxmem)).deriv]
  obtain ⟨i, hi⟩ := exists_affinePlusOctantK k.property
  obtain ⟨j, hj⟩ := exists_affinePlusRect8X hxmem
  have hcontains := envelopeBoxes_contains .plus hi hj
  have hpositive := evalPositive_sound
    (affinePlusRect8Envelope_ordered i j)
    (by simpa [affinePlusRect8Envelope] using! hcontains)
    (evalPositive_of_check (affinePlusRect8Wx_check i j))
  simpa [crossingWxE] using! hpositive

/-! ## Explicit slope data at the globally selected crossings -/

theorem affineMinus_exteriorWx_neg
    (k : Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ))
    (x : ℝ) (hx : x ∈ Icc (affineXmBox.lo : ℝ) (affineXmBox.hi : ℝ)) :
    platformExteriorWx k (highKPlatformEdge .affine k) x < 0 := by
  have hk' : affineKBox.Contains (k : ℝ) := k.property
  have hx' : affineXmBox.Contains x := by
    simpa [RatInterval.Contains] using! hx
  have hcontains := envelopeBoxes_contains .minus hk' hx'
  exact affineMinusCertificate.wx_negative_minus
    (by simpa [affineMinusCertificate, affineMinusEnvelope,
      crossingEnvironment] using! hcontains)

theorem affinePlus_exteriorWx_pos
    (k : Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ))
    (x : ℝ) (hx : x ∈ Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ)) :
    0 < platformExteriorWx k (highKPlatformEdge .affine k) x := by
  obtain ⟨i, hi⟩ := exists_affinePlusOctantK k.property
  obtain ⟨j, hj⟩ := exists_affinePlusRect8X hx
  have hcontains := envelopeBoxes_contains .plus hi hj
  have hpositive := evalPositive_sound
    (affinePlusRect8Envelope_ordered i j)
    (by simpa [affinePlusRect8Envelope] using! hcontains)
    (evalPositive_of_check (affinePlusRect8Wx_check i j))
  simpa [crossingWxE] using! hpositive

theorem constantMinus_exteriorWx_neg
    (k : Icc (constantKBox.lo : ℝ) (constantKBox.hi : ℝ))
    (x : ℝ) (hx : x ∈ Icc (constantXmBox.lo : ℝ) (constantXmBox.hi : ℝ)) :
    platformExteriorWx k (highKPlatformEdge .constant k) x < 0 := by
  have hk' : constantKBox.Contains (k : ℝ) := k.property
  have hx' : constantXmBox.Contains x := by
    simpa [RatInterval.Contains] using! hx
  have hcontains := envelopeBoxes_contains .minus hk' hx'
  exact constantMinusCertificate.wx_negative_minus
    (by simpa [constantMinusCertificate, constantMinusEnvelope,
      crossingEnvironment] using! hcontains)

theorem constantPlus_exteriorWx_pos
    (k : Icc (constantKBox.lo : ℝ) (constantKBox.hi : ℝ))
    (x : ℝ) (hx : x ∈ Icc (constantXpBox.lo : ℝ) (constantXpBox.hi : ℝ)) :
    0 < platformExteriorWx k (highKPlatformEdge .constant k) x := by
  have hk' : constantKBox.Contains (k : ℝ) := k.property
  have hx' : constantXpBox.Contains x := by
    simpa [RatInterval.Contains] using! hx
  have hcontains := envelopeBoxes_contains .plus hk' hx'
  exact constantPlusCertificate.wx_positive_plus
    (by simpa [constantPlusCertificate, constantPlusEnvelope,
      crossingEnvironment] using! hcontains)

/-- The whole affine crossing pair carries all explicit zero and transverse
slope data needed by the canonical reference bridge. -/
theorem affineCrossingPair_explicitCertificate
    (k : Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ)) :
    PlatformExplicitExteriorCrossingCertificate
      k (highKPlatformEdge .affine k)
      (affineCrossingPair.xMinus k) (affineCrossingPair.xPlus k) := by
  have hxm := affineCrossingPair.xMinus_mem k
  have hxp := affineCrossingPair.xPlus_mem k
  refine
    { xMinus_neg := ?_
      xPlus_pos := ?_
      xPlus_lt_platform := ?_
      xMinus_zero := affineCrossingPair.xMinus_zero k
      xPlus_zero := affineCrossingPair.xPlus_zero k
      xMinus_slope_neg := affineMinus_exteriorWx_neg k _ hxm
      xPlus_slope_pos := affinePlus_exteriorWx_pos k _ hxp }
  · have hupper := hxm.2
    norm_num [affineXmBox] at hupper
    linarith
  · have hlower := hxp.1
    norm_num [affineXpBox] at hlower
    linarith
  · have hkUpper := k.property.2
    have hxUpper := hxp.2
    norm_num [affineKBox, affineXpBox, highKPlatformEdge]
      at hkUpper hxUpper ⊢
    linarith

/-- Constant-edge counterpart of `affineCrossingPair_explicitCertificate`. -/
theorem constantCrossingPair_explicitCertificate
    (k : Icc (constantKBox.lo : ℝ) (constantKBox.hi : ℝ)) :
    PlatformExplicitExteriorCrossingCertificate
      k (highKPlatformEdge .constant k)
      (constantCrossingPair.xMinus k) (constantCrossingPair.xPlus k) := by
  have hxm := constantCrossingPair.xMinus_mem k
  have hxp := constantCrossingPair.xPlus_mem k
  refine
    { xMinus_neg := ?_
      xPlus_pos := ?_
      xPlus_lt_platform := ?_
      xMinus_zero := constantCrossingPair.xMinus_zero k
      xPlus_zero := constantCrossingPair.xPlus_zero k
      xMinus_slope_neg := constantMinus_exteriorWx_neg k _ hxm
      xPlus_slope_pos := constantPlus_exteriorWx_pos k _ hxp }
  · have hupper := hxm.2
    norm_num [constantXmBox] at hupper
    linarith
  · have hlower := hxp.1
    norm_num [constantXpBox] at hlower
    linarith
  · have hxUpper := hxp.2
    norm_num [constantXpBox, highKPlatformEdge] at hxUpper ⊢
    linarith

/-- Any tighter affine slab pair is the restriction of the certified
whole-range affine pair as soon as its rational parameter/root boxes are
nested in the broad global boxes. -/
theorem affineCrossingPair_eq_tightPair
    {localLo localHi localXmLo localXmHi localXpLo localXpHi : ℝ}
    (tight : ContinuousPlatformCrossingPair .affine
      localLo localHi localXmLo localXmHi localXpLo localXpHi)
    (hparam : ∀ k : Icc localLo localHi,
      (k : ℝ) ∈ Icc (affineKBox.lo : ℝ) (affineKBox.hi : ℝ))
    (hxm : Icc localXmLo localXmHi ⊆
      Icc (affineXmBox.lo : ℝ) (affineXmBox.hi : ℝ))
    (hxp : Icc localXpLo localXpHi ⊆
      Icc (affineXpBox.lo : ℝ) (affineXpBox.hi : ℝ)) :
    (∀ k : Icc localLo localHi,
      affineCrossingPair.xMinus ⟨k, hparam k⟩ = tight.xMinus k) ∧
    (∀ k : Icc localLo localHi,
      affineCrossingPair.xPlus ⟨k, hparam k⟩ = tight.xPlus k) := by
  apply crossingPair_eq_of_nested_injOn
    affineCrossingPair tight hparam hxm hxp
  · intro k
    exact affineMinus_exterior_injOn ⟨k, hparam k⟩
  · intro k
    exact affinePlus_exterior_injOn ⟨k, hparam k⟩

/-- Constant-edge counterpart of `affineCrossingPair_eq_tightPair`. -/
theorem constantCrossingPair_eq_tightPair
    {localLo localHi localXmLo localXmHi localXpLo localXpHi : ℝ}
    (tight : ContinuousPlatformCrossingPair .constant
      localLo localHi localXmLo localXmHi localXpLo localXpHi)
    (hparam : ∀ k : Icc localLo localHi,
      (k : ℝ) ∈ Icc (constantKBox.lo : ℝ) (constantKBox.hi : ℝ))
    (hxm : Icc localXmLo localXmHi ⊆
      Icc (constantXmBox.lo : ℝ) (constantXmBox.hi : ℝ))
    (hxp : Icc localXpLo localXpHi ⊆
      Icc (constantXpBox.lo : ℝ) (constantXpBox.hi : ℝ)) :
    (∀ k : Icc localLo localHi,
      constantCrossingPair.xMinus ⟨k, hparam k⟩ = tight.xMinus k) ∧
    (∀ k : Icc localLo localHi,
      constantCrossingPair.xPlus ⟨k, hparam k⟩ = tight.xPlus k) := by
  apply crossingPair_eq_of_nested_injOn
    constantCrossingPair tight hparam hxm hxp
  · intro k
    exact constantMinus_exterior_injOn ⟨k, hparam k⟩
  · intro k
    exact constantPlus_exterior_injOn ⟨k, hparam k⟩

end Erdos1038.HighKPlatformGlobalCrossingRestriction
