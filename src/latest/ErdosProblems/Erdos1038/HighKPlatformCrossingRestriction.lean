import ErdosProblems.Erdos1038.HighKPlatformCrossing

/-!
# Restriction and identification of certified platform crossings

The numerical calibration is checked on narrow parameter/root boxes, while
the final high-`k` argument uses one crossing pair on each complete platform
regime.  This file supplies the purely analytic glue: restrict a global pair
to a parameter slab, and identify it with any tight local pair once the
exterior field is injective on the global root boxes.
-/

set_option warningAsError false

open Set

namespace Erdos1038

noncomputable section

open HighKPlatformFormula

namespace HighKPlatformFormula

/-- Restrict a certified crossing pair to a smaller parameter interval.  The
root boxes are unchanged; later identification lemmas can replace them by
tighter local boxes. -/
def ContinuousPlatformCrossingPair.restrict
    {edge : HighKPlatformEdge}
    {kLo kHi xmLo xmHi xpLo xpHi localLo localHi : ℝ}
    (branches : ContinuousPlatformCrossingPair edge
      kLo kHi xmLo xmHi xpLo xpHi)
    (hparam : ∀ k : Icc localLo localHi,
      (k : ℝ) ∈ Icc kLo kHi) :
    ContinuousPlatformCrossingPair edge
      localLo localHi xmLo xmHi xpLo xpHi where
  xMinus := fun k ↦ branches.xMinus ⟨k, hparam k⟩
  xPlus := fun k ↦ branches.xPlus ⟨k, hparam k⟩
  continuous_xMinus := branches.continuous_xMinus.comp
    (continuous_subtype_val.subtype_mk _)
  continuous_xPlus := branches.continuous_xPlus.comp
    (continuous_subtype_val.subtype_mk _)
  xMinus_mem := fun k ↦ branches.xMinus_mem ⟨k, hparam k⟩
  xPlus_mem := fun k ↦ branches.xPlus_mem ⟨k, hparam k⟩
  xMinus_zero := fun k ↦ by
    simpa using! branches.xMinus_zero ⟨k, hparam k⟩
  xPlus_zero := fun k ↦ by
    simpa using! branches.xPlus_zero ⟨k, hparam k⟩

@[simp] theorem ContinuousPlatformCrossingPair.restrict_xMinus
    {edge : HighKPlatformEdge}
    {kLo kHi xmLo xmHi xpLo xpHi localLo localHi : ℝ}
    (branches : ContinuousPlatformCrossingPair edge
      kLo kHi xmLo xmHi xpLo xpHi)
    (hparam : ∀ k : Icc localLo localHi,
      (k : ℝ) ∈ Icc kLo kHi)
    (k : Icc localLo localHi) :
    (branches.restrict hparam).xMinus k =
      branches.xMinus ⟨k, hparam k⟩ := rfl

@[simp] theorem ContinuousPlatformCrossingPair.restrict_xPlus
    {edge : HighKPlatformEdge}
    {kLo kHi xmLo xmHi xpLo xpHi localLo localHi : ℝ}
    (branches : ContinuousPlatformCrossingPair edge
      kLo kHi xmLo xmHi xpLo xpHi)
    (hparam : ∀ k : Icc localLo localHi,
      (k : ℝ) ∈ Icc kLo kHi)
    (k : Icc localLo localHi) :
    (branches.restrict hparam).xPlus k =
      branches.xPlus ⟨k, hparam k⟩ := rfl

/-- A checked uniform sign for the transverse derivative makes the exterior
field injective on the certified root interval.  This extracts the fibrewise
fact used implicitly by crossing-branch uniqueness, without requiring a
second global stitching argument. -/
theorem PlatformCrossingBranchCertificate.exterior_injOn
    {logTerms sqrtSteps : ℕ} {edge : HighKPlatformEdge}
    {side : PlatformCrossingSide}
    (cert : PlatformCrossingBranchCertificate
      logTerms sqrtSteps edge side)
    {k xLo xHi other ell pi : ℝ}
    (hcoordinate : ∀ x ∈ Icc xLo xHi,
      CrossingCoordinateHasSide side x)
    (hxa : ∀ x ∈ Icc xLo xHi,
      x < highKPlatformEdge edge k)
    (ha2 : highKPlatformEdge edge k < 2)
    (hcorr : ∀ x ∈ Icc xLo xHi,
      1 - ((Real.sqrt 2 - Real.sqrt (highKPlatformEdge edge k)) /
        (Real.sqrt 2 + Real.sqrt (highKPlatformEdge edge k))) *
          platformRho (highKPlatformEdge edge k) x ≠ 0)
    (henvelope : ∀ x ∈ Icc xLo xHi, ∀ i,
      (cert.envelope i).Contains
        (crossingEnvironment side k x other ell pi i)) :
    Set.InjOn
      (fun x ↦ platformExteriorW k (highKPlatformEdge edge k) x)
      (Icc xLo xHi) := by
  have hx0 : ∀ x ∈ Icc xLo xHi, x ≠ 0 := by
    intro x hx hxzero
    subst x
    have hs := hcoordinate 0 hx
    cases side <;> simp [CrossingCoordinateHasSide] at hs
  have hcontinuous : ContinuousOn
      (fun x ↦ platformExteriorW k (highKPlatformEdge edge k) x)
      (Icc xLo xHi) := by
    intro x hx
    exact (hasDerivAt_platformExteriorW_x
      (hxa x hx) ha2 (hx0 x hx) (hcorr x hx)).continuousAt.continuousWithinAt
  cases side with
  | minus =>
      apply (strictAntiOn_of_deriv_neg
        (convex_Icc xLo xHi) hcontinuous ?_).injOn
      intro x hx
      have hxmem : x ∈ Icc xLo xHi := interior_subset hx
      rw [(hasDerivAt_platformExteriorW_x
        (hxa x hxmem) ha2 (hx0 x hxmem) (hcorr x hxmem)).deriv]
      simpa [TransverseHasSide] using!
        cert.transverse_hasSide (henvelope x hxmem)
  | plus =>
      apply (strictMonoOn_of_deriv_pos
        (convex_Icc xLo xHi) hcontinuous ?_).injOn
      intro x hx
      have hxmem : x ∈ Icc xLo xHi := interior_subset hx
      rw [(hasDerivAt_platformExteriorW_x
        (hxa x hxmem) ha2 (hx0 x hxmem) (hcorr x hxmem)).deriv]
      simpa [TransverseHasSide] using!
        cert.transverse_hasSide (henvelope x hxmem)

/-- A tight local negative crossing is the restriction of the global
negative crossing whenever the exterior field is injective on the broad
negative root box. -/
theorem crossingPair_xMinus_eq_of_nested_injOn
    {edge : HighKPlatformEdge}
    {kLo kHi xmLo xmHi xpLo xpHi : ℝ}
    {localLo localHi localXmLo localXmHi localXpLo localXpHi : ℝ}
    (global : ContinuousPlatformCrossingPair edge
      kLo kHi xmLo xmHi xpLo xpHi)
    (tight : ContinuousPlatformCrossingPair edge
      localLo localHi localXmLo localXmHi localXpLo localXpHi)
    (hparam : ∀ k : Icc localLo localHi,
      (k : ℝ) ∈ Icc kLo kHi)
    (hxm : Icc localXmLo localXmHi ⊆ Icc xmLo xmHi)
    (hinj : ∀ k : Icc localLo localHi,
      Set.InjOn
        (fun x ↦ platformExteriorW k (highKPlatformEdge edge k) x)
        (Icc xmLo xmHi)) :
    ∀ k : Icc localLo localHi,
      global.xMinus ⟨k, hparam k⟩ = tight.xMinus k := by
  intro k
  apply hinj k
  · exact global.xMinus_mem ⟨k, hparam k⟩
  · exact hxm (tight.xMinus_mem k)
  · simpa using!
      (global.xMinus_zero ⟨k, hparam k⟩).trans
        (tight.xMinus_zero k).symm

/-- Positive-root counterpart of
`crossingPair_xMinus_eq_of_nested_injOn`. -/
theorem crossingPair_xPlus_eq_of_nested_injOn
    {edge : HighKPlatformEdge}
    {kLo kHi xmLo xmHi xpLo xpHi : ℝ}
    {localLo localHi localXmLo localXmHi localXpLo localXpHi : ℝ}
    (global : ContinuousPlatformCrossingPair edge
      kLo kHi xmLo xmHi xpLo xpHi)
    (tight : ContinuousPlatformCrossingPair edge
      localLo localHi localXmLo localXmHi localXpLo localXpHi)
    (hparam : ∀ k : Icc localLo localHi,
      (k : ℝ) ∈ Icc kLo kHi)
    (hxp : Icc localXpLo localXpHi ⊆ Icc xpLo xpHi)
    (hinj : ∀ k : Icc localLo localHi,
      Set.InjOn
        (fun x ↦ platformExteriorW k (highKPlatformEdge edge k) x)
        (Icc xpLo xpHi)) :
    ∀ k : Icc localLo localHi,
      global.xPlus ⟨k, hparam k⟩ = tight.xPlus k := by
  intro k
  apply hinj k
  · exact global.xPlus_mem ⟨k, hparam k⟩
  · exact hxp (tight.xPlus_mem k)
  · simpa using!
      (global.xPlus_zero ⟨k, hparam k⟩).trans
        (tight.xPlus_zero k).symm

/-- Simultaneous identification of both tight local exterior zeroes with
the restrictions of the globally selected pair. -/
theorem crossingPair_eq_of_nested_injOn
    {edge : HighKPlatformEdge}
    {kLo kHi xmLo xmHi xpLo xpHi : ℝ}
    {localLo localHi localXmLo localXmHi localXpLo localXpHi : ℝ}
    (global : ContinuousPlatformCrossingPair edge
      kLo kHi xmLo xmHi xpLo xpHi)
    (tight : ContinuousPlatformCrossingPair edge
      localLo localHi localXmLo localXmHi localXpLo localXpHi)
    (hparam : ∀ k : Icc localLo localHi,
      (k : ℝ) ∈ Icc kLo kHi)
    (hxm : Icc localXmLo localXmHi ⊆ Icc xmLo xmHi)
    (hxp : Icc localXpLo localXpHi ⊆ Icc xpLo xpHi)
    (hinjMinus : ∀ k : Icc localLo localHi,
      Set.InjOn
        (fun x ↦ platformExteriorW k (highKPlatformEdge edge k) x)
        (Icc xmLo xmHi))
    (hinjPlus : ∀ k : Icc localLo localHi,
      Set.InjOn
        (fun x ↦ platformExteriorW k (highKPlatformEdge edge k) x)
        (Icc xpLo xpHi)) :
    (∀ k : Icc localLo localHi,
      global.xMinus ⟨k, hparam k⟩ = tight.xMinus k) ∧
    (∀ k : Icc localLo localHi,
      global.xPlus ⟨k, hparam k⟩ = tight.xPlus k) := by
  exact ⟨crossingPair_xMinus_eq_of_nested_injOn
      global tight hparam hxm hinjMinus,
    crossingPair_xPlus_eq_of_nested_injOn
      global tight hparam hxp hinjPlus⟩

/-- Transfer an affine scalar certificate from a tight local crossing pair
to the restriction of the globally selected pair. -/
theorem platformAffineCalibration_transfer_crossingPair
    {edge : HighKPlatformEdge}
    {kLo kHi xmLo xmHi xpLo xpHi : ℝ}
    {localLo localHi localXmLo localXmHi localXpLo localXpHi ell : ℝ}
    (global : ContinuousPlatformCrossingPair edge
      kLo kHi xmLo xmHi xpLo xpHi)
    (tight : ContinuousPlatformCrossingPair edge
      localLo localHi localXmLo localXmHi localXpLo localXpHi)
    (hparam : ∀ k : Icc localLo localHi,
      (k : ℝ) ∈ Icc kLo kHi)
    (k : Icc localLo localHi)
    (hminus : global.xMinus ⟨k, hparam k⟩ = tight.xMinus k)
    (hplus : global.xPlus ⟨k, hparam k⟩ = tight.xPlus k)
    (hlocal : PlatformAffineCalibration k (highKPlatformEdge edge k)
      (tight.xMinus k) (tight.xPlus k)
      (-1 / platformExteriorWx k (highKPlatformEdge edge k)
        (tight.xMinus k))
      (1 / platformExteriorWx k (highKPlatformEdge edge k)
        (tight.xPlus k))
      (platformEffectiveConstant ell k (highKPlatformEdge edge k)
        (tight.xMinus k) (tight.xPlus k)
        (-1 / platformExteriorWx k (highKPlatformEdge edge k)
          (tight.xMinus k))
        (1 / platformExteriorWx k (highKPlatformEdge edge k)
          (tight.xPlus k)))) :
    PlatformAffineCalibration k (highKPlatformEdge edge k)
      (global.xMinus ⟨k, hparam k⟩) (global.xPlus ⟨k, hparam k⟩)
      (-1 / platformExteriorWx k (highKPlatformEdge edge k)
        (global.xMinus ⟨k, hparam k⟩))
      (1 / platformExteriorWx k (highKPlatformEdge edge k)
        (global.xPlus ⟨k, hparam k⟩))
      (platformEffectiveConstant ell k (highKPlatformEdge edge k)
        (global.xMinus ⟨k, hparam k⟩) (global.xPlus ⟨k, hparam k⟩)
        (-1 / platformExteriorWx k (highKPlatformEdge edge k)
          (global.xMinus ⟨k, hparam k⟩))
        (1 / platformExteriorWx k (highKPlatformEdge edge k)
          (global.xPlus ⟨k, hparam k⟩))) := by
  rw [hminus, hplus]
  exact hlocal

/-- Constant-edge counterpart of
`platformAffineCalibration_transfer_crossingPair`. -/
theorem platformConstantEdgeCalibration_transfer_crossingPair
    {edge : HighKPlatformEdge}
    {kLo kHi xmLo xmHi xpLo xpHi : ℝ}
    {localLo localHi localXmLo localXmHi localXpLo localXpHi ell : ℝ}
    (global : ContinuousPlatformCrossingPair edge
      kLo kHi xmLo xmHi xpLo xpHi)
    (tight : ContinuousPlatformCrossingPair edge
      localLo localHi localXmLo localXmHi localXpLo localXpHi)
    (hparam : ∀ k : Icc localLo localHi,
      (k : ℝ) ∈ Icc kLo kHi)
    (k : Icc localLo localHi)
    (hminus : global.xMinus ⟨k, hparam k⟩ = tight.xMinus k)
    (hplus : global.xPlus ⟨k, hparam k⟩ = tight.xPlus k)
    (hlocal : PlatformConstantEdgeCalibration k (highKPlatformEdge edge k)
      (tight.xMinus k) (tight.xPlus k)
      (-1 / platformExteriorWx k (highKPlatformEdge edge k)
        (tight.xMinus k))
      (1 / platformExteriorWx k (highKPlatformEdge edge k)
        (tight.xPlus k))
      (platformEffectiveConstant ell k (highKPlatformEdge edge k)
        (tight.xMinus k) (tight.xPlus k)
        (-1 / platformExteriorWx k (highKPlatformEdge edge k)
          (tight.xMinus k))
        (1 / platformExteriorWx k (highKPlatformEdge edge k)
          (tight.xPlus k)))) :
    PlatformConstantEdgeCalibration k (highKPlatformEdge edge k)
      (global.xMinus ⟨k, hparam k⟩) (global.xPlus ⟨k, hparam k⟩)
      (-1 / platformExteriorWx k (highKPlatformEdge edge k)
        (global.xMinus ⟨k, hparam k⟩))
      (1 / platformExteriorWx k (highKPlatformEdge edge k)
        (global.xPlus ⟨k, hparam k⟩))
      (platformEffectiveConstant ell k (highKPlatformEdge edge k)
        (global.xMinus ⟨k, hparam k⟩) (global.xPlus ⟨k, hparam k⟩)
        (-1 / platformExteriorWx k (highKPlatformEdge edge k)
          (global.xMinus ⟨k, hparam k⟩))
        (1 / platformExteriorWx k (highKPlatformEdge edge k)
          (global.xPlus ⟨k, hparam k⟩))) := by
  rw [hminus, hplus]
  exact hlocal

end HighKPlatformFormula

end

end Erdos1038
