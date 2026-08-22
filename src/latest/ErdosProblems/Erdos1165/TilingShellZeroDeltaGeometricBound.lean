/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroSourceCapCoverage

/-!
# Concrete geometric bound for the actual-increment shell fibres

The source cofinal carrier supplies one literal exact-source reconstruction.
It fixes the prefix-correct static boundary geometry.  The finite-product
actual-increment partition then gives the geometric-mass comparison required
by the delta-indexed stopped-coordinate specification.
-/

open scoped ENNReal

namespace Erdos1165.TilingShellZeroDeltaGeometricBound

open FiniteDominoProductLaw HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroCentralTail
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open LazyDecomposition TilingLazyDecomposition
open TilingCappedMarginalization TilingOrientedSupportAwayCoordinates
open TilingPrefixedDeltaScreenGeometricBound
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroActualDeltaPartition
open TilingShellZeroDeltaReplacementFactorization
open TilingShellZeroDeltaScreenMassBound
open TilingShellZeroExternalStaticSupportData
open TilingShellZeroExternalStaticSupportPartition
open TilingShellZeroSourceCapCoverage TilingShellZeroSourcePartition
open TilingShellZeroSourceScreenForward
open TilingShellZeroSupportedSourceStaticFacts
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- For a nonempty exact-count slice, the central count is strictly smaller
than the source count. -/
theorem centralReplacementUpperCount_lt
    {total : ℕ} (htotal : 0 < total) :
    centralReplacementUpperCount shellZeroLocalRatioConstant total < total := by
  unfold centralReplacementUpperCount
  apply (Nat.floor_lt ?_).2
  · have hden : 0 < 1 + shellZeroLocalRatioConstant := by
      linarith [shellZeroLocalRatioConstant_pos]
    have hfrac : shellZeroLocalRatioConstant /
        (1 + shellZeroLocalRatioConstant) < 1 :=
      (div_lt_one hden).2 (by linarith [shellZeroLocalRatioConstant_pos])
    have htotalR : (0 : ℝ) < (total : ℝ) := Nat.cast_pos.mpr htotal
    simpa only [one_mul] using mul_lt_mul_of_pos_right hfrac htotalR
  · have hden0 : 0 ≤ 1 + shellZeroLocalRatioConstant := by
      linarith [shellZeroLocalRatioConstant_pos]
    exact mul_nonneg (div_nonneg shellZeroLocalRatioConstant_pos.le hden0)
      (Nat.cast_nonneg total)

/-- The zero-coordinate representative of the physical terminal has the
retained-coordinate boundary multiplicities on the static support. -/
theorem static_boundary_eq_coordinateCard
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) (hm : 1 < m) (hk : 0 < k) :
    ∀ b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
        (staticD eta.1.1 eta.1.2),
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (staticTerminal eta.1.1) b.1.1 =
        Fintype.card (TilingCoordinatesAt t eta.1.1.start
          eta.1.1.retained b.1) := by
  intro b
  exact boundaryLocalTime_eq_coordinateCard eta hm hk (fun _ ↦ 0) b.1
    ((away_mem_support_iff t eta.1.1.start eta.1.1.retained
      eta.1.2 b.1).1 b.2)

/-- Dominance of the source `V₂` support is a static boundary fact, hence
may be read at the zero-coordinate terminal representative. -/
theorem static_boundary_dominance
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total) (hm : 1 < m) (hk : 0 < k) :
    ∀ b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
        (staticD eta.1.1 eta.1.2),
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (staticTerminal eta.1.1)
            (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (staticTerminal eta.1.1) b.1.1 := by
  rcases eta.2 with ⟨s, hs⟩
  have hcomplete := source_complete eta hs
  rcases Set.mem_iUnion.mp hcomplete with ⟨cap, hcap⟩
  rcases hcap with ⟨_hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, _hq⟩
  have hdom := boundary_dominance_of_source eta hm hk q.1 q.2.1 q.2.2
  have hterminal : prefixedTilingInsertionTerminal eta.1.1.initial t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q.1 j : ℕ))
        eta.1.1.tail = staticTerminal eta.1.1 := by
    unfold staticTerminal
    exact prefixedTilingInsertionTerminal_eq_of_coordinates
      eta.1.1.initial t eta.1.1.start eta.1.1.retained
      (fun j ↦ (q.1 j : ℕ)) (fun _ ↦ 0) eta.1.1.tail rfl
  simpa only [hterminal] using hdom

/-- Concrete `ENNReal` geometric comparison for one supported source atom
and all of its honest actual-increment replacement clocks. -/
theorem geometric_bound
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total)
    (hm : 1 < m) (hk : 0 < k) (hlow : low < m) (htotal : 0 < total)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m externalLow externalHigh)
    (cap : ℕ) :
    ENNReal.ofReal (prefixedTilingStoppedAcceptedGeometricMass
        (sourceStoppingTime eta.1.1 m k cap) eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (coordinateCap eta.1.1 m cap)
        eta.1.1.tail.1 (sourcePredicate t o m k low externalLow externalHigh
          total cap eta.1.1 eta.1.2)) ≤
      ENNReal.ofReal
          (centralReplacementRatio shellZeroLocalRatioConstant total) *
        ∑' delta : ReplacementEndpointIncrement total
            (centralReplacementUpperCount shellZeroLocalRatioConstant total),
          ENNReal.ofReal (prefixedTilingStoppedAcceptedGeometricMass
            (replacementStoppingTime eta.1.1 m k cap delta)
            eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (coordinateCap eta.1.1 m cap) eta.1.1.tail.1
            (replacementPredicate eta cap
              (centralReplacementUpperCount shellZeroLocalRatioConstant total)
                delta)) := by
  classical
  apply ofReal_prefixedTilingStoppedAcceptedGeometricMass_le_delta_tsum
    (sourceStoppingTime eta.1.1 m k cap)
    (fun delta ↦ replacementStoppingTime eta.1.1 m k cap delta)
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained eta.1.1.tail.1
    (sourcePredicate t o m k low externalLow externalHigh total cap
      eta.1.1 eta.1.2)
    (fun delta ↦ replacementPredicate eta cap
      (centralReplacementUpperCount shellZeroLocalRatioConstant total) delta)
    (staticD eta.1.1 eta.1.2)
    (selected t o m k low externalLow externalHigh total cap
      eta.1.1 eta.1.2)
    (upper eta.1.1 eta.1.2 m)
    (sourceScreen t m cap eta.1.1 eta.1.2)
    (fun delta ↦ replacementScreen eta cap
      (centralReplacementUpperCount shellZeroLocalRatioConstant total) delta)
    (source_forward eta hm hk hexternal)
    (fun delta ↦ replacement_factorization eta hm hk hlow harithmetic
      hexternal (centralReplacementUpperCount_lt htotal) delta)
    (tilingAwayPointMass_normalization_ne_zero_of_upper_pos
      t eta.1.1.start eta.1.1.retained (staticD eta.1.1 eta.1.2)
        (upper eta.1.1 eta.1.2 m) (by intro b; unfold upper; omega))
    (centralReplacementRatio shellZeroLocalRatioConstant total)
    (centralReplacementRatio_nonneg shellZeroLocalRatioConstant_pos.le total)
  exact screenMass_source_le_ratio_mul_sum_actualDelta
    t eta.1.1.start eta.1.1.retained (staticD eta.1.1 eta.1.2)
      (upper eta.1.1 eta.1.2 m) eta.1.1.initial.1
      (staticTerminal eta.1.1) harithmetic
      ((coordinateSupportData t o m k (shellWidth48 m) low externalLow
        externalHigh total cap eta hm).toWindowData hexternal)
      (static_boundary_eq_coordinateCard eta hm hk)
      (static_boundary_dominance eta hm hk)

end

end Erdos1165.TilingShellZeroDeltaGeometricBound
