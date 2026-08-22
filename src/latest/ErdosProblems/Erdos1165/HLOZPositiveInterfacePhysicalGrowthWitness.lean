/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceSupportSelector
import ErdosProblems.Erdos1165.HLOZAllSixBandProductClosure

/-!
# Physical witness extracted from a positive shell-growth failure

The thresholded recurrence is stated only in terms of cardinal-valued shell
occupancies.  Before applying a stopped coordinate product, one must recover
an actual physical site in the upper adjacent shell and then its represented
tiling coordinate.  This module proves that deterministic extraction.  It
does not assert that the site already lies in a screened stopped fibre; that
requires the separate exact-atom coordinate reconstruction.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfacePhysicalGrowthWitness

open HLOZAllSixBandProductClosure
open HLOZDynamicThresholdedScreening
open HLOZGapRandomClockScreen HLOZTilingGapRandomClockScreen
open HLOZPositiveInterfaceSupportSelector
open HLOZProposition48Candidates
open LazyDecomposition NearFavoriteShells NearFavoriteThresholded
open ScreeningInstantiation TilingLazyDecomposition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A cardinal growth failure at interface `shell` contains a literal member
of the upper shell `shell+1` in the dynamic thick candidate family. -/
theorem exists_dynamicUpperShellSite_of_thresholdedGrowthFailure
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    {threshold : ℕ → ℕ} {G shell : ℕ} {s : WalkPath}
    (hfailure : s ∈ thresholdedGrowthFailure
      (tilingBandOccupancy t m cutoff band) threshold G shell) :
    ∃ x,
      x ∈ dynamicThickCandidates
        (tilingRandomClockVisitedSites t m cutoff band)
        (tilingRandomClockExternalLargeEvent t m cutoff band)
        (tilingRandomClockDistinguishedSites t m cutoff band) s ∧
      deficitShellLabel (tilingRandomClockTotalLocalTime m cutoff band)
        m (shellWidth48 m) s x = shell + 1 := by
  have hpos : 0 < tilingBandOccupancy t m cutoff band s (shell + 1) :=
    lt_of_le_of_lt (Nat.zero_le _) hfailure.1
  change 0 < (shellCandidates
    (dynamicThickCandidates
      (tilingRandomClockVisitedSites t m cutoff band)
      (tilingRandomClockExternalLargeEvent t m cutoff band)
      (tilingRandomClockDistinguishedSites t m cutoff band) s)
    (deficitShellLabel (tilingRandomClockTotalLocalTime m cutoff band)
      m (shellWidth48 m) s) (shell + 1)).card at hpos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  rw [mem_shellCandidates] at hx
  exact ⟨x, hx.1, hx.2⟩

/-- Under the genuine old-rank favorite profile, the physical upper-shell
witness is represented by the concrete positive-interface support.  The
conclusion retains every raw fact needed by the later coordinate recovery. -/
theorem exists_positiveInterfaceSupportWitness_of_thresholdedGrowthFailure
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    {threshold : ℕ → ℕ} {G shell : ℕ} {s : WalkPath}
    (hvalid : s ∈ validStepWalk)
    (hn : 0 < pathTruncatedLevelTime m band.oldRank cutoff s)
    (hfavorite : thresholdSites s
      (pathTruncatedLevelTime m band.oldRank cutoff s) m =
        favoriteSites s
          (pathTruncatedLevelTime m band.oldRank cutoff s))
    (hthreshold : 0 < band.externalThreshold)
    (hphase : band.vertexPhase = false)
    (hfailure : s ∈ thresholdedGrowthFailure
      (tilingBandOccupancy t m cutoff band) threshold G shell) :
    ∃ x,
      x ∈ pathPhaseFilteredExternalVisitedSites t band.orientation false s
        (pathTruncatedLevelTime m band.oldRank cutoff s) ∧
      band.externalThreshold ≤
        pathPhaseFilteredExternalLocalTime t band.orientation false s
          (pathTruncatedLevelTime m band.oldRank cutoff s) x ∧
      x ∉ favoriteTilingDominoSites t s
        (pathTruncatedLevelTime m band.oldRank cutoff s) ∧
      (m - localTime s
          (pathTruncatedLevelTime m band.oldRank cutoff s) x) /
          shellWidth48 m = shell + 1 ∧
      tilingBase t x ∈ orientedPositiveInterfaceSupportAt t
        band.orientation m band.externalThreshold s
          (pathTruncatedLevelTime m band.oldRank cutoff s) := by
  obtain ⟨x, hxthick, hxshell⟩ :=
    exists_dynamicUpperShellSite_of_thresholdedGrowthFailure hfailure
  have hx :
      x ∈ tilingRandomClockVisitedSites t m cutoff band s ∧
      s ∈ tilingRandomClockExternalLargeEvent t m cutoff band x ∧
      x ∉ tilingRandomClockDistinguishedSites t m cutoff band s := by
    simpa only [dynamicThickCandidates, Finset.mem_filter] using hxthick
  have hvisited : x ∈ pathPhaseFilteredExternalVisitedSites t
      band.orientation false s
      (pathTruncatedLevelTime m band.oldRank cutoff s) := by
    simpa only [tilingRandomClockVisitedSites, hphase] using hx.1
  have hexternal : band.externalThreshold ≤
      pathPhaseFilteredExternalLocalTime t band.orientation false s
        (pathTruncatedLevelTime m band.oldRank cutoff s) x := by
    simpa only [tilingRandomClockExternalLargeEvent, Set.mem_ofPred_eq,
      hphase] using hx.2.1
  have hout : x ∉ favoriteTilingDominoSites t s
      (pathTruncatedLevelTime m band.oldRank cutoff s) := by
    simpa only [tilingRandomClockDistinguishedSites] using hx.2.2
  have hshell :
      (m - localTime s
        (pathTruncatedLevelTime m band.oldRank cutoff s) x) /
          shellWidth48 m = shell + 1 := by
    simpa only [deficitShellLabel, tilingRandomClockTotalLocalTime] using
      hxshell
  have hsupport := tilingBase_mem_orientedPositiveInterfaceSupportAt
    t band.orientation m band.externalThreshold s
      (pathTruncatedLevelTime m band.oldRank cutoff s)
      hvalid hn hfavorite hthreshold x hvisited hexternal hout
  exact ⟨x, hvisited, hexternal, hout, hshell, hsupport⟩

end

end Erdos1165.HLOZPositiveInterfacePhysicalGrowthWitness
