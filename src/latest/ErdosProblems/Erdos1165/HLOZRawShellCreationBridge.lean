/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZAllSixBandProductClosure
import ErdosProblems.Erdos1165.HLOZQuarterCutCentralTail
import ErdosProblems.Erdos1165.HLOZThetaSourceBalance

/-!
# Raw first-shell sites at the old creation clock

This file supplies the deterministic bridge between the shell-zero part of
the random-clock screen and the canonical/opposite source families used by
the source-correct product argument.

There is a small but important tie issue.  `tilingDominantEndpointAt` is not
constant on a domino when its two endpoint local times are equal: it returns
the endpoint supplied as its argument.  Consequently one cannot map an
arbitrary raw site directly by `tilingDominantEndpointAt` and identify the
result with the image obtained from canonical domino bases.  We instead
normalize first by `tilingBase`.  That map has fibers of size at most two,
while the dominant-endpoint map is injective on canonical bases belonging to
distinct dominoes.  Thus the source split loses exactly one factor two, as in
HLOZ, and the quarter cut remains valid.
-/

open Set

namespace Erdos1165.HLOZRawShellCreationBridge

open HLOZAllSixBandProductClosure HLOZDynamicThresholdedScreening
open HLOZGapRandomClockScreen HLOZPathEvents HLOZProposition48Candidates
open HLOZQuarterCutCentralTail
open HLOZThetaSourceBalance HLOZTilingGapBandExtraction
open HLOZTilingGapRandomClockScreen NearFavoriteShells
open ScreeningInstantiation TilingExternalPhaseSplit
open LazyDecomposition SpatialInsertionFiber
open TilingLazyDecomposition TilingShellZeroSourcePartition
open TilingOrientedShellZeroSourcePartition
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-! ## The literal first-shell Finset -/

/-- The actual finite set whose cardinal is shell-zero occupancy for one
state-dependent random-clock band. -/
noncomputable def tilingBandShellZeroSites
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (s : WalkPath) : Finset Point :=
  shellCandidates
    (dynamicThickCandidates (tilingRandomClockVisitedSites t m cutoff band)
      (tilingRandomClockExternalLargeEvent t m cutoff band)
      (tilingRandomClockDistinguishedSites t m cutoff band) s)
    (deficitShellLabel (tilingRandomClockTotalLocalTime m cutoff band)
      m (shellWidth48 m) s) 0

@[simp] theorem tilingBandShellZeroSites_card
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (s : WalkPath) :
    (tilingBandShellZeroSites t m cutoff band s).card =
      tilingBandOccupancy t m cutoff band s 0 := by
  rfl

/-! ## Elementary normalization facts -/

/-- A phase-filtered retained local time is bounded by the physical local
time at the same clock. -/
theorem pathPhaseFilteredExternalLocalTime_le_localTime
    (t : DominoTiling) (o : LazyDecomposition.Orientation) (phase : Bool)
    (s : WalkPath) (n : ℕ) (x : Point) :
    pathPhaseFilteredExternalLocalTime t o phase s n x ≤ localTime s n x := by
  have hsplit := localTime_eq_phasedBoundary_add_external_add_lazy
    t o s n x
  have hphase := phasedExternalLocalTime_eq_vertexPhase_sum t o
    (LazyDecomposition.finitePathList (pathPrefix s n)) x
  have hphase' : pathPhasedExternalLocalTime t o s n x =
      phasedExternalVertexLocalTime t o .endpoint
          (LazyDecomposition.finitePathList (pathPrefix s n)) x +
        phasedExternalVertexLocalTime t o .midpoint
          (LazyDecomposition.finitePathList (pathPrefix s n)) x := by
    simpa only [pathPhasedExternalLocalTime] using hphase
  cases phase <;>
    simp only [pathPhaseFilteredExternalLocalTime,
      externalVertexPhaseOfBool] <;>
    omega

/-- `xi+` is unchanged when a site is replaced by the canonical base of its
domino. -/
theorem tilingXiPlusAt_tilingBase
    (t : DominoTiling) (s : WalkPath) (n : ℕ) (x : Point) :
    tilingXiPlusAt t s n (tilingBase t x) = tilingXiPlusAt t s n x := by
  rcases point_eq_tilingBase_or_partner_base t x with hx | hx
  · rw [← hx]
  · rw [hx]
    simp only [tilingXiPlusAt, tilingBase_partner,
      TilingSpatialInsertionFiber.tilingBase_idem,
      tilingPartner_partner, max_comm]

/-- Canonical base normalization has fibers of cardinality at most two. -/
theorem card_le_two_mul_card_image_tilingBase
    (t : DominoTiling) (S : Finset Point) :
    S.card ≤ 2 * (S.image (tilingBase t)).card := by
  classical
  let B := S.image (tilingBase t)
  have hsub : S ⊆ B ∪ B.image (tilingPartner t) := by
    intro x hx
    rcases point_eq_tilingBase_or_partner_base t x with hbase | hpartner
    · rw [Finset.mem_union]
      left
      exact Finset.mem_image.mpr ⟨x, hx, hbase.symm⟩
    · rw [Finset.mem_union]
      right
      refine Finset.mem_image.mpr ⟨tilingBase t x, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      · exact hpartner.symm
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le B (B.image (tilingPartner t))
  have himage := Finset.card_image_le (s := B) (f := tilingPartner t)
  dsimp only [B] at hcard hunion himage ⊢
  omega

theorem tilingBase_dominantEndpointAt_of_isTilingBase
    (t : DominoTiling) (s : WalkPath) (n : ℕ) (b : Point)
    (hb : IsTilingBase t b) :
    tilingBase t (tilingDominantEndpointAt t s n b) = b := by
  rcases tilingDominantEndpointAt_eq_self_or_partner t s n b with h | h
  · rw [h]
    simp [tilingBase, hb]
  · rw [h, tilingBase_partner]
    simp [tilingBase, hb]

/-- Although direct normalization of arbitrary endpoints is tie-sensitive,
dominant normalization is injective after restricting the domain to
canonical bases.  Distinct bases represent distinct dominoes. -/
theorem tilingDominantEndpointAt_injOn_nearFavoriteBases
    (t : DominoTiling) (m k w : ℕ) (s : WalkPath) :
    Set.InjOn (tilingDominantEndpointAt t s (creationTimeNat m k s))
      (tilingNearFavoriteBasesAtCreation t m k w s : Set Point) := by
  intro b hb c hc hbc
  have hbBase : IsTilingBase t b :=
    isTilingBase_of_mem_visitedTilingBases
      (Finset.mem_filter.mp hb).1
  have hcBase : IsTilingBase t c :=
    isTilingBase_of_mem_visitedTilingBases
      (Finset.mem_filter.mp hc).1
  have hbase := congrArg (tilingBase t) hbc
  simpa only [tilingBase_dominantEndpointAt_of_isTilingBase
    t s (creationTimeNat m k s) b hbBase,
    tilingBase_dominantEndpointAt_of_isTilingBase
      t s (creationTimeNat m k s) c hcBase] using hbase

theorem tilingDominantNearBasesAtCreation_card_eq
    (t : DominoTiling) (m k w : ℕ) (s : WalkPath) :
    (tilingDominantNearBasesAtCreation t m k w s).card =
      (tilingNearFavoriteBasesAtCreation t m k w s).card := by
  unfold tilingDominantNearBasesAtCreation
  exact Finset.card_image_iff.mpr
    (tilingDominantEndpointAt_injOn_nearFavoriteBases t m k w s)

theorem tilingNearFavoriteBasesAtCreation_card_le_spatialSources
    (t : DominoTiling) (m k w : ℕ) (s : WalkPath) :
    (tilingNearFavoriteBasesAtCreation t m k w s).card ≤
      (tilingCanonicalDominantNearBasesAtCreation t m k w s).card +
        (tilingOppositeDominantNearEndpointsAtCreation t m k w s).card := by
  rw [← tilingDominantNearBasesAtCreation_card_eq t m k w s,
    tilingDominantNearBasesAtCreation_eq_canonical_union_opposite]
  exact Finset.card_union_le _ _

/-! ## Shell zero lies in the creation-time near-favorite family -/

private theorem physicalLocalTime_pos_of_mem_randomClockVisited
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    {s : WalkPath} {x : Point}
    (hx : x ∈ tilingRandomClockVisitedSites t m cutoff band s) :
    0 < localTime s (pathTruncatedLevelTime m band.oldRank cutoff s) x := by
  rw [tilingRandomClockVisitedSites,
    pathPhaseFilteredExternalVisitedSites] at hx
  change x ∈ tilingExternalPhaseVisitedSites t
    (externalVertexPhaseOfBool band.vertexPhase)
      (phasedInput band.orientation
        (LazyDecomposition.finitePathList (pathPrefix s
          (pathTruncatedLevelTime m band.oldRank cutoff s)))) at hx
  rw [mem_tilingExternalPhaseVisitedSites_iff] at hx
  exact hx.trans_le
    (pathPhaseFilteredExternalLocalTime_le_localTime t band.orientation
      band.vertexPhase s
        (pathTruncatedLevelTime m band.oldRank cutoff s) x)

/-- At an actual old creation clock with no level `m+1` site, every raw
shell-zero site normalizes to one of the literal near-favorite bases. -/
theorem image_tilingBase_tilingBandShellZeroSites_subset_nearFavorite
    {t : DominoTiling} {m cutoff n : ℕ} {band : RandomClockBand}
    {s : WalkPath}
    (hm : 0 < m)
    (hcreation : ThresholdCreation s m band.oldRank n)
    (hclock : pathTruncatedLevelTime m band.oldRank cutoff s = n)
    (hnext : thresholdCount s n (m + 1) = 0) :
    (tilingBandShellZeroSites t m cutoff band s).image (tilingBase t) ⊆
      tilingNearFavoriteBasesAtCreation t m band.oldRank
        (shellWidth48 m) s := by
  classical
  intro b hb
  rw [Finset.mem_image] at hb
  obtain ⟨x, hx, rfl⟩ := hb
  rw [tilingBandShellZeroSites, mem_shellCandidates] at hx
  rcases hx with ⟨hxCandidate, hxShell⟩
  rw [dynamicThickCandidates, Finset.mem_filter] at hxCandidate
  rcases hxCandidate with ⟨hxVisited, _hxLarge, hxDistinguished⟩
  have hcreationNat : creationTimeNat m band.oldRank s = n :=
    creationTimeNat_eq_of_creation hcreation
  have hwidth : 0 < shellWidth48 m := by
    unfold shellWidth48
    exact Nat.ceil_pos.mpr
      (Real.rpow_pos_of_pos (by exact_mod_cast hm) _)
  have hwidthLe : shellWidth48 m ≤ m := by
    unfold shellWidth48
    rw [Nat.ceil_le]
    have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
    calc
      (m : ℝ) ^ ScreeningInstantiation.kappaOne ≤ (m : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hmReal (by
          norm_num [ScreeningInstantiation.kappaOne])
      _ = m := by rw [Real.rpow_one]
  have hmax : ∀ y, localTime s n y < m + 1 :=
    (thresholdCount_eq_zero_iff_forall_lt s n (m + 1)
      (Nat.zero_lt_succ m)).mp hnext
  have hfavorite : thresholdSites s n m = favoriteSites s n :=
    thresholdSites_eq_favoriteSites_at_creation_of_terminal
      band.oldRank_pos hcreation le_rfl hnext
  rw [tilingRandomClockDistinguishedSites, favoriteTilingDominoSites,
    hclock, Finset.mem_union, not_or] at hxDistinguished
  have hxNotFavorite : x ∉ favoriteSites s n := hxDistinguished.1
  have hxPartnerNotFavorite : tilingPartner t x ∉ favoriteSites s n := by
    intro hxPartner
    apply hxDistinguished.2
    exact Finset.mem_image.mpr
      ⟨tilingPartner t x, hxPartner, tilingPartner_partner t x⟩
  have hxLt : localTime s n x < m := by
    have hxLe : localTime s n x ≤ m := Nat.lt_succ_iff.mp (hmax x)
    by_contra hnot
    apply hxNotFavorite
    rw [← hfavorite]
    exact (mem_thresholdSites_iff s n m x hm).mpr
      (Nat.le_of_not_gt hnot)
  have hxPartnerLt : localTime s n (tilingPartner t x) < m := by
    have hxLe : localTime s n (tilingPartner t x) ≤ m :=
      Nat.lt_succ_iff.mp (hmax (tilingPartner t x))
    by_contra hnot
    apply hxPartnerNotFavorite
    rw [← hfavorite]
    exact (mem_thresholdSites_iff s n m (tilingPartner t x) hm).mpr
      (Nat.le_of_not_gt hnot)
  have hxDeficit :
      (m - localTime s n x) / shellWidth48 m = 0 := by
    simpa only [deficitShellLabel, tilingRandomClockTotalLocalTime,
      hclock] using hxShell
  have hxDeficitLt : m - localTime s n x < shellWidth48 m :=
    Nat.lt_of_div_eq_zero hwidth hxDeficit
  have hxLower : m - shellWidth48 m + 1 ≤ localTime s n x := by
    omega
  have hxXiLower : m - shellWidth48 m + 1 ≤
      tilingXiPlusAt t s n (tilingBase t x) := by
    rw [tilingXiPlusAt_tilingBase]
    exact hxLower.trans (le_max_left _ _)
  have hxXiUpper : tilingXiPlusAt t s n (tilingBase t x) < m := by
    rw [tilingXiPlusAt_tilingBase]
    exact max_lt hxLt hxPartnerLt
  have hxPhysical : x ∈ visitedSites s n := by
    rw [mem_visitedSites_iff_localTime_pos]
    rw [← hclock]
    exact physicalLocalTime_pos_of_mem_randomClockVisited hxVisited
  rw [tilingNearFavoriteBasesAtCreation, hcreationNat,
    Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [visitedTilingBases, Finset.mem_image]
    exact ⟨x, hxPhysical, rfl⟩
  · rw [Finset.mem_union]
    left
    rw [HLOZShellZeroReplacementWindows.mem_shellZeroSourceTotalWindow]
    exact ⟨hxXiLower, hxXiUpper⟩

/-! ## The exact factor-two source split -/

theorem tilingBandShellZeroSites_card_le_two_spatialSources
    {t : DominoTiling} {m cutoff n : ℕ} {band : RandomClockBand}
    {s : WalkPath}
    (hm : 0 < m)
    (hcreation : ThresholdCreation s m band.oldRank n)
    (hclock : pathTruncatedLevelTime m band.oldRank cutoff s = n)
    (hnext : thresholdCount s n (m + 1) = 0) :
    (tilingBandShellZeroSites t m cutoff band s).card ≤
      2 * ((tilingCanonicalDominantNearBasesAtCreation t m band.oldRank
          (shellWidth48 m) s).card +
        (tilingOppositeDominantNearEndpointsAtCreation t m band.oldRank
          (shellWidth48 m) s).card) := by
  calc
    (tilingBandShellZeroSites t m cutoff band s).card ≤
        2 * ((tilingBandShellZeroSites t m cutoff band s).image
          (tilingBase t)).card :=
      card_le_two_mul_card_image_tilingBase t _
    _ ≤ 2 * (tilingNearFavoriteBasesAtCreation t m band.oldRank
          (shellWidth48 m) s).card := by
      exact Nat.mul_le_mul_left 2 (Finset.card_le_card
        (image_tilingBase_tilingBandShellZeroSites_subset_nearFavorite
          hm hcreation hclock hnext))
    _ ≤ _ := Nat.mul_le_mul_left 2
      (tilingNearFavoriteBasesAtCreation_card_le_spatialSources
        t m band.oldRank (shellWidth48 m) s)

/-- Pigeonhole form at an arbitrary raw first-shell cut. -/
theorem quarter_cut_lt_creationSource_of_lt_tilingBandShellZeroSites
    {t : DominoTiling} {m cutoff n J : ℕ} {band : RandomClockBand}
    {s : WalkPath}
    (hm : 0 < m)
    (hcreation : ThresholdCreation s m band.oldRank n)
    (hclock : pathTruncatedLevelTime m band.oldRank cutoff s = n)
    (hnext : thresholdCount s n (m + 1) = 0)
    (hJ : J < (tilingBandShellZeroSites t m cutoff band s).card) :
    J / 4 < (tilingCanonicalDominantNearBasesAtCreation t m band.oldRank
        (shellWidth48 m) s).card ∨
      J / 4 < (tilingOppositeDominantNearEndpointsAtCreation t m band.oldRank
        (shellWidth48 m) s).card := by
  have hbound := tilingBandShellZeroSites_card_le_two_spatialSources
    (t := t) hm hcreation hclock hnext
  by_contra h
  simp only [not_or, not_lt] at h
  have hfour : 4 * (J / 4) ≤ J := Nat.mul_div_le J 4
  omega

/-- The exact source-budget form consumed by the full-gap shell-zero route. -/
theorem sourceCut48_lt_creationSource_of_shellZeroOverflow
    {t : DominoTiling} {m cutoff n : ℕ} {band : RandomClockBand}
    {s : WalkPath}
    (hm : 0 < m)
    (hcreation : ThresholdCreation s m band.oldRank n)
    (hclock : pathTruncatedLevelTime m band.oldRank cutoff s = n)
    (hnext : thresholdCount s n (m + 1) = 0)
    (hoverflow : initialBudget48 m < tilingBandOccupancy t m cutoff band s 0) :
    sourceCut48 m <
        (tilingCanonicalDominantNearBasesAtCreation t m band.oldRank
          (shellWidth48 m) s).card ∨
      sourceCut48 m <
        (tilingOppositeDominantNearEndpointsAtCreation t m band.oldRank
          (shellWidth48 m) s).card := by
  apply quarter_cut_lt_creationSource_of_lt_tilingBandShellZeroSites
    hm hcreation hclock hnext
  simpa only [tilingBandShellZeroSites_card] using hoverflow

/-! ## Orientation-refined all-six split -/

/-- Canonical dominant endpoints belonging to one temporal endpoint class. -/
noncomputable def orientedCanonicalDominantNearBasesAtCreation
    (t : DominoTiling) (o : Orientation) (m k w : ℕ)
    (s : WalkPath) : Finset Point :=
  (tilingCanonicalDominantNearBasesAtCreation t m k w s).filter
    (OrientationCompatible o)

/-- Opposite dominant endpoints belonging to one temporal endpoint class. -/
noncomputable def orientedOppositeDominantNearEndpointsAtCreation
    (t : DominoTiling) (o : Orientation) (m k w : ℕ)
    (s : WalkPath) : Finset Point :=
  (tilingOppositeDominantNearEndpointsAtCreation t m k w s).filter
    (OrientationCompatible o)

private theorem orientationCompatible_even_or_shifted (x : Point) :
    OrientationCompatible .even x ∨ OrientationCompatible .shifted x := by
  change pointParity x = 0 ∨ pointParity x = 1
  have hlt : (pointParity x).val < 2 := ZMod.val_lt _
  have hval : (pointParity x).val = 0 ∨ (pointParity x).val = 1 := by
    omega
  rcases hval with hval | hval
  · left
    exact (ZMod.val_eq_zero _).mp hval
  · right
    exact (ZMod.val_eq_one (by norm_num) _).mp hval

private theorem card_le_oriented_parts (S : Finset Point) :
    S.card ≤ (S.filter (OrientationCompatible .even)).card +
      (S.filter (OrientationCompatible .shifted)).card := by
  classical
  let E := S.filter (OrientationCompatible .even)
  let O := S.filter (OrientationCompatible .shifted)
  have hsub : S ⊆ E ∪ O := by
    intro x hx
    rw [Finset.mem_union]
    rcases orientationCompatible_even_or_shifted x with heven | hshifted
    · exact Or.inl (Finset.mem_filter.mpr ⟨hx, heven⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hx, hshifted⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le E O)

/-- After the raw-to-base factor two, the canonical/opposite and endpoint
orientation partitions leave four source classes.  This is the exact
all-six pigeonhole, with the uniform eighth cut. -/
theorem orientedSourceCut48_lt_creationSource_of_shellZeroOverflow
    {t : DominoTiling} {m cutoff n : ℕ} {band : RandomClockBand}
    {s : WalkPath}
    (hm : 0 < m)
    (hcreation : ThresholdCreation s m band.oldRank n)
    (hclock : pathTruncatedLevelTime m band.oldRank cutoff s = n)
    (hnext : thresholdCount s n (m + 1) = 0)
    (hoverflow : initialBudget48 m < tilingBandOccupancy t m cutoff band s 0) :
    orientedSourceCut48 m <
        (orientedCanonicalDominantNearBasesAtCreation t .even m
          band.oldRank (shellWidth48 m) s).card ∨
      orientedSourceCut48 m <
        (orientedCanonicalDominantNearBasesAtCreation t .shifted m
          band.oldRank (shellWidth48 m) s).card ∨
      orientedSourceCut48 m <
        (orientedOppositeDominantNearEndpointsAtCreation t .even m
          band.oldRank (shellWidth48 m) s).card ∨
      orientedSourceCut48 m <
        (orientedOppositeDominantNearEndpointsAtCreation t .shifted m
          band.oldRank (shellWidth48 m) s).card := by
  have hbound := tilingBandShellZeroSites_card_le_two_spatialSources
    (t := t) hm hcreation hclock hnext
  have hoverflow' : initialBudget48 m <
      (tilingBandShellZeroSites t m cutoff band s).card := by
    simpa only [tilingBandShellZeroSites_card] using hoverflow
  have hcanonical := card_le_oriented_parts
    (tilingCanonicalDominantNearBasesAtCreation t m band.oldRank
      (shellWidth48 m) s)
  have hopposite := card_le_oriented_parts
    (tilingOppositeDominantNearEndpointsAtCreation t m band.oldRank
      (shellWidth48 m) s)
  by_contra h
  simp only [not_or, not_lt] at h
  have height : 8 * orientedSourceCut48 m ≤ initialBudget48 m := by
    exact Nat.mul_div_le (initialBudget48 m) 8
  simp only [orientedCanonicalDominantNearBasesAtCreation,
    orientedOppositeDominantNearEndpointsAtCreation] at hcanonical hopposite h
  omega

end

end Erdos1165.HLOZRawShellCreationBridge
