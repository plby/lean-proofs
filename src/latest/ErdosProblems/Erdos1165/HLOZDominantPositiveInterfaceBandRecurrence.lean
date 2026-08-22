import ErdosProblems.Erdos1165.HLOZDominantPositiveInterfaceSupportSelector
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalCoordinateRecovery
import ErdosProblems.Erdos1165.HLOZRawShellCreationBridge
import ErdosProblems.Erdos1165.TilingOrientedVisitedBaseExternalSupport

open Set

namespace Erdos1165.HLOZDominantPositiveInterfaceBandRecurrence

open HLOZDominantPositiveInterfaceSupportSelector
open HLOZPositiveInterfaceSupportSelector
open HLOZGapRandomClockScreen HLOZPathEvents HLOZRawShellCreationBridge
open HLOZProposition48Candidates
open HLOZDynamicThresholdedScreening
open HLOZPositiveInterfacePhysicalCoordinateRecovery
open HLOZThetaSourceBalance HLOZTilingGapRandomClockScreen
open HLOZTilingGapBandExtraction
open LazyDecomposition NearFavoriteShells SpatialInsertionFiber
open ScreeningInstantiation
open TilingLazyDecomposition TilingOrientedAllCreationConcreteFamily
open TilingExternalPhaseSplit
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroSourcePartition
open TilingOrientedVisitedBaseExternalSupport
open TilingOrientedPrefixedSupportBridge
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingSpatialInsertionFiber VariableStoppedTracePartition
open PreStoppingSpatialLaw PreStoppingFiber StoppedInsertion
open PathInsertion TilingPrefixedStoppedProductDisintegration

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

def orientedEndpointStrictlyDominantAt
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (b : Point) : Prop :=
  let z := fixedOrientedTypedExternalWordCode t o n s
  let terminal := prefixedTilingInsertionTerminal z.initial t z.start
    z.retained (fun _ ↦ 0) z.tail
  prefixedTilingFixedBoundaryLocalTime z.initial.1 z.start z.retained terminal
      (tilingPartner t (orientedDominoEndpoint t o b)) <
    prefixedTilingFixedBoundaryLocalTime z.initial.1 z.start z.retained terminal
      (orientedDominoEndpoint t o b)

theorem orientedEndpointComparisonsAt_iff_physical
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (hvalid : s ∈ validStepWalk) (b : Point)
    (hb : b ∈ tilingExternalDominoBases t
      (fixedOrientedTypedExternalWordCode t o n s).start
      (fixedOrientedTypedExternalWordCode t o n s).retained) :
    (orientedEndpointDominantAt t o s n b ↔
        localTime s n (tilingPartner t (orientedDominoEndpoint t o b)) ≤
          localTime s n (orientedDominoEndpoint t o b)) ∧
      (orientedEndpointStrictlyDominantAt t o s n b ↔
        localTime s n (tilingPartner t (orientedDominoEndpoint t o b)) <
          localTime s n (orientedDominoEndpoint t o b)) := by
  let z := fixedOrientedTypedExternalWordCode t o n s
  obtain ⟨q, hword⟩ :=
    exists_prefixedTilingInsertionPrefixList_eq_incrementPrefixList
      t o n s z rfl
  let v := prefixedTilingInsertionPrefixList z.initial.1 t z.start
    z.retained q z.tail.1
  have hvlen : v.length = n := by
    dsimp only [v]
    rw [hword]
    simp [incrementPrefixList]
  have hstep : stepPrefix v.length (stepsOfWalk s) =
      directionVectorOfList v := by
    apply (incrementPrefixList_eq_iff_stepPrefix_eq_directionVector
      (stepsOfWalk s) v).mp
    rw [hvlen]
    exact hword.symm
  have hprefix : pathPrefix s v.length =
      pathPrefix (trajectory (extendPrefix (directionVectorOfList v)))
        v.length := by
    calc
      pathPrefix s v.length =
          trajectoryPrefix (stepPrefix v.length (stepsOfWalk s)) := by
        rw [trajectoryPrefix_stepPrefix, hvalid]
      _ = trajectoryPrefix (directionVectorOfList v) := congrArg _ hstep
      _ = trajectoryPrefix
          (stepPrefix v.length (extendPrefix (directionVectorOfList v))) := by
        rw [stepPrefix_extendPrefix]
      _ = pathPrefix
          (trajectory (extendPrefix (directionVectorOfList v))) v.length :=
        trajectoryPrefix_stepPrefix _ _
  have hstart : trajectory
      (extendPrefix (directionVectorOfList z.initial.1))
        z.initial.1.length = z.start := rfl
  have hterminal := prefixedTilingInsertionTerminal_eq_of_coordinates
    z.initial t z.start z.retained q (fun _ ↦ 0) z.tail hstart
  let bext : TilingExternalDomino t z.start z.retained := ⟨b, hb⟩
  have hpath : finitePathList (pathPrefix s n) =
      prefixedTilingPrefixPointPath z.initial.1 z.start
        (tilingInsertGapVector t z.start z.retained q)
        (prefixedTilingInsertionTerminal z.initial t z.start z.retained
          (fun _ ↦ 0) z.tail) := by
    rw [← hvlen, hprefix]
    calc
      finitePathList
          (pathPrefix (trajectory (extendPrefix (directionVectorOfList v)))
            v.length) =
        prefixedTilingPrefixPointPath z.initial.1 z.start
          (tilingInsertGapVector t z.start z.retained q)
          (prefixedTilingInsertionTerminal z.initial t z.start z.retained q
            z.tail) :=
        finitePathList_prefixedTilingInsertionPrefix z.initial t z.start
          z.retained q z.tail rfl
      _ = _ := by rw [hterminal]
  have hleft : localTime s n
        (tilingPartner t (orientedDominoEndpoint t o b)) =
      prefixedTilingFixedBoundaryLocalTime z.initial.1 z.start z.retained
          (prefixedTilingInsertionTerminal z.initial t z.start z.retained
            (fun _ ↦ 0) z.tail)
          (tilingPartner t (orientedDominoEndpoint t o b)) +
        tilingDominoTotal t z.start z.retained q bext := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        z.initial.1 t z.start z.retained q _ bext]
    rw [tilingBase_partner]
    exact tilingBase_orientedDominoEndpoint t o b
      (isTilingBase_of_tilingBase_eq_self t b
        (tilingExternalDomino_is_base t z.start z.retained bext))
  have hright : localTime s n (orientedDominoEndpoint t o b) =
      prefixedTilingFixedBoundaryLocalTime z.initial.1 z.start z.retained
          (prefixedTilingInsertionTerminal z.initial t z.start z.retained
            (fun _ ↦ 0) z.tail)
          (orientedDominoEndpoint t o b) +
        tilingDominoTotal t z.start z.retained q bext := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        z.initial.1 t z.start z.retained q _ bext]
    exact tilingBase_orientedDominoEndpoint t o b
      (isTilingBase_of_tilingBase_eq_self t b
        (tilingExternalDomino_is_base t z.start z.retained bext))
  constructor
  · unfold orientedEndpointDominantAt
    change prefixedTilingFixedBoundaryLocalTime z.initial.1 z.start z.retained
        (prefixedTilingInsertionTerminal z.initial t z.start z.retained
          (fun _ ↦ 0) z.tail)
        (tilingPartner t (orientedDominoEndpoint t o b)) ≤
      prefixedTilingFixedBoundaryLocalTime z.initial.1 z.start z.retained
        (prefixedTilingInsertionTerminal z.initial t z.start z.retained
          (fun _ ↦ 0) z.tail)
        (orientedDominoEndpoint t o b)
        ↔ localTime s n (tilingPartner t (orientedDominoEndpoint t o b)) ≤
          localTime s n (orientedDominoEndpoint t o b)
    rw [hleft, hright]
    omega
  · unfold orientedEndpointStrictlyDominantAt
    change prefixedTilingFixedBoundaryLocalTime z.initial.1 z.start z.retained
        (prefixedTilingInsertionTerminal z.initial t z.start z.retained
          (fun _ ↦ 0) z.tail)
        (tilingPartner t (orientedDominoEndpoint t o b)) <
      prefixedTilingFixedBoundaryLocalTime z.initial.1 z.start z.retained
        (prefixedTilingInsertionTerminal z.initial t z.start z.retained
          (fun _ ↦ 0) z.tail)
        (orientedDominoEndpoint t o b)
        ↔ localTime s n (tilingPartner t (orientedDominoEndpoint t o b)) <
          localTime s n (orientedDominoEndpoint t o b)
    rw [hleft, hright]
    omega

theorem orientedEndpointDominantAt_iff_physical_dominance
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (hvalid : s ∈ validStepWalk) (b : Point)
    (hb : b ∈ tilingExternalDominoBases t
      (fixedOrientedTypedExternalWordCode t o n s).start
      (fixedOrientedTypedExternalWordCode t o n s).retained) :
    orientedEndpointDominantAt t o s n b ↔
      localTime s n (tilingPartner t (orientedDominoEndpoint t o b)) ≤
        localTime s n (orientedDominoEndpoint t o b) :=
  (orientedEndpointComparisonsAt_iff_physical t o s n hvalid b hb).1

theorem physical_dominance_implies_orientedEndpointDominantAt
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (hvalid : s ∈ validStepWalk) (b : Point)
    (hb : b ∈ tilingExternalDominoBases t
      (fixedOrientedTypedExternalWordCode t o n s).start
      (fixedOrientedTypedExternalWordCode t o n s).retained)
    (hdominance : localTime s n
        (tilingPartner t (orientedDominoEndpoint t o b)) ≤
      localTime s n (orientedDominoEndpoint t o b)) :
    orientedEndpointDominantAt t o s n b :=
  (orientedEndpointDominantAt_iff_physical_dominance
    t o s n hvalid b hb).2 hdominance

theorem orientedEndpointCanonicallyDominantAt_of_eq_dominantEndpoint
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (hvalid : s ∈ validStepWalk) (b : Point)
    (hb : b ∈ tilingExternalDominoBases t
      (fixedOrientedTypedExternalWordCode t o n s).start
      (fixedOrientedTypedExternalWordCode t o n s).retained)
    (hendpoint : orientedDominoEndpoint t o b =
      tilingDominantEndpointAt t s n b) :
    orientedEndpointCanonicallyDominantAt t o s n b := by
  have hcomparisons :=
    orientedEndpointComparisonsAt_iff_physical t o s n hvalid b hb
  by_cases hle : localTime s n (tilingPartner t b) ≤ localTime s n b
  · have hdominantEq : tilingDominantEndpointAt t s n b = b := by
      simp [tilingDominantEndpointAt, hle]
    have hendpointEq : orientedDominoEndpoint t o b = b :=
      hendpoint.trans hdominantEq
    have hweak : orientedEndpointDominantAt t o s n b :=
      hcomparisons.1.2 (by simpa only [hendpointEq] using hle)
    unfold orientedEndpointDominantAt at hweak
    unfold orientedEndpointCanonicallyDominantAt
    rcases Nat.lt_or_eq_of_le hweak with hstrict | hequal
    · exact Or.inl hstrict
    · exact Or.inr ⟨hequal, hendpointEq⟩
  · have hdominantEq : tilingDominantEndpointAt t s n b =
        tilingPartner t b := by
      simp [tilingDominantEndpointAt, hle]
    have hendpointEq : orientedDominoEndpoint t o b =
        tilingPartner t b := hendpoint.trans hdominantEq
    have hstrictPhysical :
        localTime s n (tilingPartner t (orientedDominoEndpoint t o b)) <
          localTime s n (orientedDominoEndpoint t o b) := by
      rw [hendpointEq, tilingPartner_partner]
      exact Nat.lt_of_not_ge hle
    have hstrict : orientedEndpointStrictlyDominantAt t o s n b :=
      hcomparisons.2.2 hstrictPhysical
    unfold orientedEndpointStrictlyDominantAt at hstrict
    unfold orientedEndpointCanonicallyDominantAt
    exact Or.inl hstrict

theorem orientedDominoEndpoint_eq_dominantEndpointAt_of_canonical
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (hvalid : s ∈ validStepWalk) (b : Point)
    (hb : b ∈ tilingExternalDominoBases t
      (fixedOrientedTypedExternalWordCode t o n s).start
      (fixedOrientedTypedExternalWordCode t o n s).retained)
    (hcanonical : orientedEndpointCanonicallyDominantAt t o s n b) :
    orientedDominoEndpoint t o b = tilingDominantEndpointAt t s n b := by
  have hcomparisons :=
    orientedEndpointComparisonsAt_iff_physical t o s n hvalid b hb
  by_cases hcompat : OrientationCompatible o b
  · have hphysical : localTime s n (tilingPartner t b) ≤
        localTime s n b := by
      have hweak := orientedEndpointDominantAt_of_canonical hcanonical
      have := hcomparisons.1.1 hweak
      simpa only [orientedDominoEndpoint, if_pos hcompat] using this
    simp [orientedDominoEndpoint, hcompat, tilingDominantEndpointAt,
      hphysical]
  · have hstrictAt : orientedEndpointStrictlyDominantAt t o s n b := by
      unfold orientedEndpointCanonicallyDominantAt at hcanonical
      unfold orientedEndpointStrictlyDominantAt
      rw [orientedDominoEndpoint, if_neg hcompat] at hcanonical ⊢
      rcases hcanonical with hstrict | ⟨_hequal, hendpoint⟩
      · exact hstrict
      · exact False.elim ((tilingPartner_ne t b) hendpoint)
    have hphysical := hcomparisons.2.1 hstrictAt
    rw [orientedDominoEndpoint, if_neg hcompat,
      tilingPartner_partner] at hphysical
    simp [orientedDominoEndpoint, hcompat, tilingDominantEndpointAt,
      Nat.not_le_of_gt hphysical]

theorem mem_orientedDominantPositiveInterfacePhysicalSites_one
    (t : DominoTiling) (o : Orientation) (m : ℕ) (s : WalkPath) (n : ℕ)
    (hvalid : s ∈ validStepWalk) (hn : 0 < n) (d : Point)
    (hselected : tilingDominantEndpointAt t s n (tilingBase t d) = d)
    (hcompat : OrientationCompatible o d)
    (hpositive : 0 < localTime s n d)
    (hout : tilingBase t d ∉ (thresholdSites s n m).image (tilingBase t))
    (hdominance : localTime s n (tilingPartner t d) ≤ localTime s n d) :
    d ∈ orientedDominantPositiveInterfacePhysicalSites t o m 1 s n := by
  classical
  let b := tilingBase t d
  have hb : b ∈ tilingExternalDominoBases t
      (fixedOrientedTypedExternalWordCode t o n s).start
      (fixedOrientedTypedExternalWordCode t o n s).retained := by
    exact tilingBase_mem_fixedExternalDominoBases_of_positive_point
      t o s n hvalid hn d hcompat hpositive
  have hbSupport : b ∈ orientedPositiveInterfaceSupportAt t o m 1 s n := by
    unfold orientedPositiveInterfaceSupportAt
    rw [mem_orientedPositiveInterfaceCodeSupport_iff]
    refine ⟨hb, ?_, ?_⟩
    · exact HLOZSourceOrientedThetaProduct.card_tilingCoordinatesAt_pos
        t (fixedOrientedTypedExternalWordCode t o n s).start
          (fixedOrientedTypedExternalWordCode t o n s).retained ⟨b, hb⟩
    · exact hout
  have hendpoint : orientedDominoEndpoint t o b = d := by
    exact (eq_orientedDominoEndpoint_of_compatible_of_tilingBase_eq
      t o hcompat rfl).symm
  have hbDominant : orientedEndpointCanonicallyDominantAt t o s n b := by
    apply orientedEndpointCanonicallyDominantAt_of_eq_dominantEndpoint
      t o s n hvalid b hb
    exact hendpoint.trans (by simpa only [b] using hselected.symm)
  rw [orientedDominantPositiveInterfacePhysicalSites, Finset.mem_image]
  refine ⟨b, ?_, hendpoint⟩
  rw [orientedDominantPositiveInterfaceSupportAt, Finset.mem_filter]
  exact ⟨hbSupport, hbDominant⟩

/-- Tie-consistent normalization: first pass to the canonical base of each
raw domino, then choose its dominant endpoint. -/
noncomputable def canonicalizedDominantRandomClockBandSites
    (t : DominoTiling) (m cutoff : ℕ) (s : WalkPath)
    (band : RandomClockBand) : Finset Point :=
  ((tilingRandomClockBandSites t m cutoff s band).image (tilingBase t)).image
    (tilingDominantEndpointAt t s
      (pathTruncatedLevelTime m band.oldRank cutoff s))

noncomputable def orientedCanonicalizedDominantRandomClockBandSites
    (o : Orientation) (t : DominoTiling) (m cutoff : ℕ)
    (s : WalkPath) (band : RandomClockBand) : Finset Point :=
  (canonicalizedDominantRandomClockBandSites t m cutoff s band).filter
    (OrientationCompatible o)

theorem randomClockBandSites_card_le_two_orientedCanonicalizedDominant
    (t : DominoTiling) (m cutoff : ℕ) (s : WalkPath)
    (band : RandomClockBand) :
    (tilingRandomClockBandSites t m cutoff s band).card ≤
      2 * ((orientedCanonicalizedDominantRandomClockBandSites .even
          t m cutoff s band).card +
        (orientedCanonicalizedDominantRandomClockBandSites .shifted
          t m cutoff s band).card) := by
  classical
  let B := (tilingRandomClockBandSites t m cutoff s band).image (tilingBase t)
  let f := tilingDominantEndpointAt t s
    (pathTruncatedLevelTime m band.oldRank cutoff s)
  have hbase := card_le_two_mul_card_image_tilingBase t
    (tilingRandomClockBandSites t m cutoff s band)
  have hinj : Set.InjOn f (B : Set Point) := by
    intro b hb c hc hbc
    have hbBase : IsTilingBase t b := by
      rcases Finset.mem_image.mp hb with ⟨x, _hx, rfl⟩
      exact isTilingBase_tilingBase t x
    have hcBase : IsTilingBase t c := by
      rcases Finset.mem_image.mp hc with ⟨x, _hx, rfl⟩
      exact isTilingBase_tilingBase t x
    have h := congrArg (tilingBase t) hbc
    simpa only [f, tilingBase_dominantEndpointAt_of_isTilingBase
      t s (pathTruncatedLevelTime m band.oldRank cutoff s) b hbBase,
      tilingBase_dominantEndpointAt_of_isTilingBase
        t s (pathTruncatedLevelTime m band.oldRank cutoff s) c hcBase] using h
  have himage : B.card = (B.image f).card :=
    (Finset.card_image_iff.mpr hinj).symm
  have hunion : (B.image f).card ≤
      ((B.image f).filter (OrientationCompatible .even)).card +
        ((B.image f).filter (OrientationCompatible .shifted)).card := by
    have heq : B.image f =
        (B.image f).filter (OrientationCompatible .even) ∪
          (B.image f).filter (OrientationCompatible .shifted) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hx
        rcases PreStoppingSpatialLaw.evenPoint_or_oddPoint x with he | ho
        · exact Or.inl ⟨hx, he⟩
        · exact Or.inr ⟨hx, ho⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    calc
      (B.image f).card =
          ((B.image f).filter (OrientationCompatible .even) ∪
            (B.image f).filter (OrientationCompatible .shifted)).card :=
        congrArg Finset.card heq
      _ ≤ _ := Finset.card_union_le _ _
  calc
    (tilingRandomClockBandSites t m cutoff s band).card ≤
        2 * (B.image f).card := by
      rw [← himage]
      exact hbase
    _ ≤ 2 * (((B.image f).filter (OrientationCompatible .even)).card +
        ((B.image f).filter (OrientationCompatible .shifted)).card) :=
      Nat.mul_le_mul_left 2 hunion
    _ = _ := rfl

theorem orientedCanonicalizedDominant_subset_boundedPhysical
    {t : DominoTiling} {o : Orientation} {m cutoff n : ℕ}
    {band : RandomClockBand} {s : WalkPath}
    (hvalid : s ∈ validStepWalk) (hn : 0 < n)
    (hclock : pathTruncatedLevelTime m band.oldRank cutoff s = n)
    (hfavorite : thresholdSites s n m = favoriteSites s n) :
    orientedCanonicalizedDominantRandomClockBandSites o t m cutoff s band ⊆
      boundedCandidates
        (orientedDominantPositiveInterfacePhysicalSites t o m 1 s n)
        (fun x ↦ (m - localTime s n x) / shellWidth48 m)
        (shellCount48 m band.beta) := by
  classical
  intro d hd
  rw [orientedCanonicalizedDominantRandomClockBandSites,
    Finset.mem_filter] at hd
  rcases hd with ⟨hdImage, hdCompat⟩
  rw [canonicalizedDominantRandomClockBandSites, Finset.mem_image] at hdImage
  obtain ⟨b, hbImage, hbd⟩ := hdImage
  rw [hclock] at hbd
  rw [Finset.mem_image] at hbImage
  obtain ⟨x, hxRaw, hxb⟩ := hbImage
  rw [tilingRandomClockBandSites, mem_boundedCandidates] at hxRaw
  rcases hxRaw with ⟨hxCandidate, hxLabel⟩
  rw [Finset.mem_filter] at hxCandidate
  rcases hxCandidate with ⟨hxVisited, _hxExternal, hxOutside⟩
  have hxPositive : 0 < localTime s n x := by
    rw [tilingRandomClockVisitedSites,
      pathPhaseFilteredExternalVisitedSites, hclock] at hxVisited
    change x ∈ tilingExternalPhaseVisitedSites t
      (externalVertexPhaseOfBool band.vertexPhase)
        (phasedInput band.orientation (finitePathList (pathPrefix s n)))
        at hxVisited
    rw [mem_tilingExternalPhaseVisitedSites_iff] at hxVisited
    exact hxVisited.trans_le
      (pathPhaseFilteredExternalLocalTime_le_localTime t band.orientation
        band.vertexPhase s n x)
  have hbBase : IsTilingBase t b := by
    rw [← hxb]
    exact isTilingBase_tilingBase t x
  have hdDominance : localTime s n (tilingPartner t d) ≤
      localTime s n d := by
    rw [← hbd]
    exact tilingDominantEndpointAt_partner_le t s n b
  have hxLe : localTime s n x ≤ localTime s n d := by
    calc
      localTime s n x ≤ tilingXiPlusAt t s n x := le_max_left _ _
      _ = tilingXiPlusAt t s n b := by rw [← hxb, tilingXiPlusAt_tilingBase]
      _ = tilingXiPlusAt t s n d := by
        rw [← hbd]
        exact (tilingXiPlusAt_dominantEndpoint t s n b).symm
      _ = localTime s n d := tilingXiPlusAt_eq_base_of_partner_le hdDominance
  have hdPositive : 0 < localTime s n d := hxPositive.trans_le hxLe
  have hbaseDX : tilingBase t d = tilingBase t x := by
    rw [← hbd, tilingBase_dominantEndpointAt_of_isTilingBase
      t s n b hbBase, ← hxb]
  have hdSelected :
      tilingDominantEndpointAt t s n (tilingBase t d) = d := by
    rw [hbaseDX, hxb, hbd]
  have hdOutside : tilingBase t d ∉
      (thresholdSites s n m).image (tilingBase t) := by
    intro hb
    rw [hfavorite, Finset.mem_image] at hb
    obtain ⟨y, hyFavorite, hyBase⟩ := hb
    have hbaseYX : tilingBase t y = tilingBase t x := hyBase.trans hbaseDX
    rcases (tilingBase_eq_iff t y x).mp hbaseYX with hyx | hsame
    · apply hxOutside
      rw [tilingRandomClockDistinguishedSites, favoriteTilingDominoSites,
        hclock, Finset.mem_union]
      exact Or.inl (hyx ▸ hyFavorite)
    · have hpartner : tilingPartner t y = x :=
        (sameDomino_iff_partner_eq t y x).mp hsame
      apply hxOutside
      rw [tilingRandomClockDistinguishedSites, favoriteTilingDominoSites,
        hclock, Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨y, hyFavorite, hpartner⟩)
  rw [mem_boundedCandidates]
  refine ⟨?_, ?_⟩
  · apply mem_orientedDominantPositiveInterfacePhysicalSites_one
      t o m s n hvalid hn d hdSelected hdCompat hdPositive hdOutside
        hdDominance
  · have hsub : m - localTime s n d ≤ m - localTime s n x :=
      Nat.sub_le_sub_left hxLe m
    have hdiv : (m - localTime s n d) / shellWidth48 m ≤
        (m - localTime s n x) / shellWidth48 m := Nat.div_le_div_right hsub
    have hxLabel' :
        (m - localTime s n x) / shellWidth48 m < shellCount48 m band.beta := by
      simpa only [deficitShellLabel, tilingRandomClockTotalLocalTime,
        hclock] using hxLabel
    exact hdiv.trans_lt hxLabel'

/-- The dominant endpoint recurrence uses the universal positive retained
count threshold.  Every raw normalized candidate is represented here, even
when its endpoint orientation differs from the raw band's phase. -/
noncomputable def normalizedDominantBandOccupancy
    (t : DominoTiling) (o : Orientation) (m cutoff : ℕ)
    (band : RandomClockBand) : WalkPath → ℕ → ℕ :=
  fun s shell ↦
    (shellCandidates
      (orientedDominantPositiveInterfacePhysicalSites t o m 1 s
        (pathTruncatedLevelTime m band.oldRank cutoff s))
      (fun x ↦ (m - localTime s
        (pathTruncatedLevelTime m band.oldRank cutoff s) x) / shellWidth48 m)
      shell).card

theorem normalizedDominantShellZeroSites_subset_orientedCreationSources
    {t : DominoTiling} {o : Orientation} {m cutoff n : ℕ}
    {band : RandomClockBand} {s : WalkPath}
    (hm : 1 < m)
    (hcreation : ThresholdCreation s m band.oldRank n)
    (hclock : pathTruncatedLevelTime m band.oldRank cutoff s = n)
    (hnext : thresholdCount s n (m + 1) = 0)
    (hvalid : s ∈ validStepWalk) :
    shellCandidates
        (orientedDominantPositiveInterfacePhysicalSites t o m 1 s n)
        (fun x ↦ (m - localTime s n x) / shellWidth48 m) 0 ⊆
      orientedCanonicalDominantNearBasesAtCreation t o m band.oldRank
          (shellWidth48 m) s ∪
        orientedOppositeDominantNearEndpointsAtCreation t o m band.oldRank
          (shellWidth48 m) s := by
  classical
  intro d hd
  rw [mem_shellCandidates] at hd
  rcases hd with ⟨hdSupport, hdShell⟩
  rw [orientedDominantPositiveInterfacePhysicalSites,
    Finset.mem_image] at hdSupport
  rcases hdSupport with ⟨b, hbDominant, hbd⟩
  rw [orientedDominantPositiveInterfaceSupportAt,
    Finset.mem_filter] at hbDominant
  rcases hbDominant with ⟨hbSupport, hbCanonical⟩
  have hbCode := hbSupport
  unfold orientedPositiveInterfaceSupportAt at hbCode
  rw [mem_orientedPositiveInterfaceCodeSupport_iff] at hbCode
  rcases hbCode with ⟨hbRepresented, _hbThick, hbOutside⟩
  have hbBase : IsTilingBase t b :=
    isTilingBase_of_tilingBase_eq_self t b
      (tilingExternalDomino_is_base t
        (fixedOrientedTypedExternalWordCode t o n s).start
        (fixedOrientedTypedExternalWordCode t o n s).retained
        ⟨b, hbRepresented⟩)
  have hbaseD : tilingBase t d = b := by
    rw [← hbd]
    exact tilingBase_orientedDominoEndpoint t o b hbBase
  have hdRawImage : d ∈
      (orientedPositiveInterfaceSupportAt t o m 1 s n).image
        (orientedDominoEndpoint t o) :=
    Finset.mem_image.mpr ⟨b, hbSupport, hbd⟩
  have hfavorite : thresholdSites s n m = favoriteSites s n :=
    thresholdSites_eq_favoriteSites_at_creation_of_terminal
      band.oldRank_pos hcreation le_rfl hnext
  have hn : 0 < n := by
    have hcreation' : ThresholdCreation (trajectory (stepsOfWalk s)) m
        band.oldRank n := by
      rw [show trajectory (stepsOfWalk s) = s from hvalid]
      exact hcreation
    exact HLOZThetaOneSourceShift.thresholdCreation_time_pos_of_two_le
      (stepsOfWalk s) hm band.oldRank_pos hcreation'
  have hdPhysical : d ∈ positiveInterfacePhysicalSites t o 1 s n := by
    rw [positiveInterfacePhysicalSites_eq_support_image t o m 1 s n
      hvalid hn hfavorite (by omega)]
    exact hdRawImage
  rw [positiveInterfacePhysicalSites, Finset.mem_filter] at hdPhysical
  rcases hdPhysical with ⟨_hdVisited, hdExternal, _hdFavorite⟩
  have hdPositive : 0 < localTime s n d := by
    exact lt_of_lt_of_le (by omega : 0 < 1)
      (hdExternal.trans
        (pathPhaseFilteredExternalLocalTime_le_localTime t o false s n d))
  have hbVisited : b ∈ visitedTilingBases t s n := by
    rw [visitedTilingBases, Finset.mem_image]
    refine ⟨d, ?_, hbaseD⟩
    rw [mem_visitedSites_iff_localTime_pos]
    exact hdPositive
  have hdLt : localTime s n d < m := by
    by_contra hnot
    apply hbOutside
    rw [Finset.mem_image]
    refine ⟨d, ?_, hbaseD⟩
    rw [mem_thresholdSites_iff s n m d (by omega)]
    exact Nat.le_of_not_gt hnot
  have hdDominance : localTime s n (tilingPartner t d) ≤
      localTime s n d := by
    have hweak := orientedEndpointDominantAt_of_canonical hbCanonical
    have hphysical :=
      (orientedEndpointComparisonsAt_iff_physical t o s n hvalid b
        hbRepresented).1.1 hweak
    simpa only [hbd] using hphysical
  have hwidth : 0 < shellWidth48 m := by
    unfold shellWidth48
    exact Nat.ceil_pos.mpr
      (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < m by omega)) _)
  have hdDeficit : m - localTime s n d < shellWidth48 m :=
    Nat.lt_of_div_eq_zero hwidth hdShell
  have hdLower : m - shellWidth48 m + 1 ≤ localTime s n d := by
    omega
  have hxi : tilingXiPlusAt t s n b = localTime s n d := by
    calc
      tilingXiPlusAt t s n b = tilingXiPlusAt t s n (tilingBase t d) := by
        rw [hbaseD]
      _ = tilingXiPlusAt t s n d := tilingXiPlusAt_tilingBase t s n d
      _ = localTime s n d := tilingXiPlusAt_eq_base_of_partner_le hdDominance
  have hcreationNat : creationTimeNat m band.oldRank s = n :=
    creationTimeNat_eq_of_creation hcreation
  have hbNear : b ∈ tilingNearFavoriteBasesAtCreation t m band.oldRank
      (shellWidth48 m) s := by
    rw [tilingNearFavoriteBasesAtCreation, hcreationNat,
      Finset.mem_filter]
    refine ⟨hbVisited, ?_⟩
    rw [Finset.mem_union,
      HLOZShellZeroReplacementWindows.mem_shellZeroSourceTotalWindow,
      hxi]
    exact Or.inl ⟨hdLower, hdLt⟩
  have hendpointDominant : orientedDominoEndpoint t o b =
      tilingDominantEndpointAt t s n b :=
    orientedDominoEndpoint_eq_dominantEndpointAt_of_canonical
      t o s n hvalid b hbRepresented hbCanonical
  have hdNear : d ∈ tilingDominantNearBasesAtCreation t m band.oldRank
      (shellWidth48 m) s := by
    rw [tilingDominantNearBasesAtCreation, hcreationNat, Finset.mem_image]
    exact ⟨b, hbNear, hendpointDominant.symm.trans hbd⟩
  have hdCompat : OrientationCompatible o d := by
    rw [← hbd]
    exact orientedDominoEndpoint_compatible t o b
  rw [Finset.mem_union]
  by_cases hdBase : IsTilingBase t d
  · left
    rw [orientedCanonicalDominantNearBasesAtCreation,
      Finset.mem_filter, tilingCanonicalDominantNearBasesAtCreation,
      Finset.mem_filter]
    exact ⟨⟨hdNear, hdBase⟩, hdCompat⟩
  · right
    rw [orientedOppositeDominantNearEndpointsAtCreation,
      Finset.mem_filter, tilingOppositeDominantNearEndpointsAtCreation,
      Finset.mem_filter]
    exact ⟨⟨hdNear, hdBase⟩, hdCompat⟩

def normalizedPositiveInitialBudget48 (m : ℕ) : ℕ :=
  initialBudget48 m / 4

theorem normalizedSourceCut48_lt_creationSource_of_shellZeroOverflow
    {t : DominoTiling} {o : Orientation} {m cutoff n : ℕ}
    {band : RandomClockBand} {s : WalkPath}
    (hm : 1 < m)
    (hcreation : ThresholdCreation s m band.oldRank n)
    (hclock : pathTruncatedLevelTime m band.oldRank cutoff s = n)
    (hnext : thresholdCount s n (m + 1) = 0)
    (hvalid : s ∈ validStepWalk)
    (hoverflow : s ∈ shellOverflow
      (normalizedDominantBandOccupancy t o m cutoff band)
      (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
        shellGrowth48) 0) :
    orientedSourceCut48 m <
        (orientedCanonicalDominantNearBasesAtCreation t o m band.oldRank
          (shellWidth48 m) s).card ∨
      orientedSourceCut48 m <
        (orientedOppositeDominantNearEndpointsAtCreation t o m band.oldRank
          (shellWidth48 m) s).card := by
  have hsub := normalizedDominantShellZeroSites_subset_orientedCreationSources
    (t := t) (o := o) (band := band) hm hcreation hclock hnext hvalid
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hoverflow' : normalizedPositiveInitialBudget48 m <
      (shellCandidates
        (orientedDominantPositiveInterfacePhysicalSites t o m 1 s n)
        (fun x ↦ (m - localTime s n x) / shellWidth48 m) 0).card := by
    simpa only [shellOverflow, geometricShellThreshold_zero,
      Set.mem_ofPred_eq, normalizedDominantBandOccupancy, hclock] using hoverflow
  by_contra h
  simp only [not_or, not_lt] at h
  have hfloor : 2 * orientedSourceCut48 m ≤
      normalizedPositiveInitialBudget48 m := by
    unfold orientedSourceCut48 normalizedPositiveInitialBudget48
    omega
  omega

theorem normalized_geometric_threshold_sum_le_quarter_candidateBudget
    {m : ℕ} {beta : ℝ}
    (hbudget : geometricCandidateBudget48 m beta ≤ candidateBudget48 m beta) :
    ∑ j ∈ Finset.range (shellCount48 m beta),
        geometricShellThreshold (normalizedPositiveInitialBudget48 m)
          shellGrowth48 j ≤
      candidateBudget48 m beta / 4 := by
  have hfour : 4 *
      (∑ j ∈ Finset.range (shellCount48 m beta),
        geometricShellThreshold (normalizedPositiveInitialBudget48 m)
          shellGrowth48 j) ≤ geometricCandidateBudget48 m beta := by
    unfold geometricCandidateBudget48 normalizedPositiveInitialBudget48
      geometricShellThreshold
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    calc
      4 * ((initialBudget48 m / 4) *
          ∑ x ∈ Finset.range (shellCount48 m beta), shellGrowth48 ^ x) =
          (4 * (initialBudget48 m / 4)) *
            ∑ x ∈ Finset.range (shellCount48 m beta),
              shellGrowth48 ^ x := by ring
      _ ≤ initialBudget48 m *
            ∑ x ∈ Finset.range (shellCount48 m beta),
              shellGrowth48 ^ x := by
        gcongr
        exact Nat.mul_div_le (initialBudget48 m) 4
  have hfour' : 4 *
      (∑ j ∈ Finset.range (shellCount48 m beta),
        geometricShellThreshold (normalizedPositiveInitialBudget48 m)
          shellGrowth48 j) ≤ candidateBudget48 m beta := hfour.trans hbudget
  omega

theorem orientedCanonicalizedDominant_card_le_occupancy_sum
    {t : DominoTiling} {o : Orientation} {m cutoff n : ℕ}
    {band : RandomClockBand} {s : WalkPath}
    (hvalid : s ∈ validStepWalk) (hn : 0 < n)
    (hclock : pathTruncatedLevelTime m band.oldRank cutoff s = n)
    (hfavorite : thresholdSites s n m = favoriteSites s n) :
    (orientedCanonicalizedDominantRandomClockBandSites
        o t m cutoff s band).card ≤
      ∑ j ∈ Finset.range (shellCount48 m band.beta),
        normalizedDominantBandOccupancy t o m cutoff band s j := by
  have hsub := orientedCanonicalizedDominant_subset_boundedPhysical
    (t := t) (o := o) (band := band) hvalid hn hclock hfavorite
  calc
    (orientedCanonicalizedDominantRandomClockBandSites
        o t m cutoff s band).card ≤
        (boundedCandidates
          (orientedDominantPositiveInterfacePhysicalSites t o m 1 s n)
          (fun x ↦ (m - localTime s n x) / shellWidth48 m)
          (shellCount48 m band.beta)).card := Finset.card_le_card hsub
    _ = ∑ j ∈ Finset.range (shellCount48 m band.beta),
          normalizedDominantBandOccupancy t o m cutoff band s j := by
      rw [← sum_shellOccupancy_eq_card_boundedCandidates]
      apply Finset.sum_congr rfl
      intro j _hj
      unfold normalizedDominantBandOccupancy shellOccupancy
      rw [hclock]

theorem raw_band_overflow_implies_normalized_totalOverflow
    {t : DominoTiling} {m cutoff n : ℕ}
    {band : RandomClockBand} {s : WalkPath}
    (hvalid : s ∈ validStepWalk) (hn : 0 < n)
    (hclock : pathTruncatedLevelTime m band.oldRank cutoff s = n)
    (hfavorite : thresholdSites s n m = favoriteSites s n)
    (hbudget : geometricCandidateBudget48 m band.beta ≤
      candidateBudget48 m band.beta)
    (hoverflow : candidateBudget48 m band.beta <
      (tilingRandomClockBandSites t m cutoff s band).card) :
    s ∈ totalOverflow
        (normalizedDominantBandOccupancy t .even m cutoff band)
        (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
          shellGrowth48) (shellCount48 m band.beta) ∨
      s ∈ totalOverflow
        (normalizedDominantBandOccupancy t .shifted m cutoff band)
        (geometricShellThreshold (normalizedPositiveInitialBudget48 m)
          shellGrowth48) (shellCount48 m band.beta) := by
  have hcard := randomClockBandSites_card_le_two_orientedCanonicalizedDominant
    t m cutoff s band
  have hquarter : candidateBudget48 m band.beta / 4 <
        (orientedCanonicalizedDominantRandomClockBandSites .even
          t m cutoff s band).card ∨
      candidateBudget48 m band.beta / 4 <
        (orientedCanonicalizedDominantRandomClockBandSites .shifted
          t m cutoff s band).card := by
    by_contra h
    simp only [not_or, not_lt] at h
    have hfour : 4 * (candidateBudget48 m band.beta / 4) ≤
        candidateBudget48 m band.beta :=
      Nat.mul_div_le (candidateBudget48 m band.beta) 4
    omega
  have hthreshold :=
    normalized_geometric_threshold_sum_le_quarter_candidateBudget hbudget
  rcases hquarter with heven | hshifted
  · left
    have hocc := orientedCanonicalizedDominant_card_le_occupancy_sum
      (t := t) (o := .even) (band := band) hvalid hn hclock hfavorite
    exact lt_of_le_of_lt hthreshold (heven.trans_le hocc)
  · right
    have hocc := orientedCanonicalizedDominant_card_le_occupancy_sum
      (t := t) (o := .shifted) (band := band) hvalid hn hclock hfavorite
    exact lt_of_le_of_lt hthreshold (hshifted.trans_le hocc)

end

end Erdos1165.HLOZDominantPositiveInterfaceBandRecurrence
