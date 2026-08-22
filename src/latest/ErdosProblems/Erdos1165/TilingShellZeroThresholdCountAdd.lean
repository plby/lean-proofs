/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroEndpointIncrementCard

/-!
# The endpoint screen raises the stopped creation rank by its actual increment

The numerical endpoint contribution is now identified with the change in the
actual threshold-site count on a pair of physical prefixed insertion words.
Distinguished coordinates and unrepresented dominoes form the invariant
complement; represented away dominoes are counted by the endpoint Finset.
-/

open scoped BigOperators

namespace Erdos1165.TilingShellZeroThresholdCountAdd

open FiniteDominoProductLaw HLOZShellZeroEndpointIncrementPartition
open LazyDecomposition PreStoppingFiber PreStoppingSpatialLaw
open StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization TilingDistinguishedTraceInvariant
open TilingLazyDecomposition TilingPrefixedFavoriteTraceSupport
open TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroEndpointIncrementCard TilingShellZeroEndpointIncrementScreen
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem mem_listThresholdSites_iff
    (p : List Point) (m : ℕ) (hm : 0 < m) (y : Point) :
    y ∈ listThresholdSites p m ↔ m ≤ listLocalTime p y := by
  simp only [listThresholdSites, Finset.mem_filter, List.mem_toFinset,
    listLocalTime]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨List.count_pos_iff.mp (hm.trans_le h), h⟩

/-- The thresholded represented-away endpoints of an inserted word are
exactly the explicit endpoint Finset computed from its away totals. -/
theorem filter_listThresholdSites_eq_prefixedShellZeroThresholdedAwayEndpoints
    (initial : List Direction) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (m : ℕ) (hm : 0 < m)
    (q : TilingCappedCoordinates i cap) (ell : TruncatedTotals upper)
    (htotal : ∀ b, tilingDominoTotal t x r (fun j ↦ (q j : ℕ)) b.1 =
      (ell b : ℕ)) :
    (listThresholdSites
        (prefixedTilingPrefixPointPath initial x
          (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal) m).filter
        (fun y ↦ tilingBase t y ∈ tilingExternalDominoBases t x r ∧
          tilingBase t y ∉ D) =
      prefixedShellZeroThresholdedAwayEndpoints initial t x r terminal D
        upper m ell := by
  classical
  ext y
  rw [Finset.mem_filter, mem_listThresholdSites_iff _ _ hm]
  simp only [prefixedShellZeroThresholdedAwayEndpoints, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hlevel, hyext, hyD⟩
    let bext : TilingExternalDomino t x r := ⟨tilingBase t y, hyext⟩
    let b : TilingAwayDomino t x r D := ⟨bext, hyD⟩
    have hlocal := prefixedTilingInsertedPrefix_localTime_at_dominoPoint
      initial t x r (fun j ↦ (q j : ℕ)) terminal bext y rfl
    rw [htotal b] at hlocal
    rcases point_eq_tilingBase_or_partner_base t y with hybase | hypartner
    · left
      refine ⟨b, ?_, ?_⟩
      · have hlevel' := hlevel
        rw [hybase] at hlocal hlevel'
        exact hlocal ▸ hlevel'
      · exact hybase.symm
    · right
      refine ⟨b, ?_, ?_⟩
      · have hlevel' := hlevel
        rw [hypartner] at hlocal hlevel'
        exact hlocal ▸ hlevel'
      · exact hypartner.symm
  · rintro (⟨b, hlevel, rfl⟩ | ⟨b, hlevel, rfl⟩)
    · have hlocal := prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        initial t x r (fun j ↦ (q j : ℕ)) terminal b.1 b.1.1
          (tilingExternalDomino_is_base t x r b.1)
      rw [htotal b] at hlocal
      refine ⟨hlocal.symm ▸ hlevel, ?_, ?_⟩
      · simpa only [tilingExternalDomino_is_base] using b.1.2
      simpa only [tilingExternalDomino_is_base] using b.2
    · have hlocal := prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        initial t x r (fun j ↦ (q j : ℕ)) terminal b.1
          (tilingPartner t b.1.1)
          (tilingPartner_ofExternalDomino_has_base t x r b.1)
      rw [htotal b] at hlocal
      refine ⟨hlocal.symm ▸ hlevel, ?_, ?_⟩
      · simpa only [tilingBase_partner,
          tilingExternalDomino_is_base] using b.1.2
      · simpa only [tilingBase_partner,
          tilingExternalDomino_is_base] using b.2

/-- The complement of the represented away dominoes is fixed by the common
distinguished projection.  This includes both distinguished represented
dominoes and all sites whose domino is absent from the retained word. -/
theorem filter_not_away_listThresholdSites_eq_of_distinguished_eq
    (initial : List Direction) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (m : ℕ) (hm : 0 < m)
    (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1) :
    (listThresholdSites
        (prefixedTilingPrefixPointPath initial x
          (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal) m).filter
        (fun y ↦ ¬(tilingBase t y ∈ tilingExternalDominoBases t x r ∧
          tilingBase t y ∉ D)) =
      (listThresholdSites
        (prefixedTilingPrefixPointPath initial x
          (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal) m).filter
        (fun y ↦ ¬(tilingBase t y ∈ tilingExternalDominoBases t x r ∧
          tilingBase t y ∉ D)) := by
  classical
  ext y
  simp only [Finset.mem_filter]
  have hlocal (hnot : ¬(tilingBase t y ∈ tilingExternalDominoBases t x r ∧
      tilingBase t y ∉ D)) :
      listLocalTime
          (prefixedTilingPrefixPointPath initial x
            (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal) y =
        listLocalTime
          (prefixedTilingPrefixPointPath initial x
            (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal) y := by
    by_cases hyext : tilingBase t y ∈ tilingExternalDominoBases t x r
    · have hyD : tilingBase t y ∈ D := by
        by_contra hyD
        exact hnot ⟨hyext, hyD⟩
      exact prefixedTilingPrefixLocalTime_eq_of_distinguished_eq
        initial t x r terminal D q q' hdist y hyD
    · rw [prefixedTilingInsertedPrefix_localTime_of_base_not_mem
          initial t x r (fun j ↦ (q j : ℕ)) terminal y hyext,
        prefixedTilingInsertedPrefix_localTime_of_base_not_mem
          initial t x r (fun j ↦ (q' j : ℕ)) terminal y hyext]
  constructor
  · rintro ⟨hy, hnot⟩
    refine ⟨(mem_listThresholdSites_iff _ _ hm y).2 ?_, hnot⟩
    rw [← hlocal hnot]
    exact (mem_listThresholdSites_iff _ _ hm y).1 hy
  · rintro ⟨hy, hnot⟩
    refine ⟨(mem_listThresholdSites_iff _ _ hm y).2 ?_, hnot⟩
    rw [hlocal hnot]
    exact (mem_listThresholdSites_iff _ _ hm y).1 hy

/-- The replacement physical prefix has exactly `delta` more threshold sites
than the all-source physical prefix. -/
theorem card_listThresholdSites_add_of_endpointIncrement
    (initial : List Direction) {i cap m w : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (hm : 0 < m)
    (qSource qReplacement : TilingCappedCoordinates i cap)
    (ellSource ellReplacement : TruncatedTotals upper)
    (central delta : ℕ)
    (hdist : (splitTilingCoordinatesEquiv t x r D qSource).1 =
      (splitTilingCoordinatesEquiv t x r D qReplacement).1)
    (hbase : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 =
        Fintype.card (TilingCoordinatesAt t x r b.1))
    (hdominance : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial x r terminal
          (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1)
    (hsource : ∀ b, tilingShellZeroSourceCoordinate
      (cap := cap) (m := m) (w := w) t x r D upper b (ellSource b))
    (hreplacement : prefixedShellZeroReplacementScreenAtIncrement
      (cap := cap) (m := m) (w := w) initial t x r terminal D upper
        central delta ellReplacement)
    (htotalSource : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qSource j : ℕ)) b.1 =
        (ellSource b : ℕ))
    (htotalReplacement : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qReplacement j : ℕ)) b.1 =
        (ellReplacement b : ℕ)) :
    (listThresholdSites
      (prefixedTilingPrefixPointPath initial x
        (tilingInsertGapVector t x r (fun j ↦ (qReplacement j : ℕ)))
          terminal) m).card =
      (listThresholdSites
        (prefixedTilingPrefixPointPath initial x
          (tilingInsertGapVector t x r (fun j ↦ (qSource j : ℕ)))
            terminal) m).card + delta := by
  classical
  let sourceSites := listThresholdSites
    (prefixedTilingPrefixPointPath initial x
      (tilingInsertGapVector t x r (fun j ↦ (qSource j : ℕ))) terminal) m
  let replacementSites := listThresholdSites
    (prefixedTilingPrefixPointPath initial x
      (tilingInsertGapVector t x r (fun j ↦ (qReplacement j : ℕ))) terminal) m
  let away : Point → Prop := fun y ↦
    tilingBase t y ∈ tilingExternalDominoBases t x r ∧ tilingBase t y ∉ D
  have hsourceFilter :=
    filter_listThresholdSites_eq_prefixedShellZeroThresholdedAwayEndpoints
      initial t x r terminal D upper m hm qSource ellSource htotalSource
  have hreplacementFilter :=
    filter_listThresholdSites_eq_prefixedShellZeroThresholdedAwayEndpoints
      initial t x r terminal D upper m hm qReplacement ellReplacement
        htotalReplacement
  have hsourceIncrement : endpointIncrementOfVector
      (prefixedShellZeroEndpointContribution initial t x r terminal D upper m)
      ellSource = 0 := by
    unfold endpointIncrementOfVector
    apply Finset.sum_eq_zero
    intro b _
    exact prefixedShellZeroEndpointContribution_eq_zero_of_source
      initial t x r terminal D upper hbase hdominance b (ellSource b)
        (hsource b)
  have hsourceAway : (sourceSites.filter away).card = 0 := by
    rw [show sourceSites.filter away =
        prefixedShellZeroThresholdedAwayEndpoints initial t x r terminal D
          upper m ellSource by exact hsourceFilter,
      card_prefixedShellZeroThresholdedAwayEndpoints, hsourceIncrement]
  have hreplacementAway : (replacementSites.filter away).card = delta := by
    rw [show replacementSites.filter away =
        prefixedShellZeroThresholdedAwayEndpoints initial t x r terminal D
          upper m ellReplacement by exact hreplacementFilter,
      card_prefixedShellZeroThresholdedAwayEndpoints]
    exact hreplacement.2
  have hother := filter_not_away_listThresholdSites_eq_of_distinguished_eq
    initial t x r terminal D m hm qSource qReplacement hdist
  have hotherCard : (sourceSites.filter fun y ↦ ¬away y).card =
      (replacementSites.filter fun y ↦ ¬away y).card := by
    exact congrArg Finset.card hother
  have hsourceSplit := Finset.card_filter_add_card_filter_not
    (s := sourceSites) away
  have hreplacementSplit := Finset.card_filter_add_card_filter_not
    (s := replacementSites) away
  change replacementSites.card = sourceSites.card + delta
  omega

/-- Walk-clock form of `card_listThresholdSites_add_of_endpointIncrement`.
It is stated directly on the physical prefixed reconstructed words consumed
by stopped-fibre acceptance. -/
theorem thresholdCount_prefixedTilingInsertion_add_of_endpointIncrement
    (initial : BoundaryTail) {i cap m w : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : BoundaryTail) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (hm : 0 < m)
    (qSource qReplacement : TilingCappedCoordinates i cap)
    (ellSource ellReplacement : TruncatedTotals upper)
    (central delta : ℕ)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hdist : (splitTilingCoordinatesEquiv t x r D qSource).1 =
      (splitTilingCoordinatesEquiv t x r D qReplacement).1)
    (hbase : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1 =
        Fintype.card (TilingCoordinatesAt t x r b.1))
    (hdominance : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail)
          (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1)
    (hsource : ∀ b, tilingShellZeroSourceCoordinate
      (cap := cap) (m := m) (w := w) t x r D upper b (ellSource b))
    (hreplacement : prefixedShellZeroReplacementScreenAtIncrement
      (cap := cap) (m := m) (w := w) initial.1 t x r
        (prefixedTilingInsertionTerminal initial t x r
          (fun j ↦ (qSource j : ℕ)) tail)
        D upper central delta ellReplacement)
    (htotalSource : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qSource j : ℕ)) b.1 =
        (ellSource b : ℕ))
    (htotalReplacement : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qReplacement j : ℕ)) b.1 =
        (ellReplacement b : ℕ)) :
    let vSource := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qSource j : ℕ)) tail.1
    let vReplacement := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1
    let sSource := trajectory
      (extendPrefix (directionVectorOfList vSource))
    let sReplacement := trajectory
      (extendPrefix (directionVectorOfList vReplacement))
    thresholdCount sReplacement vReplacement.length m =
      thresholdCount sSource vSource.length m + delta := by
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (qSource j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (qReplacement j : ℕ)
  let terminal := prefixedTilingInsertionTerminal initial t x r qNat tail
  let vSource := prefixedTilingInsertionPrefixList initial.1 t x r qNat tail.1
  let vReplacement := prefixedTilingInsertionPrefixList initial.1 t x r qNat' tail.1
  let sSource := trajectory (extendPrefix (directionVectorOfList vSource))
  let sReplacement := trajectory
    (extendPrefix (directionVectorOfList vReplacement))
  have hterminal' :
      prefixedTilingInsertionTerminal initial t x r qNat' tail = terminal :=
    (prefixedTilingInsertionTerminal_eq_of_coordinates
      initial t x r qNat qNat' tail hstart).symm
  have hpathSource : finitePathList (pathPrefix sSource vSource.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r qNat) terminal := by
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r qNat tail hstart
  have hpathReplacement :
      finitePathList (pathPrefix sReplacement vReplacement.length) =
        prefixedTilingPrefixPointPath initial.1 x
          (tilingInsertGapVector t x r qNat') terminal := by
    rw [← hterminal']
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r qNat' tail hstart
  have hcard := card_listThresholdSites_add_of_endpointIncrement
    initial.1 t x r terminal D upper hm qSource qReplacement ellSource
      ellReplacement central delta hdist hbase hdominance hsource
      hreplacement htotalSource htotalReplacement
  change thresholdCount sReplacement vReplacement.length m =
    thresholdCount sSource vSource.length m + delta
  unfold thresholdCount
  rw [← listThresholdSites_finitePathList sReplacement
      vReplacement.length m hm,
    ← listThresholdSites_finitePathList sSource vSource.length m hm,
    hpathReplacement, hpathSource]
  exact hcard

end

end Erdos1165.TilingShellZeroThresholdCountAdd
