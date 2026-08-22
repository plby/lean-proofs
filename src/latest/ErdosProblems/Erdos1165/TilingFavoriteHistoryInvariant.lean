import ErdosProblems.Erdos1165.TilingDistinguishedTraceInvariant

namespace Erdos1165.TilingFavoriteHistoryInvariant

open HLOZPathEvents LazyDecomposition
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingCappedMarginalization TilingInsertedLocalTime
open TilingFavoriteTraceSupport TilingInsertionTerminalInvariant
open TilingStoppedAcceptanceFactorization
open TilingDistinguishedTraceInvariant
open PreStoppingFiber PreStoppingSpatialLaw StoppedInsertion VariableStoppedFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

theorem canonical_outside_favorite_bases_lt_pair
    {i cap : ℕ} (t : DominoTiling) (m k cutoff : ℕ)
    (hm : 0 < m) (hk : 0 < k)
    (r : TilingRetainedWord t (0, 0) i) (tail : BoundaryTail)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hD :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      favoriteTilingBases t
        (trajectory (extendPrefix (directionVectorOfList v))) v.length = D)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) r D q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) r D q').1)
    (htrunc : TilingDominoTruncation t (0, 0) r
      (tilingInsertionTerminal t r (fun j ↦ (q j : ℕ)) tail) m D
      (fun j ↦ (q j : ℕ)))
    (htrunc' : TilingDominoTruncation t (0, 0) r
      (tilingInsertionTerminal t r (fun j ↦ (q j : ℕ)) tail) m D
      (fun j ↦ (q' j : ℕ)))
    (haccepted : TilingStoppingAccepted (truncatedLevelTime m k cutoff)
      t (0, 0) r (fun j ↦ (q j : ℕ)) tail.1)
    (hfavorite :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      levelFavorite (trajectory (extendPrefix (directionVectorOfList v))) m k)
    (hlt : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff) :
    (∀ y, tilingBase t y ∉ D →
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      localTime (trajectory (extendPrefix (directionVectorOfList v)))
        v.length y < m) ∧
    (∀ y, tilingBase t y ∉ D →
      let v' := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q' j : ℕ)) tail.1
      localTime (trajectory (extendPrefix (directionVectorOfList v')))
        v'.length y < m) := by
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (q j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (q' j : ℕ)
  let v := tilingInsertionPrefixList t (0, 0) r qNat tail.1
  let v' := tilingInsertionPrefixList t (0, 0) r qNat' tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  let terminal := tilingInsertionTerminal t r qNat tail
  have hterminal' : tilingInsertionTerminal t r qNat' tail = terminal := by
    exact (tilingInsertionTerminal_eq_of_coordinates t r qNat qNat' tail).symm
  have hpath : finitePathList (pathPrefix s v.length) =
      tilingPrefixPointPath (0, 0)
        (tilingInsertGapVector t (0, 0) r qNat) terminal := by
    exact finitePathList_tilingInsertionPrefix t r qNat tail
  have hpath' : finitePathList (pathPrefix s' v'.length) =
      tilingPrefixPointPath (0, 0)
        (tilingInsertGapVector t (0, 0) r qNat') terminal := by
    rw [← hterminal']
    exact finitePathList_tilingInsertionPrefix t r qNat' tail
  have hsites : thresholdSites s v.length m = favoriteSites s v.length :=
    thresholdSites_eq_favoriteSites_at_truncatedLevelTime
      m k cutoff v.length (extendPrefix (directionVectorOfList v))
      hk hlt haccepted hfavorite
  have hout : ∀ y, tilingBase t y ∉ D → localTime s v.length y < m := by
    intro y hy
    exact localTime_lt_level_of_tilingBase_not_favorite
      t s v.length m hm hsites y (by rw [hD]; exact hy)
  refine ⟨hout, ?_⟩
  intro y hy
  by_contra hnot
  have hge' : m ≤ localTime s' v'.length y := Nat.le_of_not_gt hnot
  have hgeList' : m ≤ listLocalTime
      (tilingPrefixPointPath (0, 0)
        (tilingInsertGapVector t (0, 0) r qNat') terminal) y := by
    rwa [← hpath', ← localTime_eq_listLocalTime]
  have hgeList :=
    (tilingPrefixLocalTime_ge_level_iff_of_distinguished_eq
      t (0, 0) r terminal m D q q' hdist htrunc htrunc' y).2 hgeList'
  have hge : m ≤ localTime s v.length y := by
    rwa [localTime_eq_listLocalTime, hpath]
  exact (not_lt_of_ge hge) (hout y hy)

theorem canonical_creation_location_eq_of_favorite_trace
    {i cap : ℕ} (t : DominoTiling) (m k rank cutoff : ℕ)
    (hm : 0 < m) (hk : 0 < k) (hrank : 0 < rank)
    (r : TilingRetainedWord t (0, 0) i) (tail : BoundaryTail)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hD :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      favoriteTilingBases t
        (trajectory (extendPrefix (directionVectorOfList v))) v.length = D)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) r D q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) r D q').1)
    (htrunc : TilingDominoTruncation t (0, 0) r
      (tilingInsertionTerminal t r (fun j ↦ (q j : ℕ)) tail) m D
      (fun j ↦ (q j : ℕ)))
    (htrunc' : TilingDominoTruncation t (0, 0) r
      (tilingInsertionTerminal t r (fun j ↦ (q j : ℕ)) tail) m D
      (fun j ↦ (q' j : ℕ)))
    (haccepted : TilingStoppingAccepted (truncatedLevelTime m k cutoff)
      t (0, 0) r (fun j ↦ (q j : ℕ)) tail.1)
    (hfavorite :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      levelFavorite (trajectory (extendPrefix (directionVectorOfList v))) m k)
    (hlt : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff)
    {n n' : ℕ}
    (hcreation :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      ThresholdCreation (trajectory (extendPrefix (directionVectorOfList v)))
        m rank n)
    (hcreation' :
      let v' := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q' j : ℕ)) tail.1
      ThresholdCreation (trajectory (extendPrefix (directionVectorOfList v')))
        m rank n')
    (hn : n ≤ (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1).length)
    (hn' : n' ≤ (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1).length) :
    let v := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1
    let v' := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1
    trajectory (extendPrefix (directionVectorOfList v)) n =
      trajectory (extendPrefix (directionVectorOfList v')) n' := by
  have hout := canonical_outside_favorite_bases_lt_pair
    t m k cutoff hm hk r tail D q q' hD hdist htrunc htrunc'
      haccepted hfavorite hlt
  exact canonical_creation_location_eq_of_distinguished_eq
    t m rank hm hrank r tail D q q' hdist hout.1 hout.2
      hcreation hcreation' hn hn'

end

end Erdos1165.TilingFavoriteHistoryInvariant
