import ErdosProblems.Erdos1165.VariableStoppedTracePartition

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1165.ExactFavoriteTruncation

open LazyDecomposition PathInsertion StoppedInsertion SpatialInsertionFiber
open ShiftedPrefixBridge PrefixLevelTruncation PreStoppingFiber
open PrefixConditionalLaw PreStoppingSpatialLaw HLOZPathEvents

noncomputable section

/-!
# Exact away-domino cutoff after fixing the favorite set

The event that all terminal local times are at most `m` gives a formal
`m+1` upper bound.  HLOZ (6.7), however, conditions on the *exact* favorite
locations.  Any site away from their oriented domino bases must then have
local time strictly below `m`; equality would make it an additional
favorite.  The theorems below record this sharper, product-relevant cutoff.
-/

theorem externalDomino_compatible {o : Orientation} {i : ℕ} {x : Point}
    (r : Fin i → RetainedBlock o) (hx : OrientationCompatible o x)
    (b : ExternalDomino x r) : OrientationCompatible o b.1 := by
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp b.2
  have h := externalBase_compatible r hx j
  rwa [hj] at h

theorem localTime_lt_level_of_dominoBase_not_favorite
    (o : Orientation) (s : WalkPath) (n m : ℕ) (hm : 0 < m)
    (hsites : thresholdSites s n m = favoriteSites s n)
    (D : Finset Point) (hD : D = favoriteDominoBases o s n)
    (y : Point) (hy : dominoBase o y ∉ D) :
    localTime s n y < m := by
  by_contra hnot
  have hge : m ≤ localTime s n y := Nat.le_of_not_gt hnot
  have hthreshold : y ∈ thresholdSites s n m :=
    (mem_thresholdSites_iff s n m y hm).mpr hge
  have hfavorite : y ∈ favoriteSites s n := by
    rw [← hsites]
    exact hthreshold
  have hbase := favorite_site_base_mem o s n hfavorite
  rw [← hD] at hbase
  exact hy hbase

/-- Even-orientation exact favorite-set truncation. -/
theorem even_away_dominoTruncation_at_exact_favorite_level
    {i : ℕ} (m k cutoff n : ℕ) (omega : StepPath)
    (hm : 0 < m) (hk : 0 < k) (hn : n < cutoff)
    (htime : truncatedLevelTime m k cutoff omega = n)
    (hfavorite : levelFavorite (trajectory omega) m k)
    (r : Fin i → RetainedBlock .even) (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks omega n = insertGapVector r q) :
    EvenPrefixDominoTruncation omega n r q m
      (favoriteDominoBases .even (trajectory omega) n) := by
  have hsites := thresholdSites_eq_favoriteSites_at_truncatedLevelTime
    m k cutoff n omega hk hn htime hfavorite
  rw [EvenPrefixDominoTruncation]
  rw [← even_actualEndpointsBelow_iff_dominoTruncation
    omega n r q hword m (favoriteDominoBases .even (trajectory omega) n)]
  intro b hb
  have hbcompat : OrientationCompatible .even b.1 :=
    externalDomino_compatible r even_start_compatible b
  constructor
  · rw [← localTime_eq_listLocalTime]
    apply localTime_lt_level_of_dominoBase_not_favorite
      .even (trajectory omega) n m hm hsites
      (favoriteDominoBases .even (trajectory omega) n) rfl b.1
    rwa [dominoBase_eq_self_of_compatible hbcompat]
  · rw [← localTime_eq_listLocalTime]
    apply localTime_lt_level_of_dominoBase_not_favorite
      .even (trajectory omega) n m hm hsites
      (favoriteDominoBases .even (trajectory omega) n) rfl
      (excursionMiddle .even b.1)
    rwa [dominoBase_middle_of_compatible hbcompat]

/-- Shifted-orientation exact favorite-set truncation, including its
dropped time-zero convention and optional terminal singleton. -/
theorem shifted_away_dominoTruncation_at_exact_favorite_level
    {i : ℕ} (m k cutoff n : ℕ) (omega : StepPath)
    (hm : 0 < m) (hk : 0 < k) (hn : n < cutoff) (hpos : 0 < n)
    (htime : truncatedLevelTime m k cutoff omega = n)
    (hfavorite : levelFavorite (trajectory omega) m k)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks omega n = insertGapVector r q) :
    ShiftedPrefixDominoTruncation omega n r q m
      (favoriteDominoBases .shifted (trajectory omega) n) := by
  have hsites := thresholdSites_eq_favoriteSites_at_truncatedLevelTime
    m k cutoff n omega hk hn htime hfavorite
  rw [ShiftedPrefixDominoTruncation]
  rw [← shifted_actualEndpointsBelow_iff_dominoTruncation
    omega n hpos r q hword m
      (favoriteDominoBases .shifted (trajectory omega) n)]
  intro b hb
  have hbcompat : OrientationCompatible .shifted b.1 :=
    externalDomino_compatible r (shifted_start_compatible omega) b
  constructor
  · rw [← localTime_eq_listLocalTime]
    apply localTime_lt_level_of_dominoBase_not_favorite
      .shifted (trajectory omega) n m hm hsites
      (favoriteDominoBases .shifted (trajectory omega) n) rfl b.1
    rwa [dominoBase_eq_self_of_compatible hbcompat]
  · rw [← localTime_eq_listLocalTime]
    apply localTime_lt_level_of_dominoBase_not_favorite
      .shifted (trajectory omega) n m hm hsites
      (favoriteDominoBases .shifted (trajectory omega) n) rfl
      (excursionMiddle .shifted b.1)
    rwa [dominoBase_middle_of_compatible hbcompat]

/-! ## The corrected finite product formula -/

/-- Corrected even form of the finite product identity: after the exact
favorite set has been fixed, every away-domino cutoff is
`m - fixedPrefixMax`. -/
theorem even_exactFavoriteProductLaw
    {i : ℕ} (m k cutoff n : ℕ) (omega : StepPath)
    (hm : 0 < m) (hk : 0 < k) (hn : n < cutoff)
    (htime : truncatedLevelTime m k cutoff omega = n)
    (hfavorite : levelFavorite (trajectory omega) m k)
    (r : Fin i → RetainedBlock .even) (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks omega n = insertGapVector r q)
    {delta : Type*} [Fintype delta] (distinguishedMass : delta → ℝ)
    (hDist : (∑ d, distinguishedMass d) ≠ 0)
    (ell : UpperTruncatedDominoTotals (0, 0) r
      (favoriteDominoBases .even (trajectory omega) n)
      (fun b ↦ m - fixedEvenPrefixDominoMax omega n r b)) :
    EvenPrefixDominoTruncation omega n r q m
        (favoriteDominoBases .even (trajectory omega) n) ∧
      (∑ d, upperTotalsJointMass (0, 0) r
            (favoriteDominoBases .even (trajectory omega) n)
            (fun b ↦ m - fixedEvenPrefixDominoMax omega n r b) ell *
          distinguishedMass d) /
          (∑ z : UpperTruncatedDominoTotals (0, 0) r
              (favoriteDominoBases .even (trajectory omega) n)
              (fun b ↦ m - fixedEvenPrefixDominoMax omega n r b),
            ∑ d, upperTotalsJointMass (0, 0) r
                (favoriteDominoBases .even (trajectory omega) n)
                (fun b ↦ m - fixedEvenPrefixDominoMax omega n r b) z *
              distinguishedMass d) =
        ∏ b : AwayDomino (0, 0) r
            (favoriteDominoBases .even (trajectory omega) n),
          upperTruncatedDominoMass (0, 0) r
            (fun c ↦ m - fixedEvenPrefixDominoMax omega n r c)
            b.1 (ell b) := by
  constructor
  · exact even_away_dominoTruncation_at_exact_favorite_level
      m k cutoff n omega hm hk hn htime hfavorite r q hword
  · exact distinguished_marginal_conditional_factorization
      (0, 0) r (favoriteDominoBases .even (trajectory omega) n)
      (fun b ↦ m - fixedEvenPrefixDominoMax omega n r b)
      distinguishedMass hDist ell

/-- Corrected shifted form of the same finite product identity. -/
theorem shifted_exactFavoriteProductLaw
    {i : ℕ} (m k cutoff n : ℕ) (omega : StepPath)
    (hm : 0 < m) (hk : 0 < k) (hn : n < cutoff) (hpos : 0 < n)
    (htime : truncatedLevelTime m k cutoff omega = n)
    (hfavorite : levelFavorite (trajectory omega) m k)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks omega n = insertGapVector r q)
    {delta : Type*} [Fintype delta] (distinguishedMass : delta → ℝ)
    (hDist : (∑ d, distinguishedMass d) ≠ 0)
    (ell : UpperTruncatedDominoTotals (trajectory omega 1) r
      (favoriteDominoBases .shifted (trajectory omega) n)
      (fun b ↦ m - fixedShiftedPrefixDominoMax omega n r b)) :
    ShiftedPrefixDominoTruncation omega n r q m
        (favoriteDominoBases .shifted (trajectory omega) n) ∧
      (∑ d, upperTotalsJointMass (trajectory omega 1) r
            (favoriteDominoBases .shifted (trajectory omega) n)
            (fun b ↦ m - fixedShiftedPrefixDominoMax omega n r b) ell *
          distinguishedMass d) /
          (∑ z : UpperTruncatedDominoTotals (trajectory omega 1) r
              (favoriteDominoBases .shifted (trajectory omega) n)
              (fun b ↦ m - fixedShiftedPrefixDominoMax omega n r b),
            ∑ d, upperTotalsJointMass (trajectory omega 1) r
                (favoriteDominoBases .shifted (trajectory omega) n)
                (fun b ↦ m - fixedShiftedPrefixDominoMax omega n r b) z *
              distinguishedMass d) =
        ∏ b : AwayDomino (trajectory omega 1) r
            (favoriteDominoBases .shifted (trajectory omega) n),
          upperTruncatedDominoMass (trajectory omega 1) r
            (fun c ↦ m - fixedShiftedPrefixDominoMax omega n r c)
            b.1 (ell b) := by
  constructor
  · exact shifted_away_dominoTruncation_at_exact_favorite_level
      m k cutoff n omega hm hk hn hpos htime hfavorite r q hword
  · exact distinguished_marginal_conditional_factorization
      (trajectory omega 1) r
      (favoriteDominoBases .shifted (trajectory omega) n)
      (fun b ↦ m - fixedShiftedPrefixDominoMax omega n r b)
      distinguishedMass hDist ell

end

end Erdos1165.ExactFavoriteTruncation
