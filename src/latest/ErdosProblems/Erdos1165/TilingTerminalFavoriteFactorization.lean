/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingSpatialInsertionFiber

/-!
# Terminal level data in an all-six stateful tiling fibre

This module gives the exact deterministic factorization used at a stopped
favorite clock.  Once the retained external word is fixed, sites outside its
represented tiling dominoes carry fixed local time.  On represented
distinguished dominoes the endpoint inequalities are retained as finite
distinguished-coordinate data.  On every other represented domino they are
exactly the independent coordinate cutoff `TilingDominoTruncation`.
-/

open scoped BigOperators

namespace Erdos1165.TilingTerminalFavoriteFactorization

open LazyDecomposition PathInsertion TilingLazyDecomposition
open TilingSpatialInsertionFiber

abbrev DominoTiling := Tilings.Tiling

theorem tilingInsertionLazyLocalTime_eq_zero_of_base_not_mem {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (y : Point)
    (hy : tilingBase t y ∉ tilingExternalDominoBases t x r) :
    tilingInsertionLazyLocalTime t x r q y = 0 := by
  classical
  unfold tilingInsertionLazyLocalTime
  apply Finset.sum_eq_zero
  intro k _
  rw [tilingEndpointIndicators]
  have hne : tilingBase t (rawExternalBase x r.1 k) ≠ tilingBase t y := by
    intro h
    apply hy
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, h⟩
  simp [hne]

/-- Outside the represented dominoes, the inserted path's local time is the
fixed retained-word local time and is independent of all insertion
coordinates. -/
theorem tilingInsertedPath_localTime_of_base_not_mem {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (y : Point)
    (hy : tilingBase t y ∉ tilingExternalDominoBases t x r) :
    listLocalTime (blockPath x (tilingInsertGapVector t x r q)) y =
      tilingFixedExternalLocalTime x r.1 y := by
  rw [tilingListLocalTime_split, tilingExternalPath_insertedPath]
  unfold tilingFixedExternalLocalTime
  rw [tilingLazyLocalTime_insertedPath,
    tilingInsertionLazyLocalTime_eq_zero_of_base_not_mem t x r q y hy,
    add_zero]

/-- Fixed terminal inequalities at sites whose domino never receives an
insertion coordinate. -/
def TilingFixedOutsideBelowLevel {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (m : ℕ) : Prop :=
  ∀ y : Point, tilingBase t y ∉ tilingExternalDominoBases t x r →
    tilingFixedExternalLocalTime x r.1 y < m

/-- The finite endpoint data retained on represented distinguished
dominoes. -/
def TilingDistinguishedEndpointsBelowLevel {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (m : ℕ) (D : Finset Point) (q : Fin (i + 1) → ℕ) : Prop :=
  ∀ b : TilingExternalDomino t x r, b.1 ∈ D →
    listLocalTime (blockPath x (tilingInsertGapVector t x r q)) b.1 < m ∧
      listLocalTime (blockPath x (tilingInsertGapVector t x r q))
        (tilingPartner t b.1) < m

/-- Literal global terminal local-time inequality on the reconstructed
finite path. -/
def TilingAllSitesBelowLevel {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (m : ℕ)
    (q : Fin (i + 1) → ℕ) : Prop :=
  ∀ y : Point,
    listLocalTime (blockPath x (tilingInsertGapVector t x r q)) y < m

/-- Exact distinguished-data times away-product factorization of the global
terminal level condition. -/
theorem tilingAllSitesBelowLevel_iff_fixed_distinguished_truncation {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (m : ℕ) (D : Finset Point) (q : Fin (i + 1) → ℕ) :
    TilingAllSitesBelowLevel t x r m q ↔
      TilingFixedOutsideBelowLevel t x r m ∧
        TilingDistinguishedEndpointsBelowLevel t x r m D q ∧
          TilingDominoTruncation t x r m D q := by
  constructor
  · intro hall
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      rw [← tilingInsertedPath_localTime_of_base_not_mem t x r q y hy]
      exact hall y
    · intro b _
      exact ⟨hall b.1, hall (tilingPartner t b.1)⟩
    · apply (tilingActualEndpointsBelowLevelAway_iff_dominoTruncation
        t x r m D q).mp
      intro b _
      exact ⟨hall b.1, hall (tilingPartner t b.1)⟩
  · rintro ⟨hfixed, hdist, htrunc⟩ y
    by_cases hy : tilingBase t y ∈ tilingExternalDominoBases t x r
    · let b : TilingExternalDomino t x r := ⟨tilingBase t y, hy⟩
      have hend :
          listLocalTime (blockPath x (tilingInsertGapVector t x r q)) b.1 < m ∧
            listLocalTime (blockPath x (tilingInsertGapVector t x r q))
              (tilingPartner t b.1) < m := by
        by_cases hb : b.1 ∈ D
        · exact hdist b hb
        · exact (tilingActualEndpointsBelowLevelAway_iff_dominoTruncation
            t x r m D q).mpr htrunc b hb
      have hbase :
          listLocalTime (blockPath x (tilingInsertGapVector t x r q))
            (tilingBase t y) < m := hend.1
      have hpartner :
          listLocalTime (blockPath x (tilingInsertGapVector t x r q))
            (tilingPartner t (tilingBase t y)) < m := hend.2
      rcases point_eq_tilingBase_or_partner_base t y with hybase | hypartner
      · rw [hybase]
        exact hbase
      · rw [hypartner]
        exact hpartner
    · rw [tilingInsertedPath_localTime_of_base_not_mem t x r q y hy]
      exact hfixed y hy

/-- At favorite level `m`, the no-next-level terminal predicate is the same
factorization with upper level `m + 1`. -/
theorem tilingAllSitesBelowNextLevel_iff_fixed_distinguished_truncation
    {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) :
    TilingAllSitesBelowLevel t x r (m + 1) q ↔
      TilingFixedOutsideBelowLevel t x r (m + 1) ∧
        TilingDistinguishedEndpointsBelowLevel t x r (m + 1) D q ∧
          TilingDominoTruncation t x r (m + 1) D q :=
  tilingAllSitesBelowLevel_iff_fixed_distinguished_truncation
    t x r (m + 1) D q

end Erdos1165.TilingTerminalFavoriteFactorization
