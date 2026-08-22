/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingInsertedLocalTime
import ErdosProblems.Erdos1165.TilingTerminalFavoriteFactorization
import ErdosProblems.Erdos1165.ShiftedPrefixBridge

/-!
# Stopped acceptance and terminal favorite data for all six tilings

This module connects the literal capped creation clock used by the variable
stopped fibres to the optional-terminal path factorization.  The stopped
predicate is first reduced to terminal threshold count and new-site local
time.  After an exact prefix-path identification, adjoining the favorite
condition factors into fixed outside data, finite distinguished endpoint
data, and the product cutoff on all remaining tiling dominoes.
-/

open Set

namespace Erdos1165.TilingStoppedAcceptanceFactorization

open LazyDecomposition PathInsertion StoppedInsertion SpatialInsertionFiber
open PreStoppingFiber PreStoppingSpatialLaw VariableStoppedFiber
open HLOZPathEvents
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingInsertedLocalTime
open ShiftedPrefixBridge

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-! ## Canonical point path of an inserted direction word -/

/-- Pairing a direction list is the finite list of its consecutive
even/odd-indexed direction pairs. -/
theorem pairDirectionList_eq_ofFn_pairs (ds : List Direction) :
    pairDirectionList ds =
      List.ofFn (fun j : Fin (ds.length / 2) =>
        (ds.get ⟨2 * (j : ℕ), by omega⟩,
          ds.get ⟨2 * (j : ℕ) + 1, by omega⟩)) := by
  induction ds using List.twoStepInduction with
  | nil => rfl
  | singleton a => simp [pairDirectionList]
  | cons_cons a b ds ih _ =>
      apply List.ext_getElem?
      intro k
      cases k with
      | zero => simp [pairDirectionList]
      | succ k =>
        simp only [pairDirectionList, List.getElem?_cons_succ]
        rw [ih]
        simp only [List.getElem?_ofFn]
        split
        · rename_i h
          rw [dif_pos (by simp only [List.length_cons]; omega)]
          simp only [Option.some.injEq, Prod.mk.injEq]
          simp [show 2 * (k + 1) = 2 * k + 2 by omega]
        · rename_i h
          rw [dif_neg (by simp only [List.length_cons]; omega)]

/-- The block word read by the canonical prefix bridge is exactly the
ordinary pairing of its increment prefix. -/
theorem completePrefixBlocks_eq_prefixBlockWord (omega : StepPath) (n : ℕ) :
    completePrefixBlocks omega n = prefixBlockWord n omega := by
  unfold completePrefixBlocks prefixBlockWord incrementPrefixList
  rw [pairDirectionList_eq_ofFn_pairs]
  apply List.ext_getElem?
  intro j
  simp [stepPrefix]

/-- The possible terminal singleton of a reconstructed insertion prefix.
It is absent for an even word and is the actual endpoint for a one-direction
boundary tail. -/
def tilingInsertionTerminal {i : ℕ} (t : DominoTiling)
    (r : TilingRetainedWord t (0, 0) i) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail) : Option Point :=
  let v := tilingInsertionPrefixList t (0, 0) r q tail.1
  match tail.1 with
  | [] => none
  | _ :: _ =>
      some (trajectory (extendPrefix (directionVectorOfList v)) v.length)

/-- Exact point-list reconstruction of every all-six insertion prefix with
its canonical zero-or-one direction boundary tail. -/
theorem finitePathList_tilingInsertionPrefix {i : ℕ} (t : DominoTiling)
    (r : TilingRetainedWord t (0, 0) i) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail) :
    let v := tilingInsertionPrefixList t (0, 0) r q tail.1
    finitePathList
        (pathPrefix
          (trajectory (extendPrefix (directionVectorOfList v))) v.length) =
      tilingPrefixPointPath (0, 0)
        (tilingInsertGapVector t (0, 0) r q)
        (tilingInsertionTerminal t r q tail) := by
  let bs := tilingInsertGapVector t (0, 0) r q
  let v := tilingInsertionPrefixList t (0, 0) r q tail.1
  let omega := extendPrefix (directionVectorOfList v)
  change finitePathList (pathPrefix (trajectory omega) v.length) =
    tilingPrefixPointPath (0, 0) bs
      (tilingInsertionTerminal t r q tail)
  have hincrement : incrementPrefixList v.length omega = v := by
    unfold incrementPrefixList
    rw [stepPrefix_extendPrefix, ofFn_directionVectorOfList]
  have hblocks : completePrefixBlocks omega v.length = bs := by
    rw [completePrefixBlocks_eq_prefixBlockWord]
    unfold prefixBlockWord
    rw [hincrement]
    unfold v tilingInsertionPrefixList
    exact pairDirectionList_flatten_append_shortTail bs tail.1 tail.2
  rw [prefixPath_eq_blockPath_append_remainder, hblocks]
  change blockPath (0, 0) bs ++
      (if v.length % 2 = 0 then [] else [trajectory omega v.length]) =
    tilingPrefixPointPath (0, 0) bs
      (tilingInsertionTerminal t r q tail)
  cases htail : tail.1 with
  | nil =>
      have hv : v.length % 2 = 0 := by
        simp [v, tilingInsertionPrefixList, htail]
      simp [hv, tilingInsertionTerminal, htail, tilingPrefixPointPath]
  | cons d ds =>
      cases ds with
      | nil =>
        simp [tilingInsertionTerminal, htail, tilingPrefixPointPath, omega, v]
      | cons e es =>
        have hshort := tail.2
        simp [htail] at hshort

/-! ## Literal stopping acceptance -/

/-- Strictly before the artificial cutoff, acceptance of a reconstructed
tiling word is exactly first creation of the requested threshold site. -/
theorem tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
    {i : ℕ} (m k cutoff : ℕ) (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail)
    (hlt : (tilingInsertionPrefixList t x r q tail.1).length < cutoff) :
    TilingStoppingAccepted (truncatedLevelTime m k cutoff) t x r q tail.1 ↔
      ThresholdCreation
        (trajectory (extendPrefix (directionVectorOfList
          (tilingInsertionPrefixList t x r q tail.1))))
        m k (tilingInsertionPrefixList t x r q tail.1).length := by
  exact truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
    m k cutoff (tilingInsertionPrefixList t x r q tail.1).length _ hlt

/-- Terminal-data form of all-six tiling stopping acceptance.  It isolates
the exact threshold count and the local time of the newly created site. -/
theorem tilingStoppingAccepted_truncatedLevelTime_iff_terminal
    {i : ℕ} (m k cutoff : ℕ) (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail) (hm : 0 < m) (hk : 0 < k)
    (hpos : 0 < (tilingInsertionPrefixList t x r q tail.1).length)
    (hlt : (tilingInsertionPrefixList t x r q tail.1).length < cutoff) :
    TilingStoppingAccepted (truncatedLevelTime m k cutoff) t x r q tail.1 ↔
      let v := tilingInsertionPrefixList t x r q tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      thresholdCount s v.length m = k ∧
        localTime s v.length (s v.length) = m := by
  rw [tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
    m k cutoff t x r q tail hlt]
  exact thresholdCreation_iff_terminal_count_and_new_localTime
    _ m k _ hm hk hpos

/-! ## Optional-terminal global level factorization -/

/-- Frozen inequalities at sites outside every represented tiling domino. -/
def TilingPrefixFixedOutsideBelowLevel {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i) (terminal : Option Point)
    (level : ℕ) : Prop :=
  ∀ y : Point, tilingBase t y ∉ tilingExternalDominoBases t x r →
    tilingFixedBoundaryLocalTime x r terminal y < level

/-- Finite endpoint inequalities on the represented distinguished dominoes. -/
def TilingPrefixDistinguishedEndpointsBelowLevel {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (level : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) : Prop :=
  ∀ b : TilingExternalDomino t x r, b.1 ∈ D →
    listLocalTime
        (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal)
        b.1 < level ∧
      listLocalTime
        (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal)
        (tilingPartner t b.1) < level

/-- Literal global upper-level condition on the reconstructed prefix,
including its possible final unpaired direction. -/
def TilingPrefixAllSitesBelowLevel {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i) (terminal : Option Point)
    (level : ℕ) (q : Fin (i + 1) → ℕ) : Prop :=
  ∀ y : Point,
    listLocalTime
      (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) y <
        level

/-- Outside represented dominoes, the optional-terminal path local time is
the frozen retained-prefix local time and is independent of all insertion
coordinates. -/
theorem tilingInsertedPrefix_localTime_of_base_not_mem {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (terminal : Option Point) (y : Point)
    (hy : tilingBase t y ∉ tilingExternalDominoBases t x r) :
    listLocalTime
        (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) y =
      tilingFixedBoundaryLocalTime x r terminal y := by
  rw [tilingListLocalTime_split, tilingExternalPath_insertedPrefix,
    tilingLazyPoints_insertedPrefix]
  unfold tilingFixedBoundaryLocalTime
  rw [TilingSpatialInsertionFiber.tilingLazyLocalTime_insertedPath,
    TilingTerminalFavoriteFactorization.tilingInsertionLazyLocalTime_eq_zero_of_base_not_mem
      t x r q y hy,
    add_zero]

/-- Exact optional-terminal distinguished-data times product-cutoff
factorization of the global upper-level condition. -/
theorem tilingPrefixAllSitesBelowLevel_iff_factorization {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (level : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) :
    TilingPrefixAllSitesBelowLevel t x r terminal level q ↔
      TilingPrefixFixedOutsideBelowLevel t x r terminal level ∧
        TilingPrefixDistinguishedEndpointsBelowLevel
          t x r terminal level D q ∧
          TilingInsertedLocalTime.TilingDominoTruncation
            t x r terminal level D q := by
  constructor
  · intro hall
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      rw [← tilingInsertedPrefix_localTime_of_base_not_mem
        t x r q terminal y hy]
      exact hall y
    · intro b _
      exact ⟨hall b.1, hall (tilingPartner t b.1)⟩
    · apply (tilingActualEndpointsBelow_iff_dominoTruncation
        t x r terminal level D q).mp
      intro b _
      exact ⟨hall b.1, hall (tilingPartner t b.1)⟩
  · rintro ⟨hfixed, hdist, htrunc⟩ y
    by_cases hy : tilingBase t y ∈ tilingExternalDominoBases t x r
    · let b : TilingExternalDomino t x r := ⟨tilingBase t y, hy⟩
      have hend :
          listLocalTime
              (tilingPrefixPointPath x
                (tilingInsertGapVector t x r q) terminal) b.1 < level ∧
            listLocalTime
              (tilingPrefixPointPath x
                (tilingInsertGapVector t x r q) terminal)
              (tilingPartner t b.1) < level := by
        by_cases hb : b.1 ∈ D
        · exact hdist b hb
        · exact (tilingActualEndpointsBelow_iff_dominoTruncation
            t x r terminal level D q).mpr htrunc b hb
      have hbase := hend.1
      have hpartner := hend.2
      rcases point_eq_tilingBase_or_partner_base t y with hybase | hypartner
      · rw [hybase]
        exact hbase
      · rw [hypartner]
        exact hpartner
    · rw [tilingInsertedPrefix_localTime_of_base_not_mem
        t x r q terminal y hy]
      exact hfixed y hy

/-! ## Accepted favorite atoms -/

/-- On an explicitly identified reconstructed prefix, the no-next-level
favorite condition is precisely the optional-terminal tiling factorization. -/
theorem levelFavorite_iff_tilingPrefixFactorization_at_acceptedWord
    {i : ℕ} (m k cutoff : ℕ) (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail) (terminal : Option Point) (D : Finset Point)
    (hk : 0 < k)
    (hacc : TilingStoppingAccepted
      (truncatedLevelTime m k cutoff) t x r q tail.1)
    (hlt : (tilingInsertionPrefixList t x r q tail.1).length < cutoff)
    (hpath :
      let v := tilingInsertionPrefixList t x r q tail.1
      finitePathList
          (pathPrefix
            (trajectory (extendPrefix (directionVectorOfList v))) v.length) =
        tilingPrefixPointPath x
          (tilingInsertGapVector t x r q) terminal) :
    levelFavorite
        (trajectory (extendPrefix (directionVectorOfList
          (tilingInsertionPrefixList t x r q tail.1)))) m k ↔
      TilingPrefixFixedOutsideBelowLevel t x r terminal (m + 1) ∧
        TilingPrefixDistinguishedEndpointsBelowLevel
          t x r terminal (m + 1) D q ∧
          TilingInsertedLocalTime.TilingDominoTruncation
            t x r terminal (m + 1) D q := by
  let v := tilingInsertionPrefixList t x r q tail.1
  let omega := extendPrefix (directionVectorOfList v)
  have htime : truncatedLevelTime m k cutoff omega = v.length := hacc
  rw [levelFavorite_iff_all_localTime_lt_succ_at_truncatedLevelTime
    m k cutoff v.length omega hk hlt htime,
    ← tilingPrefixAllSitesBelowLevel_iff_factorization
      t x r terminal (m + 1) D q]
  unfold TilingPrefixAllSitesBelowLevel
  constructor <;> intro h y
  · rw [← hpath, ← localTime_eq_listLocalTime]
    exact h y
  · rw [localTime_eq_listLocalTime, hpath]
    exact h y

/-- Full terminal factorization of a stopped favorite atom: creation
acceptance contributes only the terminal threshold count and new-site local
time, while the favorite condition contributes fixed outside data,
distinguished endpoint data, and away-domino truncation. -/
theorem tilingStoppingAccepted_and_levelFavorite_iff_terminal_factorization
    {i : ℕ} (m k cutoff : ℕ) (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail) (terminal : Option Point) (D : Finset Point)
    (hm : 0 < m) (hk : 0 < k)
    (hpos : 0 < (tilingInsertionPrefixList t x r q tail.1).length)
    (hlt : (tilingInsertionPrefixList t x r q tail.1).length < cutoff)
    (hpath :
      let v := tilingInsertionPrefixList t x r q tail.1
      finitePathList
          (pathPrefix
            (trajectory (extendPrefix (directionVectorOfList v))) v.length) =
        tilingPrefixPointPath x
          (tilingInsertGapVector t x r q) terminal) :
    let v := tilingInsertionPrefixList t x r q tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    (TilingStoppingAccepted
        (truncatedLevelTime m k cutoff) t x r q tail.1 ∧
      levelFavorite s m k) ↔
      (thresholdCount s v.length m = k ∧
          localTime s v.length (s v.length) = m) ∧
        TilingPrefixFixedOutsideBelowLevel t x r terminal (m + 1) ∧
          TilingPrefixDistinguishedEndpointsBelowLevel
            t x r terminal (m + 1) D q ∧
            TilingInsertedLocalTime.TilingDominoTruncation
      t x r terminal (m + 1) D q := by
  dsimp only
  constructor
  · rintro ⟨hacc, hfavorite⟩
    exact ⟨
      (tilingStoppingAccepted_truncatedLevelTime_iff_terminal
        m k cutoff t x r q tail hm hk hpos hlt).mp hacc,
      (levelFavorite_iff_tilingPrefixFactorization_at_acceptedWord
        m k cutoff t x r q tail terminal D hk hacc hlt hpath).mp hfavorite⟩
  · rintro ⟨hterminal, hfactor⟩
    have hacc :=
      (tilingStoppingAccepted_truncatedLevelTime_iff_terminal
        m k cutoff t x r q tail hm hk hpos hlt).mpr hterminal
    exact ⟨hacc,
      (levelFavorite_iff_tilingPrefixFactorization_at_acceptedWord
        m k cutoff t x r q tail terminal D hk hacc hlt hpath).mpr hfactor⟩

/-- Canonical stopped-atom specialization with no auxiliary path-equality
hypothesis.  The deterministic direction word itself supplies the exact
optional-terminal point path. -/
theorem tilingStoppingAccepted_and_levelFavorite_iff_canonical_factorization
    {i : ℕ} (m k cutoff : ℕ) (t : DominoTiling)
    (r : TilingRetainedWord t (0, 0) i) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail) (D : Finset Point)
    (hm : 0 < m) (hk : 0 < k)
    (hpos : 0 < (tilingInsertionPrefixList t (0, 0) r q tail.1).length)
    (hlt : (tilingInsertionPrefixList t (0, 0) r q tail.1).length < cutoff) :
    let v := tilingInsertionPrefixList t (0, 0) r q tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    let terminal := tilingInsertionTerminal t r q tail
    (TilingStoppingAccepted
        (truncatedLevelTime m k cutoff) t (0, 0) r q tail.1 ∧
      levelFavorite s m k) ↔
      (thresholdCount s v.length m = k ∧
          localTime s v.length (s v.length) = m) ∧
        TilingPrefixFixedOutsideBelowLevel
          t (0, 0) r terminal (m + 1) ∧
          TilingPrefixDistinguishedEndpointsBelowLevel
            t (0, 0) r terminal (m + 1) D q ∧
            TilingInsertedLocalTime.TilingDominoTruncation
              t (0, 0) r terminal (m + 1) D q := by
  exact tilingStoppingAccepted_and_levelFavorite_iff_terminal_factorization
    m k cutoff t (0, 0) r q tail (tilingInsertionTerminal t r q tail) D
      hm hk hpos hlt (finitePathList_tilingInsertionPrefix t r q tail)

end

end Erdos1165.TilingStoppedAcceptanceFactorization
