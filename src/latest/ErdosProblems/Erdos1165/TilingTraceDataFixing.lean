/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingStoppedAcceptanceFactorization
import ErdosProblems.Erdos1165.TilingVariableStoppedTracePartition

/-!
# Data fixed by an all-six favorite trace code

Membership in a non-null favorite trace piece fixes the retained external
word, boundary tail, favorite sites and bases, spatial start, and terminal
site at the genuine creation time.  These projection lemmas make those
invariances available to the capped-coordinate marginalization layer.
-/

namespace Erdos1165.TilingTraceDataFixing

open HLOZPathEvents VariableStoppedTracePartition
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition
open TilingStoppedAcceptanceFactorization
open StoppedInsertion SpatialInsertionFiber PreStoppingFiber VariableStoppedFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The external trace code of a canonical reconstructed insertion word is
exactly its retained stateful word and boundary tail, independently of the
insertion coordinates. -/
theorem fixedTilingExternalWordCode_tilingInsertionPrefix
    {i : ℕ} (t : DominoTiling)
    (r : TilingRetainedWord t (0, 0) i) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail) :
    let v := tilingInsertionPrefixList t (0, 0) r q tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    fixedTilingExternalWordCode t v.length s =
      (List.ofFn r.1, tail) := by
  let bs := tilingInsertGapVector t (0, 0) r q
  let v := tilingInsertionPrefixList t (0, 0) r q tail.1
  let omega := extendPrefix (directionVectorOfList v)
  let s := trajectory omega
  change fixedTilingExternalWordCode t v.length s =
    (List.ofFn r.1, tail)
  have hincrement : incrementPrefixList v.length omega = v := by
    unfold incrementPrefixList
    rw [stepPrefix_extendPrefix, ofFn_directionVectorOfList]
  have hword : prefixBlockWord v.length omega = bs := by
    unfold prefixBlockWord
    rw [hincrement]
    unfold v tilingInsertionPrefixList
    exact pairDirectionList_flatten_append_shortTail bs tail.1 tail.2
  have htail : prefixDirectionTail v.length omega = tail.1 := by
    unfold prefixDirectionTail
    rw [hincrement]
    unfold v tilingInsertionPrefixList
    exact unpairedDirectionTail_flatten_append_shortTail bs tail.1 tail.2
  unfold fixedTilingExternalWordCode
  simp only [s, stepsOfWalk_trajectory]
  apply Prod.ext
  · rw [hword, deleteTilingBlocks_tilingInsertGapVector]
  · apply Subtype.ext
    exact htail

/-- All concrete spatial fields fixed by a non-null trace code at time `n`. -/
structure FixedFavoriteTilingTraceDataAt (t : DominoTiling) (n : ℕ)
    (s : WalkPath)
    (z : TilingExternalWordCode t × TilingCreationFavoriteData) : Prop where
  externalCode_eq : fixedTilingExternalWordCode t n s = z.1
  favoriteSites_eq : favoriteSites s n = z.2.1.1
  favoriteBases_eq : favoriteTilingBases t s n = z.2.1.2
  start_eq : (0, 0) = z.2.2.1
  terminal_eq : s n = z.2.2.2

/-- A non-null trace-piece member fixes the raw external and favorite code at
the genuine variable creation time. -/
theorem mem_favoriteTilingCreationPiece_some_fixes_creationCode
    (t : DominoTiling) (m k : ℕ)
    (z : TilingExternalWordCode t × TilingCreationFavoriteData)
    {s : WalkPath} (hs : s ∈ favoriteTilingCreationPiece t m k (some z)) :
    tilingCreationExternalCode t m k s = z.1 ∧
      tilingCreationFavoriteData t m k s = z.2 := by
  exact ⟨hs.1.2, hs.2⟩

/-- If the creation represented by a trace piece occurs at `n`, every
external/favorite field of that piece is the corresponding literal datum at
time `n`. -/
theorem fixedFavoriteTilingTraceDataAt_of_mem_piece_of_creation
    (t : DominoTiling) (m k n : ℕ)
    (z : TilingExternalWordCode t × TilingCreationFavoriteData)
    {s : WalkPath} (hs : s ∈ favoriteTilingCreationPiece t m k (some z))
    (hcreation : ThresholdCreation s m k n) :
    FixedFavoriteTilingTraceDataAt t n s z := by
  have htime : creationTimeNat m k s = n :=
    creationTimeNat_eq_of_creation hcreation
  obtain ⟨hexternal, hfavorite⟩ :=
    mem_favoriteTilingCreationPiece_some_fixes_creationCode t m k z hs
  unfold tilingCreationExternalCode at hexternal
  unfold tilingCreationFavoriteData at hfavorite
  rw [htime] at hexternal hfavorite
  refine {
    externalCode_eq := hexternal
    favoriteSites_eq := ?_
    favoriteBases_eq := ?_
    start_eq := ?_
    terminal_eq := ?_ }
  · exact congrArg (fun data ↦ data.1.1) hfavorite
  · exact congrArg (fun data ↦ data.1.2) hfavorite
  · exact congrArg (fun data ↦ data.2.1) hfavorite
  · exact congrArg (fun data ↦ data.2.2) hfavorite

/-- Stopped-acceptance specialization: the deterministic reconstructed word
itself supplies the threshold creation needed to read every trace field at
its terminal length. -/
theorem fixedFavoriteTilingTraceDataAt_of_acceptedWord
    {i : ℕ} (t : DominoTiling) (m k cutoff : ℕ)
    (r : TilingRetainedWord t (0, 0) i) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail)
    (z : TilingExternalWordCode t × TilingCreationFavoriteData)
    (hpiece :
      let v := tilingInsertionPrefixList t (0, 0) r q tail.1
      trajectory (extendPrefix (directionVectorOfList v)) ∈
        favoriteTilingCreationPiece t m k (some z))
    (haccepted : TilingStoppingAccepted
      (truncatedLevelTime m k cutoff) t (0, 0) r q tail.1)
    (hlt :
      (tilingInsertionPrefixList t (0, 0) r q tail.1).length < cutoff) :
    let v := tilingInsertionPrefixList t (0, 0) r q tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    FixedFavoriteTilingTraceDataAt t v.length s z := by
  let v := tilingInsertionPrefixList t (0, 0) r q tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  have hcreation : ThresholdCreation s m k v.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m k cutoff t (0, 0) r q tail hlt).mp haccepted
  exact fixedFavoriteTilingTraceDataAt_of_mem_piece_of_creation
    t m k v.length z hpiece hcreation

/-- In particular, the distinguished domino bases used by the terminal
factorization are exactly the bases stored in the trace code. -/
theorem favoriteTilingBases_eq_code_of_acceptedWord
    {i : ℕ} (t : DominoTiling) (m k cutoff : ℕ)
    (r : TilingRetainedWord t (0, 0) i) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail)
    (z : TilingExternalWordCode t × TilingCreationFavoriteData)
    (hpiece :
      let v := tilingInsertionPrefixList t (0, 0) r q tail.1
      trajectory (extendPrefix (directionVectorOfList v)) ∈
        favoriteTilingCreationPiece t m k (some z))
    (haccepted : TilingStoppingAccepted
      (truncatedLevelTime m k cutoff) t (0, 0) r q tail.1)
    (hlt :
      (tilingInsertionPrefixList t (0, 0) r q tail.1).length < cutoff) :
    let v := tilingInsertionPrefixList t (0, 0) r q tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    favoriteTilingBases t s v.length = z.2.1.2 := by
  exact (fixedFavoriteTilingTraceDataAt_of_acceptedWord
    t m k cutoff r q tail z hpiece haccepted hlt).favoriteBases_eq

end

end Erdos1165.TilingTraceDataFixing
