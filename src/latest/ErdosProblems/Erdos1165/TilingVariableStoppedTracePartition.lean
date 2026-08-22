/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingSpatialInsertionFiber
import ErdosProblems.Erdos1165.CappedCoordinateMassCertificate
import ErdosProblems.Erdos1165.VariableStoppedTracePartition

/-!
# Variable stopped-trace partitions for every HLOZ domino tiling

The index below contains the statefully retained block word, the possible
one-direction terminal boundary, the exact favorite sites and their tiling
bases, the spatial start, and the terminal creation site.  It contains neither
the physical creation time nor the total number of removed excursions.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.TilingVariableStoppedTracePartition

open HLOZPathEvents HLOZStoppedProductRefinement HLOZStoppedSpatialScreening
open HLOZTraceCappedProductScreening CappedCoordinateMassCertificate
open VariableStoppedTracePartition VariableStoppedFiber
open TilingLazyDecomposition TilingSpatialInsertionFiber
open LazyDecomposition PathInsertion SpatialInsertionFiber StoppedInsertion

noncomputable section

local instance : MeasurableSpace (List Block × BoundaryTail) := ⊤
local instance : MeasurableSingletonClass (List Block × BoundaryTail) :=
  ⟨fun _ ↦ trivial⟩

abbrev DominoTiling := Tilings.Tiling

/-- The canonical external word and terminal incomplete direction.  Invalid
retained lists merely index empty insertion fibres; canonical path codes are
always statefully valid. -/
abbrev TilingExternalWordCode (_t : DominoTiling) := List Block × BoundaryTail

/-- Exact spatial data frozen at the variable creation time. -/
abbrev TilingCreationFavoriteData :=
  (Finset Point × Finset Point) × (Point × Point)

/-- The fine countable code consumed by the stage partition. -/
abbrev FavoriteTilingTraceCode (t : DominoTiling) :=
  Option (TilingExternalWordCode t × TilingCreationFavoriteData)

/-- Canonical stateful external code at deterministic time `n`. -/
def fixedTilingExternalWordCode (t : DominoTiling) (n : ℕ)
    (s : WalkPath) : TilingExternalWordCode t :=
  let omega := stepsOfWalk s
  (deleteTilingBlocks t (0, 0) (prefixBlockWord n omega),
    ⟨prefixDirectionTail n omega,
      unpairedDirectionTail_length_le_one (incrementPrefixList n omega)⟩)

theorem measurable_fixedTilingExternalWordCode (t : DominoTiling) (n : ℕ) :
    Measurable (fixedTilingExternalWordCode t n) := by
  let F : (Fin n → Direction) → TilingExternalWordCode t := fun u ↦
    (deleteTilingBlocks t (0, 0)
        (pairDirectionList (List.ofFn u)),
      ⟨unpairedDirectionTail (List.ofFn u),
        unpairedDirectionTail_length_le_one (List.ofFn u)⟩)
  have hF : Measurable F := measurable_of_countable _
  have hprefix : Measurable fun s : WalkPath ↦ stepPrefix n (stepsOfWalk s) :=
    (measurable_stepPrefix n).comp measurable_stepsOfWalk
  convert hF.comp hprefix using 1
  funext s
  rfl

/-- Exact favorite data at deterministic time. -/
def fixedTilingCreationFavoriteData (t : DominoTiling) (n : ℕ)
    (s : WalkPath) : TilingCreationFavoriteData :=
  ((favoriteSites s n, (favoriteSites s n).image (tilingBase t)),
    ((0, 0), s n))

theorem measurable_fixedTilingCreationFavoriteData (t : DominoTiling) (n : ℕ) :
    Measurable (fixedTilingCreationFavoriteData t n) := by
  exact ((measurable_favoriteSites n).prodMk
    ((measurable_of_countable
      (fun D : Finset Point ↦ D.image (tilingBase t))).comp
        (measurable_favoriteSites n))).prodMk
      (measurable_const.prodMk (measurable_pi_apply n))

/-- External code at the genuine variable rank-`k` creation time. -/
def tilingCreationExternalCode (t : DominoTiling) (m k : ℕ)
    (s : WalkPath) : TilingExternalWordCode t :=
  fixedTilingExternalWordCode t (creationTimeNat m k s) s

theorem measurable_tilingCreationExternalCode (t : DominoTiling) (m k : ℕ) :
    Measurable (tilingCreationExternalCode t m k) := by
  exact measurable_natIndexed (creationTimeNat m k)
    (measurable_creationTimeNat m k) (fixedTilingExternalWordCode t)
    (measurable_fixedTilingExternalWordCode t)

/-- Favorite data at the same genuine variable creation time. -/
def tilingCreationFavoriteData (t : DominoTiling) (m k : ℕ)
    (s : WalkPath) : TilingCreationFavoriteData :=
  fixedTilingCreationFavoriteData t (creationTimeNat m k s) s

theorem measurable_tilingCreationFavoriteData (t : DominoTiling) (m k : ℕ) :
    Measurable (tilingCreationFavoriteData t m k) := by
  exact measurable_natIndexed (creationTimeNat m k)
    (measurable_creationTimeNat m k) (fixedTilingCreationFavoriteData t)
    (measurable_fixedTilingCreationFavoriteData t)

/-- Literal WalkPath piece.  The `none` branch is the null off-support part;
the `some` branch fixes the stateful external and favorite data. -/
def favoriteTilingCreationPiece (t : DominoTiling) (m k : ℕ) :
    FavoriteTilingTraceCode t → Set WalkPath
  | none => thresholdReachStage m k \ validStepWalk
  | some z =>
      thresholdReachStage m k ∩ validStepWalk ∩
        {s | tilingCreationExternalCode t m k s = z.1} ∩
        {s | tilingCreationFavoriteData t m k s = z.2}

theorem measurableSet_favoriteTilingCreationPiece (t : DominoTiling)
    (m k : ℕ) (z : FavoriteTilingTraceCode t) :
    MeasurableSet (favoriteTilingCreationPiece t m k z) := by
  cases z with
  | none =>
      exact (measurableSet_thresholdReachStage m k).diff measurableSet_validStepWalk
  | some z =>
      exact (((measurableSet_thresholdReachStage m k).inter measurableSet_validStepWalk).inter
        (measurableSet_eq_fun (measurable_tilingCreationExternalCode t m k)
          measurable_const)).inter
        (measurableSet_eq_fun (measurable_tilingCreationFavoriteData t m k)
          measurable_const)

theorem disjoint_favoriteTilingCreationPiece_of_ne (t : DominoTiling)
    (m k : ℕ) {z w : FavoriteTilingTraceCode t} (hzw : z ≠ w) :
    Disjoint (favoriteTilingCreationPiece t m k z)
      (favoriteTilingCreationPiece t m k w) := by
  classical
  rw [Set.disjoint_left]
  intro s hz hw
  cases z with
  | none =>
      cases w with
      | none => exact hzw rfl
      | some w => exact hz.2 hw.1.1.2
  | some z =>
      cases w with
      | none => exact hw.2 hz.1.1.2
      | some w =>
          apply hzw
          congr 1
          apply Prod.ext
          · exact hz.1.2.symm.trans hw.1.2
          · exact hz.2.symm.trans hw.2

theorem iUnion_favoriteTilingCreationPiece (t : DominoTiling) (m k : ℕ) :
    (⋃ z : FavoriteTilingTraceCode t, favoriteTilingCreationPiece t m k z) =
      thresholdReachStage m k := by
  classical
  ext s
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨z, hz⟩
    cases z with
    | none => exact hz.1
    | some z => exact hz.1.1.1
  · intro hs
    by_cases hvalid : s ∈ validStepWalk
    · refine ⟨some (tilingCreationExternalCode t m k s,
          tilingCreationFavoriteData t m k s), ?_⟩
      exact ⟨⟨⟨hs, hvalid⟩, rfl⟩, rfl⟩
    · exact ⟨none, hs, hvalid⟩

theorem simpleRandomWalk_favoriteTilingCreationPiece_none
    (t : DominoTiling) (m k : ℕ) :
    simpleRandomWalk (favoriteTilingCreationPiece t m k none) = 0 := by
  change simpleRandomWalk (walkCreationPiece (o := .even) m k none) = 0
  exact simpleRandomWalk_walkCreationPiece_none (o := .even) m k

/-! ## Restriction to the three transition stages -/

def favoriteTilingStagePiece (t : DominoTiling) (m k : ℕ)
    (stage : Set WalkPath) (z : FavoriteTilingTraceCode t) : Set WalkPath :=
  favoriteTilingCreationPiece t m k z ∩ stage

theorem measurableSet_favoriteTilingStagePiece (t : DominoTiling) (m k : ℕ)
    {stage : Set WalkPath} (hstage : MeasurableSet stage)
    (z : FavoriteTilingTraceCode t) :
    MeasurableSet (favoriteTilingStagePiece t m k stage z) :=
  (measurableSet_favoriteTilingCreationPiece t m k z).inter hstage

theorem disjoint_favoriteTilingStagePiece_of_ne (t : DominoTiling) (m k : ℕ)
    (stage : Set WalkPath) {z w : FavoriteTilingTraceCode t} (hzw : z ≠ w) :
    Disjoint (favoriteTilingStagePiece t m k stage z)
      (favoriteTilingStagePiece t m k stage w) :=
  (disjoint_favoriteTilingCreationPiece_of_ne t m k hzw).mono
    inter_subset_left inter_subset_left

theorem iUnion_favoriteTilingStagePiece (t : DominoTiling) (m k : ℕ)
    {stage : Set WalkPath} (hstage : stage ⊆ thresholdReachStage m k) :
    (⋃ z : FavoriteTilingTraceCode t, favoriteTilingStagePiece t m k stage z) =
      stage := by
  ext s
  constructor
  · rintro hs
    rcases Set.mem_iUnion.mp hs with ⟨z, _hz, hmem⟩
    exact hmem
  · intro hs
    have hreach := hstage hs
    rw [← iUnion_favoriteTilingCreationPiece t m k] at hreach
    rcases Set.mem_iUnion.mp hreach with ⟨z, hz⟩
    exact Set.mem_iUnion.mpr ⟨z, hz, hs⟩

/-- Populate every structural field of the coordinate-system-neutral product
screen from the genuine all-six variable trace partition. -/
def someTraceCappedProductScreeningOfFavoriteTilingStage
    (t : DominoTiling) (m k : ℕ) (stage next : Set WalkPath)
    (cost : ℝ≥0∞) (hstageMeasurable : MeasurableSet stage)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hnext : next ⊆ stage)
    (spec : CoordinateMassSpec
      (favoriteTilingStagePiece t m k stage) next cost) :
    SomeTraceCappedProductScreening stage next cost where
  Index := FavoriteTilingTraceCode t
  countableIndex := inferInstance
  screening := {
    piece := favoriteTilingStagePiece t m k stage
    measurable_piece := measurableSet_favoriteTilingStagePiece t m k
      hstageMeasurable
    disjoint_piece := fun _z _w hzw ↦
      disjoint_favoriteTilingStagePiece_of_ne t m k stage hzw
    union_piece := iUnion_favoriteTilingStagePiece t m k hstage
    next_subset_stage := hnext
    certificate := cappedProductScreenCertificateOfCoordinateMassSpec spec }

end

end Erdos1165.TilingVariableStoppedTracePartition
