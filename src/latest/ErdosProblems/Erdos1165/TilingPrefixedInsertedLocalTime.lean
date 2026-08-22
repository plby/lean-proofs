/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingPrefixedStoppedProductDisintegration
import ErdosProblems.Erdos1165.TilingInsertedLocalTime

/-!
# Local time for a physically prefixed tiling fibre

The shifted oriented fibres begin with a genuine path prefix from the origin.
The insertion-only boundary local time therefore misses the visits in that
prefix (in particular the time-zero visit at the origin).  We concatenate the
physical prefix point path with the retained suffix after dropping its already
represented starting point.  This counts the joining point exactly once.
-/

open Set

namespace Erdos1165.TilingPrefixedInsertedLocalTime

open LazyDecomposition PathInsertion PreStoppingFiber SpatialInsertionFiber
open StoppedInsertion VariableStoppedTracePartition
open TilingLazyDecomposition
open TilingInsertedLocalTime TilingSpatialInsertionFiber
open TilingPrefixedStoppedProductDisintegration

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Physical point path obtained by adjoining a suffix which starts at `x` to
an initial direction word.  The suffix start is dropped to avoid counting the
joining point twice. -/
def prefixedTilingPrefixPointPath (initial : List Direction) (x : Point)
    (bs : List Block) (terminal : Option Point) : List Point :=
  finitePathList (pathPrefix
      (trajectory (extendPrefix (directionVectorOfList initial)))
      initial.length) ++
    (tilingPrefixPointPath x bs terminal).tail

/-- Fixed external local time in the complete physical prefixed cylinder. -/
def prefixedTilingFixedBoundaryLocalTime (initial : List Direction) {i : ℕ}
    {t : DominoTiling} (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (y : Point) : ℕ :=
  listLocalTime
    (prefixedTilingPrefixPointPath initial x (List.ofFn r.1) terminal) y

/-- Larger fixed endpoint local time on a represented domino, now including
the physical initial prefix. -/
def prefixedTilingFixedBoundaryDominoMax (initial : List Direction) {i : ℕ}
    {t : DominoTiling} (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (b : TilingExternalDomino t x r) : ℕ :=
  max (prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1)
    (prefixedTilingFixedBoundaryLocalTime initial x r terminal
      (tilingPartner t b.1))

private theorem tilingPrefixPointPath_head (x : Point)
    (bs : List Block) (terminal : Option Point) :
    (tilingPrefixPointPath x bs terminal).head? = some x := by
  cases terminal <;> simp [tilingPrefixPointPath, blockPath]

private theorem listLocalTime_tail_add_start (x y : Point) (xs : List Point)
    (hhead : xs.head? = some x) :
    listLocalTime xs.tail y + (if x = y then 1 else 0) =
      listLocalTime xs y := by
  cases xs with
  | nil => simp at hhead
  | cons z zs =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst z
      by_cases hxy : x = y
      · subst y
        simp [listLocalTime]
      · simp [listLocalTime, hxy]

/-- Exact external-plus-lazy local time on the physical prefixed path.  The
initial-prefix correction is present on both sides, while the inserted away
total is unchanged. -/
theorem prefixedTilingInsertedPrefix_localTime_at_dominoPoint
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (terminal : Option Point) (b : TilingExternalDomino t x r) (y : Point)
    (hy : tilingBase t y = b.1) :
    listLocalTime
        (prefixedTilingPrefixPointPath initial x
          (tilingInsertGapVector t x r q) terminal) y =
      prefixedTilingFixedBoundaryLocalTime initial x r terminal y +
        tilingDominoTotal t x r q b := by
  have hins := tilingInsertedPrefix_localTime_at_dominoPoint
    t x r q terminal b y hy
  have hinserted := listLocalTime_tail_add_start x y
    (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal)
    (tilingPrefixPointPath_head x _ terminal)
  have hfixed := listLocalTime_tail_add_start x y
    (tilingPrefixPointPath x (List.ofFn r.1) terminal)
    (tilingPrefixPointPath_head x _ terminal)
  unfold prefixedTilingFixedBoundaryLocalTime
  unfold prefixedTilingPrefixPointPath
  unfold tilingFixedBoundaryLocalTime at hins
  unfold listLocalTime at ⊢ hins hinserted hfixed
  simp only [List.count_append]
  omega

/-- At empty physical prefix and suffix start `0`, the corrected boundary is
the old insertion-only boundary. -/
@[simp] theorem prefixedTilingFixedBoundaryLocalTime_nil_zero {i : ℕ}
    {t : DominoTiling} (r : TilingRetainedWord t 0 i)
    (terminal : Option Point) (y : Point) :
    prefixedTilingFixedBoundaryLocalTime [] 0 r terminal y =
      tilingFixedBoundaryLocalTime 0 r terminal y := by
  unfold prefixedTilingFixedBoundaryLocalTime prefixedTilingPrefixPointPath
  have hhead := tilingPrefixPointPath_head
    (0 : Point) (List.ofFn r.1) terminal
  cases hpath : tilingPrefixPointPath (0 : Point) (List.ofFn r.1) terminal with
  | nil => simp [hpath] at hhead
  | cons z zs =>
      simp only [hpath, List.head?_cons, Option.some.injEq] at hhead
      subst z
      simp [hpath, tilingFixedBoundaryLocalTime, listLocalTime,
        finitePathList, pathPrefix, trajectory, extendPrefix]

end

end Erdos1165.TilingPrefixedInsertedLocalTime
