/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.TilingTypedFavoriteFactorization
import ErdosProblems.Erdos1165.HLOZTilingGapRandomClockScreen
import ErdosProblems.Erdos1165.TilingPrefixedStoppedProductDisintegration
import ErdosProblems.Erdos1165.WalkOneStepShift

/-!
# Typed stopped-insertion semantics of phased tiling lazy overflow

This file identifies the literal lazy-overflow predicate on reconstructed
typed insertion prefixes.  The even phase is represented by the current
typed word.  The shifted phase is deliberately stated on the one-step
recentered prefix: deleting time zero changes the two-step block pairing and
therefore cannot reuse the same retained word.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZTypedTilingLazyOverflowScreen

open HLOZTilingGapRandomClockScreen TilingCappedMarginalization
open LazyDecomposition TilingInsertedLocalTime TilingLazyDecomposition
open PreStoppingFiber SpatialInsertionFiber StoppedInsertion ShiftedPrefixBridge
open TilingSpatialInsertionFiber TilingStoppedAcceptanceFactorization
open TilingTypedFavoriteFactorization TilingTypedFavoriteTrace
open TilingPrefixedStoppedProductDisintegration
open VariableStoppedFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

@[simp] lemma phasedInput_even (p : List Point) :
    phasedInput .even p = p := by
  cases p <;> rfl

/-- In the even phase, boundary plus tiling-lazy local time of a reconstructed
insertion prefix is exactly the coordinate insertion local time. -/
theorem phasedBoundary_add_lazy_even_tilingInsertionPrefix
    {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (terminal : Option Point) (y : Point) :
    phasedBoundaryLocalTime .even
          (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) y +
        phasedLazyLocalTime t .even
          (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) y =
      tilingInsertionLazyLocalTime t x r q y := by
  simp only [phasedBoundaryLocalTime, zero_add, phasedLazyLocalTime,
    phasedInput_even]
  rw [tilingLazyPoints_insertedPrefix]
  exact tilingLazyLocalTime_insertedPath x r q y

/-- Every point with positive insertion-lazy local time belongs to a
represented tiling domino. -/
theorem exists_domino_of_tilingInsertionLazyLocalTime_pos
    {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (y : Point) (hy : 0 < tilingInsertionLazyLocalTime t x r q y) :
    ∃ b : TilingExternalDomino t x r, tilingBase t y = b.1 := by
  by_contra hnone
  have hzero : tilingInsertionLazyLocalTime t x r q y = 0 := by
    unfold tilingInsertionLazyLocalTime
    apply Finset.sum_eq_zero
    intro k _hk
    have hbase : tilingBase t (rawExternalBase x r.1 k) ≠ tilingBase t y := by
      intro heq
      apply hnone
      exact ⟨tilingCoordinateDomino t x r k, heq.symm⟩
    rw [tilingEndpointIndicators]
    simp [hbase]
  omega

/-- The even phased lazy overflow of a reconstructed insertion prefix is
exactly the event that one represented domino total exceeds the cap. -/
theorem tilingLazyOverflow_even_tilingInsertionPrefix_iff
    {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (terminal : Option Point) (cap : ℕ) :
    (∃ y, cap <
        phasedBoundaryLocalTime .even
            (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) y +
          phasedLazyLocalTime t .even
            (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) y) ↔
      ∃ b : TilingExternalDomino t x r,
        cap < tilingDominoTotal t x r q b := by
  constructor
  · rintro ⟨y, hy⟩
    rw [phasedBoundary_add_lazy_even_tilingInsertionPrefix] at hy
    obtain ⟨b, hb⟩ := exists_domino_of_tilingInsertionLazyLocalTime_pos
      t x r q y (by omega)
    refine ⟨b, ?_⟩
    rw [tilingInsertionLazyLocalTime_at_dominoPoint t x r q b y hb] at hy
    exact hy
  · rintro ⟨b, hb⟩
    refine ⟨b.1, ?_⟩
    rw [phasedBoundary_add_lazy_even_tilingInsertionPrefix,
      tilingInsertionLazyLocalTime_at_dominoPoint t x r q b b.1
        (tilingExternalDomino_is_base t x r b)]
    exact hb

/-! ## The exact distinguished/away split

The stopped geometric product law is only a law for coordinates away from
the distinguished favorite dominoes.  Consequently the literal lazy event
must first be split into its distinguished and away parts; replacing the
whole event by an away screen would silently discard the first part. -/

/-- Overflow carried by a represented distinguished domino. -/
def distinguishedTilingDominoOverflow {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) (lazyCap : ℕ) : Prop :=
  ∃ b : TilingExternalDomino t x r,
    b.1 ∈ D ∧ lazyCap < tilingDominoTotal t x r q b

/-- Overflow carried by a represented domino away from the distinguished
favorite set. -/
def awayTilingDominoOverflow {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) (lazyCap : ℕ) : Prop :=
  ∃ b : TilingAwayDomino t x r D,
    lazyCap < tilingDominoTotal t x r q b.1

/-- Literal even-phase lazy overflow is the disjoint-by-membership union of
the distinguished overflow and the away overflow.  This theorem has no
`hdistinguished` premise and therefore records exactly what the finite away
product screen does, and does not, cover. -/
theorem tilingLazyOverflow_even_tilingInsertionPrefix_iff_distinguished_or_away
    {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (terminal : Option Point) (D : Finset Point) (lazyCap : ℕ) :
    (∃ y, lazyCap <
        phasedBoundaryLocalTime .even
            (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) y +
          phasedLazyLocalTime t .even
            (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) y) ↔
      distinguishedTilingDominoOverflow t x r D q lazyCap ∨
        awayTilingDominoOverflow t x r D q lazyCap := by
  rw [tilingLazyOverflow_even_tilingInsertionPrefix_iff]
  constructor
  · rintro ⟨b, hb⟩
    by_cases hD : b.1 ∈ D
    · exact Or.inl ⟨b, hD, hb⟩
    · exact Or.inr ⟨⟨b, hD⟩, hb⟩
  · rintro (⟨b, _hD, hb⟩ | ⟨b, hb⟩)
    · exact ⟨b, hb⟩
    · exact ⟨b.1, hb⟩

/-- The distinguished bound is not a consequence of a retained word and a
distinguished set alone.  Whenever the set contains one represented domino,
there is an insertion assignment overflowing that domino.  Thus a literal
all-coordinate lazy screen must obtain the distinguished bound from an
additional stage restriction; it cannot be manufactured by away-coordinate
factorization. -/
theorem exists_distinguishedTilingDominoOverflow_assignment
    {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (k : Fin (i + 1))
    (hk : (tilingCoordinateDomino t x r k).1 ∈ D) (lazyCap : ℕ) :
    ∃ q : Fin (i + 1) → ℕ,
      distinguishedTilingDominoOverflow t x r D q lazyCap := by
  let q : Fin (i + 1) → ℕ := fun _ ↦ lazyCap + 1
  let b := tilingCoordinateDomino t x r k
  have hcoord :
      (⟨k, rfl⟩ : TilingCoordinatesAt t x r b) ∈
        (Finset.univ : Finset (TilingCoordinatesAt t x r b)) :=
    Finset.mem_univ _
  have hle : q k ≤ tilingDominoTotal t x r q b := by
    unfold tilingDominoTotal
    have hsingle :
        q (⟨k, rfl⟩ : TilingCoordinatesAt t x r b).1 ≤
          ∑ j : TilingCoordinatesAt t x r b, q j.1 := by
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j : TilingCoordinatesAt t x r b ↦ q j.1)
        (fun j _hj ↦ Nat.zero_le (q j.1)) hcoord
    exact hsingle
  refine ⟨q, b, hk, ?_⟩
  exact (by dsimp only [q]; omega : lazyCap < q k).trans_le hle

/-- Path-level specialization to the canonical typed insertion walk and its
actual stopped-prefix length. -/
theorem typedInsertionWalk_mem_tilingLazyOverflowAt_even_iff
    {t : DominoTiling} (z : TypedFavoriteTilingTraceCode t)
    {coordinateCap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) coordinateCap)
    (lazyCap : ℕ) :
    let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
    TilingLazyOverflowAt t .even v.length lazyCap (typedInsertionWalk z q) ↔
      ∃ b : TilingExternalDomino t (0, 0) (typedRetained z),
        lazyCap < tilingDominoTotal t (0, 0) (typedRetained z)
          (fun j ↦ (q j : ℕ)) b := by
  let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
  have hreconstruct := finitePathList_tilingInsertionPrefix t
    (typedRetained z) (fun j ↦ (q j : ℕ)) (typedBoundaryTail z)
  change (∃ y, lazyCap <
      phasedBoundaryLocalTime .even
          (finitePathList (pathPrefix (typedInsertionWalk z q) v.length)) y +
        phasedLazyLocalTime t .even
          (finitePathList (pathPrefix (typedInsertionWalk z q) v.length)) y) ↔ _
  change finitePathList (pathPrefix (typedInsertionWalk z q) v.length) = _
    at hreconstruct
  rw [hreconstruct]
  exact tilingLazyOverflow_even_tilingInsertionPrefix_iff t (0, 0)
    (typedRetained z) (fun j ↦ (q j : ℕ))
    (tilingInsertionTerminal t (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z)) lazyCap

/-! ## The literal finite away-total acceptor -/

/-- Boolean acceptor saying that at least one reconstructed away-domino
total exceeds the lazy cap.  It is cap-independent; the auxiliary coordinate
cap only changes which assignments are available in the stopped cylinder. -/
def lazyOverflowAwayTotalsAccepts {Domino : Type*} [Fintype Domino]
    {upper : Domino → ℕ} (lazyCap : ℕ)
    (ell : FiniteDominoProductLaw.TruncatedTotals upper) : Bool :=
  decide (∃ b, lazyCap < ell b)

@[simp] theorem lazyOverflowAwayTotalsAccepts_eq_true_iff
    {Domino : Type*} [Fintype Domino]
    {upper : Domino → ℕ} (lazyCap : ℕ)
    (ell : FiniteDominoProductLaw.TruncatedTotals upper) :
    lazyOverflowAwayTotalsAccepts lazyCap ell = true ↔
      ∃ b, lazyCap < ell b := by
  simp [lazyOverflowAwayTotalsAccepts]

/-- On an assignment lying inside the displayed strict truncation, the
explicit finite screen is exactly a lazy overflow of one actual away-domino
total.  No probability or factorization premise occurs here. -/
theorem tilingAwayTotalsScreen_lazyOverflowAccepts_iff
    {i coordinateCap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (q : TilingCappedCoordinates i coordinateCap)
    (hsupport : ∀ b, tilingDominoTotal t x r
      (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (lazyCap : ℕ) :
    TilingAwayTotalsScreen t x r D upper
        (fun ell ↦ lazyOverflowAwayTotalsAccepts lazyCap ell = true)
        (splitTilingCoordinatesEquiv t x r D q).2 ↔
      ∃ b : TilingAwayDomino t x r D,
        lazyCap < tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 := by
  constructor
  · rintro ⟨ell, hell, htot⟩
    obtain ⟨b, hb⟩ :=
      (lazyOverflowAwayTotalsAccepts_eq_true_iff lazyCap ell).mp hell
    refine ⟨b, ?_⟩
    rw [← tilingAwayTotal_split_eq_dominoTotal t x r D q b,
      htot b]
    exact hb
  · rintro ⟨b, hb⟩
    let ell : FiniteDominoProductLaw.TruncatedTotals upper :=
      fun b' ↦ ⟨tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b'.1,
        hsupport b'⟩
    refine ⟨ell, ?_, ?_⟩
    · apply (lazyOverflowAwayTotalsAccepts_eq_true_iff lazyCap ell).2
      exact ⟨b, hb⟩
    · intro b'
      exact tilingAwayTotal_split_eq_dominoTotal t x r D q b'

/-- The same literal Boolean screen with a deterministic boundary correction
attached to each represented domino.  This is the form used by the shifted
physical-prefix fibre: the first physical vertex contributes one visit to its
domino before the paired suffix starts. -/
def lazyOverflowAwayTotalsAcceptsWithBoundary
    {Domino : Type*} [Fintype Domino] {upper : Domino → ℕ}
    (extra : Domino → ℕ) (lazyCap : ℕ)
    (ell : FiniteDominoProductLaw.TruncatedTotals upper) : Bool :=
  decide (∃ b, lazyCap < ell b + extra b)

@[simp] theorem lazyOverflowAwayTotalsAcceptsWithBoundary_eq_true_iff
    {Domino : Type*} [Fintype Domino] {upper : Domino → ℕ}
    (extra : Domino → ℕ) (lazyCap : ℕ)
    (ell : FiniteDominoProductLaw.TruncatedTotals upper) :
    lazyOverflowAwayTotalsAcceptsWithBoundary extra lazyCap ell = true ↔
      ∃ b, lazyCap < ell b + extra b := by
  simp [lazyOverflowAwayTotalsAcceptsWithBoundary]

/-- Exact away-total semantics of the shifted boundary-corrected acceptor.
The correction is deterministic on the retained trace, so it does not alter
the coordinate-product factorization. -/
theorem tilingAwayTotalsScreen_lazyOverflowAcceptsWithBoundary_iff
    {i coordinateCap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (q : TilingCappedCoordinates i coordinateCap)
    (hsupport : ∀ b, tilingDominoTotal t x r
      (fun k ↦ (q k : ℕ)) b.1 < upper b)
    (extra : TilingAwayDomino t x r D → ℕ) (lazyCap : ℕ) :
    TilingAwayTotalsScreen t x r D upper
        (fun ell ↦
          lazyOverflowAwayTotalsAcceptsWithBoundary extra lazyCap ell = true)
        (splitTilingCoordinatesEquiv t x r D q).2 ↔
      ∃ b : TilingAwayDomino t x r D,
        lazyCap < tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b.1 +
          extra b := by
  constructor
  · rintro ⟨ell, hell, htot⟩
    obtain ⟨b, hb⟩ :=
      (lazyOverflowAwayTotalsAcceptsWithBoundary_eq_true_iff
        extra lazyCap ell).mp hell
    refine ⟨b, ?_⟩
    rw [← tilingAwayTotal_split_eq_dominoTotal t x r D q b,
      htot b]
    exact hb
  · rintro ⟨b, hb⟩
    let ell : FiniteDominoProductLaw.TruncatedTotals upper :=
      fun b' ↦ ⟨tilingDominoTotal t x r (fun k ↦ (q k : ℕ)) b'.1,
        hsupport b'⟩
    refine ⟨ell, ?_, ?_⟩
    · apply (lazyOverflowAwayTotalsAcceptsWithBoundary_eq_true_iff
        extra lazyCap ell).2
      exact ⟨b, hb⟩
    · intro b'
      exact tilingAwayTotal_split_eq_dominoTotal t x r D q b'

/-- Once the distinguished represented dominoes are known not to overflow,
the literal even-phase event is precisely the away-total acceptor.  The
distinguished bound is deterministic stopped-stage information; all random
coordinates remaining in the screen are away coordinates. -/
theorem tilingLazyOverflow_even_tilingInsertionPrefix_iff_away
    {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (terminal : Option Point) (D : Finset Point) (lazyCap : ℕ)
    (hdistinguished : ∀ b : TilingExternalDomino t x r,
      b.1 ∈ D → tilingDominoTotal t x r q b ≤ lazyCap) :
    (∃ y, lazyCap <
        phasedBoundaryLocalTime .even
            (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) y +
          phasedLazyLocalTime t .even
            (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) y) ↔
      ∃ b : TilingAwayDomino t x r D,
        lazyCap < tilingDominoTotal t x r q b := by
  rw [tilingLazyOverflow_even_tilingInsertionPrefix_iff]
  constructor
  · rintro ⟨b, hb⟩
    have hbD : b.1 ∉ D := by
      intro hmem
      exact (Nat.not_lt_of_ge (hdistinguished b hmem)) hb
    exact ⟨⟨b, hbD⟩, hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b.1, hb⟩

/-! ## Shifted semantics for a genuinely prefixed fibre -/

/-- The physical walk reconstructed by the new prefixed stopped-fibre
primitive.  Its prefix is not a translated suffix: the original initial word
is literally prepended to the insertion word. -/
def prefixedTilingInsertionWalk (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (tail : List Direction) : WalkPath :=
  trajectory (extendPrefix (directionVectorOfList
    (prefixedTilingInsertionPrefixList initial t x r q tail)))

private theorem get_pairDirectionList (suffix : List Direction) (n : ℕ)
    (hn : n < (pairDirectionList suffix).length) :
    (pairDirectionList suffix).get ⟨n, hn⟩ =
      (suffix.get ⟨2 * n, by
          rw [pairDirectionList_length] at hn
          omega⟩,
        suffix.get ⟨2 * n + 1, by
          rw [pairDirectionList_length] at hn
          omega⟩) := by
  induction suffix using List.twoStepInduction generalizing n with
  | nil => simp [pairDirectionList] at hn
  | singleton a => simp [pairDirectionList] at hn
  | cons_cons a b rest ih _ =>
      cases n with
      | zero => rfl
      | succ n =>
          simpa [pairDirectionList, Nat.mul_succ, Nat.add_assoc] using
            ih n (by simpa [pairDirectionList] using hn)

private theorem completeSegmentBlocks_extendPrefix_append
    (pre suffix : List Direction) :
    completeSegmentBlocks
        (extendPrefix (directionVectorOfList (pre ++ suffix)))
        pre.length suffix.length = pairDirectionList suffix := by
  apply List.ext_get
  · simp [completeSegmentBlocks, pairDirectionList_length]
  · intro n hnleft hnright
    rw [get_pairDirectionList suffix n hnright]
    simp only [completeSegmentBlocks, List.get_ofFn]
    unfold directionVectorOfList extendPrefix
    simp only [List.get_eq_getElem]
    have hfirst : pre.length + 2 * n < (pre ++ suffix).length := by
      simp only [List.length_append]
      rw [pairDirectionList_length] at hnright
      omega
    have hsecond : pre.length + 2 * n + 1 <
        (pre ++ suffix).length := by
      simp only [List.length_append]
      rw [pairDirectionList_length] at hnright
      omega
    have hsuffixFirst : 2 * n < suffix.length := by
      rw [pairDirectionList_length] at hnright
      omega
    have hsuffixSecond : 2 * n + 1 < suffix.length := by
      rw [pairDirectionList_length] at hnright
      omega
    change
      ((if h : pre.length + 2 * n < (pre ++ suffix).length then
          (pre ++ suffix)[pre.length + 2 * n] else 0),
        (if h : pre.length + 2 * n + 1 < (pre ++ suffix).length then
          (pre ++ suffix)[pre.length + 2 * n + 1] else 0)) =
        (suffix[2 * n]'hsuffixFirst, suffix[2 * n + 1]'hsuffixSecond)
    rw [dif_pos hfirst, dif_pos hsecond]
    simp only [List.getElem_append_right (by omega : pre.length ≤
      pre.length + 2 * n), Nat.add_sub_cancel_left]
    rw [List.getElem_append_right (by omega : pre.length ≤
      pre.length + 2 * n + 1)]
    congr 2
    omega

/-- Removing the physical first direction from a singleton-prefixed word
recovers exactly the stateful tiling insertion blocks of its suffix. -/
theorem shiftedCompletePrefixBlocks_prefixedTilingInsertionPrefixList
    (d : Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) (htail : tail.length ≤ 1) :
    let v := prefixedTilingInsertionPrefixList [d] t x r q tail
    shiftedCompletePrefixBlocks
        (extendPrefix (directionVectorOfList v)) v.length =
      tilingInsertGapVector t x r q := by
  let suffix := tilingInsertionPrefixList t x r q tail
  let v := prefixedTilingInsertionPrefixList [d] t x r q tail
  let omega := extendPrefix (directionVectorOfList v)
  dsimp only
  calc
    shiftedCompletePrefixBlocks omega v.length = pairDirectionList suffix := by
      simpa [shiftedCompletePrefixBlocks, omega, v, suffix,
        prefixedTilingInsertionPrefixList] using
          completeSegmentBlocks_extendPrefix_append [d] suffix
    _ = tilingInsertGapVector t x r q :=
      pairDirectionList_flatten_append_shortTail
        (tilingInsertGapVector t x r q) tail htail

/-- After the physical initial point is retained and the shifted phase drops
it, the remaining lazy local time is exactly the insertion lazy local time
of the suffix fibre.  The only extra term is the one time-zero visit. -/
theorem phasedBoundary_add_lazy_shifted_prefixedInsertion
    {i : ℕ} (t : DominoTiling) (origin x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (terminal : Option Point) (y : Point) :
    phasedBoundaryLocalTime .shifted
          (origin :: tilingPrefixPointPath x
            (tilingInsertGapVector t x r q) terminal) y +
        phasedLazyLocalTime t .shifted
          (origin :: tilingPrefixPointPath x
            (tilingInsertGapVector t x r q) terminal) y =
      (if origin = y then 1 else 0) +
        tilingInsertionLazyLocalTime t x r q y := by
  simp only [phasedBoundaryLocalTime, phasedLazyLocalTime, phasedInput]
  rw [tilingLazyPoints_insertedPrefix]
  exact congrArg ((if origin = y then 1 else 0) + ·)
    (tilingLazyLocalTime_insertedPath x r q y)

/-- Boundary correction carried by one represented domino in the shifted
physical prefix. -/
def shiftedDominoBoundaryExtra {i : ℕ} (t : DominoTiling)
    (origin x : Point) (r : TilingRetainedWord t x i)
    (b : TilingExternalDomino t x r) : ℕ :=
  if tilingBase t origin = b.1 then 1 else 0

/-- The shifted phased overflow of the correctly prefixed insertion word is
one represented domino total, plus its deterministic time-zero correction.
Positivity of the lazy cap rules out a boundary-only overflow outside the
represented suffix. -/
theorem tilingLazyOverflow_shifted_prefixedInsertion_iff
    {i : ℕ} (t : DominoTiling) (origin x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (terminal : Option Point) (lazyCap : ℕ) (hcap : 0 < lazyCap) :
    (∃ y, lazyCap <
        phasedBoundaryLocalTime .shifted
            (origin :: tilingPrefixPointPath x
              (tilingInsertGapVector t x r q) terminal) y +
          phasedLazyLocalTime t .shifted
            (origin :: tilingPrefixPointPath x
              (tilingInsertGapVector t x r q) terminal) y) ↔
      ∃ b : TilingExternalDomino t x r,
        lazyCap < tilingDominoTotal t x r q b +
          shiftedDominoBoundaryExtra t origin x r b := by
  constructor
  · rintro ⟨y, hy⟩
    rw [phasedBoundary_add_lazy_shifted_prefixedInsertion] at hy
    have hlazy : 0 < tilingInsertionLazyLocalTime t x r q y := by
      by_contra hnot
      have hzero : tilingInsertionLazyLocalTime t x r q y = 0 :=
        Nat.eq_zero_of_not_pos hnot
      rw [hzero, add_zero] at hy
      split at hy <;> omega
    obtain ⟨b, hb⟩ := exists_domino_of_tilingInsertionLazyLocalTime_pos
      t x r q y hlazy
    refine ⟨b, hy.trans_le ?_⟩
    rw [tilingInsertionLazyLocalTime_at_dominoPoint t x r q b y hb]
    by_cases horigin : origin = y
    · subst y
      simp only [↓reduceIte]
      exact (Nat.add_comm _ _).le
    · simp [horigin]
  · rintro ⟨b, hb⟩
    by_cases horigin : tilingBase t origin = b.1
    · refine ⟨origin, ?_⟩
      have hb' : lazyCap < tilingDominoTotal t x r q b + 1 := by
        simpa [shiftedDominoBoundaryExtra, horigin] using hb
      rw [phasedBoundary_add_lazy_shifted_prefixedInsertion,
        tilingInsertionLazyLocalTime_at_dominoPoint t x r q b origin horigin]
      rw [if_pos rfl]
      omega
    · refine ⟨b.1, ?_⟩
      have hb' : lazyCap < tilingDominoTotal t x r q b := by
        simpa [shiftedDominoBoundaryExtra, horigin] using hb
      rw [phasedBoundary_add_lazy_shifted_prefixedInsertion,
        tilingInsertionLazyLocalTime_at_dominoPoint t x r q b b.1
          (tilingExternalDomino_is_base t x r b)]
      have hne : origin ≠ b.1 := by
        intro heq
        apply horigin
        rw [heq, tilingExternalDomino_is_base]
      change lazyCap < (if origin = b.1 then 1 else 0) +
        tilingDominoTotal t x r q b
      rw [if_neg hne, zero_add]
      exact hb'

/-- Distinguished part of the shifted lazy overflow.  The deterministic
boundary correction is attached to the represented domino containing the
physical initial vertex. -/
def distinguishedShiftedTilingDominoOverflow {i : ℕ} (t : DominoTiling)
    (origin x : Point) (r : TilingRetainedWord t x i) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) (lazyCap : ℕ) : Prop :=
  ∃ b : TilingExternalDomino t x r,
    b.1 ∈ D ∧ lazyCap < tilingDominoTotal t x r q b +
      shiftedDominoBoundaryExtra t origin x r b

/-- Away part of the shifted lazy overflow. -/
def awayShiftedTilingDominoOverflow {i : ℕ} (t : DominoTiling)
    (origin x : Point) (r : TilingRetainedWord t x i) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) (lazyCap : ℕ) : Prop :=
  ∃ b : TilingAwayDomino t x r D,
    lazyCap < tilingDominoTotal t x r q b.1 +
      shiftedDominoBoundaryExtra t origin x r b.1

/-- Exact shifted counterpart of the distinguished/away split.  In
particular, the physical initial vertex is not dropped: it appears through
`shiftedDominoBoundaryExtra`. -/
theorem tilingLazyOverflow_shifted_prefixedInsertion_iff_distinguished_or_away
    {i : ℕ} (t : DominoTiling) (origin x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (terminal : Option Point) (D : Finset Point) (lazyCap : ℕ)
    (hcap : 0 < lazyCap) :
    (∃ y, lazyCap <
        phasedBoundaryLocalTime .shifted
            (origin :: tilingPrefixPointPath x
              (tilingInsertGapVector t x r q) terminal) y +
          phasedLazyLocalTime t .shifted
            (origin :: tilingPrefixPointPath x
              (tilingInsertGapVector t x r q) terminal) y) ↔
      distinguishedShiftedTilingDominoOverflow
          t origin x r D q lazyCap ∨
        awayShiftedTilingDominoOverflow t origin x r D q lazyCap := by
  rw [tilingLazyOverflow_shifted_prefixedInsertion_iff
    t origin x r q terminal lazyCap hcap]
  constructor
  · rintro ⟨b, hb⟩
    by_cases hD : b.1 ∈ D
    · exact Or.inl ⟨b, hD, hb⟩
    · exact Or.inr ⟨⟨b, hD⟩, hb⟩
  · rintro (⟨b, _hD, hb⟩ | ⟨b, hb⟩)
    · exact ⟨b, hb⟩
    · exact ⟨b.1, hb⟩

/-- Once the distinguished represented dominoes are known not to overflow,
the shifted physical-prefix event is exactly the away-total Boolean screen
with its deterministic first-vertex correction. -/
theorem tilingLazyOverflow_shifted_prefixedInsertion_iff_away
    {i : ℕ} (t : DominoTiling) (origin x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (terminal : Option Point) (D : Finset Point) (lazyCap : ℕ)
    (hcap : 0 < lazyCap)
    (hdistinguished : ∀ b : TilingExternalDomino t x r,
      b.1 ∈ D →
        tilingDominoTotal t x r q b +
          shiftedDominoBoundaryExtra t origin x r b ≤ lazyCap) :
    (∃ y, lazyCap <
        phasedBoundaryLocalTime .shifted
            (origin :: tilingPrefixPointPath x
              (tilingInsertGapVector t x r q) terminal) y +
          phasedLazyLocalTime t .shifted
            (origin :: tilingPrefixPointPath x
              (tilingInsertGapVector t x r q) terminal) y) ↔
      ∃ b : TilingAwayDomino t x r D,
        lazyCap < tilingDominoTotal t x r q b.1 +
          shiftedDominoBoundaryExtra t origin x r b.1 := by
  rw [tilingLazyOverflow_shifted_prefixedInsertion_iff
    t origin x r q terminal lazyCap hcap]
  constructor
  · rintro ⟨b, hb⟩
    have hbD : b.1 ∉ D := by
      intro hmem
      exact (Nat.not_lt_of_ge (hdistinguished b hmem)) hb
    exact ⟨⟨b, hbD⟩, hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b.1, hb⟩

end

end Erdos1165.HLOZTypedTilingLazyOverflowScreen
