import ErdosProblems.Erdos1165.TilingCappedMarginalization
import ErdosProblems.Erdos1165.TilingInsertionTerminalInvariant
import ErdosProblems.Erdos1165.TilingTraceDataFixing

/-!
# Favorite trace support for all-six capped insertion coordinates

On a non-null favorite trace fibre, the favorite domino bases are fixed by
the trace code.  If a reconstructed word is accepted at the genuine capped
creation clock and is a level-`m` favorite word, its away insertion totals
therefore lie in exactly the strict coordinatewise truncation used by the
finite product law.  This is the pathwise cap-support half of the stopped
product disintegration; it contains no probability assumption.
-/

namespace Erdos1165.TilingFavoriteTraceSupport

open HLOZPathEvents VariableStoppedTracePartition
open LazyDecomposition
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingInsertedLocalTime TilingStoppedAcceptanceFactorization
open TilingVariableStoppedTracePartition TilingTraceDataFixing
open TilingInsertionTerminalInvariant
open TilingCappedMarginalization
open PathInsertion PreStoppingFiber StoppedInsertion VariableStoppedFiber
open PreStoppingSpatialLaw

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- An accepted reconstructed word in a fixed favorite trace piece has
exactly the strict away-domino support of the capped product law. -/
theorem tilingAwayTotalsScreen_of_acceptedFavoriteTrace
    {i cap : ℕ} (t : DominoTiling) (m k cutoff : ℕ)
    (hm : 0 < m) (hk : 0 < k)
    (r : TilingRetainedWord t (0, 0) i)
    (q : TilingCappedCoordinates i cap) (tail : BoundaryTail)
    (z : TilingExternalWordCode t × TilingCreationFavoriteData)
    (hpiece :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      trajectory (extendPrefix (directionVectorOfList v)) ∈
        favoriteTilingCreationPiece t m k (some z))
    (haccepted : TilingStoppingAccepted
      (truncatedLevelTime m k cutoff) t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1)
    (hlt :
      (tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1).length < cutoff)
    (hfavorite :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      levelFavorite (trajectory (extendPrefix (directionVectorOfList v))) m k) :
    TilingAwayTotalsScreen t (0, 0) r z.2.1.2
      (tilingFavoriteAwayUpper t (0, 0) r
        (tilingInsertionTerminal t r (fun j ↦ (q j : ℕ)) tail) m z.2.1.2)
      (fun _ ↦ True)
      (splitTilingCoordinatesEquiv t (0, 0) r z.2.1.2 q).2 := by
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (q j : ℕ)
  let v := tilingInsertionPrefixList t (0, 0) r qNat tail.1
  let omega := extendPrefix (directionVectorOfList v)
  let s := trajectory omega
  have htime : truncatedLevelTime m k cutoff omega = v.length := by
    exact haccepted
  have hpath : finitePathList (pathPrefix s v.length) =
      tilingPrefixPointPath (0, 0) (tilingInsertGapVector t (0, 0) r qNat)
        (tilingInsertionTerminal t r qNat tail) := by
    exact finitePathList_tilingInsertionPrefix t r qNat tail
  have htrunc : TilingDominoTruncation t (0, 0) r
      (tilingInsertionTerminal t r qNat tail) m
      (favoriteTilingBases t s v.length) qNat := by
    exact tilingDominoTruncation_at_truncatedLevelTime t m k cutoff
      v.length omega hm hk hlt htime hfavorite (0, 0) r qNat
      (tilingInsertionTerminal t r qNat tail) hpath
  have hbases : favoriteTilingBases t s v.length = z.2.1.2 := by
    exact favoriteTilingBases_eq_code_of_acceptedWord
      t m k cutoff r qNat tail z hpiece haccepted hlt
  rw [hbases] at htrunc
  exact (tilingAwayTotalsScreen_true_iff_dominoTruncation
    (cap := cap) t (0, 0) r
    (tilingInsertionTerminal t r qNat tail) m z.2.1.2 q).2 htrunc

/-! ## Reducing both marginal identities to fibre invariance -/

/-- The zero assignment on every away-domino coordinate. -/
def zeroTilingAwayCoordinates {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) : TilingAwayCoordinates (cap := cap) t x r D :=
  fun _ _ ↦ 0

/-- The distinguished-coordinate selector obtained by testing the base
accepted predicate against the canonical zero away assignment. -/
noncomputable def distinguishedAcceptedSelector
    (tau : StepPath → ℕ) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction) (base : TilingCappedCoordinates i cap → Prop)
    (D : Finset Point)
    (d : TilingDistinguishedCoordinates (cap := cap) t x r D) : Prop :=
  let q := (splitTilingCoordinatesEquiv t x r D).symm
    (d, zeroTilingAwayCoordinates (cap := cap) t x r D)
  base q ∧ TilingStoppingAccepted tau t x r (fun j ↦ (q j : ℕ)) tail

/-- Zero away coordinates satisfy every strictly positive total cutoff. -/
theorem zeroTilingAwayCoordinates_mem_trueScreen {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b, 0 < upper b) :
    TilingAwayTotalsScreen t x r D upper (fun _ ↦ True)
      (zeroTilingAwayCoordinates (cap := cap) t x r D) := by
  rw [tilingAwayTotalsScreen_true_iff]
  intro b
  simpa [tilingAwayTotal, zeroTilingAwayCoordinates] using hupper b

/-- If an accepted base predicate is supported on the away truncation and
is invariant after the distinguished coordinates are fixed, then its exact
factorization is automatic.  This is the sole logical identification needed
by the two finite marginal sums. -/
theorem acceptedBase_iff_distinguishedSelector_and_awayScreen
    (tau : StepPath → ℕ) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction) (base : TilingCappedCoordinates i cap → Prop)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (hupper : ∀ b, 0 < upper b)
    (hsupport : ∀ q,
      base q ∧ TilingStoppingAccepted tau t x r
          (fun j ↦ (q j : ℕ)) tail →
        TilingAwayTotalsScreen t x r D upper (fun _ ↦ True)
          (splitTilingCoordinatesEquiv t x r D q).2)
    (hinvariant : ∀ q q',
      (splitTilingCoordinatesEquiv t x r D q).1 =
          (splitTilingCoordinatesEquiv t x r D q').1 →
      TilingAwayTotalsScreen t x r D upper (fun _ ↦ True)
          (splitTilingCoordinatesEquiv t x r D q).2 →
      TilingAwayTotalsScreen t x r D upper (fun _ ↦ True)
          (splitTilingCoordinatesEquiv t x r D q').2 →
      (base q ∧ TilingStoppingAccepted tau t x r
          (fun j ↦ (q j : ℕ)) tail ↔
        base q' ∧ TilingStoppingAccepted tau t x r
          (fun j ↦ (q' j : ℕ)) tail))
    (q : TilingCappedCoordinates i cap) :
    base q ∧ TilingStoppingAccepted tau t x r
        (fun j ↦ (q j : ℕ)) tail ↔
      distinguishedAcceptedSelector tau t x r tail base D
          (splitTilingCoordinatesEquiv t x r D q).1 ∧
        TilingAwayTotalsScreen t x r D upper (fun _ ↦ True)
          (splitTilingCoordinatesEquiv t x r D q).2 := by
  let d := (splitTilingCoordinatesEquiv t x r D q).1
  let a0 := zeroTilingAwayCoordinates (cap := cap) t x r D
  let q0 := (splitTilingCoordinatesEquiv t x r D).symm (d, a0)
  have hq0split : splitTilingCoordinatesEquiv t x r D q0 = (d, a0) :=
    (splitTilingCoordinatesEquiv t x r D).apply_symm_apply (d, a0)
  have hq0screen : TilingAwayTotalsScreen t x r D upper (fun _ ↦ True)
      (splitTilingCoordinatesEquiv t x r D q0).2 := by
    rw [hq0split]
    exact zeroTilingAwayCoordinates_mem_trueScreen t x r D upper hupper
  have hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q0).1 := by
    rw [hq0split]
  change (base q ∧ TilingStoppingAccepted tau t x r
      (fun j ↦ (q j : ℕ)) tail) ↔
    (base q0 ∧ TilingStoppingAccepted tau t x r
      (fun j ↦ (q0 j : ℕ)) tail) ∧
      TilingAwayTotalsScreen t x r D upper (fun _ ↦ True)
        (splitTilingCoordinatesEquiv t x r D q).2
  constructor
  · intro hq
    have hscreen := hsupport q hq
    exact ⟨(hinvariant q q0 hdist hscreen hq0screen).mp hq, hscreen⟩
  · rintro ⟨hq0, hscreen⟩
    exact (hinvariant q q0 hdist hscreen hq0screen).mpr hq0

/-- Add an arbitrary finite screening predicate to a base coordinate
predicate. -/
def screenedByAwayTotals {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (screen : FiniteDominoProductLaw.TruncatedTotals upper → Prop)
    (base : TilingCappedCoordinates i cap → Prop)
    (q : TilingCappedCoordinates i cap) : Prop :=
  base q ∧ TilingAwayTotalsScreen t x r D upper screen
    (splitTilingCoordinatesEquiv t x r D q).2

theorem screenedByAwayTotals_subset_base {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (screen : FiniteDominoProductLaw.TruncatedTotals upper → Prop)
    (base : TilingCappedCoordinates i cap → Prop) (q)
    (h : screenedByAwayTotals t x r D upper screen base q) : base q :=
  h.1

/-- Once the base predicate has the exact true-screen factorization, adding
an away-total screen gives the exact screened factorization required by the
stopped product identity. -/
theorem screenedByAwayTotals_and_accepted_iff
    (tau : StepPath → ℕ) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction) (base : TilingCappedCoordinates i cap → Prop)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (screen : FiniteDominoProductLaw.TruncatedTotals upper → Prop)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    (hbase : ∀ q,
      base q ∧ TilingStoppingAccepted tau t x r
          (fun j ↦ (q j : ℕ)) tail ↔
        selected (splitTilingCoordinatesEquiv t x r D q).1 ∧
          TilingAwayTotalsScreen t x r D upper (fun _ ↦ True)
            (splitTilingCoordinatesEquiv t x r D q).2)
    (q : TilingCappedCoordinates i cap) :
    screenedByAwayTotals t x r D upper screen base q ∧
        TilingStoppingAccepted tau t x r (fun j ↦ (q j : ℕ)) tail ↔
      selected (splitTilingCoordinatesEquiv t x r D q).1 ∧
        TilingAwayTotalsScreen t x r D upper screen
          (splitTilingCoordinatesEquiv t x r D q).2 := by
  constructor
  · rintro ⟨⟨hbaseq, hscreen⟩, haccepted⟩
    exact ⟨(hbase q).mp ⟨hbaseq, haccepted⟩ |>.1, hscreen⟩
  · rintro ⟨hselected, hscreen⟩
    have htrue : TilingAwayTotalsScreen t x r D upper (fun _ ↦ True)
        (splitTilingCoordinatesEquiv t x r D q).2 := by
      rcases hscreen with ⟨ell, hs, hell⟩
      exact ⟨ell, trivial, hell⟩
    have haccepted := (hbase q).mpr ⟨hselected, htrue⟩
    exact ⟨⟨haccepted.1, hscreen⟩, haccepted.2⟩

/-! ## Invariance of the terminal threshold profile -/

/-- After the away endpoints are strictly below `level`, fixing the
distinguished coordinate projection fixes membership in the terminal
`level`-threshold set at every lattice point. -/
theorem tilingPrefixLocalTime_ge_level_iff_of_distinguished_eq
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (level : ℕ) (D : Finset Point)
    (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1)
    (htrunc : TilingDominoTruncation t x r terminal level D
      (fun j ↦ (q j : ℕ)))
    (htrunc' : TilingDominoTruncation t x r terminal level D
      (fun j ↦ (q' j : ℕ)))
    (y : Point) :
    level ≤ listLocalTime
        (tilingPrefixPointPath x
          (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal) y ↔
      level ≤ listLocalTime
        (tilingPrefixPointPath x
          (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal) y := by
  by_cases hy : tilingBase t y ∈ tilingExternalDominoBases t x r
  · let b : TilingExternalDomino t x r := ⟨tilingBase t y, hy⟩
    by_cases hb : b.1 ∈ D
    · have htotal := tilingDominoTotal_eq_of_distinguished_eq
        t x r D q q' hdist b hb
      rw [tilingInsertedPrefix_localTime_at_dominoPoint
          t x r (fun j ↦ (q j : ℕ)) terminal b y rfl,
        tilingInsertedPrefix_localTime_at_dominoPoint
          t x r (fun j ↦ (q' j : ℕ)) terminal b y rfl,
        htotal]
    · have hbelow :=
        (tilingActualEndpointsBelow_iff_dominoTruncation
          t x r terminal level D (fun j ↦ (q j : ℕ))).2 htrunc b hb
      have hbelow' :=
        (tilingActualEndpointsBelow_iff_dominoTruncation
          t x r terminal level D (fun j ↦ (q' j : ℕ))).2 htrunc' b hb
      rcases point_eq_tilingBase_or_partner_base t y with hybase | hypartner
      · rw [hybase]
        exact iff_of_false (not_le_of_gt hbelow.1) (not_le_of_gt hbelow'.1)
      · rw [hypartner]
        exact iff_of_false (not_le_of_gt hbelow.2) (not_le_of_gt hbelow'.2)
  · rw [tilingInsertedPrefix_localTime_of_base_not_mem
        t x r (fun j ↦ (q j : ℕ)) terminal y hy,
      tilingInsertedPrefix_localTime_of_base_not_mem
        t x r (fun j ↦ (q' j : ℕ)) terminal y hy]

/-- At a distinguished domino endpoint the complete terminal local time,
not just its threshold indicator, is fixed by the distinguished projection. -/
theorem tilingPrefixLocalTime_eq_of_distinguished_eq_of_base_mem
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1)
    (y : Point) (hy : tilingBase t y ∈ D)
    (hyrepresented : tilingBase t y ∈ tilingExternalDominoBases t x r) :
    listLocalTime
        (tilingPrefixPointPath x
          (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal) y =
      listLocalTime
        (tilingPrefixPointPath x
          (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal) y := by
  let b : TilingExternalDomino t x r := ⟨tilingBase t y, hyrepresented⟩
  have htotal := tilingDominoTotal_eq_of_distinguished_eq
    t x r D q q' hdist b hy
  rw [tilingInsertedPrefix_localTime_at_dominoPoint
      t x r (fun j ↦ (q j : ℕ)) terminal b y rfl,
    tilingInsertedPrefix_localTime_at_dominoPoint
      t x r (fun j ↦ (q' j : ℕ)) terminal b y rfl,
    htotal]

/-- A point whose tiling base is distinguished has coordinate-invariant
terminal local time whether or not that domino occurs in the retained
external word.  In the latter case both local times are the same fixed
outside contribution. -/
theorem tilingPrefixLocalTime_eq_of_distinguished_eq
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1)
    (y : Point) (hy : tilingBase t y ∈ D) :
    listLocalTime
        (tilingPrefixPointPath x
          (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal) y =
      listLocalTime
        (tilingPrefixPointPath x
          (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal) y := by
  by_cases hrepresented :
      tilingBase t y ∈ tilingExternalDominoBases t x r
  · exact tilingPrefixLocalTime_eq_of_distinguished_eq_of_base_mem
      t x r terminal D q q' hdist y hy hrepresented
  · rw [tilingInsertedPrefix_localTime_of_base_not_mem
        t x r (fun j ↦ (q j : ℕ)) terminal y hrepresented,
      tilingInsertedPrefix_localTime_of_base_not_mem
        t x r (fun j ↦ (q' j : ℕ)) terminal y hrepresented]

/-- Raising the endpoint cutoff preserves the strict domino truncation. -/
theorem tilingDominoTruncation_mono_level {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) {level level' : ℕ} (hle : level ≤ level')
    (D : Finset Point) (q : Fin (i + 1) → ℕ)
    (h : TilingDominoTruncation t x r terminal level D q) :
    TilingDominoTruncation t x r terminal level' D q := by
  rw [← tilingActualEndpointsBelow_iff_dominoTruncation] at h ⊢
  intro b hb
  exact ⟨(h b hb).1.trans_le hle, (h b hb).2.trans_le hle⟩

/-- Consequently the terminal threshold count of two canonical inserted
prefixes is the same whenever they share the same optional terminal point,
distinguished coordinates, and strict away support. -/
theorem thresholdCount_tilingInsertionPrefix_eq_of_distinguished_eq
    {i cap : ℕ} (t : DominoTiling)
    (r : TilingRetainedWord t (0, 0) i) (tail : BoundaryTail)
    (terminal : Option Point) (level : ℕ) (hm : 0 < level)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hterminal : tilingInsertionTerminal t r
        (fun j ↦ (q j : ℕ)) tail = terminal)
    (hterminal' : tilingInsertionTerminal t r
        (fun j ↦ (q' j : ℕ)) tail = terminal)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) r D q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) r D q').1)
    (htrunc : TilingDominoTruncation t (0, 0) r terminal level D
      (fun j ↦ (q j : ℕ)))
    (htrunc' : TilingDominoTruncation t (0, 0) r terminal level D
      (fun j ↦ (q' j : ℕ))) :
    let v := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1
    let v' := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1
    thresholdCount
        (trajectory (extendPrefix (directionVectorOfList v))) v.length level =
      thresholdCount
        (trajectory (extendPrefix (directionVectorOfList v'))) v'.length level := by
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (q j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (q' j : ℕ)
  let v := tilingInsertionPrefixList t (0, 0) r qNat tail.1
  let v' := tilingInsertionPrefixList t (0, 0) r qNat' tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  have hpath : finitePathList (pathPrefix s v.length) =
      tilingPrefixPointPath (0, 0) (tilingInsertGapVector t (0, 0) r qNat)
        terminal := by
    rw [← hterminal]
    exact finitePathList_tilingInsertionPrefix t r qNat tail
  have hpath' : finitePathList (pathPrefix s' v'.length) =
      tilingPrefixPointPath (0, 0) (tilingInsertGapVector t (0, 0) r qNat')
        terminal := by
    rw [← hterminal']
    exact finitePathList_tilingInsertionPrefix t r qNat' tail
  unfold thresholdCount
  congr 1
  ext y
  rw [mem_thresholdSites_iff s v.length level y hm,
    mem_thresholdSites_iff s' v'.length level y hm,
    localTime_eq_listLocalTime, localTime_eq_listLocalTime,
    hpath, hpath']
  exact tilingPrefixLocalTime_ge_level_iff_of_distinguished_eq
    t (0, 0) r terminal level D q q' hdist htrunc htrunc' y

/-- Set-valued version of the preceding terminal threshold invariance. -/
theorem thresholdSites_tilingInsertionPrefix_eq_of_distinguished_eq
    {i cap : ℕ} (t : DominoTiling)
    (r : TilingRetainedWord t (0, 0) i) (tail : BoundaryTail)
    (terminal : Option Point) (level : ℕ) (hm : 0 < level)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hterminal : tilingInsertionTerminal t r
        (fun j ↦ (q j : ℕ)) tail = terminal)
    (hterminal' : tilingInsertionTerminal t r
        (fun j ↦ (q' j : ℕ)) tail = terminal)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) r D q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) r D q').1)
    (htrunc : TilingDominoTruncation t (0, 0) r terminal level D
      (fun j ↦ (q j : ℕ)))
    (htrunc' : TilingDominoTruncation t (0, 0) r terminal level D
      (fun j ↦ (q' j : ℕ))) :
    let v := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1
    let v' := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1
    thresholdSites
        (trajectory (extendPrefix (directionVectorOfList v))) v.length level =
      thresholdSites
        (trajectory (extendPrefix (directionVectorOfList v'))) v'.length level := by
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (q j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (q' j : ℕ)
  let v := tilingInsertionPrefixList t (0, 0) r qNat tail.1
  let v' := tilingInsertionPrefixList t (0, 0) r qNat' tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  have hpath : finitePathList (pathPrefix s v.length) =
      tilingPrefixPointPath (0, 0) (tilingInsertGapVector t (0, 0) r qNat)
        terminal := by
    rw [← hterminal]
    exact finitePathList_tilingInsertionPrefix t r qNat tail
  have hpath' : finitePathList (pathPrefix s' v'.length) =
      tilingPrefixPointPath (0, 0) (tilingInsertGapVector t (0, 0) r qNat')
        terminal := by
    rw [← hterminal']
    exact finitePathList_tilingInsertionPrefix t r qNat' tail
  ext y
  rw [mem_thresholdSites_iff s v.length level y hm,
    mem_thresholdSites_iff s' v'.length level y hm,
    localTime_eq_listLocalTime, localTime_eq_listLocalTime,
    hpath, hpath']
  exact tilingPrefixLocalTime_ge_level_iff_of_distinguished_eq
    t (0, 0) r terminal level D q q' hdist htrunc htrunc' y

/-- For two accepted level-favorite words, the trace-code favorite-site
field is fixed by the distinguished coordinates and strict away support. -/
theorem favoriteSites_tilingInsertionPrefix_eq_of_distinguished_eq
    {i cap : ℕ} (t : DominoTiling) (m k cutoff : ℕ)
    (hm : 0 < m) (hk : 0 < k)
    (r : TilingRetainedWord t (0, 0) i) (tail : BoundaryTail)
    (terminal : Option Point) (D : Finset Point)
    (q q' : TilingCappedCoordinates i cap)
    (hterminal : tilingInsertionTerminal t r
        (fun j ↦ (q j : ℕ)) tail = terminal)
    (hterminal' : tilingInsertionTerminal t r
        (fun j ↦ (q' j : ℕ)) tail = terminal)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) r D q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) r D q').1)
    (htrunc : TilingDominoTruncation t (0, 0) r terminal m D
      (fun j ↦ (q j : ℕ)))
    (htrunc' : TilingDominoTruncation t (0, 0) r terminal m D
      (fun j ↦ (q' j : ℕ)))
    (haccepted : TilingStoppingAccepted (truncatedLevelTime m k cutoff)
      t (0, 0) r (fun j ↦ (q j : ℕ)) tail.1)
    (haccepted' : TilingStoppingAccepted (truncatedLevelTime m k cutoff)
      t (0, 0) r (fun j ↦ (q' j : ℕ)) tail.1)
    (hfavorite :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      levelFavorite (trajectory (extendPrefix (directionVectorOfList v))) m k)
    (hfavorite' :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q' j : ℕ)) tail.1
      levelFavorite (trajectory (extendPrefix (directionVectorOfList v))) m k)
    (hlt : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff)
    (hlt' : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1).length < cutoff) :
    let v := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1
    let v' := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1
    favoriteSites
        (trajectory (extendPrefix (directionVectorOfList v))) v.length =
      favoriteSites
        (trajectory (extendPrefix (directionVectorOfList v'))) v'.length := by
  let v := tilingInsertionPrefixList t (0, 0) r
    (fun j ↦ (q j : ℕ)) tail.1
  let v' := tilingInsertionPrefixList t (0, 0) r
    (fun j ↦ (q' j : ℕ)) tail.1
  let omega := extendPrefix (directionVectorOfList v)
  let omega' := extendPrefix (directionVectorOfList v')
  have hsites := thresholdSites_tilingInsertionPrefix_eq_of_distinguished_eq
    t r tail terminal m hm D q q' hterminal hterminal' hdist htrunc htrunc'
  have hfavoriteSites : thresholdSites (trajectory omega) v.length m =
      favoriteSites (trajectory omega) v.length :=
    thresholdSites_eq_favoriteSites_at_truncatedLevelTime
      m k cutoff v.length omega hk hlt haccepted hfavorite
  have hfavoriteSites' : thresholdSites (trajectory omega') v'.length m =
      favoriteSites (trajectory omega') v'.length :=
    thresholdSites_eq_favoriteSites_at_truncatedLevelTime
      m k cutoff v'.length omega' hk hlt' haccepted' hfavorite'
  exact hfavoriteSites.symm.trans (hsites.trans hfavoriteSites')

/-- The external-word component of the trace code is completely
independent of the insertion coordinates. -/
theorem fixedTilingExternalWordCode_insertionCoordinates_eq
    {i cap : ℕ} (t : DominoTiling)
    (r : TilingRetainedWord t (0, 0) i) (tail : BoundaryTail)
    (q q' : TilingCappedCoordinates i cap) :
    let v := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1
    let v' := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1
    fixedTilingExternalWordCode t v.length
        (trajectory (extendPrefix (directionVectorOfList v))) =
      fixedTilingExternalWordCode t v'.length
        (trajectory (extendPrefix (directionVectorOfList v'))) := by
  dsimp only
  rw [fixedTilingExternalWordCode_tilingInsertionPrefix,
    fixedTilingExternalWordCode_tilingInsertionPrefix]

/-- Equality of the terminal favorite-site set and terminal point is exactly
equality of the favorite-data component of a tiling trace code. -/
theorem fixedTilingCreationFavoriteData_eq_of_sites_terminal_eq
    (t : DominoTiling) (n n' : ℕ) (s s' : WalkPath)
    (hsites : favoriteSites s n = favoriteSites s' n')
    (hterminal : s n = s' n') :
    fixedTilingCreationFavoriteData t n s =
      fixedTilingCreationFavoriteData t n' s' := by
  unfold fixedTilingCreationFavoriteData
  rw [hsites, hterminal]

/-- Deterministic creation times together with equal fixed-prefix trace data
give equal variable favorite trace codes. -/
theorem tilingCreationCodes_eq_of_fixedPrefixData
    (t : DominoTiling) (m k n n' : ℕ) (s s' : WalkPath)
    (htime : creationTimeNat m k s = n)
    (htime' : creationTimeNat m k s' = n')
    (hexternal : fixedTilingExternalWordCode t n s =
      fixedTilingExternalWordCode t n' s')
    (hsites : favoriteSites s n = favoriteSites s' n')
    (hterminal : s n = s' n') :
    tilingCreationExternalCode t m k s =
        tilingCreationExternalCode t m k s' ∧
      tilingCreationFavoriteData t m k s =
        tilingCreationFavoriteData t m k s' := by
  constructor
  · unfold tilingCreationExternalCode
    rw [htime, htime']
    exact hexternal
  · unfold tilingCreationFavoriteData
    rw [htime, htime']
    exact fixedTilingCreationFavoriteData_eq_of_sites_terminal_eq
      t n n' s s' hsites hterminal

/-- Membership in a non-null favorite trace piece is invariant between two
reaching valid paths with the same variable external and favorite codes. -/
theorem mem_favoriteTilingCreationPiece_some_iff_of_codes_eq
    (t : DominoTiling) (m k : ℕ)
    (z : TilingExternalWordCode t × TilingCreationFavoriteData)
    {s s' : WalkPath} (hreach : s ∈ thresholdReachStage m k)
    (hreach' : s' ∈ thresholdReachStage m k)
    (hvalid : s ∈ validStepWalk) (hvalid' : s' ∈ validStepWalk)
    (hexternal : tilingCreationExternalCode t m k s =
      tilingCreationExternalCode t m k s')
    (hfavorite : tilingCreationFavoriteData t m k s =
      tilingCreationFavoriteData t m k s') :
    s ∈ favoriteTilingCreationPiece t m k (some z) ↔
      s' ∈ favoriteTilingCreationPiece t m k (some z) := by
  change ((((s ∈ thresholdReachStage m k) ∧ s ∈ validStepWalk) ∧
      tilingCreationExternalCode t m k s = z.1) ∧
        tilingCreationFavoriteData t m k s = z.2) ↔
    (((s' ∈ thresholdReachStage m k ∧ s' ∈ validStepWalk) ∧
      tilingCreationExternalCode t m k s' = z.1) ∧
        tilingCreationFavoriteData t m k s' = z.2)
  simp only [hreach, hreach', hvalid, hvalid', true_and]
  rw [hexternal, hfavorite]

/-! ## Coordinate-cap coherence -/

/-- A predicate on genuine natural insertion coordinates gives a monotone
family of capped stopped fibres.  The proof embeds each finite coordinate
without changing its natural value or its stopped cylinder. -/
theorem monotone_tilingPreStoppingFiberEvent_of_natPredicate
    (tau : StepPath → ℕ) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (tail : List Direction)
    (P : (Fin (i + 1) → ℕ) → Prop) :
    Monotone fun cap ↦ tilingPreStoppingFiberEvent tau t x r cap tail
      (fun q ↦ P (fun j ↦ (q j : ℕ))) := by
  intro cap cap' hcap omega homega
  rcases Set.mem_iUnion.mp homega with ⟨q, hq⟩
  let q' : TilingCappedCoordinates i cap' := fun j ↦
    Fin.castLE (Nat.succ_le_succ hcap) (q.1 j)
  have hval : ∀ j, (q' j : ℕ) = (q.1 j : ℕ) := fun _ ↦ rfl
  have hP : P (fun j ↦ (q' j : ℕ)) := by
    simpa only [hval] using q.2.1
  have haccepted : TilingStoppingAccepted tau t x r
      (fun j ↦ (q' j : ℕ)) tail := by
    simpa only [hval] using q.2.2
  apply Set.mem_iUnion.mpr
  refine ⟨⟨q', hP, haccepted⟩, ?_⟩
  simpa only [hval] using hq

/-- Every accepted natural-valued insertion word occurs at the explicit cap
given by the sum of its coordinates. -/
theorem tilingStoppedInsertionAtom_subset_iUnion_capped_natPredicate
    (tau : StepPath → ℕ) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (tail : List Direction)
    (P : (Fin (i + 1) → ℕ) → Prop) (q : Fin (i + 1) → ℕ)
    (hP : P q) (haccepted : TilingStoppingAccepted tau t x r q tail) :
    tilingStoppedInsertionAtom tau t x r q tail ⊆
      ⋃ cap, tilingPreStoppingFiberEvent tau t x r cap tail
        (fun qc ↦ P (fun j ↦ (qc j : ℕ))) := by
  classical
  let cap := ∑ j, q j
  have hle (j : Fin (i + 1)) : q j ≤ cap := by
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  let qc : TilingCappedCoordinates i cap := fun j ↦
    ⟨q j, Nat.lt_succ_of_le (hle j)⟩
  have hval : ∀ j, (qc j : ℕ) = q j := fun _ ↦ rfl
  intro omega homega
  apply Set.mem_iUnion.mpr
  refine ⟨cap, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨⟨qc, ?_, ?_⟩, ?_⟩
  · simpa only [hval] using hP
  · simpa only [hval] using haccepted
  · simpa only [hval] using homega

/-- Stopped acceptance itself is invariant once the terminal point belongs
to a distinguished represented domino and both away profiles satisfy the
strict level support.  All dependence on physical word length is kept in the
explicit positivity/cutoff hypotheses. -/
theorem tilingStoppingAccepted_iff_of_distinguished_eq_of_truncated
    {i cap : ℕ} (t : DominoTiling) (m k cutoff : ℕ)
    (hm : 0 < m) (hk : 0 < k)
    (r : TilingRetainedWord t (0, 0) i) (tail : BoundaryTail)
    (terminal : Option Point) (terminalPoint : Point)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hterminal : tilingInsertionTerminal t r
        (fun j ↦ (q j : ℕ)) tail = terminal)
    (hterminal' : tilingInsertionTerminal t r
        (fun j ↦ (q' j : ℕ)) tail = terminal)
    (hend :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      trajectory (extendPrefix (directionVectorOfList v)) v.length =
        terminalPoint)
    (hend' :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q' j : ℕ)) tail.1
      trajectory (extendPrefix (directionVectorOfList v)) v.length =
        terminalPoint)
    (hbase : tilingBase t terminalPoint ∈ D)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) r D q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) r D q').1)
    (htrunc : TilingDominoTruncation t (0, 0) r terminal m D
      (fun j ↦ (q j : ℕ)))
    (htrunc' : TilingDominoTruncation t (0, 0) r terminal m D
      (fun j ↦ (q' j : ℕ)))
    (hpos : 0 < (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1).length)
    (hpos' : 0 < (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1).length)
    (hlt : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff)
    (hlt' : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1).length < cutoff) :
    TilingStoppingAccepted (truncatedLevelTime m k cutoff)
        t (0, 0) r (fun j ↦ (q j : ℕ)) tail.1 ↔
      TilingStoppingAccepted (truncatedLevelTime m k cutoff)
        t (0, 0) r (fun j ↦ (q' j : ℕ)) tail.1 := by
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (q j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (q' j : ℕ)
  let v := tilingInsertionPrefixList t (0, 0) r qNat tail.1
  let v' := tilingInsertionPrefixList t (0, 0) r qNat' tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  have hcount : thresholdCount s v.length m =
      thresholdCount s' v'.length m :=
    thresholdCount_tilingInsertionPrefix_eq_of_distinguished_eq
      t r tail terminal m hm D q q' hterminal hterminal'
      hdist htrunc htrunc'
  have hpath : finitePathList (pathPrefix s v.length) =
      tilingPrefixPointPath (0, 0) (tilingInsertGapVector t (0, 0) r qNat)
        terminal := by
    rw [← hterminal]
    exact finitePathList_tilingInsertionPrefix t r qNat tail
  have hpath' : finitePathList (pathPrefix s' v'.length) =
      tilingPrefixPointPath (0, 0) (tilingInsertGapVector t (0, 0) r qNat')
        terminal := by
    rw [← hterminal']
    exact finitePathList_tilingInsertionPrefix t r qNat' tail
  have hlocal : localTime s v.length terminalPoint =
      localTime s' v'.length terminalPoint := by
    rw [localTime_eq_listLocalTime, localTime_eq_listLocalTime,
      hpath, hpath']
    exact tilingPrefixLocalTime_eq_of_distinguished_eq
      t (0, 0) r terminal D q q' hdist terminalPoint hbase
  rw [tilingStoppingAccepted_truncatedLevelTime_iff_terminal
      m k cutoff t (0, 0) r qNat tail hm hk hpos hlt,
    tilingStoppingAccepted_truncatedLevelTime_iff_terminal
      m k cutoff t (0, 0) r qNat' tail hm hk hpos' hlt']
  dsimp only [s, s', v, v']
  rw [hend, hend', hcount, hlocal]

/-- On two accepted prefixes with the same distinguished coordinates and
strict level-`m` away support, the level-favorite condition is invariant.
This supplies the favorite-data part of trace-code invariance without fixing
the physical creation time. -/
theorem levelFavorite_tilingInsertionPrefix_iff_of_distinguished_eq
    {i cap : ℕ} (t : DominoTiling) (m k cutoff : ℕ) (hk : 0 < k)
    (r : TilingRetainedWord t (0, 0) i) (tail : BoundaryTail)
    (terminal : Option Point) (D : Finset Point)
    (q q' : TilingCappedCoordinates i cap)
    (hterminal : tilingInsertionTerminal t r
        (fun j ↦ (q j : ℕ)) tail = terminal)
    (hterminal' : tilingInsertionTerminal t r
        (fun j ↦ (q' j : ℕ)) tail = terminal)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) r D q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) r D q').1)
    (htrunc : TilingDominoTruncation t (0, 0) r terminal m D
      (fun j ↦ (q j : ℕ)))
    (htrunc' : TilingDominoTruncation t (0, 0) r terminal m D
      (fun j ↦ (q' j : ℕ)))
    (haccepted : TilingStoppingAccepted (truncatedLevelTime m k cutoff)
      t (0, 0) r (fun j ↦ (q j : ℕ)) tail.1)
    (haccepted' : TilingStoppingAccepted (truncatedLevelTime m k cutoff)
      t (0, 0) r (fun j ↦ (q' j : ℕ)) tail.1)
    (hlt : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff)
    (hlt' : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1).length < cutoff) :
    let v := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1
    let v' := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1
    levelFavorite (trajectory (extendPrefix (directionVectorOfList v))) m k ↔
      levelFavorite
        (trajectory (extendPrefix (directionVectorOfList v'))) m k := by
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (q j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (q' j : ℕ)
  let v := tilingInsertionPrefixList t (0, 0) r qNat tail.1
  let v' := tilingInsertionPrefixList t (0, 0) r qNat' tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  have hpath : finitePathList (pathPrefix s v.length) =
      tilingPrefixPointPath (0, 0) (tilingInsertGapVector t (0, 0) r qNat)
        terminal := by
    rw [← hterminal]
    exact finitePathList_tilingInsertionPrefix t r qNat tail
  have hpath' : finitePathList (pathPrefix s' v'.length) =
      tilingPrefixPointPath (0, 0) (tilingInsertGapVector t (0, 0) r qNat')
        terminal := by
    rw [← hterminal']
    exact finitePathList_tilingInsertionPrefix t r qNat' tail
  have htruncSucc : TilingDominoTruncation t (0, 0) r terminal (m + 1) D
      qNat := tilingDominoTruncation_mono_level
        t (0, 0) r terminal (Nat.le_succ m) D qNat htrunc
  have htruncSucc' : TilingDominoTruncation t (0, 0) r terminal (m + 1) D
      qNat' := tilingDominoTruncation_mono_level
        t (0, 0) r terminal (Nat.le_succ m) D qNat' htrunc'
  dsimp only
  rw [levelFavorite_iff_all_localTime_lt_succ_at_truncatedLevelTime
      m k cutoff v.length (extendPrefix (directionVectorOfList v)) hk hlt
      haccepted,
    levelFavorite_iff_all_localTime_lt_succ_at_truncatedLevelTime
      m k cutoff v'.length (extendPrefix (directionVectorOfList v')) hk hlt'
      haccepted']
  constructor
  · intro h y
    by_contra hnot
    have hge' : m + 1 ≤ localTime s' v'.length y := Nat.le_of_not_gt hnot
    have hgeList' : m + 1 ≤ listLocalTime
        (tilingPrefixPointPath (0, 0)
          (tilingInsertGapVector t (0, 0) r qNat') terminal) y := by
      rwa [← hpath', ← localTime_eq_listLocalTime]
    have hgeList :=
      (tilingPrefixLocalTime_ge_level_iff_of_distinguished_eq
        t (0, 0) r terminal (m + 1) D q q' hdist htruncSucc
          htruncSucc' y).2 hgeList'
    have hge : m + 1 ≤ localTime s v.length y := by
      rwa [localTime_eq_listLocalTime, hpath]
    exact (not_lt_of_ge hge) (h y)
  · intro h y
    by_contra hnot
    have hge : m + 1 ≤ localTime s v.length y := Nat.le_of_not_gt hnot
    have hgeList : m + 1 ≤ listLocalTime
        (tilingPrefixPointPath (0, 0)
          (tilingInsertGapVector t (0, 0) r qNat) terminal) y := by
      rwa [← hpath, ← localTime_eq_listLocalTime]
    have hgeList' :=
      (tilingPrefixLocalTime_ge_level_iff_of_distinguished_eq
        t (0, 0) r terminal (m + 1) D q q' hdist htruncSucc
          htruncSucc' y).1 hgeList
    have hge' : m + 1 ≤ localTime s' v'.length y := by
      rwa [localTime_eq_listLocalTime, hpath']
    exact (not_lt_of_ge hge') (h y)

/-! ## Canonical endpoint specializations -/

/-- Stopped acceptance invariance with the common optional terminal and
actual stopped endpoint supplied automatically by the insertion word. -/
theorem tilingStoppingAccepted_iff_of_distinguished_eq_of_truncated_canonical
    {i cap : ℕ} (t : DominoTiling) (m k cutoff : ℕ)
    (hm : 0 < m) (hk : 0 < k)
    (r : TilingRetainedWord t (0, 0) i) (tail : BoundaryTail)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hbase :
      let v := tilingInsertionPrefixList t (0, 0) r
        (fun j ↦ (q j : ℕ)) tail.1
      tilingBase t
          (trajectory (extendPrefix (directionVectorOfList v)) v.length) ∈ D)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) r D q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) r D q').1)
    (htrunc : TilingDominoTruncation t (0, 0) r
      (tilingInsertionTerminal t r (fun j ↦ (q j : ℕ)) tail) m D
      (fun j ↦ (q j : ℕ)))
    (htrunc' : TilingDominoTruncation t (0, 0) r
      (tilingInsertionTerminal t r (fun j ↦ (q j : ℕ)) tail) m D
      (fun j ↦ (q' j : ℕ)))
    (hpos : 0 < (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1).length)
    (hpos' : 0 < (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1).length)
    (hlt : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff)
    (hlt' : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1).length < cutoff) :
    TilingStoppingAccepted (truncatedLevelTime m k cutoff)
        t (0, 0) r (fun j ↦ (q j : ℕ)) tail.1 ↔
      TilingStoppingAccepted (truncatedLevelTime m k cutoff)
        t (0, 0) r (fun j ↦ (q' j : ℕ)) tail.1 := by
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (q j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (q' j : ℕ)
  let v := tilingInsertionPrefixList t (0, 0) r qNat tail.1
  let terminal := tilingInsertionTerminal t r qNat tail
  let terminalPoint := trajectory
    (extendPrefix (directionVectorOfList v)) v.length
  have hterminal' : tilingInsertionTerminal t r qNat' tail = terminal := by
    exact (tilingInsertionTerminal_eq_of_coordinates t r qNat qNat' tail).symm
  have hend' :
      let v' := tilingInsertionPrefixList t (0, 0) r qNat' tail.1
      trajectory (extendPrefix (directionVectorOfList v')) v'.length =
        terminalPoint := by
    exact (canonical_tilingInsertion_endpoint_eq_of_coordinates
      t r qNat qNat' tail).symm
  exact tilingStoppingAccepted_iff_of_distinguished_eq_of_truncated
    t m k cutoff hm hk r tail terminal terminalPoint D q q'
    rfl hterminal' rfl hend' hbase hdist htrunc htrunc'
    hpos hpos' hlt hlt'

/-- Level-favorite invariance with the common optional terminal supplied
canonically from the insertion word. -/
theorem levelFavorite_tilingInsertionPrefix_iff_of_distinguished_eq_canonical
    {i cap : ℕ} (t : DominoTiling) (m k cutoff : ℕ) (hk : 0 < k)
    (r : TilingRetainedWord t (0, 0) i) (tail : BoundaryTail)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
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
    (haccepted' : TilingStoppingAccepted (truncatedLevelTime m k cutoff)
      t (0, 0) r (fun j ↦ (q' j : ℕ)) tail.1)
    (hlt : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff)
    (hlt' : (tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1).length < cutoff) :
    let v := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q j : ℕ)) tail.1
    let v' := tilingInsertionPrefixList t (0, 0) r
      (fun j ↦ (q' j : ℕ)) tail.1
    levelFavorite (trajectory (extendPrefix (directionVectorOfList v))) m k ↔
      levelFavorite
        (trajectory (extendPrefix (directionVectorOfList v'))) m k := by
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (q j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (q' j : ℕ)
  let terminal := tilingInsertionTerminal t r qNat tail
  have hterminal' : tilingInsertionTerminal t r qNat' tail = terminal := by
    exact (tilingInsertionTerminal_eq_of_coordinates t r qNat qNat' tail).symm
  exact levelFavorite_tilingInsertionPrefix_iff_of_distinguished_eq
    t m k cutoff hk r tail terminal D q q' rfl hterminal' hdist
    htrunc htrunc' haccepted haccepted' hlt hlt'

end

end Erdos1165.TilingFavoriteTraceSupport
