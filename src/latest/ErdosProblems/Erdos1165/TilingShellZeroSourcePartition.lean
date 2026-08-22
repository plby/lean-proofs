/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingCappedMarginalization
import ErdosProblems.Erdos1165.HLOZShellZeroReplacementWindows
import ErdosProblems.Erdos1165.TilingVariableStoppedTracePartition

/-!
# The source-correct shell-zero trace partition

This file records the path predicates occurring in HLOZ (4.49)--(4.54).
The three classes `V₁`, `V₂`, and `V₃`, the good external-local-time
condition `Theta = ∅`, and the enlarged condition `Dtilde` are evaluated at
the genuine rank-`k` creation time.  The source event is partitioned by the
complete statefully deleted tiling word, without fixing physical time.

The last section isolates the source-correct disjointness mechanism.  Its
clock is allowed to depend on the path.  This is essential here: fixing a
retained word does not fix the number of inserted two-step excursions and
hence does not fix physical time.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.TilingShellZeroSourcePartition

open HLOZPathEvents HLOZShellZeroReplacementProduct
open HLOZShellZeroReplacementWindows HeterogeneousProductTail
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingCappedMarginalization FiniteDominoProductLaw
open TilingVariableStoppedTracePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-! ## Sound path-dependent threshold-jump disjointness -/

/-- Variable-clock form of the `B_eta` disjointness mechanism.  The clock
depends on the path because the retained word does not determine the total
number of inserted excursions. -/
structure VariableClockThresholdJumpReplacementFamily
    {Omega Index : Type*} [MeasurableSpace Omega]
    (replacement : Index → Set Omega) where
  clock : Index → Omega → ℕ
  traceAt : Omega → ℕ → Index
  thresholdCount : Omega → ℕ → ℕ
  monotone_thresholdCount : ∀ omega, Monotone (thresholdCount omega)
  rank : ℕ
  trace_eq : ∀ z omega, omega ∈ replacement z →
    traceAt omega (clock z omega) = z
  count_before : ∀ z omega, omega ∈ replacement z →
    thresholdCount omega (clock z omega - 1) = rank
  count_at : ∀ z omega, omega ∈ replacement z →
    thresholdCount omega (clock z omega) = rank + 1

theorem pairwise_disjoint_of_variableClockThresholdJump
    {Omega Index : Type*} [MeasurableSpace Omega]
    {replacement : Index → Set Omega}
    (data : VariableClockThresholdJumpReplacementFamily replacement) :
    Pairwise fun z w ↦ Disjoint (replacement z) (replacement w) := by
  intro z w hzw
  rw [Set.disjoint_left]
  intro omega hz hw
  by_cases hclock : data.clock z omega = data.clock w omega
  · apply hzw
    calc
      z = data.traceAt omega (data.clock z omega) :=
        (data.trace_eq z omega hz).symm
      _ = data.traceAt omega (data.clock w omega) := by rw [hclock]
      _ = w := data.trace_eq w omega hw
  · rcases lt_or_gt_of_ne hclock with hlt | hgt
    · have htime : data.clock z omega ≤ data.clock w omega - 1 := by omega
      have hmono := data.monotone_thresholdCount omega htime
      rw [data.count_at z omega hz, data.count_before w omega hw] at hmono
      omega
    · have htime : data.clock w omega ≤ data.clock z omega - 1 := by omega
      have hmono := data.monotone_thresholdCount omega htime
      rw [data.count_at w omega hw, data.count_before z omega hz] at hmono
      omega

/-! ## The literal `V` and `Theta` predicates -/

/-- Domino bases encountered by the walk by physical time `n`. -/
def visitedTilingBases (t : DominoTiling) (s : WalkPath) (n : ℕ) :
    Finset Point :=
  (visitedSites s n).image (tilingBase t)

/-- Total local time of the two endpoints of the domino with base `b`.
This auxiliary quantity is not the `xi⁺` coordinate used in HLOZ's
shell-zero source partition. -/
def tilingDominoLocalTime (t : DominoTiling) (s : WalkPath)
    (n : ℕ) (b : Point) : ℕ :=
  localTime s n b + localTime s n (tilingPartner t b)

/-- HLOZ's `xi⁺` on the unoriented pair represented by the base `b`. -/
def tilingXiPlusAt (t : DominoTiling) (s : WalkPath)
    (n : ℕ) (b : Point) : ℕ :=
  max (localTime s n b) (localTime s n (tilingPartner t b))

theorem tilingXiPlusAt_eq_base_of_partner_le
    {t : DominoTiling} {s : WalkPath} {n : ℕ} {b : Point}
    (h : localTime s n (tilingPartner t b) ≤ localTime s n b) :
    tilingXiPlusAt t s n b = localTime s n b := by
  exact max_eq_left h

/-- External retained local time of the canonical base endpoint. -/
def tilingExternalBaseLocalTime (t : DominoTiling) (s : WalkPath)
    (n : ℕ) (b : Point) : ℕ :=
  LazyDecomposition.listLocalTime
    (tilingExternalPath t
      (LazyDecomposition.finitePathList (pathPrefix s n))) b

/-- HLOZ's `V_η^(1)`: exactly one endpoint has level `m`. -/
def tilingVOneAt (t : DominoTiling) (m : ℕ) (s : WalkPath)
    (n : ℕ) (b : Point) : Prop :=
  (localTime s n b = m ∧ localTime s n (tilingPartner t b) < m) ∨
    (localTime s n (tilingPartner t b) = m ∧ localTime s n b < m)

/-- HLOZ's `V_η^(2)(I)`: the base endpoint is dominant and its single-site
local time lies in `I`.  In the paper `xi⁺` is the maximum of the two
endpoint local times, so under base dominance it is exactly this base local
time.  Taking `I = I₁` gives the source class and taking `I = I₀` gives the
artificial replacement class. -/
def tilingVTwoAt (t : DominoTiling) (window : Finset ℕ)
    (s : WalkPath) (n : ℕ) (b : Point) : Prop :=
  localTime s n (tilingPartner t b) ≤ localTime s n b ∧
    localTime s n b ∈ window

/-- HLOZ's `V_η^(3)`.  The parameter `low` is the lower cutoff used in
the paper (the repository's numerical layer supplies its rounded value). -/
def tilingVThreeAt (t : DominoTiling) (m low : ℕ)
    (s : WalkPath) (n : ℕ) (b : Point) : Prop :=
  localTime s n b ≤ low ∨
    (localTime s n b < localTime s n (tilingPartner t b) ∧
      localTime s n (tilingPartner t b) < m)

/-- Finite set version of `V₁`; only visited dominoes can belong to it. -/
def tilingVOneBases (t : DominoTiling) (m : ℕ)
    (s : WalkPath) (n : ℕ) : Finset Point :=
  by
    classical
    exact (visitedTilingBases t s n).filter (tilingVOneAt t m s n)

/-- Finite set version of `V₂(I)`. -/
def tilingVTwoBases (t : DominoTiling) (window : Finset ℕ)
    (s : WalkPath) (n : ℕ) : Finset Point :=
  by
    classical
    exact (visitedTilingBases t s n).filter (tilingVTwoAt t window s n)

/-- The `V₂`-restricted external-local-time screen used by the shell source.
This is the intersection of the paper's global `Theta_η` with the
base-dominant `V₂(I₀ ∪ I₁)` family; it is not the unrestricted global
`Theta_η` of (4.16). -/
def tilingThetaBases (t : DominoTiling) (m w externalLow externalHigh : ℕ)
    (s : WalkPath) (n : ℕ) : Finset Point :=
  (visitedTilingBases t s n).filter fun b ↦
    localTime s n (tilingPartner t b) ≤ localTime s n b ∧
      localTime s n b ∈
        (shellZeroSourceTotalWindow m w ∪
          shellZeroReplacementTotalWindow m w) ∧
      ¬(externalLow ≤ tilingExternalBaseLocalTime t s n b ∧
        tilingExternalBaseLocalTime t s n b < externalHigh)

/-- Explicit source-facing name for the legacy shell screen. -/
abbrev tilingRestrictedThetaBases := tilingThetaBases

/-- The paper's global `Theta_η`: every canonical tiling base whose
single-site local time lies in `I₀ ∪ I₁` and whose retained external local
time is outside the prescribed interval.  No dominance condition is part of
this global event. -/
def tilingGlobalThetaBases (t : DominoTiling)
    (m w externalLow externalHigh : ℕ)
    (s : WalkPath) (n : ℕ) : Finset Point :=
  (visitedTilingBases t s n).filter fun b ↦
    localTime s n b ∈
        (shellZeroSourceTotalWindow m w ∪
          shellZeroReplacementTotalWindow m w) ∧
      ¬(externalLow ≤ tilingExternalBaseLocalTime t s n b ∧
        tilingExternalBaseLocalTime t s n b < externalHigh)

theorem tilingRestrictedThetaBases_subset_global
    (t : DominoTiling) (m w externalLow externalHigh : ℕ)
    (s : WalkPath) (n : ℕ) :
    tilingRestrictedThetaBases t m w externalLow externalHigh s n ⊆
      tilingGlobalThetaBases t m w externalLow externalHigh s n := by
  intro b hb
  simp only [tilingRestrictedThetaBases, tilingThetaBases,
    tilingGlobalThetaBases, Finset.mem_filter] at hb ⊢
  exact ⟨hb.1, hb.2.2⟩

/-- Exact restricted/global identity: the shell screen is the dominant
subfamily of global `Theta_η`. -/
theorem tilingRestrictedThetaBases_eq_global_filter_dominant
    (t : DominoTiling) (m w externalLow externalHigh : ℕ)
    (s : WalkPath) (n : ℕ) :
    tilingRestrictedThetaBases t m w externalLow externalHigh s n =
      (tilingGlobalThetaBases t m w externalLow externalHigh s n).filter
        (fun b ↦ localTime s n (tilingPartner t b) ≤ localTime s n b) := by
  ext b
  simp only [tilingRestrictedThetaBases, tilingThetaBases,
    tilingGlobalThetaBases, Finset.mem_filter]
  tauto

/-- `D_η`: `V₁` has the prescribed cardinality, every tiling base is in
one of `V₁,V₂(I₁),V₃`, and the terminal site has level `m`. -/
def tilingDEtaAt (t : DominoTiling) (m k w low : ℕ)
    (s : WalkPath) (n : ℕ) : Prop :=
  (tilingVOneBases t m s n).card = k ∧
    (∀ b, IsTilingBase t b →
      tilingVOneAt t m s n b ∨
        tilingVTwoAt t (shellZeroSourceTotalWindow m w) s n b ∨
        tilingVThreeAt t m low s n b) ∧
    localTime s n (s n) = m

/-- The enlarged `Dtilde_η` used for replacement: `V₂(I₀)` is
admitted in addition, and the terminal domino belongs to `V₁`. -/
def tilingDtildeEtaAt (t : DominoTiling) (m k w low : ℕ)
    (s : WalkPath) (n : ℕ) : Prop :=
  (tilingVOneBases t m s n).card = k ∧
    (∀ b, IsTilingBase t b →
      tilingVOneAt t m s n b ∨
        tilingVTwoAt t (shellZeroSourceTotalWindow m w) s n b ∨
        tilingVTwoAt t (shellZeroReplacementTotalWindow m w) s n b ∨
        tilingVThreeAt t m low s n b) ∧
    localTime s n (s n) = m ∧
    tilingVOneAt t m s n (tilingBase t (s n))

/-! ## The source event and its variable-time trace atoms -/

/-- Literal HLOZ shell-zero source event, with the numerical lower and
external-center cutoffs made explicit. -/
def shellZeroSourceEvent (t : DominoTiling)
    (m k w low externalLow externalHigh cut : ℕ) : Set WalkPath :=
  {s | ReachesThreshold s m k ∧
    let n := creationTimeNat m k s
    tilingDEtaAt t m k w low s n ∧
      tilingThetaBases t m w externalLow externalHigh s n = ∅ ∧
      cut < (tilingVTwoBases t (shellZeroSourceTotalWindow m w) s n).card}

/-- The exact-`r` slice of the shell-zero source event.  HLOZ applies the
central-count replacement separately on each such slice. -/
def shellZeroExactSourceEvent (t : DominoTiling)
    (m k w low externalLow externalHigh r : ℕ) : Set WalkPath :=
  {s | ReachesThreshold s m k ∧
    let n := creationTimeNat m k s
    tilingDEtaAt t m k w low s n ∧
      tilingThetaBases t m w externalLow externalHigh s n = ∅ ∧
      (tilingVTwoBases t (shellZeroSourceTotalWindow m w) s n).card = r}

/-- The large shell-zero source is the union of its exact selected-count
slices. -/
theorem shellZeroSourceEvent_eq_iUnion_exact (t : DominoTiling)
    (m k w low externalLow externalHigh cut : ℕ) :
    shellZeroSourceEvent t m k w low externalLow externalHigh cut =
      ⋃ r : {r : ℕ // cut < r},
        shellZeroExactSourceEvent t m k w low externalLow externalHigh r := by
  ext s
  simp only [shellZeroSourceEvent, shellZeroExactSourceEvent,
    Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨hreach, hD, htheta, hcut⟩
    exact ⟨⟨(tilingVTwoBases t (shellZeroSourceTotalWindow m w) s
      (creationTimeNat m k s)).card, hcut⟩, hreach, hD, htheta, rfl⟩
  · rintro ⟨⟨r, hr⟩, hreach, hD, htheta, hcard⟩
    exact ⟨hreach, hD, htheta, hcard.symm ▸ hr⟩

/-- One `D_η ∩ {Theta_η = ∅}` source atom, indexed only by the
statefully retained external word.  Physical creation time remains free. -/
def shellZeroSourceTraceAtom (t : DominoTiling)
    (m k w low externalLow externalHigh cut : ℕ)
    (eta : TilingExternalWordCode t) : Set WalkPath :=
  shellZeroSourceEvent t m k w low externalLow externalHigh cut ∩
    {s | tilingCreationExternalCode t m k s = eta}

/-- Exact-`r` retained-trace atom. -/
def shellZeroExactSourceTraceAtom (t : DominoTiling)
    (m k w low externalLow externalHigh r : ℕ)
    (eta : TilingExternalWordCode t) : Set WalkPath :=
  shellZeroExactSourceEvent t m k w low externalLow externalHigh r ∩
    {s | tilingCreationExternalCode t m k s = eta}

theorem shellZeroSourceTraceAtom_subset (t : DominoTiling)
    (m k w low externalLow externalHigh cut : ℕ)
    (eta : TilingExternalWordCode t) :
    shellZeroSourceTraceAtom t m k w low externalLow externalHigh cut eta ⊆
      shellZeroSourceEvent t m k w low externalLow externalHigh cut :=
  inter_subset_left

/-- The exact source coverage by countably many retained external traces. -/
theorem iUnion_shellZeroSourceTraceAtom (t : DominoTiling)
    (m k w low externalLow externalHigh cut : ℕ) :
    (⋃ eta : TilingExternalWordCode t,
        shellZeroSourceTraceAtom t m k w low externalLow externalHigh cut eta) =
      shellZeroSourceEvent t m k w low externalLow externalHigh cut := by
  ext s
  simp only [Set.mem_iUnion, shellZeroSourceTraceAtom, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨eta, hs, _⟩
    exact hs
  · intro hs
    exact ⟨tilingCreationExternalCode t m k s, hs, rfl⟩

/-- Exact source coverage at fixed `r`, the granularity at which the central
replacement count and new creation rank are constant. -/
theorem iUnion_shellZeroExactSourceTraceAtom (t : DominoTiling)
    (m k w low externalLow externalHigh r : ℕ) :
    (⋃ eta : TilingExternalWordCode t,
        shellZeroExactSourceTraceAtom t m k w low externalLow externalHigh
          r eta) =
      shellZeroExactSourceEvent t m k w low externalLow externalHigh r := by
  ext s
  simp only [Set.mem_iUnion, shellZeroExactSourceTraceAtom,
    Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨eta, hs, _⟩
    exact hs
  · intro hs
    exact ⟨tilingCreationExternalCode t m k s, hs, rfl⟩

/-! ## Exact fixed-count coordinate predicates -/

/-- The exact source slice: exactly `total` coordinates lie in `I₀∪I₁`
and all of them lie in the source window `I₁`. -/
def exactAllSourceCount
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*}
    (source replacement : ∀ c, State c → Prop)
    [∀ c, DecidablePred (source c)] [∀ c, DecidablePred (replacement c)]
    (total : ℕ) (ell : ∀ c, State c) : Prop :=
  (pairSupport source replacement ell).card = total ∧
    upperCount source ell = total

/-- The fixed central replacement slice.  In HLOZ the chosen number is
`floor(C/(1+C) * total)`; keeping it explicit separates path semantics from
the numerical choice. -/
def exactCentralSourceCount
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*}
    (source replacement : ∀ c, State c → Prop)
    [∀ c, DecidablePred (source c)] [∀ c, DecidablePred (replacement c)]
    (total central : ℕ) (ell : ∀ c, State c) : Prop :=
  (pairSupport source replacement ell).card = total ∧
    upperCount source ell = central

/-- Number of new level-`m` dominoes produced by replacing a total of
`total` source coordinates while retaining `central` of them in `I₁`. -/
def replacementNewCount (total central : ℕ) : ℕ := total - central

/-- The creation rank forced by a rank-`k` source and a fixed central
replacement count. -/
def replacementCreationRank (k total central : ℕ) : ℕ :=
  k + replacementNewCount total central

theorem exactAllSourceCount_pairSupport_card
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*}
    (source replacement : ∀ c, State c → Prop)
    [∀ c, DecidablePred (source c)] [∀ c, DecidablePred (replacement c)]
    {total : ℕ} {ell : ∀ c, State c}
    (h : exactAllSourceCount source replacement total ell) :
    (pairSupport source replacement ell).card = total := h.1

theorem exactCentralSourceCount_newCount
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*}
    (source replacement : ∀ c, State c → Prop)
    [∀ c, DecidablePred (source c)] [∀ c, DecidablePred (replacement c)]
    {total central : ℕ} {ell : ∀ c, State c}
    (hdisjoint : ∀ c v, ¬(source c v ∧ replacement c v))
    (h : exactCentralSourceCount source replacement total central ell) :
    (pairSupport source replacement ell).card - upperCount source ell =
      replacementNewCount total central := by
  rw [h.1, h.2]
  rfl

/-! ## Literal `I₁/I₀` predicates on all-six away-domino totals -/

/-- The inserted lazy-count window corresponding to HLOZ's `I₁` after
translation by the retained external count at the base site. -/
def tilingShellZeroSourceCoordinate
    {i cap m w : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (b : TilingAwayDomino t x r D) (v : Fin (upper b)) : Prop :=
  (v : ℕ) ∈ shellZeroSourceFailureWindow m w
    (Fintype.card (TilingCoordinatesAt t x r b.1))

/-- The artificial inserted lazy-count window corresponding to HLOZ's `I₀`
after translation by the retained external count at the base site. -/
def tilingShellZeroReplacementCoordinate
    {i cap m w : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (b : TilingAwayDomino t x r D) (v : Fin (upper b)) : Prop :=
  (v : ℕ) ∈ shellZeroReplacementFailureWindow m w
    (Fintype.card (TilingCoordinatesAt t x r b.1))

/-- Exact-`total`, all-`I₁` source predicate on the away-total vector. -/
def tilingExactAllSourceCount
    {i cap m w : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (total : ℕ)
    (ell : TruncatedTotals upper) : Prop := by
  classical
  exact exactAllSourceCount
      (tilingShellZeroSourceCoordinate (cap := cap) (m := m) (w := w)
        t x r D upper)
      (tilingShellZeroReplacementCoordinate (cap := cap) (m := m) (w := w)
        t x r D upper) total ell

/-- Exact-`total` replacement predicate with exactly `central` coordinates
left in `I₁` and the other selected coordinates moved to `I₀`. -/
def tilingExactCentralSourceCount
    {i cap m w : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (total central : ℕ)
    (ell : TruncatedTotals upper) : Prop := by
  classical
  exact exactCentralSourceCount
      (tilingShellZeroSourceCoordinate (cap := cap) (m := m) (w := w)
        t x r D upper)
      (tilingShellZeroReplacementCoordinate (cap := cap) (m := m) (w := w)
        t x r D upper) total central ell

theorem tilingShellZeroCoordinate_disjoint
    {i cap m w : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (htranslate : ∀ b : TilingAwayDomino t x r D,
      Fintype.card (TilingCoordinatesAt t x r b.1) ≤ m - w + 1) :
    ∀ b v, ¬(tilingShellZeroSourceCoordinate (cap := cap)
        (m := m) (w := w) t x r D upper b v ∧
      tilingShellZeroReplacementCoordinate (cap := cap)
        (m := m) (w := w) t x r D upper b v) := by
  intro b v h
  exact Finset.disjoint_left.mp
    (shellZeroFailureWindows_disjoint (htranslate b)) h.1 h.2

/-! ## The fixed-central-count replacement event -/

/-- HLOZ's `B_eta` at fixed source count `total` and fixed retained source
count `central`.  The new threshold rank is therefore
`k + total - central`. -/
def shellZeroReplacementTraceAtom (t : DominoTiling)
    (m k w low externalLow externalHigh total central : ℕ)
    (eta : TilingExternalWordCode t) : Set WalkPath :=
  let rank := replacementCreationRank k total central
  {s | ReachesThreshold s m rank ∧
    let n := creationTimeNat m rank s
    tilingDtildeEtaAt t m k w low s n ∧
      tilingThetaBases t m w externalLow externalHigh s n = ∅ ∧
      (tilingVTwoBases t (shellZeroSourceTotalWindow m w) s n).card =
        central ∧
      (tilingVTwoBases t (shellZeroReplacementTotalWindow m w) s n).card =
        total - central ∧
      fixedTilingExternalWordCode t n s = eta}

theorem shellZeroReplacementTraceAtom_creation
    {t : DominoTiling} {m k w low externalLow externalHigh total central : ℕ}
    {eta : TilingExternalWordCode t} {s : WalkPath}
    (hs : s ∈ shellZeroReplacementTraceAtom t m k w low externalLow
      externalHigh total central eta) :
    ThresholdCreation s m (replacementCreationRank k total central)
      (creationTimeNat m (replacementCreationRank k total central) s) := by
  simpa only [creationTimeNat, hs.1, dif_pos] using
    (thresholdCreation_natFind hs.1)

theorem shellZeroReplacementTraceAtom_trace
    {t : DominoTiling} {m k w low externalLow externalHigh total central : ℕ}
    {eta : TilingExternalWordCode t} {s : WalkPath}
    (hs : s ∈ shellZeroReplacementTraceAtom t m k w low externalLow
      externalHigh total central eta) :
    fixedTilingExternalWordCode t
        (creationTimeNat m (replacementCreationRank k total central) s) s =
      eta := by
  exact hs.2.2.2.2.2

lemma thresholdCount_pred_eq_of_creation
    {s : WalkPath} {m rank n : ℕ} (hm : 1 < m) (hrank : 0 < rank)
    (h : ThresholdCreation s m rank n) :
    thresholdCount s (n - 1) m = rank - 1 := by
  have hzero : thresholdCount s 0 m = 0 := by
    rw [thresholdCount_eq_zero_iff_forall_lt s 0 m (by omega)]
    intro x
    exact (localTime_le_time_add_one s 0 x).trans_lt (by omega)
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have := h.1
    rw [hn0, hzero] at this
    omega
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hprev : thresholdCount s q m < rank := h.2 q (Nat.lt_succ_self q)
  have hat : thresholdCount s (q + 1) m = rank :=
    thresholdCount_eq_of_creation hrank h
  have hstep := thresholdCount_succ_le s q m
  change thresholdCount s q m = rank - 1
  omega

/-- At fixed `total`, all replacement atoms have the same newly-created
rank, while their physical creation time remains path-dependent. -/
def shellZeroVariableClockJump (t : DominoTiling)
    (m k w low externalLow externalHigh total central : ℕ)
    (hm : 1 < m)
    (hrank : 0 < replacementCreationRank k total central) :
    VariableClockThresholdJumpReplacementFamily
      (shellZeroReplacementTraceAtom t m k w low externalLow externalHigh
        total central) where
  clock := fun _ s ↦
    creationTimeNat m (replacementCreationRank k total central) s
  traceAt := fun s n ↦ fixedTilingExternalWordCode t n s
  thresholdCount := fun s n ↦ thresholdCount s n m
  monotone_thresholdCount := fun s ↦ thresholdCount_mono_time s m
  rank := replacementCreationRank k total central - 1
  trace_eq := fun _ _ hs ↦ shellZeroReplacementTraceAtom_trace hs
  count_before := fun _ _ hs ↦
    thresholdCount_pred_eq_of_creation hm hrank
      (shellZeroReplacementTraceAtom_creation hs)
  count_at := by
    intro eta s hs
    have hcreation := shellZeroReplacementTraceAtom_creation hs
    have hcount := thresholdCount_eq_of_creation hrank hcreation
    simpa only [Nat.sub_add_cancel hrank] using hcount

theorem pairwise_disjoint_shellZeroReplacementTraceAtom
    (t : DominoTiling)
    (m k w low externalLow externalHigh total central : ℕ)
    (hm : 1 < m)
    (hrank : 0 < replacementCreationRank k total central) :
    Pairwise fun eta eta' ↦
      Disjoint
        (shellZeroReplacementTraceAtom t m k w low externalLow externalHigh
          total central eta)
        (shellZeroReplacementTraceAtom t m k w low externalLow externalHigh
          total central eta') :=
  pairwise_disjoint_of_variableClockThresholdJump
    (shellZeroVariableClockJump t m k w low externalLow externalHigh
      total central hm hrank)

/-- Source-correct global certificate using the path-dependent threshold
clock. -/
def globalDisjointReplacementCertificateOfVariableClockJump
    {Omega Index : Type*} [MeasurableSpace Omega] [Countable Index]
    (mu : Measure Omega) (source : Set Omega) (q : ℝ≥0∞)
    (sourceAtom replacement : Index → Set Omega)
    (hsource : source ⊆ ⋃ z, sourceAtom z)
    (hatom : ∀ z, mu (sourceAtom z) ≤ q * mu (replacement z))
    (hmeasurable : ∀ z, MeasurableSet (replacement z))
    (jump : VariableClockThresholdJumpReplacementFamily replacement) :
    GlobalDisjointReplacementCertificate
      (Index := Index) mu source q where
  sourceAtom := sourceAtom
  replacement := replacement
  source_subset := hsource
  atom_le := hatom
  measurable_replacement := hmeasurable
  disjoint_replacement := pairwise_disjoint_of_variableClockThresholdJump jump

end

end Erdos1165.TilingShellZeroSourcePartition
