/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZFilteredSourceCorrectBandProductClosure
import ErdosProblems.Erdos1165.HLOZTraceCappedProductScreening
import ErdosProblems.Erdos1165.HLOZTilingGapBandExtraction

/-!
# The source-side `D_eta` / `Theta_eta` split

Proposition 4.5 controls an external/lazy imbalance only after the old
creation clock has been fixed.  It does not imply the deterministic
`D_eta` classification, and it does not turn a shell defined using the local
time of one endpoint into a shell defined using a domino total.  This file
keeps those mechanisms separate.

The `Theta` failure is enumerated by the finitely many visited domino bases
at the old creation clock.  The resulting lower/upper slot events are literal
path events.  A family of stopped-coordinate trace screens for those events
constructs the actual `GeometricBalanceLaw`; no probability bound for the
union is assumed.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZThetaSourceBalance

open Balancedness GeometricChernoff HLOZGapEstimate HLOZPathEvents
open HLOZThresholdedShellScreening HLOZTraceCappedProductScreening
open HLOZGapRandomClockScreen HLOZTilingGapBandExtraction
open HLOZTilingGapRandomClockScreen
open HLOZProposition48Candidates
open LazyDecomposition
open HLOZShellZeroReplacementWindows
open ScreeningInstantiation TilingLazyDecomposition
open TilingShellZeroLiteralScreen TilingShellZeroSourcePartition
open TilingOrientedShellZeroSourcePartition
open HLOZSourceOrientedExternalLocalTime
open SpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev DominoTiling := Tilings.Tiling

/-! ## Finite-prefix versions of the source predicates -/

def prefixVisitedTilingBases {n : ℕ} (t : DominoTiling)
    (u : Fin (n + 1) → Point) : Finset Point :=
  (visitedPrefix u).image (tilingBase t)

def prefixTilingDominoLocalTime {n : ℕ} (t : DominoTiling)
    (u : Fin (n + 1) → Point) (b : Point) : ℕ :=
  localTimePrefix u b + localTimePrefix u (tilingPartner t b)

def prefixTilingExternalBaseLocalTime {n : ℕ} (t : DominoTiling)
    (u : Fin (n + 1) → Point) (b : Point) : ℕ :=
  LazyDecomposition.listLocalTime
    (tilingExternalPath t (LazyDecomposition.finitePathList u)) b

def prefixTilingVOneAt {n : ℕ} (t : DominoTiling) (m : ℕ)
    (u : Fin (n + 1) → Point) (b : Point) : Prop :=
  (localTimePrefix u b = m ∧ localTimePrefix u (tilingPartner t b) < m) ∨
    (localTimePrefix u (tilingPartner t b) = m ∧ localTimePrefix u b < m)

def prefixTilingVTwoAt {n : ℕ} (t : DominoTiling) (window : Finset ℕ)
    (u : Fin (n + 1) → Point) (b : Point) : Prop :=
  localTimePrefix u (tilingPartner t b) ≤ localTimePrefix u b ∧
    localTimePrefix u b ∈ window

def prefixTilingVThreeAt {n : ℕ} (t : DominoTiling) (m low : ℕ)
    (u : Fin (n + 1) → Point) (b : Point) : Prop :=
  localTimePrefix u b ≤ low ∨
    (localTimePrefix u b < localTimePrefix u (tilingPartner t b) ∧
      localTimePrefix u (tilingPartner t b) < m)

def prefixTilingVOneBases {n : ℕ} (t : DominoTiling) (m : ℕ)
    (u : Fin (n + 1) → Point) : Finset Point := by
  classical
  exact (prefixVisitedTilingBases t u).filter (prefixTilingVOneAt t m u)

def prefixTilingVTwoBases {n : ℕ} (t : DominoTiling) (window : Finset ℕ)
    (u : Fin (n + 1) → Point) : Finset Point := by
  classical
  exact (prefixVisitedTilingBases t u).filter (prefixTilingVTwoAt t window u)

def prefixTilingThetaBases {n : ℕ} (t : DominoTiling)
    (m w externalLow externalHigh : ℕ)
  (u : Fin (n + 1) → Point) : Finset Point :=
  (prefixVisitedTilingBases t u).filter fun b ↦
    localTimePrefix u (tilingPartner t b) ≤ localTimePrefix u b ∧
      localTimePrefix u b ∈
        (HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w ∪
          HLOZShellZeroReplacementWindows.shellZeroReplacementTotalWindow m w) ∧
      ¬(externalLow ≤ prefixTilingExternalBaseLocalTime t u b ∧
        prefixTilingExternalBaseLocalTime t u b < externalHigh)

/-- Prefix version of the `V₂`-restricted shell screen. -/
abbrev prefixTilingRestrictedThetaBases {n : ℕ} (t : DominoTiling)
    (m w externalLow externalHigh : ℕ)
    (u : Fin (n + 1) → Point) : Finset Point :=
  prefixTilingThetaBases t m w externalLow externalHigh u

/-- Prefix version of the paper's global (non-dominance-restricted)
`Theta_η`. -/
def prefixTilingGlobalThetaBases {n : ℕ} (t : DominoTiling)
    (m w externalLow externalHigh : ℕ)
    (u : Fin (n + 1) → Point) : Finset Point :=
  (prefixVisitedTilingBases t u).filter fun b ↦
    localTimePrefix u b ∈
        (HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w ∪
          HLOZShellZeroReplacementWindows.shellZeroReplacementTotalWindow m w) ∧
      ¬(externalLow ≤ prefixTilingExternalBaseLocalTime t u b ∧
        prefixTilingExternalBaseLocalTime t u b < externalHigh)

def prefixTilingDEtaAt {n : ℕ} (t : DominoTiling) (m k w low : ℕ)
    (u : Fin (n + 1) → Point) : Prop :=
  (prefixTilingVOneBases t m u).card = k ∧
    (∀ b, IsTilingBase t b →
      prefixTilingVOneAt t m u b ∨
        prefixTilingVTwoAt t
          (HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w) u b ∨
        prefixTilingVThreeAt t m low u b) ∧
    localTimePrefix u (u ⟨n, by omega⟩) = m

@[simp] theorem prefixTilingThetaBases_pathPrefix
    (t : DominoTiling) (m w externalLow externalHigh n : ℕ)
    (s : WalkPath) :
    prefixTilingThetaBases t m w externalLow externalHigh (pathPrefix s n) =
      tilingThetaBases t m w externalLow externalHigh s n := by
  rfl

@[simp] theorem prefixTilingGlobalThetaBases_pathPrefix
    (t : DominoTiling) (m w externalLow externalHigh n : ℕ)
    (s : WalkPath) :
    prefixTilingGlobalThetaBases t m w externalLow externalHigh
        (pathPrefix s n) =
      tilingGlobalThetaBases t m w externalLow externalHigh s n := by
  rfl

@[simp] theorem prefixTilingDEtaAt_pathPrefix
    (t : DominoTiling) (m k w low n : ℕ) (s : WalkPath) :
    prefixTilingDEtaAt t m k w low (pathPrefix s n) ↔
      tilingDEtaAt t m k w low s n := by
  rfl

@[simp] theorem prefixTilingVTwoBases_pathPrefix
    (t : DominoTiling) (window : Finset ℕ) (n : ℕ) (s : WalkPath) :
    prefixTilingVTwoBases t window (pathPrefix s n) =
      tilingVTwoBases t window s n := by
  rfl

theorem measurable_fixedTilingThetaBases
    (t : DominoTiling) (m w externalLow externalHigh n : ℕ) :
    Measurable fun s : WalkPath ↦
      tilingThetaBases t m w externalLow externalHigh s n := by
  change Measurable
    ((prefixTilingThetaBases t m w externalLow externalHigh) ∘ pathPrefix (n := n))
  exact (measurable_of_countable _).comp (measurable_pathPrefix n)

theorem measurable_fixedTilingGlobalThetaBases
    (t : DominoTiling) (m w externalLow externalHigh n : ℕ) :
    Measurable fun s : WalkPath ↦
      tilingGlobalThetaBases t m w externalLow externalHigh s n := by
  change Measurable
    ((prefixTilingGlobalThetaBases t m w externalLow externalHigh) ∘
      pathPrefix (n := n))
  exact (measurable_of_countable _).comp (measurable_pathPrefix n)

theorem measurable_fixedTilingDEtaFlag
    (t : DominoTiling) (m k w low n : ℕ) :
    Measurable fun s : WalkPath ↦ decide (tilingDEtaAt t m k w low s n) := by
  change Measurable
    ((fun u : Fin (n + 1) → Point ↦
      decide (prefixTilingDEtaAt t m k w low u)) ∘ pathPrefix (n := n))
  exact (measurable_of_countable _).comp (measurable_pathPrefix n)

theorem measurable_fixedTilingVTwoBases
    (t : DominoTiling) (window : Finset ℕ) (n : ℕ) :
    Measurable fun s : WalkPath ↦ tilingVTwoBases t window s n := by
  change Measurable
    ((prefixTilingVTwoBases t window) ∘ pathPrefix (n := n))
  exact (measurable_of_countable _).comp (measurable_pathPrefix n)

/-! ## Genuine creation-clock source events -/

def tilingThetaAtCreation (t : DominoTiling)
    (m k w externalLow externalHigh : ℕ) (s : WalkPath) : Finset Point :=
  tilingThetaBases t m w externalLow externalHigh s (creationTimeNat m k s)

/-- Creation-clock global `Theta_η`, kept separate from the legacy
`V₂`-restricted `tilingThetaAtCreation`. -/
def tilingGlobalThetaAtCreation (t : DominoTiling)
    (m k w externalLow externalHigh : ℕ) (s : WalkPath) : Finset Point :=
  tilingGlobalThetaBases t m w externalLow externalHigh s
    (creationTimeNat m k s)

def tilingDEtaAtCreation (t : DominoTiling) (m k w low : ℕ)
    (s : WalkPath) : Prop :=
  tilingDEtaAt t m k w low s (creationTimeNat m k s)

def tilingVTwoAtCreation (t : DominoTiling) (m k w : ℕ)
    (s : WalkPath) : Finset Point :=
  tilingVTwoBases t
    (HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w) s
    (creationTimeNat m k s)

theorem measurable_tilingThetaAtCreation
    (t : DominoTiling) (m k w externalLow externalHigh : ℕ) :
    Measurable (tilingThetaAtCreation t m k w externalLow externalHigh) := by
  exact measurable_natIndexed (creationTimeNat m k)
    (measurable_creationTimeNat m k)
    (fun n s ↦ tilingThetaBases t m w externalLow externalHigh s n)
    (measurable_fixedTilingThetaBases t m w externalLow externalHigh)

theorem measurable_tilingGlobalThetaAtCreation
    (t : DominoTiling) (m k w externalLow externalHigh : ℕ) :
    Measurable
      (tilingGlobalThetaAtCreation t m k w externalLow externalHigh) := by
  exact measurable_natIndexed (creationTimeNat m k)
    (measurable_creationTimeNat m k)
    (fun n s ↦ tilingGlobalThetaBases t m w externalLow externalHigh s n)
    (measurable_fixedTilingGlobalThetaBases t m w externalLow externalHigh)

theorem tilingThetaAtCreation_subset_global
    (t : DominoTiling) (m k w externalLow externalHigh : ℕ)
    (s : WalkPath) :
    tilingThetaAtCreation t m k w externalLow externalHigh s ⊆
      tilingGlobalThetaAtCreation t m k w externalLow externalHigh s :=
  tilingRestrictedThetaBases_subset_global t m w externalLow externalHigh s
    (creationTimeNat m k s)

theorem measurable_tilingDEtaAtCreationFlag
    (t : DominoTiling) (m k w low : ℕ) :
    Measurable fun s : WalkPath ↦ decide (tilingDEtaAtCreation t m k w low s) := by
  exact measurable_natIndexed (creationTimeNat m k)
    (measurable_creationTimeNat m k)
    (fun n s ↦ decide (tilingDEtaAt t m k w low s n))
    (measurable_fixedTilingDEtaFlag t m k w low)

theorem measurable_tilingVTwoAtCreation
    (t : DominoTiling) (m k w : ℕ) :
    Measurable (tilingVTwoAtCreation t m k w) := by
  exact measurable_natIndexed (creationTimeNat m k)
    (measurable_creationTimeNat m k)
    (fun n s ↦ tilingVTwoBases t
      (HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w) s n)
    (measurable_fixedTilingVTwoBases t
      (HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w))

/-! ## Deterministic construction of `D_eta` -/

/-- No two different level-`m` sites at the old clock occupy one tiling
domino.  This is the clock-local form of `Pi_m^k`. -/
def TilingThresholdDominoSeparated (t : DominoTiling)
    (s : WalkPath) (n m : ℕ) : Prop :=
  ∀ x ∈ thresholdSites s n m, ∀ y ∈ thresholdSites s n m,
    x ≠ y → ¬Tilings.sameDomino t x y

private theorem tilingVOneBases_eq_thresholdBaseImage
    {t : DominoTiling} {s : WalkPath} {n m : ℕ}
    (hm : 0 < m) (hmax : ∀ y, localTime s n y ≤ m)
    (hsep : TilingThresholdDominoSeparated t s n m) :
    tilingVOneBases t m s n =
      (thresholdSites s n m).image (tilingBase t) := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨hbvisited, hbV⟩ := Finset.mem_filter.mp hb
    obtain ⟨z, hzvisited, hzbase⟩ := Finset.mem_image.mp hbvisited
    have hbase : tilingBase t b = b := by
      rw [← hzbase, TilingSpatialInsertionFiber.tilingBase_idem]
    rw [Finset.mem_image]
    rcases hbV with hbV | hbV
    · refine ⟨b, (mem_thresholdSites_iff s n m b hm).mpr ?_, hbase⟩
      exact hbV.1.ge
    · let y := tilingPartner t b
      refine ⟨y, (mem_thresholdSites_iff s n m y hm).mpr hbV.1.ge, ?_⟩
      exact (tilingBase_partner t b).trans hbase
  · intro hb
    obtain ⟨x, hxthreshold, hxb⟩ := Finset.mem_image.mp hb
    have hxlevel : localTime s n x = m := by
      apply Nat.le_antisymm (hmax x)
      exact (mem_thresholdSites_iff s n m x hm).mp hxthreshold
    have hpartnerNot : tilingPartner t x ∉ thresholdSites s n m := by
      intro hp
      exact hsep x hxthreshold (tilingPartner t x) hp
        (tilingPartner_ne t x).symm
        ((sameDomino_iff_partner_eq t x (tilingPartner t x)).2 rfl)
    have hpartnerLt : localTime s n (tilingPartner t x) < m := by
      by_contra hnot
      exact hpartnerNot ((mem_thresholdSites_iff s n m _ hm).mpr
        (Nat.le_of_not_gt hnot))
    have hbvisited : b ∈ visitedTilingBases t s n := by
      rw [visitedTilingBases, Finset.mem_image]
      exact ⟨x, (Finset.mem_filter.mp hxthreshold).1, hxb⟩
    change b ∈ (visitedTilingBases t s n).filter (tilingVOneAt t m s n)
    rw [Finset.mem_filter]
    refine ⟨hbvisited, ?_⟩
    rcases point_eq_tilingBase_or_partner_base t x with hxbase | hxpartner
    · left
      subst b
      rw [← hxbase]
      exact ⟨hxlevel, hpartnerLt⟩
    · right
      have hbEq : b = tilingPartner t x := by
        have hxpartner' : tilingPartner t x = tilingBase t x := by
          exact (congrArg (tilingPartner t) hxpartner).trans
            (tilingPartner_partner t (tilingBase t x))
        exact hxb.symm.trans hxpartner'.symm
      have hpartnerB : tilingPartner t b = x := by
        rw [hbEq, tilingPartner_partner]
      simpa only [hbEq, tilingPartner_partner] using And.intro hxlevel hpartnerLt

/-- The deterministic `D_eta` lemma used before Proposition 4.5.  The only
inputs are the genuine old creation, absence of level `m+1`, clock-local
domino separation, and the literal lower cutoff `low = m-w`. -/
theorem tilingDEtaAt_of_creation_of_dominoSeparated
    {t : DominoTiling} {s : WalkPath} {m k w low n : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hlow : low = m - w)
    (hcreation : ThresholdCreation s m k n)
    (hnext : thresholdCount s n (m + 1) = 0)
    (hsep : TilingThresholdDominoSeparated t s n m) :
    tilingDEtaAt t m k w low s n := by
  have hmaxLt : ∀ y, localTime s n y < m + 1 :=
    (thresholdCount_eq_zero_iff_forall_lt s n (m + 1)
      (Nat.zero_lt_succ m)).mp hnext
  have hmax : ∀ y, localTime s n y ≤ m := fun y ↦ Nat.lt_succ_iff.mp (hmaxLt y)
  have hcard : (tilingVOneBases t m s n).card = k := by
    rw [tilingVOneBases_eq_thresholdBaseImage hm hmax hsep]
    rw [Finset.card_image_iff.mpr]
    · exact thresholdCount_eq_of_creation hk hcreation
    · intro x hx y hy hbase
      by_contra hxy
      have hdom : Tilings.sameDomino t x y :=
        Or.resolve_left ((tilingBase_eq_iff t x y).mp hbase) hxy
      exact hsep x hx y hy hxy
        hdom
  have hterminal : localTime s n (s n) = m := by
    apply Nat.le_antisymm (hmax (s n))
    exact (mem_thresholdSites_iff s n m (s n) hm).mp
      (position_mem_thresholdSites_of_creation hk hcreation)
  refine ⟨hcard, ?_, hterminal⟩
  intro b hbbase
  have hbmax := hmax b
  have hpmax := hmax (tilingPartner t b)
  by_cases hbLevel : localTime s n b = m
  · by_cases hpLevel : localTime s n (tilingPartner t b) = m
    · have hbThreshold : b ∈ thresholdSites s n m :=
        (mem_thresholdSites_iff s n m b hm).mpr hbLevel.ge
      have hpThreshold : tilingPartner t b ∈ thresholdSites s n m :=
        (mem_thresholdSites_iff s n m (tilingPartner t b) hm).mpr hpLevel.ge
      exact False.elim (hsep b hbThreshold (tilingPartner t b) hpThreshold
        (tilingPartner_ne t b).symm
        ((sameDomino_iff_partner_eq t b (tilingPartner t b)).2 rfl))
    · left; left
      exact ⟨hbLevel, lt_of_le_of_ne hpmax hpLevel⟩
  · by_cases hpLevel : localTime s n (tilingPartner t b) = m
    · left; right
      exact ⟨hpLevel, lt_of_le_of_ne hbmax hbLevel⟩
    · have hbLt : localTime s n b < m := lt_of_le_of_ne hbmax hbLevel
      have hpLt : localTime s n (tilingPartner t b) < m :=
        lt_of_le_of_ne hpmax hpLevel
      by_cases hblow : localTime s n b ≤ low
      · right; right; left; exact hblow
      by_cases hdominant : localTime s n (tilingPartner t b) ≤ localTime s n b
      · right; left
        refine ⟨hdominant, ?_⟩
        rw [HLOZShellZeroReplacementWindows.mem_shellZeroSourceTotalWindow]
        omega
      · right; right; right
        exact ⟨Nat.lt_of_not_ge hdominant, hpLt⟩

theorem tilingDEtaAtCreation_of_creation_of_dominoSeparated
    {t : DominoTiling} {s : WalkPath} {m k w low n : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hlow : low = m - w)
    (hcreation : ThresholdCreation s m k n)
    (hnext : thresholdCount s n (m + 1) = 0)
    (hsep : TilingThresholdDominoSeparated t s n m) :
    tilingDEtaAtCreation t m k w low s := by
  rw [tilingDEtaAtCreation, creationTimeNat_eq_of_creation hcreation]
  exact tilingDEtaAt_of_creation_of_dominoSeparated hm hk hlow hcreation hnext hsep

/-! ## Dominant endpoint normalization and the two parity classes -/

/-- Choose the endpoint attaining `xi⁺`.  This is a stopped-prefix
operation; unlike `tilingBase`, it is allowed to choose the other endpoint
when the canonical base is not dominant. -/
def tilingDominantEndpointAt (t : DominoTiling) (s : WalkPath) (n : ℕ)
    (x : Point) : Point :=
  if localTime s n (tilingPartner t x) ≤ localTime s n x then x
  else tilingPartner t x

theorem tilingDominantEndpointAt_eq_self_or_partner
    (t : DominoTiling) (s : WalkPath) (n : ℕ) (x : Point) :
    tilingDominantEndpointAt t s n x = x ∨
      tilingDominantEndpointAt t s n x = tilingPartner t x := by
  unfold tilingDominantEndpointAt
  split_ifs <;> simp

theorem tilingDominantEndpointAt_partner_le
    (t : DominoTiling) (s : WalkPath) (n : ℕ) (x : Point) :
    localTime s n (tilingPartner t (tilingDominantEndpointAt t s n x)) ≤
      localTime s n (tilingDominantEndpointAt t s n x) := by
  unfold tilingDominantEndpointAt
  split_ifs with h
  · exact h
  · rw [tilingPartner_partner]
    exact Nat.le_of_lt (Nat.lt_of_not_ge h)

theorem tilingXiPlusAt_dominantEndpoint
    (t : DominoTiling) (s : WalkPath) (n : ℕ) (x : Point) :
    tilingXiPlusAt t s n (tilingDominantEndpointAt t s n x) =
      tilingXiPlusAt t s n x := by
  rcases tilingDominantEndpointAt_eq_self_or_partner t s n x with h | h
  · rw [h]
  · rw [h]
    simp only [tilingXiPlusAt, tilingPartner_partner, max_comm]

/-- Canonicalization really lands at the designated base endpoint.  This is
kept public because the source split must distinguish a genuine `V₂` base
from the opposite, dominant endpoint of the same domino. -/
theorem isTilingBase_tilingBase (t : DominoTiling) (x : Point) :
    IsTilingBase t (tilingBase t x) := by
  by_contra h
  have hfix := TilingSpatialInsertionFiber.tilingBase_idem t x
  rw [tilingBase, if_neg h] at hfix
  cases t with
  | checker d =>
      fin_cases d <;>
        simp [unshift, tilingDisplacement, Tilings.directionVector] at hfix
      all_goals
        have hfst := congrArg Prod.fst hfix
        have hsnd := congrArg Prod.snd hfix
        omega
  | evenColumns =>
      simp [unshift, tilingDisplacement] at hfix
      have hfst := congrArg Prod.fst hfix
      omega
  | oddColumns =>
      simp [unshift, tilingDisplacement] at hfix
      have hfst := congrArg Prod.fst hfix
      omega

theorem not_isTilingBase_tilingPartner_of_isTilingBase
    (t : DominoTiling) (x : Point) (hx : IsTilingBase t x) :
    ¬ IsTilingBase t (tilingPartner t x) := by
  cases t with
  | checker d =>
      have hpar := Tilings.checkerEven_shift_direction_eq_false x d hx
      rw [tilingPartner, if_pos hx]
      change ¬Tilings.checkerEven (Tilings.shift x (Tilings.directionVector d)) = true
      intro heq
      rw [hpar] at heq
      contradiction
  | evenColumns =>
      rcases x with ⟨x₁, x₂⟩
      simp_all [tilingPartner, IsTilingBase, tilingDisplacement,
        Tilings.columnEven, Tilings.shift]
      omega
  | oddColumns =>
      rcases x with ⟨x₁, x₂⟩
      simp_all [tilingPartner, IsTilingBase, tilingDisplacement,
        Tilings.columnEven, Tilings.shift]
      omega

theorem isTilingBase_of_mem_visitedTilingBases
    {t : DominoTiling} {s : WalkPath} {n : ℕ} {b : Point}
    (hb : b ∈ visitedTilingBases t s n) : IsTilingBase t b := by
  rw [visitedTilingBases, Finset.mem_image] at hb
  obtain ⟨x, _, rfl⟩ := hb
  exact isTilingBase_tilingBase t x

/-- Any finite raw site family loses at most a factor two when normalized
to its dominant endpoints: each normalized endpoint accounts only for the
two endpoints of its domino.  This is the literal `#M ≤ 2 #M_*` seam. -/
theorem card_le_two_mul_card_image_tilingDominantEndpointAt
    (t : DominoTiling) (s : WalkPath) (n : ℕ) (S : Finset Point) :
    S.card ≤ 2 * (S.image (tilingDominantEndpointAt t s n)).card := by
  classical
  let D := S.image (tilingDominantEndpointAt t s n)
  have hsub : S ⊆ D ∪ D.image (tilingPartner t) := by
    intro x hx
    rcases tilingDominantEndpointAt_eq_self_or_partner t s n x with hdom | hdom
    · rw [Finset.mem_union]
      exact Or.inl (Finset.mem_image.mpr ⟨x, hx, hdom⟩)
    · rw [Finset.mem_union]
      apply Or.inr
      refine Finset.mem_image.mpr ⟨tilingDominantEndpointAt t s n x, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      · rw [hdom, tilingPartner_partner]
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le D (D.image (tilingPartner t))
  have himage := Finset.card_image_le (s := D) (f := tilingPartner t)
  dsimp only [D] at hcard hunion himage ⊢
  omega

/-- The actual near-level base family before choosing the dominant endpoint. -/
noncomputable def tilingNearFavoriteBasesAtCreation
    (t : DominoTiling) (m k w : ℕ) (s : WalkPath) : Finset Point :=
  let n := creationTimeNat m k s
  (visitedTilingBases t s n).filter fun b ↦
    tilingXiPlusAt t s n b ∈
      (HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w ∪
        HLOZShellZeroReplacementWindows.shellZeroReplacementTotalWindow m w)

/-- HLOZ's dominant candidate bases `M_e ∪ M_o`. -/
noncomputable def tilingDominantNearBasesAtCreation
    (t : DominoTiling) (m k w : ℕ) (s : WalkPath) : Finset Point :=
  (tilingNearFavoriteBasesAtCreation t m k w s).image
    (tilingDominantEndpointAt t s (creationTimeNat m k s))

/-- The part of the normalized family whose dominant endpoint is the
canonical base.  This is exactly the part to which the literal same-path
`V₂`/`Theta` source predicate applies. -/
noncomputable def tilingCanonicalDominantNearBasesAtCreation
    (t : DominoTiling) (m k w : ℕ) (s : WalkPath) : Finset Point :=
  (tilingDominantNearBasesAtCreation t m k w s).filter (IsTilingBase t)

/-- The opposite-endpoint part of `M_o`.  It is deliberately not identified
with `tilingVTwoBases t` on the original path: that assertion is false.  Its
source screen has to be pulled back through the paper's one-step shift. -/
noncomputable def tilingOppositeDominantNearEndpointsAtCreation
    (t : DominoTiling) (m k w : ℕ) (s : WalkPath) : Finset Point :=
  (tilingDominantNearBasesAtCreation t m k w s).filter
    (fun x ↦ ¬ IsTilingBase t x)

theorem tilingDominantNearBasesAtCreation_eq_canonical_union_opposite
    (t : DominoTiling) (m k w : ℕ) (s : WalkPath) :
    tilingDominantNearBasesAtCreation t m k w s =
      tilingCanonicalDominantNearBasesAtCreation t m k w s ∪
        tilingOppositeDominantNearEndpointsAtCreation t m k w s := by
  classical
  ext x
  simp only [tilingCanonicalDominantNearBasesAtCreation,
    tilingOppositeDominantNearEndpointsAtCreation, Finset.mem_union,
    Finset.mem_filter]
  by_cases hx : IsTilingBase t x <;> simp [hx]

theorem tilingNearFavoriteBasesAtCreation_card_le_two_spatialSources
    (t : DominoTiling) (m k w : ℕ) (s : WalkPath) :
    (tilingNearFavoriteBasesAtCreation t m k w s).card ≤
      2 * ((tilingCanonicalDominantNearBasesAtCreation t m k w s).card +
        (tilingOppositeDominantNearEndpointsAtCreation t m k w s).card) := by
  have hnormalize := card_le_two_mul_card_image_tilingDominantEndpointAt
    t s (creationTimeNat m k s) (tilingNearFavoriteBasesAtCreation t m k w s)
  have hunion : (tilingDominantNearBasesAtCreation t m k w s).card ≤
      (tilingCanonicalDominantNearBasesAtCreation t m k w s).card +
        (tilingOppositeDominantNearEndpointsAtCreation t m k w s).card := by
    rw [tilingDominantNearBasesAtCreation_eq_canonical_union_opposite]
    exact Finset.card_union_le _ _
  exact hnormalize.trans (Nat.mul_le_mul_left 2 hunion)

/-- The exact integer pigeonhole used after `#M ≤ 2(#M_e+#M_o)`.
The quarter-cut is deliberate: keeping the original cut on either half is
not a valid consequence of the factor-two normalization. -/
theorem quarter_cut_lt_canonical_or_opposite_of_lt_nearFavorite
    (t : DominoTiling) (m k w J : ℕ) (s : WalkPath)
    (hJ : J < (tilingNearFavoriteBasesAtCreation t m k w s).card) :
    J / 4 < (tilingCanonicalDominantNearBasesAtCreation t m k w s).card ∨
      J / 4 <
        (tilingOppositeDominantNearEndpointsAtCreation t m k w s).card := by
  have hbound := tilingNearFavoriteBasesAtCreation_card_le_two_spatialSources
    t m k w s
  by_contra h
  simp only [not_or, not_lt] at h
  have hfour : 4 * (J / 4) ≤ J := Nat.mul_div_le J 4
  omega

/-- The canonical half of the normalized family is literally the union of
the source and replacement `V₂` sets.  The opposite half is intentionally
absent: it must be estimated after the one-step shift, not reinterpreted as
a same-path base set. -/
theorem tilingCanonicalDominantNearBasesAtCreation_eq_vTwo_union
    (t : DominoTiling) (m k w : ℕ) (s : WalkPath) :
    tilingCanonicalDominantNearBasesAtCreation t m k w s =
      tilingVTwoBases t (HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w)
          s (creationTimeNat m k s) ∪
        tilingVTwoBases t (HLOZShellZeroReplacementWindows.shellZeroReplacementTotalWindow m w)
          s (creationTimeNat m k s) := by
  classical
  ext b
  constructor
  · intro hb
    rw [tilingCanonicalDominantNearBasesAtCreation, Finset.mem_filter] at hb
    rcases hb with ⟨hbD, hbbase⟩
    rw [tilingDominantNearBasesAtCreation, Finset.mem_image] at hbD
    obtain ⟨x, hx, hxb⟩ := hbD
    rw [tilingNearFavoriteBasesAtCreation, Finset.mem_filter] at hx
    have hxbase := isTilingBase_of_mem_visitedTilingBases hx.1
    have hxeq : x = b := by
      rcases tilingDominantEndpointAt_eq_self_or_partner t s
          (creationTimeNat m k s) x with hdom | hdom
      · exact hdom.symm.trans hxb
      · exfalso
        apply not_isTilingBase_tilingPartner_of_isTilingBase t x hxbase
        rw [← hdom, hxb]
        exact hbbase
    subst x
    have hdominant := tilingDominantEndpointAt_partner_le t s
      (creationTimeNat m k s) b
    rw [hxb] at hdominant
    have hwindow : localTime s (creationTimeNat m k s) b ∈
        HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w ∪
          HLOZShellZeroReplacementWindows.shellZeroReplacementTotalWindow m w := by
      rw [← tilingXiPlusAt_eq_base_of_partner_le hdominant]
      exact hx.2
    rw [Finset.mem_union] at hwindow ⊢
    rcases hwindow with hsource | hreplacement
    · left
      rw [tilingVTwoBases, Finset.mem_filter]
      exact ⟨hx.1, hdominant, hsource⟩
    · right
      rw [tilingVTwoBases, Finset.mem_filter]
      exact ⟨hx.1, hdominant, hreplacement⟩
  · intro hb
    rw [Finset.mem_union] at hb
    rcases hb with hb | hb
    all_goals
      rw [tilingVTwoBases, Finset.mem_filter] at hb
      rw [tilingCanonicalDominantNearBasesAtCreation, Finset.mem_filter]
      refine ⟨?_, isTilingBase_of_mem_visitedTilingBases hb.1⟩
      rw [tilingDominantNearBasesAtCreation, Finset.mem_image]
      refine ⟨b, ?_, ?_⟩
      · rw [tilingNearFavoriteBasesAtCreation, Finset.mem_filter]
        refine ⟨hb.1, ?_⟩
        rw [tilingXiPlusAt_eq_base_of_partner_le hb.2.1,
          Finset.mem_union]
        first | exact Or.inl hb.2.2 | exact Or.inr hb.2.2
      · unfold tilingDominantEndpointAt
        rw [if_pos hb.2.1]

theorem tilingVTwoReplacementBases_eq_empty_of_thresholdCount_succ_eq_zero
    {t : DominoTiling} {m w n : ℕ} {s : WalkPath}
    (hnext : thresholdCount s n (m + 1) = 0) :
    tilingVTwoBases t
        (HLOZShellZeroReplacementWindows.shellZeroReplacementTotalWindow m w)
        s n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  rw [tilingVTwoBases, Finset.mem_filter] at hb
  have hlt := (thresholdCount_eq_zero_iff_forall_lt s n (m + 1)
    (Nat.zero_lt_succ m)).mp hnext b
  have hge : m + 1 ≤ localTime s n b :=
    (HLOZShellZeroReplacementWindows.mem_shellZeroReplacementTotalWindow.mp
      hb.2.2).1
  omega

theorem tilingCanonicalDominantNearBasesAtCreation_eq_vTwo_of_next_zero
    (t : DominoTiling) (m k w : ℕ) (s : WalkPath)
    (hnext : thresholdCount s (creationTimeNat m k s) (m + 1) = 0) :
    tilingCanonicalDominantNearBasesAtCreation t m k w s =
      tilingVTwoAtCreation t m k w s := by
  rw [tilingCanonicalDominantNearBasesAtCreation_eq_vTwo_union,
    tilingVTwoReplacementBases_eq_empty_of_thresholdCount_succ_eq_zero hnext,
    Finset.union_empty]
  rfl

/-- The parity-specific dominant candidate family (`M_e` or `M_o`). -/
noncomputable def tilingOrientedDominantNearBasesAtCreation
    (o : LazyDecomposition.Orientation) (t : DominoTiling)
    (m k w : ℕ) (s : WalkPath) : Finset Point :=
  (tilingDominantNearBasesAtCreation t m k w s).filter
    (SpatialInsertionFiber.OrientationCompatible o)

theorem tilingDominantNearBasesAtCreation_eq_even_union_shifted
    (t : DominoTiling) (m k w : ℕ) (s : WalkPath) :
    tilingDominantNearBasesAtCreation t m k w s =
      tilingOrientedDominantNearBasesAtCreation .even t m k w s ∪
        tilingOrientedDominantNearBasesAtCreation .shifted t m k w s := by
  classical
  ext x
  simp only [tilingOrientedDominantNearBasesAtCreation, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · intro hx
    rcases PreStoppingSpatialLaw.evenPoint_or_oddPoint x with heven | hodd
    · exact Or.inl ⟨hx, heven⟩
    · exact Or.inr ⟨hx, hodd⟩
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx

theorem tilingNearFavoriteBasesAtCreation_card_le_two_oriented
    (t : DominoTiling) (m k w : ℕ) (s : WalkPath) :
    (tilingNearFavoriteBasesAtCreation t m k w s).card ≤
      2 * ((tilingOrientedDominantNearBasesAtCreation .even t m k w s).card +
        (tilingOrientedDominantNearBasesAtCreation .shifted t m k w s).card) := by
  have hnormalize := card_le_two_mul_card_image_tilingDominantEndpointAt
    t s (creationTimeNat m k s) (tilingNearFavoriteBasesAtCreation t m k w s)
  have hunion : (tilingDominantNearBasesAtCreation t m k w s).card ≤
      (tilingOrientedDominantNearBasesAtCreation .even t m k w s).card +
        (tilingOrientedDominantNearBasesAtCreation .shifted t m k w s).card := by
    rw [tilingDominantNearBasesAtCreation_eq_even_union_shifted]
    exact Finset.card_union_le _ _
  exact hnormalize.trans (Nat.mul_le_mul_left 2 hunion)

theorem tilingThetaAtCreation_subset_dominantNearBases
    (t : DominoTiling) (m k w externalLow externalHigh : ℕ) (s : WalkPath) :
    tilingThetaAtCreation t m k w externalLow externalHigh s ⊆
      tilingDominantNearBasesAtCreation t m k w s := by
  classical
  intro b hb
  have hbdata := Finset.mem_filter.mp hb
  have hdominant := hbdata.2.1
  have hnear : b ∈ tilingNearFavoriteBasesAtCreation t m k w s := by
    rw [tilingNearFavoriteBasesAtCreation, Finset.mem_filter]
    refine ⟨hbdata.1, ?_⟩
    rw [tilingXiPlusAt_eq_base_of_partner_le hdominant]
    exact hbdata.2.2.1
  rw [tilingDominantNearBasesAtCreation, Finset.mem_image]
  refine ⟨b, hnear, ?_⟩
  unfold tilingDominantEndpointAt
  rw [if_pos hdominant]

theorem tilingThetaAtCreation_subset_canonicalDominantNearBases
    (t : DominoTiling) (m k w externalLow externalHigh : ℕ) (s : WalkPath) :
    tilingThetaAtCreation t m k w externalLow externalHigh s ⊆
      tilingCanonicalDominantNearBasesAtCreation t m k w s := by
  intro b hb
  rw [tilingCanonicalDominantNearBasesAtCreation, Finset.mem_filter]
  refine ⟨tilingThetaAtCreation_subset_dominantNearBases
    t m k w externalLow externalHigh s hb, ?_⟩
  exact isTilingBase_of_mem_visitedTilingBases (Finset.mem_filter.mp hb).1

/-! The same normalization is exposed directly for the random-clock band
sets used by the gap screen.  No assertion is made that an undominated raw
band site is itself a `V₂` coordinate. -/

noncomputable def tilingDominantRandomClockBandSites
    (t : DominoTiling) (m cutoff : ℕ) (s : WalkPath)
    (band : RandomClockBand) : Finset Point :=
  (tilingRandomClockBandSites t m cutoff s band).image
    (tilingDominantEndpointAt t s
      (pathTruncatedLevelTime m band.oldRank cutoff s))

noncomputable def tilingOrientedDominantRandomClockBandSites
    (o : LazyDecomposition.Orientation) (t : DominoTiling)
    (m cutoff : ℕ) (s : WalkPath) (band : RandomClockBand) : Finset Point :=
  (tilingDominantRandomClockBandSites t m cutoff s band).filter
    (SpatialInsertionFiber.OrientationCompatible o)

theorem tilingDominantRandomClockBandSites_eq_even_union_shifted
    (t : DominoTiling) (m cutoff : ℕ) (s : WalkPath)
    (band : RandomClockBand) :
    tilingDominantRandomClockBandSites t m cutoff s band =
      tilingOrientedDominantRandomClockBandSites .even t m cutoff s band ∪
        tilingOrientedDominantRandomClockBandSites .shifted t m cutoff s band := by
  classical
  ext x
  simp only [tilingOrientedDominantRandomClockBandSites, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · intro hx
    rcases PreStoppingSpatialLaw.evenPoint_or_oddPoint x with heven | hodd
    · exact Or.inl ⟨hx, heven⟩
    · exact Or.inr ⟨hx, hodd⟩
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx

theorem tilingRandomClockBandSites_card_le_two_orientedDominant
    (t : DominoTiling) (m cutoff : ℕ) (s : WalkPath)
    (band : RandomClockBand) :
    (tilingRandomClockBandSites t m cutoff s band).card ≤
      2 * ((tilingOrientedDominantRandomClockBandSites .even
          t m cutoff s band).card +
        (tilingOrientedDominantRandomClockBandSites .shifted
          t m cutoff s band).card) := by
  have hnormalize := card_le_two_mul_card_image_tilingDominantEndpointAt
    t s (pathTruncatedLevelTime m band.oldRank cutoff s)
      (tilingRandomClockBandSites t m cutoff s band)
  have hunion : (tilingDominantRandomClockBandSites t m cutoff s band).card ≤
      (tilingOrientedDominantRandomClockBandSites .even
        t m cutoff s band).card +
      (tilingOrientedDominantRandomClockBandSites .shifted
        t m cutoff s band).card := by
    rw [tilingDominantRandomClockBandSites_eq_even_union_shifted]
    exact Finset.card_union_le _ _
  exact hnormalize.trans (Nat.mul_le_mul_left 2 hunion)

theorem thresholdDominoSeparated_of_singleton
    {t : DominoTiling} {s : WalkPath} {n m : ℕ} {x : Point}
    (hsites : thresholdSites s n m = {x}) :
    TilingThresholdDominoSeparated t s n m := by
  intro y hy z hz hyz
  rw [hsites, Finset.mem_singleton] at hy hz
  exact (hyz (hy.trans hz.symm)).elim

theorem thresholdDominoSeparated_of_pair
    {t : DominoTiling} {s : WalkPath} {n m : ℕ} {x₁ x₂ : Point}
    (hsites : thresholdSites s n m = {x₁, x₂})
    (h₁₂ : ¬Tilings.sameDomino t x₁ x₂) :
    TilingThresholdDominoSeparated t s n m := by
  intro x hx y hy hxy
  rw [hsites] at hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · exact h₁₂
  · rcases hy with rfl | rfl
    · exact fun hdom ↦ h₁₂ ((Tilings.sameDomino_comm t _ _).mpr hdom)
    · exact (hxy rfl).elim

theorem thresholdDominoSeparated_of_triple
    {t : DominoTiling} {s : WalkPath} {n m : ℕ} {x₁ x₂ x₃ : Point}
    (hsites : thresholdSites s n m = {x₁, x₂, x₃})
    (h₁₂ : ¬Tilings.sameDomino t x₁ x₂)
    (h₁₃ : ¬Tilings.sameDomino t x₁ x₃)
    (h₂₃ : ¬Tilings.sameDomino t x₂ x₃) :
    TilingThresholdDominoSeparated t s n m := by
  intro x hx y hy hxy
  rw [hsites] at hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl
  · rcases hy with rfl | rfl | rfl
    · exact (hxy rfl).elim
    · exact h₁₂
    · exact h₁₃
  · rcases hy with rfl | rfl | rfl
    · exact fun hdom ↦ h₁₂ ((Tilings.sameDomino_comm t _ _).mpr hdom)
    · exact (hxy rfl).elim
    · exact h₂₃
  · rcases hy with rfl | rfl | rfl
    · exact fun hdom ↦ h₁₃ ((Tilings.sameDomino_comm t _ _).mpr hdom)
    · exact fun hdom ↦ h₂₃ ((Tilings.sameDomino_comm t _ _).mpr hdom)
    · exact (hxy rfl).elim

/-! The three upper-transition stages carry the exact structural part of
`D_eta`; no extra structural exceptional event is needed on these stages. -/

theorem firstTransitionEvent_next_zero_at_creation
    (t : DominoTiling) (m : ℕ) (a : (GapScale × GapScale) × GapScale)
    {s : WalkPath} (hs : s ∈ firstTransitionEvent t m a) :
    thresholdCount s (creationTimeNat m 1 s) (m + 1) = 0 := by
  simp only [firstTransitionEvent, Set.mem_iUnion] at hs
  obtain ⟨n₁, n₂, h₁, h₂, hnext, _⟩ := hs
  have htime : n₁ < n₂ := creation_time_lt (by omega) (by omega)
    (by omega) h₁ h₂
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  have hnext₁ : thresholdCount s n₁ (m + 1) = 0 := by
    change thresholdCount s n₁ (m + 1) ≤ thresholdCount s n₂ (m + 1) at hmono
    omega
  rw [creationTimeNat_eq_of_creation h₁]
  exact hnext₁

theorem secondTransitionEvent_next_zero_at_creation
    (t : DominoTiling) (m : ℕ) (a : (GapScale × GapScale) × GapScale)
    {s : WalkPath} (hs : s ∈ secondTransitionEvent t m a) :
    thresholdCount s (creationTimeNat m 2 s) (m + 1) = 0 := by
  simp only [secondTransitionEvent, Set.mem_iUnion] at hs
  obtain ⟨n₁, n₂, n₃, h₁, h₂, h₃, hnext, _⟩ := hs
  have htime : n₂ < n₃ := creation_time_lt (by omega) (by omega)
    (by omega) h₂ h₃
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  have hnext₂ : thresholdCount s n₂ (m + 1) = 0 := by
    change thresholdCount s n₂ (m + 1) ≤ thresholdCount s n₃ (m + 1) at hmono
    omega
  rw [creationTimeNat_eq_of_creation h₂]
  exact hnext₂

theorem thirdTransitionEvent_next_zero_at_creation
    (t : DominoTiling) (m : ℕ) (a : (GapScale × GapScale) × GapScale)
    {s : WalkPath} (hs : s ∈ thirdTransitionEvent t m a) :
    thresholdCount s (creationTimeNat m 3 s) (m + 1) = 0 := by
  simp only [thirdTransitionEvent, Set.mem_iUnion] at hs
  obtain ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, _⟩ := hs
  have htime : n₃ < n₄ := creation_time_lt (by omega) (by omega)
    (by omega) h₃ h₄
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  have hnext₃ : thresholdCount s n₃ (m + 1) = 0 := by
    change thresholdCount s n₃ (m + 1) ≤ thresholdCount s n₄ (m + 1) at hmono
    omega
  rw [creationTimeNat_eq_of_creation h₃]
  exact hnext₃

theorem canonicalDominantNearBases_eq_vTwo_on_firstTransition
    (t : DominoTiling) (m w : ℕ) (a : (GapScale × GapScale) × GapScale)
    {s : WalkPath} (hs : s ∈ firstTransitionEvent t m a) :
    tilingCanonicalDominantNearBasesAtCreation t m 1 w s =
      tilingVTwoAtCreation t m 1 w s :=
  tilingCanonicalDominantNearBasesAtCreation_eq_vTwo_of_next_zero
    t m 1 w s (firstTransitionEvent_next_zero_at_creation t m a hs)

theorem canonicalDominantNearBases_eq_vTwo_on_secondTransition
    (t : DominoTiling) (m w : ℕ) (a : (GapScale × GapScale) × GapScale)
    {s : WalkPath} (hs : s ∈ secondTransitionEvent t m a) :
    tilingCanonicalDominantNearBasesAtCreation t m 2 w s =
      tilingVTwoAtCreation t m 2 w s :=
  tilingCanonicalDominantNearBasesAtCreation_eq_vTwo_of_next_zero
    t m 2 w s (secondTransitionEvent_next_zero_at_creation t m a hs)

theorem canonicalDominantNearBases_eq_vTwo_on_thirdTransition
    (t : DominoTiling) (m w : ℕ) (a : (GapScale × GapScale) × GapScale)
    {s : WalkPath} (hs : s ∈ thirdTransitionEvent t m a) :
    tilingCanonicalDominantNearBasesAtCreation t m 3 w s =
      tilingVTwoAtCreation t m 3 w s :=
  tilingCanonicalDominantNearBasesAtCreation_eq_vTwo_of_next_zero
    t m 3 w s (thirdTransitionEvent_next_zero_at_creation t m a hs)

theorem firstTransitionEvent_subset_sourceProfileAtCreation
    (t : DominoTiling) (m w low : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (hm : 0 < m) (hlow : low = m - w) :
    firstTransitionEvent t m a ⊆
      thresholdReachStage m 1 ∩ {s | tilingDEtaAtCreation t m 1 w low s} := by
  intro s hs
  simp only [firstTransitionEvent, Set.mem_iUnion] at hs
  obtain ⟨n₁, n₂, h₁, h₂, hnext, h₁₂, ha⟩ := hs
  have htime : n₁ < n₂ := creation_time_lt (by omega) (by omega)
    (by omega) h₁ h₂
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  have hnext₁ : thresholdCount s n₁ (m + 1) = 0 := by
    change thresholdCount s n₁ (m + 1) ≤ thresholdCount s n₂ (m + 1) at hmono
    omega
  refine ⟨⟨n₁, h₁.1⟩, ?_⟩
  exact tilingDEtaAtCreation_of_creation_of_dominoSeparated hm (by omega) hlow
    h₁ hnext₁ (thresholdDominoSeparated_of_singleton
      (thresholdSites_eq_singleton_at_first_creation h₁))

theorem secondTransitionEvent_subset_sourceProfileAtCreation
    (t : DominoTiling) (m w low : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (hm : 0 < m) (hlow : low = m - w) :
    secondTransitionEvent t m a ⊆
      thresholdReachStage m 2 ∩ {s | tilingDEtaAtCreation t m 2 w low s} := by
  intro s hs
  simp only [secondTransitionEvent, Set.mem_iUnion] at hs
  obtain ⟨n₁, n₂, n₃, h₁, h₂, h₃, hnext, h₁₂, h₁₃, h₂₃, ha₁, ha₂⟩ := hs
  have htime : n₂ < n₃ := creation_time_lt (by omega) (by omega)
    (by omega) h₂ h₃
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  have hnext₂ : thresholdCount s n₂ (m + 1) = 0 := by
    change thresholdCount s n₂ (m + 1) ≤ thresholdCount s n₃ (m + 1) at hmono
    omega
  refine ⟨⟨n₂, h₂.1⟩, ?_⟩
  exact tilingDEtaAtCreation_of_creation_of_dominoSeparated hm (by omega) hlow
    h₂ hnext₂ (thresholdDominoSeparated_of_pair
      (thresholdSites_eq_pair_at_second_creation h₁ h₂) h₁₂)

theorem thirdTransitionEvent_subset_sourceProfileAtCreation
    (t : DominoTiling) (m w low : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (hm : 0 < m) (hlow : low = m - w) :
    thirdTransitionEvent t m a ⊆
      thresholdReachStage m 3 ∩ {s | tilingDEtaAtCreation t m 3 w low s} := by
  intro s hs
  simp only [thirdTransitionEvent, Set.mem_iUnion] at hs
  obtain ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep,
    ha₁, ha₂, ha₃⟩ := hs
  have htime : n₃ < n₄ := creation_time_lt (by omega) (by omega)
    (by omega) h₃ h₄
  have hmono := thresholdCount_mono_time s (m + 1) htime.le
  have hnext₃ : thresholdCount s n₃ (m + 1) = 0 := by
    change thresholdCount s n₃ (m + 1) ≤ thresholdCount s n₄ (m + 1) at hmono
    omega
  rcases hsep with ⟨h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄⟩
  refine ⟨⟨n₃, h₃.1⟩, ?_⟩
  exact tilingDEtaAtCreation_of_creation_of_dominoSeparated hm (by omega) hlow
    h₃ hnext₃ (thresholdDominoSeparated_of_triple
      (thresholdSites_eq_triple_at_third_creation h₁ h₂ h₃)
      h₁₂ h₁₃ h₂₃)

def tilingSourceGoodAtCreationEvent (t : DominoTiling)
    (m k w low externalLow externalHigh : ℕ) : Set WalkPath :=
  thresholdReachStage m k ∩
    {s | tilingDEtaAtCreation t m k w low s} ∩
    {s | tilingThetaAtCreation t m k w externalLow externalHigh s = ∅}

def tilingStageThetaFailureEvent (preliminary : Set WalkPath)
    (t : DominoTiling) (m k w low externalLow externalHigh : ℕ) : Set WalkPath :=
  preliminary ∩ thresholdReachStage m k ∩
    {s | tilingDEtaAtCreation t m k w low s} ∩
    {s | tilingThetaAtCreation t m k w externalLow externalHigh s ≠ ∅}

/-- The part not covered by Proposition 4.5.  This event is intentionally
separate from `Theta`: a moderate-deviation estimate cannot establish the
`D_eta` classification. -/
def tilingStageStructuralSourceFailureEvent (preliminary : Set WalkPath)
    (t : DominoTiling) (m k w low : ℕ) : Set WalkPath :=
  preliminary \ (thresholdReachStage m k ∩
    {s | tilingDEtaAtCreation t m k w low s})

theorem firstTransitionEvent_disjoint_structuralSourceFailure
    (t : DominoTiling) (m w low : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (preliminary : Set WalkPath) (hm : 0 < m) (hlow : low = m - w) :
    Disjoint (firstTransitionEvent t m a ∩ preliminary)
      (tilingStageStructuralSourceFailureEvent preliminary t m 1 w low) := by
  rw [Set.disjoint_left]
  intro s hs hbad
  exact hbad.2 ((firstTransitionEvent_subset_sourceProfileAtCreation
    t m w low a hm hlow) hs.1)

theorem secondTransitionEvent_disjoint_structuralSourceFailure
    (t : DominoTiling) (m w low : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (preliminary : Set WalkPath) (hm : 0 < m) (hlow : low = m - w) :
    Disjoint (secondTransitionEvent t m a ∩ preliminary)
      (tilingStageStructuralSourceFailureEvent preliminary t m 2 w low) := by
  rw [Set.disjoint_left]
  intro s hs hbad
  exact hbad.2 ((secondTransitionEvent_subset_sourceProfileAtCreation
    t m w low a hm hlow) hs.1)

theorem thirdTransitionEvent_disjoint_structuralSourceFailure
    (t : DominoTiling) (m w low : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (preliminary : Set WalkPath) (hm : 0 < m) (hlow : low = m - w) :
    Disjoint (thirdTransitionEvent t m a ∩ preliminary)
      (tilingStageStructuralSourceFailureEvent preliminary t m 3 w low) := by
  rw [Set.disjoint_left]
  intro s hs hbad
  exact hbad.2 ((thirdTransitionEvent_subset_sourceProfileAtCreation
    t m w low a hm hlow) hs.1)

theorem measurableSet_tilingSourceGoodAtCreationEvent
    (t : DominoTiling) (m k w low externalLow externalHigh : ℕ) :
    MeasurableSet (tilingSourceGoodAtCreationEvent t m k w low
      externalLow externalHigh) := by
  have hD : MeasurableSet {s : WalkPath |
      tilingDEtaAtCreation t m k w low s} := by
    simpa only [decide_eq_true_eq] using
      (measurableSet_eq_fun
        (measurable_tilingDEtaAtCreationFlag t m k w low)
        (g := fun _ ↦ true) measurable_const)
  have htheta : MeasurableSet {s : WalkPath |
      tilingThetaAtCreation t m k w externalLow externalHigh s = ∅} :=
    measurableSet_eq_fun
      (measurable_tilingThetaAtCreation t m k w externalLow externalHigh)
      (g := fun _ ↦ (∅ : Finset Point)) measurable_const
  exact ((measurableSet_thresholdReachStage m k).inter hD).inter htheta

/-- The literal shell-zero source is measurable at the genuine creation
clock.  In particular, selecting it does not require an abstract
measurability premise in the filtered product assembly. -/
theorem measurableSet_shellZeroSourceEvent
    (t : DominoTiling) (m k w low externalLow externalHigh cut : ℕ) :
    MeasurableSet (shellZeroSourceEvent t m k w low externalLow
      externalHigh cut) := by
  have hD : MeasurableSet {s : WalkPath |
      tilingDEtaAtCreation t m k w low s} := by
    simpa only [decide_eq_true_eq] using
      (measurableSet_eq_fun
        (measurable_tilingDEtaAtCreationFlag t m k w low)
        (g := fun _ ↦ true) measurable_const)
  have htheta : MeasurableSet {s : WalkPath |
      tilingThetaAtCreation t m k w externalLow externalHigh s = ∅} :=
    measurableSet_eq_fun
      (measurable_tilingThetaAtCreation t m k w externalLow externalHigh)
      (g := fun _ ↦ (∅ : Finset Point)) measurable_const
  have hcut : MeasurableSet {s : WalkPath |
      cut < (tilingVTwoAtCreation t m k w s).card} :=
    measurableSet_lt measurable_const
      ((measurable_of_countable (fun S : Finset Point ↦ S.card)).comp
        (measurable_tilingVTwoAtCreation t m k w))
  rw [show shellZeroSourceEvent t m k w low externalLow externalHigh cut =
      thresholdReachStage m k ∩ {s | tilingDEtaAtCreation t m k w low s} ∩
        {s | tilingThetaAtCreation t m k w externalLow externalHigh s = ∅} ∩
        {s | cut < (tilingVTwoAtCreation t m k w s).card} by
    ext s
    simp only [shellZeroSourceEvent, thresholdReachStage,
      tilingDEtaAtCreation, tilingThetaAtCreation, tilingVTwoAtCreation,
      Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]]
  exact (((measurableSet_thresholdReachStage m k).inter hD).inter htheta).inter hcut

theorem measurableSet_filteredShellZeroSourceEvent
    {preliminary : Set WalkPath} (hpreliminary : MeasurableSet preliminary)
    (t : DominoTiling) (m k low externalLow externalHigh cut : ℕ) :
    MeasurableSet (filteredShellZeroSourceEvent preliminary t m k low
      externalLow externalHigh cut) := by
  exact hpreliminary.inter
    (measurableSet_shellZeroSourceEvent t m k (shellWidth48 m) low
      externalLow externalHigh cut)

/-! ## Endpoint-oriented source observability -/

def prefixOrientedTilingVTwoBases {n : ℕ}
    (t : DominoTiling) (o : Orientation) (window : Finset ℕ)
    (u : Fin (n + 1) → Point) : Finset Point :=
  (prefixTilingVTwoBases t window u).filter (OrientationCompatible o)

@[simp] theorem prefixOrientedTilingVTwoBases_pathPrefix
    (t : DominoTiling) (o : Orientation) (window : Finset ℕ)
    (n : ℕ) (s : WalkPath) :
    prefixOrientedTilingVTwoBases t o window (pathPrefix s n) =
      orientedTilingVTwoBases t o window s n := by
  rfl

theorem measurable_fixedOrientedTilingVTwoBases
    (t : DominoTiling) (o : Orientation) (window : Finset ℕ) (n : ℕ) :
    Measurable fun s : WalkPath ↦ orientedTilingVTwoBases t o window s n := by
  change Measurable
    ((prefixOrientedTilingVTwoBases t o window) ∘ pathPrefix (n := n))
  exact (measurable_of_countable _).comp (measurable_pathPrefix n)

def prefixOrientedTilingThetaBases {n : ℕ}
    (t : DominoTiling) (o : Orientation)
    (m w externalLow externalHigh : ℕ)
    (u : Fin (n + 1) → Point) : Finset Point :=
  (prefixOrientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m w ∪
        shellZeroReplacementTotalWindow m w) u).filter fun b ↦
      ¬(externalLow ≤ prefixTilingSourceExternalBaseLocalTime t o u b ∧
        prefixTilingSourceExternalBaseLocalTime t o u b < externalHigh)

@[simp] theorem prefixOrientedTilingThetaBases_pathPrefix
    (t : DominoTiling) (o : Orientation)
    (m w externalLow externalHigh n : ℕ) (s : WalkPath) :
    prefixOrientedTilingThetaBases t o m w externalLow externalHigh
        (pathPrefix s n) =
      orientedTilingThetaBases t o m w externalLow externalHigh s n := by
  rfl

theorem measurable_fixedOrientedTilingThetaBases
    (t : DominoTiling) (o : Orientation)
    (m w externalLow externalHigh n : ℕ) :
    Measurable fun s : WalkPath ↦
      orientedTilingThetaBases t o m w externalLow externalHigh s n := by
  change Measurable
    ((prefixOrientedTilingThetaBases t o m w externalLow externalHigh) ∘
      pathPrefix (n := n))
  exact (measurable_of_countable _).comp (measurable_pathPrefix n)

def orientedTilingThetaAtCreation
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) (s : WalkPath) : Finset Point :=
  orientedTilingThetaBases t o m w externalLow externalHigh s
    (creationTimeNat m k s)

def orientedTilingVTwoAtCreation
    (t : DominoTiling) (o : Orientation) (m k w : ℕ)
    (s : WalkPath) : Finset Point :=
  orientedTilingVTwoBases t o (shellZeroSourceTotalWindow m w) s
    (creationTimeNat m k s)

theorem measurable_orientedTilingThetaAtCreation
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) :
    Measurable (orientedTilingThetaAtCreation t o m k w externalLow
      externalHigh) := by
  exact measurable_natIndexed (creationTimeNat m k)
    (measurable_creationTimeNat m k)
    (fun n s ↦ orientedTilingThetaBases t o m w externalLow externalHigh s n)
    (measurable_fixedOrientedTilingThetaBases t o m w externalLow externalHigh)

theorem measurable_orientedTilingVTwoAtCreation
    (t : DominoTiling) (o : Orientation) (m k w : ℕ) :
    Measurable (orientedTilingVTwoAtCreation t o m k w) := by
  exact measurable_natIndexed (creationTimeNat m k)
    (measurable_creationTimeNat m k)
    (fun n s ↦ orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m w) s n)
    (measurable_fixedOrientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m w))

theorem measurableSet_orientedShellZeroSourceEvent
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh cut : ℕ) :
    MeasurableSet (orientedShellZeroSourceEvent t o m k w low externalLow
      externalHigh cut) := by
  have hD : MeasurableSet {s : WalkPath |
      tilingDEtaAtCreation t m k w low s} := by
    simpa only [decide_eq_true_eq] using
      (measurableSet_eq_fun
        (measurable_tilingDEtaAtCreationFlag t m k w low)
        (g := fun _ ↦ true) measurable_const)
  have htheta : MeasurableSet {s : WalkPath |
      orientedTilingThetaAtCreation t o m k w externalLow externalHigh s = ∅} :=
    measurableSet_eq_fun
      (measurable_orientedTilingThetaAtCreation t o m k w externalLow externalHigh)
      (g := fun _ ↦ (∅ : Finset Point)) measurable_const
  have hcut : MeasurableSet {s : WalkPath |
      cut < (orientedTilingVTwoAtCreation t o m k w s).card} :=
    measurableSet_lt measurable_const
      ((measurable_of_countable (fun S : Finset Point ↦ S.card)).comp
        (measurable_orientedTilingVTwoAtCreation t o m k w))
  rw [show orientedShellZeroSourceEvent t o m k w low externalLow
      externalHigh cut =
      thresholdReachStage m k ∩ {s | tilingDEtaAtCreation t m k w low s} ∩
        {s | orientedTilingThetaAtCreation t o m k w externalLow externalHigh s = ∅} ∩
        {s | cut < (orientedTilingVTwoAtCreation t o m k w s).card} by
    ext s
    simp only [orientedShellZeroSourceEvent, thresholdReachStage,
      tilingDEtaAtCreation, orientedTilingThetaAtCreation,
      orientedTilingVTwoAtCreation, Set.mem_inter_iff, Set.mem_ofPred_eq,
      and_assoc]]
  exact (((measurableSet_thresholdReachStage m k).inter hD).inter htheta).inter hcut

theorem measurableSet_orientedFilteredShellZeroSourceEvent
    {preliminary : Set WalkPath} (hpreliminary : MeasurableSet preliminary)
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh cut : ℕ) :
    MeasurableSet (orientedFilteredShellZeroSourceEvent preliminary t o m k w
      low externalLow externalHigh cut) := by
  exact hpreliminary.inter
    (measurableSet_orientedShellZeroSourceEvent t o m k w low externalLow
      externalHigh cut)

theorem measurableSet_tilingStageThetaFailureEvent
    {preliminary : Set WalkPath} (hpreliminary : MeasurableSet preliminary)
    (t : DominoTiling) (m k w low externalLow externalHigh : ℕ) :
    MeasurableSet (tilingStageThetaFailureEvent preliminary t m k w low
      externalLow externalHigh) := by
  have hD : MeasurableSet {s : WalkPath |
      tilingDEtaAtCreation t m k w low s} := by
    simpa only [decide_eq_true_eq] using
      (measurableSet_eq_fun
        (measurable_tilingDEtaAtCreationFlag t m k w low)
        (g := fun _ ↦ true) measurable_const)
  have hthetaEq : MeasurableSet {s : WalkPath |
      tilingThetaAtCreation t m k w externalLow externalHigh s = ∅} :=
    measurableSet_eq_fun
      (measurable_tilingThetaAtCreation t m k w externalLow externalHigh)
      (g := fun _ ↦ (∅ : Finset Point)) measurable_const
  have hthetaNe : MeasurableSet {s : WalkPath |
      tilingThetaAtCreation t m k w externalLow externalHigh s ≠ ∅} := by
    rw [show {s : WalkPath |
        tilingThetaAtCreation t m k w externalLow externalHigh s ≠ ∅} =
      {s : WalkPath |
        tilingThetaAtCreation t m k w externalLow externalHigh s = ∅}ᶜ by
        ext s; simp]
    exact hthetaEq.compl
  exact (((hpreliminary.inter (measurableSet_thresholdReachStage m k)).inter
    hD).inter hthetaNe)

theorem measurableSet_tilingStageStructuralSourceFailureEvent
    {preliminary : Set WalkPath} (hpreliminary : MeasurableSet preliminary)
    (t : DominoTiling) (m k w low : ℕ) :
    MeasurableSet
      (tilingStageStructuralSourceFailureEvent preliminary t m k w low) := by
  have hD : MeasurableSet {s : WalkPath |
      tilingDEtaAtCreation t m k w low s} := by
    simpa only [decide_eq_true_eq] using
      (measurableSet_eq_fun
        (measurable_tilingDEtaAtCreationFlag t m k w low)
        (g := fun _ ↦ true) measurable_const)
  exact hpreliminary.diff ((measurableSet_thresholdReachStage m k).inter hD)

theorem preliminary_subset_structural_union_theta_union_good
    (preliminary : Set WalkPath) (t : DominoTiling)
    (m k w low externalLow externalHigh : ℕ) :
    preliminary ⊆
      tilingStageStructuralSourceFailureEvent preliminary t m k w low ∪
      tilingStageThetaFailureEvent preliminary t m k w low externalLow
        externalHigh ∪
      (preliminary ∩ tilingSourceGoodAtCreationEvent t m k w low
        externalLow externalHigh) := by
  intro s hs
  by_cases hsource : s ∈ thresholdReachStage m k ∩
      {s | tilingDEtaAtCreation t m k w low s}
  · by_cases htheta : tilingThetaAtCreation t m k w externalLow externalHigh s = ∅
    · right
      exact ⟨hs, ⟨⟨hsource.1, hsource.2⟩, htheta⟩⟩
    · left; right
      exact ⟨⟨⟨hs, hsource.1⟩, hsource.2⟩, htheta⟩
  · left; left
    exact ⟨hs, hsource⟩

/-! ## Finite slot enumeration of `Theta` -/

def tilingThetaLowerSlotBad (t : DominoTiling)
    (m k w externalLow externalHigh cutoff : ℕ) (slot : Fin (cutoff + 1)) :
    Set WalkPath :=
  {s | creationTimeNat m k s ≤ cutoff ∧
    ∃ b, finsetSlot
        (tilingThetaAtCreation t m k w externalLow externalHigh s) slot = some b ∧
      tilingExternalBaseLocalTime t s (creationTimeNat m k s) b < externalLow}

def tilingThetaUpperSlotBad (t : DominoTiling)
    (m k w externalLow externalHigh cutoff : ℕ) (slot : Fin (cutoff + 1)) :
    Set WalkPath :=
  {s | creationTimeNat m k s ≤ cutoff ∧
    ∃ b, finsetSlot
        (tilingThetaAtCreation t m k w externalLow externalHigh s) slot = some b ∧
      externalHigh ≤
        tilingExternalBaseLocalTime t s (creationTimeNat m k s) b}

def tilingThetaOnTimeBalancedEvent (t : DominoTiling)
    (m k w externalLow externalHigh cutoff : ℕ) : Set WalkPath :=
  {s | creationTimeNat m k s ≤ cutoff →
    tilingThetaAtCreation t m k w externalLow externalHigh s = ∅}

lemma tilingThetaAtCreation_card_le_time_add_one
    (t : DominoTiling) (m k w externalLow externalHigh : ℕ) (s : WalkPath) :
    (tilingThetaAtCreation t m k w externalLow externalHigh s).card ≤
      creationTimeNat m k s + 1 := by
  let n := creationTimeNat m k s
  calc
    (tilingThetaAtCreation t m k w externalLow externalHigh s).card ≤
        (visitedTilingBases t s n).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (visitedSites s n).card := by
      unfold visitedTilingBases
      exact Finset.card_image_le
    _ ≤ n + 1 := by
      unfold visitedSites visitedPrefix
      calc
        (Finset.univ.image (pathPrefix s n)).card ≤
            (Finset.univ : Finset (Fin (n + 1))).card := Finset.card_image_le
        _ = n + 1 := by simp

theorem tilingThetaOnTimeBalancedEvent_compl_eq_slots
    (t : DominoTiling) (m k w externalLow externalHigh cutoff : ℕ) :
    (tilingThetaOnTimeBalancedEvent t m k w externalLow externalHigh cutoff)ᶜ =
      Screening.someCandidateBad (Finset.univ : Finset (Fin (cutoff + 1)))
        (Balancedness.twoSidedBad
          (tilingThetaLowerSlotBad t m k w externalLow externalHigh cutoff)
          (tilingThetaUpperSlotBad t m k w externalLow externalHigh cutoff)) := by
  ext s
  simp only [tilingThetaOnTimeBalancedEvent, Set.mem_compl_iff,
    Set.mem_ofPred_eq, not_forall, Screening.someCandidateBad,
    Balancedness.twoSidedBad, Finset.mem_univ, true_and, Set.mem_union]
  constructor
  · rintro ⟨hclock, htheta⟩
    obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr htheta
    obtain ⟨slot, hslotlt, hslot⟩ := exists_finsetSlot_eq_some hb
    have hcard := tilingThetaAtCreation_card_le_time_add_one
      t m k w externalLow externalHigh s
    have hslotCutoff : slot < cutoff + 1 := by omega
    let j : Fin (cutoff + 1) := ⟨slot, hslotCutoff⟩
    have hbtheta := finsetSlot_eq_some_mem hslot
    have houtside := (Finset.mem_filter.mp hbtheta).2.2.2
    rw [not_and_or] at houtside
    rcases houtside with hlower | hupper
    · exact ⟨j, Or.inl ⟨hclock, b, by simpa only [j] using hslot,
        Nat.lt_of_not_ge hlower⟩⟩
    · exact ⟨j, Or.inr ⟨hclock, b, by simpa only [j] using hslot,
        Nat.le_of_not_gt hupper⟩⟩
  · rintro ⟨slot, hlower | hupper⟩
    · rcases hlower with ⟨hclock, b, hslot, _⟩
      exact ⟨hclock, Finset.nonempty_iff_ne_empty.mp
        ⟨b, finsetSlot_eq_some_mem hslot⟩⟩
    · rcases hupper with ⟨hclock, b, hslot, _⟩
      exact ⟨hclock, Finset.nonempty_iff_ne_empty.mp
        ⟨b, finsetSlot_eq_some_mem hslot⟩⟩

/-! ## Literal stopped-coordinate construction of the balance law -/

/-- Per-slot stopped-coordinate screens.  The fields are trace/product
certificates against the exact geometric tails, rather than path-probability
estimates. -/
structure TilingThetaSlotTraceData (t : DominoTiling)
    (m k w externalLow externalHigh cutoff : ℕ) where
  successes : Fin (cutoff + 1) → ℕ
  successes_pos : ∀ slot, 0 < successes slot
  successes_le : ∀ slot, successes slot ≤ m
  deviation_le : ∀ slot, geometricDeviation m ≤ successes slot
  lower : ∀ slot, SomeTraceCappedProductScreening Set.univ
    (tilingThetaLowerSlotBad t m k w externalLow externalHigh cutoff slot)
    (ENNReal.ofReal
      ((geometric15Vector (successes slot)).real
        {g | geometricSum g ≤
          (successes slot : ℝ) / 15 - geometricDeviation m}))
  upper : ∀ slot, SomeTraceCappedProductScreening Set.univ
    (tilingThetaUpperSlotBad t m k w externalLow externalHigh cutoff slot)
    (ENNReal.ofReal
      ((geometric15Vector (successes slot)).real
        {g | (successes slot : ℝ) / 15 + geometricDeviation m ≤
          geometricSum g}))
  measurable_lower : ∀ slot, MeasurableSet
    (tilingThetaLowerSlotBad t m k w externalLow externalHigh cutoff slot)
  measurable_upper : ∀ slot, MeasurableSet
    (tilingThetaUpperSlotBad t m k w externalLow externalHigh cutoff slot)

private theorem measure_univ_le_one : simpleRandomWalk (Set.univ : Set WalkPath) ≤ 1 := by
  simp

private theorem measure_bad_le_of_univ_trace
    {bad : Set WalkPath} {cost : ℝ≥0∞}
    (hbad : MeasurableSet bad)
    (hcost : cost ≠ ∞)
    (screen : SomeTraceCappedProductScreening Set.univ bad cost) :
    simpleRandomWalk bad ≤ cost := by
  calc
    simpleRandomWalk bad ≤ cost * simpleRandomWalk (Set.univ : Set WalkPath) :=
      @transition_measure_le_of_traceCappedProductScreening screen.Index
        screen.countableIndex Set.univ bad hbad cost hcost
        screen.screening
    _ ≤ cost * 1 := by
      simpa only [mul_comm] using mul_le_mul_left measure_univ_le_one cost
    _ = cost := mul_one _

/-- Construct the actual finite-site `GeometricBalanceLaw` for the on-time
`Theta` event from literal stopped-coordinate trace screens. -/
def tilingThetaGeometricBalanceLaw
    {t : DominoTiling} {m k w externalLow externalHigh cutoff : ℕ}
    (hm : 0 < m)
    (data : TilingThetaSlotTraceData t m k w externalLow externalHigh cutoff) :
    GeometricBalanceLaw (Site := Fin (cutoff + 1)) simpleRandomWalk
      (tilingThetaOnTimeBalancedEvent t m k w externalLow externalHigh cutoff) m where
  sites := Finset.univ
  lowerBad := tilingThetaLowerSlotBad t m k w externalLow externalHigh cutoff
  upperBad := tilingThetaUpperSlotBad t m k w externalLow externalHigh cutoff
  budget := cutoff + 1
  successes := data.successes
  identify := tilingThetaOnTimeBalancedEvent_compl_eq_slots
    t m k w externalLow externalHigh cutoff
  m_pos := hm
  card_le := by simp
  successes_pos := fun x _ ↦ data.successes_pos x
  successes_le := fun x _ ↦ data.successes_le x
  deviation_le := fun x _ ↦ data.deviation_le x
  lower_law := fun x _ ↦ measure_bad_le_of_univ_trace
    (data.measurable_lower x) ENNReal.ofReal_ne_top (data.lower x)
  upper_law := fun x _ ↦ measure_bad_le_of_univ_trace
    (data.measurable_upper x) ENNReal.ofReal_ne_top (data.upper x)

theorem simpleRandomWalk_tilingThetaOnTimeFailure_le
    {t : DominoTiling} {m k w externalLow externalHigh cutoff : ℕ}
    (hm : 0 < m)
    (data : TilingThetaSlotTraceData t m k w externalLow externalHigh cutoff) :
    simpleRandomWalk.real
        (tilingThetaOnTimeBalancedEvent t m k w externalLow externalHigh cutoff)ᶜ ≤
      (((cutoff + 1 : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
          ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal := by
  exact measureReal_compl_le_of_geometricBalanceLaw simpleRandomWalk _ m
    (tilingThetaGeometricBalanceLaw hm data)

end

end Erdos1165.HLOZThetaSourceBalance
