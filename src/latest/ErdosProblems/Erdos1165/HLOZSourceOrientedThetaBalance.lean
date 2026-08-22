/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedProposition44
import ErdosProblems.Erdos1165.HLOZThetaSourceBalance
import ErdosProblems.Erdos1165.HLOZTraceCappedProductScreening
import ErdosProblems.Erdos1165.HLOZUpperEstimates
import ErdosProblems.Erdos1165.HLOZShellZeroExternalWindow
import ErdosProblems.Erdos1165.HLOZNegativeBinomialTruncation
import ErdosProblems.Erdos1165.TilingStoppedWeightedOnePoint

/-!
# Endpoint-oriented Proposition 4.5 screen

The source balance screen has two genuinely different parts.  Bases with
large endpoint-chain local time are first restricted by Proposition 4.4 and
then union-bounded over its finite relevant-site family.  Bases below that
threshold are union-bounded over physical-time slots, but use the stronger
`m^(3/4)` deviation and hence an `exp (-c * sqrt m)` one-site cost.  In
particular this file never multiplies the physical cutoff by the weaker
`exp (-c * m^(1-2*kappaOne))` cost.

The word `Theta` below is qualified carefully.  The global oriented slice has
no dominance condition.  The shell source uses only its intersection with
the oriented `V₂` family; this is the restricted screen.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaBalance

open ExternalProposition44 HLOZGapEstimate HLOZPathEvents
open HLOZGapBetaNumerics
open HLOZSourceOrientedExternalLocalTime HLOZSourceOrientedProposition44
open HLOZThetaSourceBalance HLOZThresholdedShellScreening
open HLOZTraceCappedProductScreening HLOZUpperEstimates
open HLOZShellZeroReplacementWindows
open HLOZShellZeroExternalWindow
open HLOZNegativeBinomialTruncation
open LazyDecomposition ScreeningInstantiation
open SpatialInsertionFiber
open TilingExternalPhaseSplit TilingLazyDecomposition
open TilingOrientedShellZeroSourcePartition TilingShellZeroSourcePartition
open TilingStoppedProductDisintegration TilingStoppedWeightedOnePoint
open VariableStoppedTracePartition

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev DominoTiling := Tilings.Tiling

/-! ## Global and restricted oriented Theta -/

/-- One temporal-orientation slice of the paper's global `Theta`.  It has no
base-dominance condition. -/
def orientedGlobalThetaBases (t : DominoTiling) (o : Orientation)
    (m w externalLow externalHigh : ℕ) (s : WalkPath) (n : ℕ) :
    Finset Point :=
  (visitedTilingBases t s n).filter fun b ↦
    OrientationCompatible o b ∧
      localTime s n b ∈
        (shellZeroSourceTotalWindow m w ∪
          shellZeroReplacementTotalWindow m w) ∧
      ¬(externalLow ≤ tilingSourceExternalBaseLocalTime t o s n b ∧
        tilingSourceExternalBaseLocalTime t o s n b < externalHigh)

/-- The shell-source screen is a subset of the oriented global screen.  Its
extra condition is precisely membership in the dominant `V₂` family. -/
theorem orientedTilingThetaBases_subset_orientedGlobalThetaBases
    (t : DominoTiling) (o : Orientation)
    (m w externalLow externalHigh : ℕ) (s : WalkPath) (n : ℕ) :
    orientedTilingThetaBases t o m w externalLow externalHigh s n ⊆
      orientedGlobalThetaBases t o m w externalLow externalHigh s n := by
  intro b hb
  rw [orientedTilingThetaBases, Finset.mem_filter,
    mem_orientedTilingVTwoBases_iff] at hb
  rw [orientedGlobalThetaBases, Finset.mem_filter]
  rw [tilingVTwoBases, Finset.mem_filter] at hb
  exact ⟨hb.1.1.1, hb.1.2, hb.1.1.2.2, hb.2⟩

/-! ## Monotonicity of the literal endpoint chain -/

/-- Endpoint-chain local time is monotone in physical time on the actual
simple-walk support.  The endpoint phase discards an incomplete final block,
so extending the physical prefix only appends to the deleted endpoint word. -/
theorem tilingSourceExternalBaseLocalTime_mono_of_valid
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (b : Point)
    {n N : ℕ} (hnN : n ≤ N) (hvalid : s ∈ validStepWalk) :
    tilingSourceExternalBaseLocalTime t o s n b ≤
      tilingSourceExternalBaseLocalTime t o s N b := by
  let omega := stepsOfWalk s
  have hs : trajectory omega = s := hvalid
  rw [← hs]
  cases o with
  | even =>
      change phasedExternalVertexLocalTime t .even .endpoint
          (finitePathList (pathPrefix (trajectory omega) n)) b ≤
        phasedExternalVertexLocalTime t .even .endpoint
          (finitePathList (pathPrefix (trajectory omega) N)) b
      rw [phasedExternalEndpointLocalTime_even,
        phasedExternalEndpointLocalTime_even]
      exact (tilingRawEndpointPath_prefix t (0, 0) 0
        (Nat.div_le_div_right hnN) omega).count_le b
  | shifted =>
      by_cases hn : n = 0
      · subst n
        exact Nat.zero_le _
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hNpos : 0 < N := hnpos.trans_le hnN
        change phasedExternalVertexLocalTime t .shifted .endpoint
            (finitePathList (pathPrefix (trajectory omega) n)) b ≤
          phasedExternalVertexLocalTime t .shifted .endpoint
            (finitePathList (pathPrefix (trajectory omega) N)) b
        rw [phasedExternalEndpointLocalTime_shifted t omega n hnpos,
          phasedExternalEndpointLocalTime_shifted t omega N hNpos]
        exact (tilingRawEndpointPath_prefix t (trajectory omega 1) 1
          (Nat.div_le_div_right (Nat.sub_le_sub_right hnN 1)) omega).count_le b

/-! ## The two source-balance pieces -/

/-- Restricted `Theta` bases at the rank-`k` creation clock whose source
external local time is in the Proposition 4.4 relevant-site regime. -/
def orientedRestrictedThetaHighAtCreation (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) (s : WalkPath) : Finset Point :=
  (orientedTilingThetaAtCreation t o m k w externalLow externalHigh s).filter
    fun b ↦ hlozThickLevel44 m ≤
      tilingSourceExternalBaseLocalTime t o s (creationTimeNat m k s) b

/-- The complementary low-external part.  This is the part to which the
stronger `m^(3/4)` geometric deviation is applied. -/
def orientedRestrictedThetaLowAtCreation (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) (s : WalkPath) : Finset Point :=
  (orientedTilingThetaAtCreation t o m k w externalLow externalHigh s).filter
    fun b ↦ tilingSourceExternalBaseLocalTime t o s
      (creationTimeNat m k s) b < hlozThickLevel44 m

theorem orientedTilingThetaAtCreation_eq_high_union_low
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) (s : WalkPath) :
    orientedTilingThetaAtCreation t o m k w externalLow externalHigh s =
      orientedRestrictedThetaHighAtCreation t o m k w externalLow externalHigh s ∪
        orientedRestrictedThetaLowAtCreation t o m k w externalLow externalHigh s := by
  ext b
  simp only [orientedRestrictedThetaHighAtCreation,
    orientedRestrictedThetaLowAtCreation, Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hb
    by_cases h : hlozThickLevel44 m ≤
        tilingSourceExternalBaseLocalTime t o s (creationTimeNat m k s) b
    · exact Or.inl ⟨hb, h⟩
    · exact Or.inr ⟨hb, Nat.lt_of_not_ge h⟩
  · rintro (⟨hb, _⟩ | ⟨hb, _⟩) <;> exact hb

/-- Proposition 4.4 candidates with no distinguished sites removed. -/
def orientedThetaCandidateSites44 (t : DominoTiling) (o : Orientation)
    (m : ℕ) (s : WalkPath) : Finset Point :=
  tilingSourceExternalCandidateSites t o (hlozCutoff44 m)
    (hlozThickLevel44 m) (fun _ ↦ ∅) s

def orientedThetaCandidateOverflow44 (t : DominoTiling) (o : Orientation)
    (m : ℕ) : Set WalkPath :=
  tilingSourceExternalCandidateOverflow t o (hlozCutoff44 m)
    (hlozThickLevel44 m) (hlozSiteBudget44 m) (fun _ ↦ ∅)

/-- One high-external candidate slot.  The relevant-site Finset is evaluated
at the deterministic Proposition 4.4 cutoff. -/
def orientedThetaHighSlotBad (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ)
    (slot : Fin (hlozSiteBudget44 m)) : Set WalkPath :=
  {s | s ∈ validStepWalk ∧ creationTimeNat m k s ≤ hlozCutoff44 m ∧
    ∃ b, finsetSlot (orientedThetaCandidateSites44 t o m s) slot = some b ∧
      b ∈ orientedRestrictedThetaHighAtCreation t o m k w externalLow
        externalHigh s}

/-- One low-external physical-time slot.  Its one-site law uses the stronger
large deviation below. -/
def orientedThetaLowSlotBad (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ)
    (slot : Fin (hlozCutoff44 m + 1)) : Set WalkPath :=
  {s | s ∈ validStepWalk ∧ creationTimeNat m k s ≤ hlozCutoff44 m ∧
    ∃ b, finsetSlot
        (orientedRestrictedThetaLowAtCreation t o m k w externalLow
          externalHigh s) slot = some b}

def someOrientedThetaHighSlotBad (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (Finset.univ : Finset (Fin (hlozSiteBudget44 m)))
    (orientedThetaHighSlotBad t o m k w externalLow externalHigh)

def someOrientedThetaLowSlotBad (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (Finset.univ : Finset (Fin (hlozCutoff44 m + 1)))
    (orientedThetaLowSlotBad t o m k w externalLow externalHigh)

/-- The exact paid event for one oriented restricted-Theta screen. -/
def orientedRestrictedThetaPaidEvent (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) : Set WalkPath :=
  validStepWalkᶜ ∪ (orientedThetaCandidateOverflow44 t o m ∪
    (someOrientedThetaHighSlotBad t o m k w externalLow externalHigh ∪
      someOrientedThetaLowSlotBad t o m k w externalLow externalHigh))

/-! ## Deterministic support and slot routing -/

lemma orientedRestrictedThetaHighAtCreation_subset_candidates44
    {t : DominoTiling} {o : Orientation}
    {m k w externalLow externalHigh : ℕ} {s : WalkPath}
    (hvalid : s ∈ validStepWalk)
    (hclock : creationTimeNat m k s ≤ hlozCutoff44 m) :
    orientedRestrictedThetaHighAtCreation t o m k w externalLow externalHigh s ⊆
      orientedThetaCandidateSites44 t o m s := by
  intro b hb
  rw [orientedRestrictedThetaHighAtCreation, Finset.mem_filter] at hb
  have hbtheta := hb.1
  have hcompatible : OrientationCompatible o b := by
    rw [orientedTilingThetaAtCreation, orientedTilingThetaBases,
      Finset.mem_filter, mem_orientedTilingVTwoBases_iff] at hbtheta
    exact hbtheta.1.2
  apply mem_tilingSourceExternalCandidateSites_of_thick
    (Nat.succ_pos _) hcompatible
  · exact hb.2.trans
      (tilingSourceExternalBaseLocalTime_mono_of_valid t o s b hclock hvalid)
  · simp

theorem restrictedTheta_onTime_subset_paid
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) :
    {s | creationTimeNat m k s ≤ hlozCutoff44 m ∧
      orientedTilingThetaAtCreation t o m k w externalLow externalHigh s ≠ ∅} ⊆
      orientedRestrictedThetaPaidEvent t o m k w externalLow externalHigh := by
  intro s hs
  rcases hs with ⟨hclock, htheta⟩
  by_cases hvalid : s ∈ validStepWalk
  · rw [orientedTilingThetaAtCreation_eq_high_union_low] at htheta
    by_cases hhigh :
        (orientedRestrictedThetaHighAtCreation t o m k w externalLow
          externalHigh s).Nonempty
    · by_cases hoverflow : s ∈ orientedThetaCandidateOverflow44 t o m
      · right; left
        exact hoverflow
      · right; right; left
        obtain ⟨b, hb⟩ := hhigh
        have hbcand := orientedRestrictedThetaHighAtCreation_subset_candidates44
          hvalid hclock hb
        obtain ⟨j, hjlt, hj⟩ := exists_finsetSlot_eq_some hbcand
        have hjbudget : j < hlozSiteBudget44 m :=
          hjlt.trans_le (tilingSourceExternalCandidateSites_card_le_of_not_overflow
            hoverflow)
        refine ⟨⟨j, hjbudget⟩, Finset.mem_univ _, ?_⟩
        exact ⟨hvalid, hclock, b, by simpa using hj, hb⟩
    · right; right; right
      have hlow :
          (orientedRestrictedThetaLowAtCreation t o m k w externalLow
            externalHigh s).Nonempty := by
        obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr htheta
        rw [Finset.mem_union] at hb
        rcases hb with hb | hb
        · exact (hhigh ⟨b, hb⟩).elim
        · exact ⟨b, hb⟩
      obtain ⟨b, hb⟩ := hlow
      obtain ⟨j, hjlt, hj⟩ := exists_finsetSlot_eq_some hb
      have hcard :
          (orientedRestrictedThetaLowAtCreation t o m k w externalLow
            externalHigh s).card ≤ creationTimeNat m k s + 1 := by
        calc
          _ ≤ (orientedTilingThetaAtCreation t o m k w externalLow
              externalHigh s).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          _ ≤ (orientedTilingVTwoBases t o
              (shellZeroSourceTotalWindow m w ∪
                shellZeroReplacementTotalWindow m w) s
              (creationTimeNat m k s)).card := by
            exact Finset.card_le_card (Finset.filter_subset _ _)
          _ ≤ (tilingVTwoBases t
              (shellZeroSourceTotalWindow m w ∪
                shellZeroReplacementTotalWindow m w) s
              (creationTimeNat m k s)).card := by
            exact Finset.card_le_card (Finset.filter_subset _ _)
          _ ≤ (visitedTilingBases t s (creationTimeNat m k s)).card := by
            exact Finset.card_le_card (Finset.filter_subset _ _)
          _ ≤ (visitedSites s (creationTimeNat m k s)).card := by
            unfold visitedTilingBases
            exact Finset.card_image_le
          _ ≤ creationTimeNat m k s + 1 := by
            unfold visitedSites visitedPrefix
            calc
              (Finset.univ.image
                  (pathPrefix s (creationTimeNat m k s))).card ≤
                  (Finset.univ : Finset
                    (Fin (creationTimeNat m k s + 1))).card :=
                Finset.card_image_le
              _ = creationTimeNat m k s + 1 := by simp
      have hjcut : j < hlozCutoff44 m + 1 := by omega
      refine ⟨⟨j, hjcut⟩, Finset.mem_univ _, ?_⟩
      exact ⟨hvalid, hclock, b, by simpa using hj⟩
  · left
    exact hvalid

/-! ## Literal per-slot trace data -/

/-- The strong low-external deviation in the second half of Proposition 4.5. -/
noncomputable def thetaLowDeviation (m : ℕ) : ℝ :=
  9 * (m : ℝ) ^ (3 / 4 : ℝ)

noncomputable def thetaLowRateScale (m : ℕ) : ℝ :=
  (m : ℝ) ^ (1 / 2 : ℝ)

noncomputable def thetaHighOneSlotCost (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
    ENNReal.ofReal (Real.exp (-17 * balanceRateScale m))

noncomputable def thetaLowOneSlotCost (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-17 * thetaLowRateScale m))

/-! ## Exact source-window deviation arithmetic -/

/-- If the retained endpoint count lies below the concrete source window,
then every local-time total in `I₀ ∪ I₁` is an upper geometric-tail
deviation.  The shell width is fixed to the source value; no arbitrary
external-window premise is used. -/
theorem theta_high_lower_deviation
    {m w i v : ℕ}
    (hi : i < shellZeroExternalLow48 m)
    (hw : w = HLOZProposition48Candidates.shellWidth48 m)
    (htotal : i + v ∈ shellZeroSourceTotalWindow m w ∪
      shellZeroReplacementTotalWindow m w) :
    (i : ℝ) / 15 + geometricDeviation m ≤ (v : ℝ) := by
  have hiR : (i : ℝ) < (15 / 16 : ℝ) *
      ((m : ℝ) - shellZeroCenterRadius m) := by
    exact Nat.lt_ceil.mp hi
  have hmw : (m : ℝ) - (w : ℝ) < ((m - w + 1 : ℕ) : ℝ) := by
    by_cases hwm : w ≤ m
    · rw [Nat.cast_add, Nat.cast_sub hwm, Nat.cast_one]
      linarith
    · have hlt : (m : ℝ) < (w : ℝ) := by
        exact_mod_cast Nat.lt_of_not_ge hwm
      have : (0 : ℝ) ≤ ((m - w + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  have htotalR : (m : ℝ) - (w : ℝ) < (i + v : ℕ) := by
    rw [Finset.mem_union] at htotal
    rcases htotal with hs | hr
    · simp only [mem_shellZeroSourceTotalWindow] at hs
      exact hmw.trans_le (by exact_mod_cast hs.1)
    · simp only [mem_shellZeroReplacementTotalWindow] at hr
      have hle : m - w + 1 ≤ m + 1 := by omega
      exact hmw.trans_le (by exact_mod_cast hle.trans hr.1)
  subst w
  unfold shellZeroCenterRadius at hiR
  norm_num only [Nat.cast_add] at htotalR
  nlinarith

/-- The upper side of the concrete retained-count window gives the lower
geometric tail for every total in `I₀ ∪ I₁`. -/
theorem theta_high_upper_deviation
    {m w i v : ℕ}
    (hi : shellZeroExternalHigh48 m ≤ i)
    (hw : w = HLOZProposition48Candidates.shellWidth48 m)
    (htotal : i + v ∈ shellZeroSourceTotalWindow m w ∪
      shellZeroReplacementTotalWindow m w) :
    (v : ℝ) ≤ (i : ℝ) / 15 - geometricDeviation m := by
  have hfloor : Nat.floor ((15 / 16 : ℝ) *
      ((m : ℝ) + shellZeroCenterRadius m)) < i := by
    unfold shellZeroExternalHigh48 at hi
    omega
  have hcenter0 : 0 ≤ (15 / 16 : ℝ) *
      ((m : ℝ) + shellZeroCenterRadius m) := by
    apply mul_nonneg (by norm_num)
    unfold shellZeroCenterRadius
    exact add_nonneg (Nat.cast_nonneg _)
      (add_nonneg (Nat.cast_nonneg _) (geometricDeviation_nonneg m))
  have hiR : (15 / 16 : ℝ) *
      ((m : ℝ) + shellZeroCenterRadius m) < (i : ℝ) :=
    (Nat.floor_lt hcenter0).mp hfloor
  have htotalR : ((i + v : ℕ) : ℝ) < (m : ℝ) + (w : ℝ) := by
    rw [Finset.mem_union] at htotal
    rcases htotal with hs | hr
    · simp only [mem_shellZeroSourceTotalWindow] at hs
      exact_mod_cast (hs.2.trans_le (Nat.le_add_right m w))
    · simp only [mem_shellZeroReplacementTotalWindow] at hr
      exact_mod_cast hr.2
  subst w
  unfold shellZeroCenterRadius at hiR
  norm_num only [Nat.cast_add] at htotalR
  nlinarith

/-- Below the Proposition 4.4 thick threshold, a near-level total forces the
larger `m^(3/4)` upper deviation used in the second half of Proposition 4.5. -/
theorem theta_low_deviation_of_total
    {m w i v : ℕ}
    (hi : i < hlozThickLevel44 m)
    (htotal : i + v ∈ shellZeroSourceTotalWindow m w ∪
      shellZeroReplacementTotalWindow m w)
    (hthreshold0 : 0 ≤ hlozThickThresholdReal44 m)
    (hdom : (w : ℝ) + thetaLowDeviation m ≤
      (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ)) :
    (i : ℝ) / 15 + thetaLowDeviation m ≤ (v : ℝ) := by
  have hiFloor : i ≤ Nat.floor (hlozThickThresholdReal44 m) := by
    unfold hlozThickLevel44 at hi
    omega
  have hiR : (i : ℝ) ≤ hlozThickThresholdReal44 m :=
    (show (i : ℝ) ≤ (Nat.floor (hlozThickThresholdReal44 m) : ℕ) by
      exact_mod_cast hiFloor).trans (Nat.floor_le hthreshold0)
  have hmw : (m : ℝ) - (w : ℝ) < ((m - w + 1 : ℕ) : ℝ) := by
    by_cases hwm : w ≤ m
    · rw [Nat.cast_add, Nat.cast_sub hwm, Nat.cast_one]
      linarith
    · have hlt : (m : ℝ) < (w : ℝ) := by
        exact_mod_cast Nat.lt_of_not_ge hwm
      have : (0 : ℝ) ≤ ((m - w + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  have htotalR : (m : ℝ) - (w : ℝ) < (i + v : ℕ) := by
    rw [Finset.mem_union] at htotal
    rcases htotal with hs | hr
    · simp only [mem_shellZeroSourceTotalWindow] at hs
      exact hmw.trans_le (by exact_mod_cast hs.1)
    · simp only [mem_shellZeroReplacementTotalWindow] at hr
      have hle : m - w + 1 ≤ m + 1 := by omega
      exact hmw.trans_le (by exact_mod_cast hle.trans hr.1)
  unfold hlozThickThresholdReal44 at hiR
  norm_num only [Nat.cast_add] at htotalR
  nlinarith

/-- All deterministic scale comparisons required by the low-external slot
are eventually true at the concrete source width. -/
theorem eventually_theta_low_arithmetic :
    ∀ᶠ m : ℕ in atTop,
      0 ≤ hlozThickThresholdReal44 m ∧
      (HLOZProposition48Candidates.shellWidth48 m : ℝ) +
          thetaLowDeviation m ≤
        (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ) ∧
      thetaLowDeviation m ≤ (m : ℝ) / 2 := by
  have hwidth :=
    HLOZSharpWindowProductClosure.eventually_shellWidth48_cast_le_two_rpow
  have hthreeQuarter := eventually_const_mul_nat_rpow_le
    (180 : ℝ) (3 / 4 : ℝ) (4 / 5 : ℝ) (by norm_num)
  have hkappa := eventually_const_mul_nat_rpow_le
    (40 : ℝ) kappaOne (4 / 5 : ℝ) (by norm_num [kappaOne])
  have hpositive := eventually_const_mul_nat_rpow_le
    (16 / 15 : ℝ) (4 / 5 : ℝ) 1 (by norm_num)
  have hhalf := eventually_const_mul_nat_rpow_le
    (18 : ℝ) (3 / 4 : ℝ) 1 (by norm_num)
  filter_upwards [hwidth, hthreeQuarter, hkappa, hpositive, hhalf]
      with m hwidthM hthreeM hkappaM hpositiveM hhalfM
  constructor
  · unfold hlozThickThresholdReal44
    simp only [Real.rpow_one] at hpositiveM
    nlinarith
  constructor
  · simp only [thetaLowDeviation]
    nlinarith
  · simp only [thetaLowDeviation, Real.rpow_one] at hhalfM ⊢
    calc
      9 * (m : ℝ) ^ (3 / 4 : ℝ) =
          (18 * (m : ℝ) ^ (3 / 4 : ℝ)) / 2 := by ring
      _ ≤ (m : ℝ) / 2 :=
        div_le_div_of_nonneg_right hhalfM (by norm_num)

lemma thetaLowDeviation_nonneg (m : ℕ) : 0 ≤ thetaLowDeviation m := by
  unfold thetaLowDeviation
  positivity

lemma thetaLowDeviation_sq_div_four {m : ℕ} (hm : 0 < m) :
    thetaLowDeviation m ^ 2 / (4 * (m : ℝ)) =
      (81 / 4 : ℝ) * thetaLowRateScale m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpow :
      ((m : ℝ) ^ (3 / 4 : ℝ)) ^ 2 =
        (m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) := by
    calc
      ((m : ℝ) ^ (3 / 4 : ℝ)) ^ 2 =
          ((m : ℝ) ^ (3 / 4 : ℝ)) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = (m : ℝ) ^ ((3 / 4 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul hmR.le _ _).symm
      _ = (m : ℝ) ^ ((1 / 2 : ℝ) + 1) := by congr 1; norm_num
      _ = (m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) := by
        rw [Real.rpow_add hmR, Real.rpow_one]
  unfold thetaLowDeviation thetaLowRateScale
  rw [mul_pow, hpow]
  field_simp
  ring

lemma seventeen_thetaLowRateScale_le_rate {m : ℕ} (hm : 0 < m) :
    17 * thetaLowRateScale m ≤
      thetaLowDeviation m ^ 2 / (4 * (m : ℝ)) := by
  rw [thetaLowDeviation_sq_div_four hm]
  exact mul_le_mul_of_nonneg_right (by norm_num)
    (by unfold thetaLowRateScale; positivity)

/-- Literal geometric law for the large low-external deviation. -/
theorem geometricSum_upper_tail_le_thetaLowCost
    {m i : ℕ} (hm : 0 < m) (hi : 0 < i) (him : i ≤ m)
    (hdeviation : thetaLowDeviation m ≤ i) :
    (GeometricChernoff.geometric15Vector i).real
        {g | (i : ℝ) / 15 + thetaLowDeviation m ≤
          GeometricChernoff.geometricSum g} ≤
      Real.exp (-17 * thetaLowRateScale m) := by
  refine (GeometricChernoff.geometricSum_upper_tail i hi
    (thetaLowDeviation_nonneg m) hdeviation).trans ?_
  apply Real.exp_le_exp.mpr
  rw [show -thetaLowDeviation m ^ 2 / (4 * (i : ℝ)) =
      -(thetaLowDeviation m ^ 2 / (4 * (i : ℝ))) by ring,
    show -17 * thetaLowRateScale m =
      -(17 * thetaLowRateScale m) by ring]
  apply neg_le_neg
  refine (seventeen_thetaLowRateScale_le_rate hm).trans ?_
  have hsquare : 0 ≤ thetaLowDeviation m ^ 2 := sq_nonneg _
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have himR : (i : ℝ) ≤ m := by exact_mod_cast him
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ))
      (by positivity : (0 : ℝ) < 4 * (i : ℝ))]
  nlinarith

/-! ## Literal negative-binomial window masses -/

/-- The two translated first-strip windows used by the source and its
replacement. -/
def thetaFailureWindow (m w i : ℕ) : Finset ℕ :=
  shellZeroSourceFailureWindow m w i ∪
    shellZeroReplacementFailureWindow m w i

lemma add_mem_total_union_of_mem_thetaFailureWindow
    {m w i v : ℕ} (hv : v ∈ thetaFailureWindow m w i) :
    i + v ∈ shellZeroSourceTotalWindow m w ∪
      shellZeroReplacementTotalWindow m w := by
  rw [thetaFailureWindow, Finset.mem_union] at hv
  rw [Finset.mem_union]
  rcases hv with hs | hr
  · left
    simp only [mem_shellZeroSourceFailureWindow] at hs
    simp only [mem_shellZeroSourceTotalWindow]
    omega
  · right
    simp only [mem_shellZeroReplacementFailureWindow] at hr
    simp only [mem_shellZeroReplacementTotalWindow]
    omega

lemma retained_lt_total_upper_of_mem_thetaFailureWindow
    {m w i v : ℕ} (hv : v ∈ thetaFailureWindow m w i) :
    i < m + w := by
  rw [thetaFailureWindow, Finset.mem_union] at hv
  rcases hv with hs | hr
  · simp only [mem_shellZeroSourceFailureWindow] at hs
    omega
  · simp only [mem_shellZeroReplacementFailureWindow] at hr
    omega

lemma seventeen_balanceRateScale_le_geometric_rate_add_width
    {m w : ℕ} (hm : 0 < m) (hw : (w : ℝ) ≤ (m : ℝ) / 10) :
    17 * balanceRateScale m ≤
      geometricDeviation m ^ 2 / (4 * ((m + w : ℕ) : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : (0 : ℝ) < 4 * ((m + w : ℕ) : ℝ) := by positivity
  have heq := geometricDeviation_sq_div_four hm
  have hrate0 := balanceRateScale_nonneg m
  rw [le_div_iff₀ hden]
  rw [div_eq_iff (by positivity : (4 * (m : ℝ)) ≠ 0)] at heq
  norm_num only [Nat.cast_add]
  nlinarith

lemma seventeen_thetaLowRateScale_le_rate_add_width
    {m w : ℕ} (hm : 0 < m) (hw : (w : ℝ) ≤ (m : ℝ) / 10) :
    17 * thetaLowRateScale m ≤
      thetaLowDeviation m ^ 2 / (4 * ((m + w : ℕ) : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : (0 : ℝ) < 4 * ((m + w : ℕ) : ℝ) := by positivity
  have heq := thetaLowDeviation_sq_div_four hm
  have hrate0 : 0 ≤ thetaLowRateScale m := by
    unfold thetaLowRateScale
    positivity
  rw [le_div_iff₀ hden]
  rw [div_eq_iff (by positivity : (4 * (m : ℝ)) ≠ 0)] at heq
  norm_num only [Nat.cast_add]
  nlinarith

/-- High-external lower-side imbalance: the exact finite lazy-total window
has the source's `exp (-17 S_m)` mass bound. -/
theorem thetaFailureWindowMass_le_high_lower_cost
    {m w i : ℕ} (hm : 0 < m) (hi : 0 < i)
    (hwidth : (w : ℝ) ≤ (m : ℝ) / 10)
    (hiExternal : i < shellZeroExternalLow48 m)
    (hw : w = HLOZProposition48Candidates.shellWidth48 m)
    (hdeviation : geometricDeviation m ≤ (m + w : ℕ)) :
    SmallWindow.windowMass i (thetaFailureWindow m w i) ≤
      Real.exp (-17 * balanceRateScale m) := by
  by_cases hempty : thetaFailureWindow m w i = ∅
  · rw [hempty, SmallWindow.windowMass]
    simp only [Finset.sum_empty]
    positivity
  obtain ⟨v0, hv0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have him : i ≤ m + w :=
    (retained_lt_total_upper_of_mem_thetaFailureWindow hv0).le
  let a := geometricDeviation m
  let k := Nat.ceil ((i : ℝ) / 15 + a)
  have hwindow : ∀ v ∈ thetaFailureWindow m w i, k ≤ v := by
    intro v hv
    apply Nat.ceil_le.mpr
    exact theta_high_lower_deviation hiExternal hw
      (add_mem_total_union_of_mem_thetaFailureWindow hv)
  have hmw : 0 < m + w := by omega
  have hraw := windowMass_le_exp_neg_upper_ambient hmw hi him
    (geometricDeviation_nonneg m) hdeviation (Nat.le_ceil _) _ hwindow
  refine hraw.trans ?_
  apply Real.exp_le_exp.mpr
  rw [show -geometricDeviation m ^ 2 / (4 * ((m + w : ℕ) : ℝ)) =
      -(geometricDeviation m ^ 2 / (4 * ((m + w : ℕ) : ℝ))) by ring,
    show -17 * balanceRateScale m = -(17 * balanceRateScale m) by ring]
  exact neg_le_neg
    (seventeen_balanceRateScale_le_geometric_rate_add_width hm hwidth)

/-- High-external upper-side imbalance, using the exact lower tail. -/
theorem thetaFailureWindowMass_le_high_upper_cost
    {m w i : ℕ} (hm : 0 < m) (hi : 0 < i)
    (hwidth : (w : ℝ) ≤ (m : ℝ) / 10)
    (hiExternal : shellZeroExternalHigh48 m ≤ i)
    (hw : w = HLOZProposition48Candidates.shellWidth48 m)
    (hdeviation : geometricDeviation m ≤ (m + w : ℕ)) :
    SmallWindow.windowMass i (thetaFailureWindow m w i) ≤
      Real.exp (-17 * balanceRateScale m) := by
  by_cases hempty : thetaFailureWindow m w i = ∅
  · rw [hempty, SmallWindow.windowMass]
    simp only [Finset.sum_empty]
    positivity
  obtain ⟨v0, hv0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have him : i ≤ m + w :=
    (retained_lt_total_upper_of_mem_thetaFailureWindow hv0).le
  have hmean : geometricDeviation m ≤ (i : ℝ) / 15 := by
    have hdev := theta_high_upper_deviation hiExternal hw
      (add_mem_total_union_of_mem_thetaFailureWindow hv0)
    have hv0R : (0 : ℝ) ≤ v0 := Nat.cast_nonneg _
    linarith
  let a := geometricDeviation m
  let k := Nat.floor ((i : ℝ) / 15 - a)
  have hnonneg : 0 ≤ (i : ℝ) / 15 - a := sub_nonneg.mpr hmean
  have hwindow : ∀ v ∈ thetaFailureWindow m w i, v ≤ k := by
    intro v hv
    apply Nat.le_floor
    exact theta_high_upper_deviation hiExternal hw
      (add_mem_total_union_of_mem_thetaFailureWindow hv)
  have hmw : 0 < m + w := by omega
  have hraw := windowMass_le_exp_neg_lower_ambient hmw hi him
    (geometricDeviation_nonneg m) hdeviation (Nat.floor_le hnonneg) _ hwindow
  refine hraw.trans ?_
  apply Real.exp_le_exp.mpr
  rw [show -geometricDeviation m ^ 2 / (4 * ((m + w : ℕ) : ℝ)) =
      -(geometricDeviation m ^ 2 / (4 * ((m + w : ℕ) : ℝ))) by ring,
    show -17 * balanceRateScale m = -(17 * balanceRateScale m) by ring]
  exact neg_le_neg
    (seventeen_balanceRateScale_le_geometric_rate_add_width hm hwidth)

/-- Low-external half of Proposition 4.5.  The ambient-scale Chernoff theorem
is essential here: no false condition `thetaLowDeviation m ≤ i` is needed. -/
theorem thetaFailureWindowMass_le_low_cost
    {m w i : ℕ} (hm : 0 < m) (hi : 0 < i)
    (hwidth : (w : ℝ) ≤ (m : ℝ) / 10)
    (hiExternal : i < hlozThickLevel44 m)
    (hthreshold0 : 0 ≤ hlozThickThresholdReal44 m)
    (hdom : (w : ℝ) + thetaLowDeviation m ≤
      (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ))
    (hdeviation : thetaLowDeviation m ≤ (m + w : ℕ)) :
    SmallWindow.windowMass i (thetaFailureWindow m w i) ≤
      Real.exp (-17 * thetaLowRateScale m) := by
  by_cases hempty : thetaFailureWindow m w i = ∅
  · rw [hempty, SmallWindow.windowMass]
    simp only [Finset.sum_empty]
    positivity
  obtain ⟨v0, hv0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have him : i ≤ m + w :=
    (retained_lt_total_upper_of_mem_thetaFailureWindow hv0).le
  let a := thetaLowDeviation m
  let k := Nat.ceil ((i : ℝ) / 15 + a)
  have hwindow : ∀ v ∈ thetaFailureWindow m w i, k ≤ v := by
    intro v hv
    apply Nat.ceil_le.mpr
    exact theta_low_deviation_of_total hiExternal
      (add_mem_total_union_of_mem_thetaFailureWindow hv)
      hthreshold0 hdom
  have hmw : 0 < m + w := by omega
  have hraw := windowMass_le_exp_neg_upper_ambient hmw hi him
    (thetaLowDeviation_nonneg m) hdeviation (Nat.le_ceil _) _ hwindow
  refine hraw.trans ?_
  apply Real.exp_le_exp.mpr
  rw [show -thetaLowDeviation m ^ 2 / (4 * ((m + w : ℕ) : ℝ)) =
      -(thetaLowDeviation m ^ 2 / (4 * ((m + w : ℕ) : ℝ))) by ring,
    show -17 * thetaLowRateScale m =
      -(17 * thetaLowRateScale m) by ring]
  exact neg_le_neg
    (seventeen_thetaLowRateScale_le_rate_add_width hm hwidth)

/-- Literal stopped-product certificates for the two finite slot families.
These fields are coordinate-mass certificates, not event-probability bounds. -/
structure OrientedThetaTraceData (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) where
  high : ∀ slot : Fin (hlozSiteBudget44 m),
    SomeTraceCappedProductScreening Set.univ
      (orientedThetaHighSlotBad t o m k w externalLow externalHigh slot)
      (thetaHighOneSlotCost m)
  low : ∀ slot : Fin (hlozCutoff44 m + 1),
    SomeTraceCappedProductScreening Set.univ
      (orientedThetaLowSlotBad t o m k w externalLow externalHigh slot)
      (thetaLowOneSlotCost m)
  measurable_high : ∀ slot, MeasurableSet
    (orientedThetaHighSlotBad t o m k w externalLow externalHigh slot)
  measurable_low : ∀ slot, MeasurableSet
    (orientedThetaLowSlotBad t o m k w externalLow externalHigh slot)

private theorem simpleRandomWalk_bad_le_of_univ_trace
    {bad : Set WalkPath} {cost : ℝ≥0∞}
    (hbad : MeasurableSet bad) (hcost : cost ≠ ∞)
    (screen : SomeTraceCappedProductScreening Set.univ bad cost) :
    simpleRandomWalk bad ≤ cost := by
  calc
    simpleRandomWalk bad ≤ cost * simpleRandomWalk (Set.univ : Set WalkPath) :=
      @transition_measure_le_of_traceCappedProductScreening screen.Index
        screen.countableIndex Set.univ bad hbad cost hcost screen.screening
    _ = cost := by simp

theorem simpleRandomWalk_someOrientedThetaHighSlotBad_le
    {t : DominoTiling} {o : Orientation}
    {m k w externalLow externalHigh : ℕ}
    (data : OrientedThetaTraceData t o m k w externalLow externalHigh) :
    simpleRandomWalk
        (someOrientedThetaHighSlotBad t o m k w externalLow externalHigh) ≤
      (hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m := by
  calc
    simpleRandomWalk
        (someOrientedThetaHighSlotBad t o m k w externalLow externalHigh) ≤
      ∑ slot : Fin (hlozSiteBudget44 m),
        simpleRandomWalk
          (orientedThetaHighSlotBad t o m k w externalLow externalHigh slot) :=
      Screening.measure_someCandidateBad_le_sum simpleRandomWalk _ _
    _ ≤ ∑ _slot : Fin (hlozSiteBudget44 m), thetaHighOneSlotCost m := by
      gcongr with slot
      exact simpleRandomWalk_bad_le_of_univ_trace
        (data.measurable_high slot) (by simp [thetaHighOneSlotCost])
          (data.high slot)
    _ = (hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m := by simp

theorem simpleRandomWalk_someOrientedThetaLowSlotBad_le
    {t : DominoTiling} {o : Orientation}
    {m k w externalLow externalHigh : ℕ}
    (data : OrientedThetaTraceData t o m k w externalLow externalHigh) :
    simpleRandomWalk
        (someOrientedThetaLowSlotBad t o m k w externalLow externalHigh) ≤
      (hlozCutoff44 m + 1 : ℕ) * thetaLowOneSlotCost m := by
  calc
    simpleRandomWalk
        (someOrientedThetaLowSlotBad t o m k w externalLow externalHigh) ≤
      ∑ slot : Fin (hlozCutoff44 m + 1),
        simpleRandomWalk
          (orientedThetaLowSlotBad t o m k w externalLow externalHigh slot) :=
      Screening.measure_someCandidateBad_le_sum simpleRandomWalk _ _
    _ ≤ ∑ _slot : Fin (hlozCutoff44 m + 1), thetaLowOneSlotCost m := by
      gcongr with slot
      exact simpleRandomWalk_bad_le_of_univ_trace
        (data.measurable_low slot) (by simp [thetaLowOneSlotCost])
          (data.low slot)
    _ = (hlozCutoff44 m + 1 : ℕ) * thetaLowOneSlotCost m := by simp

/-- Total coefficient of the source-correct oriented Proposition 4.5 screen. -/
noncomputable def orientedThetaCost (m : ℕ) : ℝ≥0∞ :=
  hlozFailureRate44 m +
    (hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m +
    (hlozCutoff44 m + 1 : ℕ) * thetaLowOneSlotCost m

theorem simpleRandomWalk_orientedRestrictedThetaPaidEvent_le
    {t : DominoTiling} {o : Orientation}
    {m k w externalLow externalHigh : ℕ}
    (hcandidate : simpleRandomWalk (orientedThetaCandidateOverflow44 t o m) ≤
      hlozFailureRate44 m)
    (data : OrientedThetaTraceData t o m k w externalLow externalHigh) :
    simpleRandomWalk
        (orientedRestrictedThetaPaidEvent t o m k w externalLow externalHigh) ≤
      orientedThetaCost m := by
  unfold orientedRestrictedThetaPaidEvent orientedThetaCost
  calc
    simpleRandomWalk
        (validStepWalkᶜ ∪ (orientedThetaCandidateOverflow44 t o m ∪
          (someOrientedThetaHighSlotBad t o m k w externalLow externalHigh ∪
          someOrientedThetaLowSlotBad t o m k w externalLow externalHigh))) ≤
      simpleRandomWalk validStepWalkᶜ +
        (simpleRandomWalk (orientedThetaCandidateOverflow44 t o m) +
          (simpleRandomWalk
              (someOrientedThetaHighSlotBad t o m k w externalLow externalHigh) +
            simpleRandomWalk
              (someOrientedThetaLowSlotBad t o m k w externalLow externalHigh))) := by
      calc
        _ ≤ simpleRandomWalk validStepWalkᶜ +
            simpleRandomWalk
              (orientedThetaCandidateOverflow44 t o m ∪
                (someOrientedThetaHighSlotBad t o m k w externalLow externalHigh ∪
                  someOrientedThetaLowSlotBad t o m k w externalLow externalHigh)) :=
          measure_union_le _ _
        _ ≤ simpleRandomWalk validStepWalkᶜ +
            (simpleRandomWalk (orientedThetaCandidateOverflow44 t o m) +
              simpleRandomWalk
                (someOrientedThetaHighSlotBad t o m k w externalLow externalHigh ∪
                  someOrientedThetaLowSlotBad t o m k w externalLow externalHigh)) :=
          by
            gcongr
            exact measure_union_le _ _
        _ ≤ simpleRandomWalk validStepWalkᶜ +
            (simpleRandomWalk (orientedThetaCandidateOverflow44 t o m) +
              (simpleRandomWalk
                  (someOrientedThetaHighSlotBad t o m k w externalLow externalHigh) +
            simpleRandomWalk
                (someOrientedThetaLowSlotBad t o m k w externalLow externalHigh))) :=
          by
            gcongr
            exact measure_union_le _ _
    _ ≤ 0 + (hlozFailureRate44 m +
        ((hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m +
          (hlozCutoff44 m + 1 : ℕ) * thetaLowOneSlotCost m)) :=
      add_le_add
        HLOZLazyOverflowClosure.simpleRandomWalk_validStepWalk_compl.le
        (add_le_add hcandidate
          (add_le_add
            (simpleRandomWalk_someOrientedThetaHighSlotBad_le data)
            (simpleRandomWalk_someOrientedThetaLowSlotBad_le data)))
    _ = _ := by
      rw [zero_add]
      ac_rfl

/-! ## Source-scale numerical absorption -/

lemma hlozRateScale44_eq_balanceRateScale (m : ℕ) :
    hlozRateScale44 m = balanceRateScale m := by
  unfold hlozRateScale44 balanceRateScale kappaOne
  norm_num

theorem thetaHighBudgetCost_le_two_failureRate (m : ℕ) :
    (hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m ≤
      2 * hlozFailureRate44 m := by
  let S := hlozRateScale44 m
  have hbudgetReal : (hlozSiteBudget44 m : ℝ) ≤ Real.exp (16 * S) := by
    exact Nat.floor_le (Real.exp_nonneg _)
  have hbudget : (hlozSiteBudget44 m : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (16 * S)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_mono hbudgetReal
  have hexp : ENNReal.ofReal (Real.exp (16 * S)) *
      ENNReal.ofReal (Real.exp (-17 * S)) =
        ENNReal.ofReal (Real.exp (-S)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    ring
  rw [thetaHighOneSlotCost, hlozFailureRate44]
  rw [show balanceRateScale m = S by
    exact (hlozRateScale44_eq_balanceRateScale m).symm]
  calc
    (hlozSiteBudget44 m : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (-17 * S)) +
          ENNReal.ofReal (Real.exp (-17 * S))) =
      2 * ((hlozSiteBudget44 m : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-17 * S))) := by ring
    _ ≤ 2 * (ENNReal.ofReal (Real.exp (16 * S)) *
        ENNReal.ofReal (Real.exp (-17 * S))) := by gcongr
    _ = 2 * ENNReal.ofReal (Real.exp (-S)) := by rw [hexp]

theorem eventually_thetaLowBudgetCost_le_three_exp_neg_sqrt :
    ∀ᶠ m : ℕ in atTop,
      (hlozCutoff44 m + 1 : ℕ) * thetaLowOneSlotCost m ≤
        3 * ENNReal.ofReal (Real.exp (-15 * thetaLowRateScale m)) := by
  filter_upwards [eventually_hlozCutoffLog44_le_nine_fifths_sqrt]
      with m hlog
  let L := levelCutoffLog hlozDelta44 m
  let R := thetaLowRateScale m
  have hcutReal : ((hlozCutoff44 m + 1 : ℕ) : ℝ) ≤
      3 * Real.exp L := by
    simpa only [L] using hlozCutoff44_cast_add_one_le m
  have hcut : ((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (3 * Real.exp L) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_mono hcutReal
  have hexponent : L - 17 * R ≤ -15 * R := by
    have hR0 : 0 ≤ R := by
      dsimp only [R, thetaLowRateScale]
      positivity
    have hLR : L ≤ (9 / 5 : ℝ) * R := by
      simpa only [L, R, thetaLowRateScale] using hlog
    nlinarith
  rw [thetaLowOneSlotCost]
  calc
    ((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-17 * R)) ≤
      ENNReal.ofReal (3 * Real.exp L) *
        ENNReal.ofReal (Real.exp (-17 * R)) := by gcongr
    _ = 3 * ENNReal.ofReal (Real.exp (L - 17 * R)) := by
      rw [show ENNReal.ofReal (3 * Real.exp L) =
          3 * ENNReal.ofReal (Real.exp L) by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          ENNReal.ofReal_ofNat]]
      rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← Real.exp_add]
      congr 2
      ring
    _ ≤ 3 * ENNReal.ofReal (Real.exp (-15 * R)) := by
      gcongr

theorem eventually_orientedThetaCost_le_six_failureRate :
    ∀ᶠ m : ℕ in atTop,
      orientedThetaCost m ≤ 6 * hlozFailureRate44 m := by
  filter_upwards [eventually_thetaLowBudgetCost_le_three_exp_neg_sqrt,
      eventually_ge_atTop (1 : ℕ)] with m hlow hm
  let S := hlozRateScale44 m
  let R := thetaLowRateScale m
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hSR : S ≤ R := by
    dsimp only [S, R, hlozRateScale44, thetaLowRateScale]
    exact Real.rpow_le_rpow_of_exponent_le hmR (by norm_num)
  have hexp : Real.exp (-15 * R) ≤ Real.exp (-S) := by
    apply Real.exp_le_exp.mpr
    have hS0 : 0 ≤ S := by
      dsimp only [S, hlozRateScale44]
      positivity
    nlinarith
  have hlow' : (hlozCutoff44 m + 1 : ℕ) * thetaLowOneSlotCost m ≤
      3 * hlozFailureRate44 m := by
    refine hlow.trans ?_
    unfold hlozFailureRate44
    gcongr
  unfold orientedThetaCost
  have hhigh := thetaHighBudgetCost_le_two_failureRate m
  calc
    hlozFailureRate44 m +
        (hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m +
        (hlozCutoff44 m + 1 : ℕ) * thetaLowOneSlotCost m ≤
      hlozFailureRate44 m + 2 * hlozFailureRate44 m +
        3 * hlozFailureRate44 m := by gcongr
    _ = 6 * hlozFailureRate44 m := by ring

theorem eventually_orientedThetaCost_le_exp (c : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      orientedThetaCost m ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  have hpower := eventually_const_mul_log_sq_le_nat_rpow
    (Real.log 6 + c) (5 / 16 : ℝ) (by norm_num)
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_orientedThetaCost_le_six_failureRate, hpower,
      hlog.eventually (eventually_ge_atTop 1)] with m hcost hpowerM hlogM
  refine hcost.trans ?_
  unfold hlozFailureRate44 hlozRateScale44
  have hlogSq : 1 ≤ Real.log (m : ℝ) ^ 2 := by nlinarith
  have hdominates : Real.log (6 : ℕ) +
      c * Real.log (m : ℝ) ^ 2 ≤ (m : ℝ) ^ (5 / 16 : ℝ) := by
    calc
    Real.log (6 : ℕ) + c * Real.log (m : ℝ) ^ 2 ≤
        (Real.log 6 + c) * Real.log (m : ℝ) ^ 2 := by
      have hlog6 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
      norm_num only [Nat.cast_ofNat]
      nlinarith
    _ ≤ (m : ℝ) ^ (5 / 16 : ℝ) := hpowerM
  have h := Gap.ennreal_nat_mul_exp_neg_le_exp_neg (J := 6) (by norm_num)
    hdominates
  norm_num only [Nat.cast_ofNat] at h
  rw [show -(c * Real.log (m : ℝ) ^ 2) =
      -c * Real.log (m : ℝ) ^ 2 by ring] at h
  exact h

/-- Premise-free Proposition 4.4 payment for this exact candidate family. -/
theorem eventually_orientedThetaCandidateOverflow_lt_failureRate
    (t : DominoTiling) (o : Orientation) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (orientedThetaCandidateOverflow44 t o m) <
        hlozFailureRate44 m := by
  simpa [orientedThetaCandidateOverflow44] using
    (eventually_sourceCandidateOverflow_lt_failureRate t o
      (fun _ _ ↦ (∅ : Finset Point)))

/-- A family of literal slot certificates gives the complete oriented
restricted-Theta estimate, with Proposition 4.4 discharged internally. -/
theorem eventually_simpleRandomWalk_orientedRestrictedThetaPaidEvent_le_exp
    (t : DominoTiling) (o : Orientation) (k : ℕ)
    (w externalLow externalHigh : ℕ → ℕ)
    (data : ∀ m, OrientedThetaTraceData t o m k (w m)
      (externalLow m) (externalHigh m)) (c : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (orientedRestrictedThetaPaidEvent t o m k (w m)
        (externalLow m) (externalHigh m)) ≤
          ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  filter_upwards [eventually_orientedThetaCandidateOverflow_lt_failureRate t o,
      eventually_orientedThetaCost_le_exp c] with m hcandidate hcost
  exact (simpleRandomWalk_orientedRestrictedThetaPaidEvent_le
    hcandidate.le (data m)).trans hcost

theorem simpleRandomWalk_orientedRestrictedThetaPaidEvent_series_ne_top
    (t : DominoTiling) (o : Orientation) (k : ℕ)
    (w externalLow externalHigh : ℕ → ℕ)
    (data : ∀ m, OrientedThetaTraceData t o m k (w m)
      (externalLow m) (externalHigh m)) :
    ∑' m, simpleRandomWalk (orientedRestrictedThetaPaidEvent t o m k (w m)
      (externalLow m) (externalHigh m)) ≠ ∞ :=
  measure_series_ne_top_of_eventually_exp_neg_log_sq_bound simpleRandomWalk _
    (by norm_num : (0 : ℝ) < 1)
    (eventually_simpleRandomWalk_orientedRestrictedThetaPaidEvent_le_exp
      t o k w externalLow externalHigh data 1)

end

end Erdos1165.HLOZSourceOrientedThetaBalance
