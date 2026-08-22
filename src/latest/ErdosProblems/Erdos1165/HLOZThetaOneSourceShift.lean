/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZThetaSourceBalance
import ErdosProblems.Erdos1165.RestartBridge
import ErdosProblems.Erdos1165.WalkOneStepShift
import ErdosProblems.Erdos1165.WalkHorizontalReflection

/-!
# The genuine one-step source shift for the odd dominant class

The `M_o` part of the source screen is not a `V₂` base family on the
original path.  It is pulled back from a canonical base family after deleting
the first increment and recentering.  This file records the deterministic
local-time and threshold-clock transport for that operation.  The temporal
two-step prefix phase is not used as a substitute for this spatial shift.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZThetaOneSourceShift

open HLOZPathEvents HLOZThetaSourceBalance RestartBridge
open HLOZTilingGapBandExtraction
open TilingLazyDecomposition TilingShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

theorem oneStepRecenter_add_first (omega : StepPath) (n : ℕ) :
    oneStepRecenter (trajectory omega) n + trajectory omega 1 =
      trajectory omega (n + 1) := by
  rw [oneStepRecenter_trajectory]
  have h := trajectory_add_sub_trajectory omega 1 n
  rw [show 1 + n = n + 1 by omega] at h
  rw [sub_eq_iff_eq_add.mp h]

theorem localTime_zero_eq_if (s : WalkPath) (x : Point) :
    localTime s 0 x = if s 0 = x then 1 else 0 := by
  simp [localTime, localTimePrefix, pathPrefix]
  split <;> simp_all

/-- Apart from the discarded time-zero visit, local time is transported
exactly by the spatial recentering. -/
theorem localTime_oneStepRecenter_eq_of_ne_origin
    (omega : StepPath) (n : ℕ) (x : Point) (hx : x ≠ 0) :
    localTime (oneStepRecenter (trajectory omega)) n
        (x - trajectory omega 1) =
      localTime (trajectory omega) (n + 1) x := by
  induction n with
  | zero =>
      rw [localTime_succ]
      have hzeroLeft : localTime (oneStepRecenter (trajectory omega)) 0
          (x - trajectory omega 1) =
          if (0 : Point) = x - trajectory omega 1 then 1 else 0 := by
        rw [localTime_zero_eq_if, oneStepRecenter_zero]
      have hzeroRight : localTime (trajectory omega) 0 x = 0 := by
        rw [localTime_zero_eq_if, trajectory_zero,
          if_neg (by
            intro h
            apply hx
            rw [← h]
            rfl)]
      rw [hzeroLeft, hzeroRight, zero_add]
      by_cases h : (0 : Point) = x - trajectory omega 1
      · rw [if_pos h]
        have hxeq : trajectory omega 1 = x :=
          (sub_eq_zero.mp h.symm).symm
        rw [if_pos hxeq]
      · rw [if_neg h]
        have hne : trajectory omega 1 ≠ x := by
          intro heq
          apply h
          simp [heq]
        rw [if_neg hne]
  | succ n ih =>
      rw [localTime_succ, localTime_succ, ih]
      have hpos := oneStepRecenter_add_first omega (n + 1)
      by_cases h : oneStepRecenter (trajectory omega) (n + 1) =
          x - trajectory omega 1
      · rw [if_pos h]
        have h' : trajectory omega (n + 1 + 1) = x := by
          calc
            trajectory omega (n + 1 + 1) =
                oneStepRecenter (trajectory omega) (n + 1) +
                  trajectory omega 1 := hpos.symm
            _ = (x - trajectory omega 1) + trajectory omega 1 := by rw [h]
            _ = x := sub_add_cancel _ _
        rw [if_pos h']
      · rw [if_neg h]
        have h' : trajectory omega (n + 1 + 1) ≠ x := by
          intro heq
          apply h
          apply (eq_sub_iff_add_eq).2
          exact hpos.trans heq
        rw [if_neg h']

/-- If the discarded origin is below level `m`, the entire threshold set is
translated bijectively. -/
theorem thresholdSites_oneStepRecenter_eq_image
    (omega : StepPath) (n m : ℕ) (hm : 0 < m)
    (horigin : localTime (trajectory omega) (n + 1) 0 < m) :
    thresholdSites (oneStepRecenter (trajectory omega)) n m =
      (thresholdSites (trajectory omega) (n + 1) m).image
        (fun x ↦ x - trajectory omega 1) := by
  classical
  ext y
  rw [mem_thresholdSites_iff _ _ _ _ hm, Finset.mem_image]
  constructor
  · intro hy
    let x : Point := y + trajectory omega 1
    have hyx : y = x - trajectory omega 1 := by
      dsimp only [x]
      abel
    have hxne : x ≠ 0 := by
      intro hxzero
      have hle := localTime_shift_le_localTime_add omega 1 n y
      rw [show 1 + n = n + 1 by omega,
        ← oneStepRecenter_trajectory] at hle
      have hsite : trajectory omega 1 + y = 0 := by
        dsimp only [x] at hxzero
        rw [← hxzero]
        abel
      rw [hsite] at hle
      omega
    refine ⟨x, ?_, hyx.symm⟩
    rw [mem_thresholdSites_iff _ _ _ _ hm]
    rw [← localTime_oneStepRecenter_eq_of_ne_origin omega n x hxne,
      ← hyx]
    exact hy
  · rintro ⟨x, hx, rfl⟩
    have hxlevel := (mem_thresholdSites_iff _ _ _ _ hm).mp hx
    have hxne : x ≠ 0 := by
      intro hxzero
      rw [hxzero] at hxlevel
      omega
    rw [localTime_oneStepRecenter_eq_of_ne_origin omega n x hxne]
    exact hxlevel

theorem thresholdCount_oneStepRecenter_eq
    (omega : StepPath) (n m : ℕ) (hm : 0 < m)
    (horigin : localTime (trajectory omega) (n + 1) 0 < m) :
    thresholdCount (oneStepRecenter (trajectory omega)) n m =
      thresholdCount (trajectory omega) (n + 1) m := by
  rw [thresholdCount, thresholdCount,
    thresholdSites_oneStepRecenter_eq_image omega n m hm horigin]
  exact Finset.card_image_of_injective _ (fun _ _ h ↦ by
    have h' := congrArg (fun z ↦ z + trajectory omega 1) h
    simpa using h')

theorem thresholdCreation_oneStepRecenter
    (omega : StepPath) (n m k : ℕ) (hm : 0 < m)
    (hcreation : ThresholdCreation (trajectory omega) m k (n + 1))
    (horigin : localTime (trajectory omega) (n + 1) 0 < m) :
    ThresholdCreation (oneStepRecenter (trajectory omega)) m k n := by
  constructor
  · rw [thresholdCount_oneStepRecenter_eq omega n m hm horigin]
    exact hcreation.1
  · intro q hqn
    have horiginQ : localTime (trajectory omega) (q + 1) 0 < m := by
      exact (localTime_mono_time (trajectory omega) 0 (by omega)).trans_lt horigin
    rw [thresholdCount_oneStepRecenter_eq omega q m hm horiginQ]
    exact hcreation.2 (q + 1) (by omega)

/-! ## Checkerboard geometry under the genuine one-step shift -/

/-- Deleting one step reverses the orientation of a checkerboard domino.
The checkerboard base class itself is also reversed by the odd translation. -/
def shiftedCheckerTiling (d : Tilings.CheckerDirection) : DominoTiling :=
  .checker (oppositeDirection d)

@[simp] theorem oppositeDirection_involutive (d : Direction) :
    oppositeDirection (oppositeDirection d) = d := by
  fin_cases d <;> rfl

theorem trajectory_one_eq_directionVector (omega : StepPath) :
    trajectory omega 1 = directionVector (omega 0) := by
  rw [show 1 = 0 + 1 by omega, trajectory_succ, trajectory_zero]
  rcases directionVector (omega 0) with ⟨a, b⟩
  change (0 + a, 0 + b) = (a, b)
  simp

/-- Translation by the first nearest-neighbor step swaps checkerboard parity. -/
theorem checkerEven_sub_trajectory_one_eq_not
    (omega : StepPath) (x : Point) :
    (Tilings.checkerEven (x - trajectory omega 1) = true) ↔
      ¬ Tilings.checkerEven x = true := by
  rw [trajectory_one_eq_directionVector]
  rcases x with ⟨x₁, x₂⟩
  generalize hd₀ : omega 0 = d₀
  fin_cases d₀ <;>
    simp only [Tilings.checkerEven, directionVector, Prod.fst_sub,
      Prod.snd_sub, beq_iff_eq] <;>
    omega

theorem isTilingBase_shiftedChecker_iff_not
    (omega : StepPath) (d : Tilings.CheckerDirection) (x : Point) :
    IsTilingBase (shiftedCheckerTiling d) (x - trajectory omega 1) ↔
      ¬ IsTilingBase (.checker d) x := by
  exact checkerEven_sub_trajectory_one_eq_not omega x

/-- The mate of a shifted opposite endpoint is the shift of its original
mate.  Reversing `d` here is essential; keeping the same directed tiling
would pair it with the wrong neighbor. -/
theorem tilingPartner_shiftedChecker_sub
    (omega : StepPath) (d : Tilings.CheckerDirection) (x : Point)
    (hx : ¬ IsTilingBase (.checker d) x) :
    tilingPartner (shiftedCheckerTiling d) (x - trajectory omega 1) =
      tilingPartner (.checker d) x - trajectory omega 1 := by
  have hshiftBase :
      IsTilingBase (shiftedCheckerTiling d) (x - trajectory omega 1) :=
    (isTilingBase_shiftedChecker_iff_not omega d x).2 hx
  rw [tilingPartner, if_pos hshiftBase, tilingPartner, if_neg hx,
    trajectory_one_eq_directionVector]
  rcases x with ⟨x₁, x₂⟩
  generalize hd₀ : omega 0 = d₀
  fin_cases d <;> fin_cases d₀ <;>
    simp [shiftedCheckerTiling, tilingDisplacement, Tilings.directionVector,
      directionVector, Tilings.shift, unshift, oppositeDirection] <;>
    omega

theorem tilingPartner_shiftedChecker_sub_general
    (omega : StepPath) (d : Tilings.CheckerDirection) (x : Point) :
    tilingPartner (shiftedCheckerTiling d) (x - trajectory omega 1) =
      tilingPartner (.checker d) x - trajectory omega 1 := by
  by_cases hx : IsTilingBase (.checker d) x
  · have hshift : ¬ IsTilingBase (shiftedCheckerTiling d)
        (x - trajectory omega 1) := by
      intro h
      exact (isTilingBase_shiftedChecker_iff_not omega d x).mp h hx
    rw [tilingPartner, if_neg hshift, tilingPartner, if_pos hx,
      trajectory_one_eq_directionVector]
    rcases x with ⟨x₁, x₂⟩
    generalize hd₀ : omega 0 = d₀
    fin_cases d <;> fin_cases d₀ <;>
      simp [shiftedCheckerTiling, tilingDisplacement, Tilings.directionVector,
        directionVector, Tilings.shift, unshift, oppositeDirection] <;>
      omega
  · exact tilingPartner_shiftedChecker_sub omega d x hx

theorem sameDomino_shiftedChecker_sub_iff
    (omega : StepPath) (d : Tilings.CheckerDirection) (x y : Point) :
    Tilings.sameDomino (shiftedCheckerTiling d)
        (x - trajectory omega 1) (y - trajectory omega 1) ↔
      Tilings.sameDomino (.checker d) x y := by
  rw [sameDomino_iff_partner_eq, sameDomino_iff_partner_eq,
    tilingPartner_shiftedChecker_sub_general]
  constructor
  · intro h
    have h' := congrArg (fun z ↦ z + trajectory omega 1) h
    simpa using h'
  · intro h
    rw [h]

theorem thresholdDominoSeparated_oneStepRecenter
    (omega : StepPath) (d : Tilings.CheckerDirection) (n m : ℕ)
    (hm : 0 < m) (horigin : localTime (trajectory omega) (n + 1) 0 < m)
    (hsep : TilingThresholdDominoSeparated (.checker d)
      (trajectory omega) (n + 1) m) :
    TilingThresholdDominoSeparated (shiftedCheckerTiling d)
      (oneStepRecenter (trajectory omega)) n m := by
  intro a ha b hb hab hdom
  rw [thresholdSites_oneStepRecenter_eq_image omega n m hm horigin] at ha hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hb
  subst b
  have hxy : x ≠ y := by
    intro h
    apply hab
    rw [h]
  exact hsep x hx y hy hxy
    ((sameDomino_shiftedChecker_sub_iff omega d x y).mp hdom)

theorem thresholdCreation_time_pos_of_two_le
    (omega : StepPath) {m k N : ℕ} (hm : 2 ≤ m) (hk : 0 < k)
    (hcreation : ThresholdCreation (trajectory omega) m k N) : 0 < N := by
  by_contra hN
  have hNzero : N = 0 := Nat.eq_zero_of_not_pos hN
  have hcount := hcreation.1
  rw [hNzero, PreStoppingFiber.thresholdCount_trajectory_zero_time] at hcount
  simp only [if_neg (by omega : ¬ m ≤ 1)] at hcount
  omega

/-- The deterministic `D_eta` profile itself transports through `theta_1`;
there is no summable structural failure to pay. -/
theorem tilingDEtaAtCreation_oneStepRecenter
    (omega : StepPath) (d : Tilings.CheckerDirection)
    {m k w low N : ℕ} (hm : 2 ≤ m) (hk : 0 < k)
    (hlow : low = m - w)
    (hcreation : ThresholdCreation (trajectory omega) m k N)
    (hnext : thresholdCount (trajectory omega) N (m + 1) = 0)
    (hsep : TilingThresholdDominoSeparated (.checker d)
      (trajectory omega) N m)
    (horigin : localTime (trajectory omega) N 0 < m) :
    tilingDEtaAtCreation (shiftedCheckerTiling d) m k w low
      (oneStepRecenter (trajectory omega)) := by
  have hNpos := thresholdCreation_time_pos_of_two_le omega hm hk hcreation
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
  have hshiftCreation := thresholdCreation_oneStepRecenter omega n m k
    (by omega) hcreation (by simpa only [Nat.succ_eq_add_one] using horigin)
  have horigin' : localTime (trajectory omega) (n + 1) 0 < m := by
    simpa only [Nat.succ_eq_add_one] using horigin
  have horiginNext : localTime (trajectory omega) (n + 1) 0 < m + 1 :=
    horigin'.trans (Nat.lt_succ_self m)
  have hshiftNext : thresholdCount (oneStepRecenter (trajectory omega)) n
      (m + 1) = 0 := by
    rw [thresholdCount_oneStepRecenter_eq omega n (m + 1) (by omega)
      horiginNext]
    exact hnext
  apply tilingDEtaAtCreation_of_creation_of_dominoSeparated (by omega) hk hlow
    hshiftCreation hshiftNext
  exact thresholdDominoSeparated_oneStepRecenter omega d n m (by omega)
    (by simpa only [Nat.succ_eq_add_one] using horigin) hsep

/-- Off the origin domino, both local-time coordinates of an odd dominant
endpoint transport exactly to the canonical `V₂` coordinate of the recentered
path. -/
theorem tilingVTwoAt_oneStepRecenter_iff_of_opposite
    (omega : StepPath) (d : Tilings.CheckerDirection) (n : ℕ)
    (window : Finset ℕ) (x : Point)
    (hxbase : ¬ IsTilingBase (.checker d) x)
    (hxzero : x ≠ 0) (hpartnerZero : tilingPartner (.checker d) x ≠ 0) :
    tilingVTwoAt (shiftedCheckerTiling d) window
        (oneStepRecenter (trajectory omega)) n
        (x - trajectory omega 1) ↔
      tilingVTwoAt (.checker d) window (trajectory omega) (n + 1) x := by
  unfold tilingVTwoAt
  rw [tilingPartner_shiftedChecker_sub omega d x hxbase,
    localTime_oneStepRecenter_eq_of_ne_origin omega n x hxzero,
    localTime_oneStepRecenter_eq_of_ne_origin omega n
      (tilingPartner (.checker d) x) hpartnerZero]

/-- The discarded visit at time zero is the only loss in the origin local
time.  This exact identity handles the case where the partner of an
opposite dominant endpoint is the origin. -/
theorem localTime_oneStepRecenter_origin_add_one
    (omega : StepPath) (n : ℕ) :
    localTime (oneStepRecenter (trajectory omega)) n
        (0 - trajectory omega 1) + 1 =
      localTime (trajectory omega) (n + 1) 0 := by
  rw [localTime_eq_sum_indicator, localTime_eq_sum_indicator]
  have hright :
      (∑ k ∈ Finset.range (n + 1 + 1),
          if trajectory omega k = 0 then 1 else 0) =
        (∑ k ∈ Finset.range (n + 1),
          if trajectory omega (k + 1) = 0 then 1 else 0) + 1 := by
    rw [show n + 1 + 1 = (n + 1) + 1 by omega,
      Finset.sum_range_succ']
    simp [trajectory_zero]
  rw [hright]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hadd := oneStepRecenter_add_first omega j
  by_cases hleft : oneStepRecenter (trajectory omega) j =
      0 - trajectory omega 1
  · have hright : trajectory omega (j + 1) = 0 := by
      have h := congrArg (fun z ↦ z + trajectory omega 1) hleft
      simpa [hadd] using h
    simp [hleft, hright]
  · have hright : trajectory omega (j + 1) ≠ 0 := by
      intro hzero
      apply hleft
      apply add_right_cancel (b := trajectory omega 1)
      simp [hadd, hzero]
    have hleft' : oneStepRecenter (trajectory omega) j ≠
        -trajectory omega 1 := by
      simpa only [zero_sub] using hleft
    simp [hleft', hright]

/-- One-sided `V₂` transport for the opposite dominant class.  If the old
partner is the origin, its shifted local time loses one, so the dominance
inequality is preserved (indeed improved); no separate origin-domino
exception is needed. -/
theorem tilingVTwoAt_oneStepRecenter_of_opposite
    (omega : StepPath) (d : Tilings.CheckerDirection) (n : ℕ)
    (window : Finset ℕ) (x : Point)
    (hxbase : ¬ IsTilingBase (.checker d) x) (hxzero : x ≠ 0)
    (hxVTwo : tilingVTwoAt (.checker d) window
      (trajectory omega) (n + 1) x) :
    tilingVTwoAt (shiftedCheckerTiling d) window
      (oneStepRecenter (trajectory omega)) n
      (x - trajectory omega 1) := by
  rcases hxVTwo with ⟨hdominance, hwindow⟩
  unfold tilingVTwoAt
  rw [tilingPartner_shiftedChecker_sub omega d x hxbase,
    localTime_oneStepRecenter_eq_of_ne_origin omega n x hxzero]
  refine ⟨?_, hwindow⟩
  by_cases hpartnerZero : tilingPartner (.checker d) x = 0
  · rw [hpartnerZero]
    rw [hpartnerZero] at hdominance
    have horigin := localTime_oneStepRecenter_origin_add_one omega n
    omega
  · rw [localTime_oneStepRecenter_eq_of_ne_origin omega n
      (tilingPartner (.checker d) x) hpartnerZero]
    exact hdominance

/-! ## Creation clocks and shifted source events -/

/-- At a genuine positive creation clock, deleting the first step subtracts
exactly one from the creation time, provided the discarded origin is below
the level. -/
theorem creationTimeNat_oneStepRecenter_eq_pred_of_creation
    (omega : StepPath) {m k N : ℕ} (hm : 2 ≤ m) (hk : 0 < k)
    (hcreation : ThresholdCreation (trajectory omega) m k N)
    (horigin : localTime (trajectory omega) N 0 < m) :
    creationTimeNat m k (oneStepRecenter (trajectory omega)) =
      creationTimeNat m k (trajectory omega) - 1 := by
  have hNpos := thresholdCreation_time_pos_of_two_le omega hm hk hcreation
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
  have hshift := thresholdCreation_oneStepRecenter omega n m k (by omega)
    hcreation (by simpa only [Nat.succ_eq_add_one] using horigin)
  rw [creationTimeNat_eq_of_creation hshift,
    creationTimeNat_eq_of_creation hcreation]
  omega

/-- The odd source screen is literally the preimage of the canonical source
screen under the genuine one-step recentering. -/
def shiftedCheckerSourceEvent (d : Tilings.CheckerDirection)
    (m k w low externalLow externalHigh cut : ℕ) : Set WalkPath :=
  oneStepRecenter ⁻¹'
    shellZeroSourceEvent (shiftedCheckerTiling d) m k w low
      externalLow externalHigh cut

theorem measurableSet_shiftedCheckerSourceEvent
    (d : Tilings.CheckerDirection)
    (m k w low externalLow externalHigh cut : ℕ) :
    MeasurableSet (shiftedCheckerSourceEvent d m k w low
      externalLow externalHigh cut) :=
  (measurableSet_shellZeroSourceEvent (shiftedCheckerTiling d) m k w low
    externalLow externalHigh cut).preimage measurable_oneStepRecenter

/-- No density or quasi-invariance loss occurs in the odd screen: the
one-step recentered walk has exactly the simple-random-walk law. -/
theorem simpleRandomWalk_shiftedCheckerSourceEvent
    (d : Tilings.CheckerDirection)
    (m k w low externalLow externalHigh cut : ℕ) :
    simpleRandomWalk (shiftedCheckerSourceEvent d m k w low
        externalLow externalHigh cut) =
      simpleRandomWalk
        (shellZeroSourceEvent (shiftedCheckerTiling d) m k w low
          externalLow externalHigh cut) := by
  exact simpleRandomWalk_preimage_oneStepRecenter
    (measurableSet_shellZeroSourceEvent (shiftedCheckerTiling d) m k w low
      externalLow externalHigh cut)

/-! ## The explicit origin-domino obstruction -/

/-- The sole obstruction created by deleting time zero: the origin itself
has reached level `m`, so removing its automatic visit may change the
threshold clock.  An opposite endpoint whose partner is the origin is not
exceptional: its partner local time merely drops by one and dominance is
preserved. -/
def checkerOriginShiftExceptionEvent (_d : Tilings.CheckerDirection)
    (m k _w : ℕ) : Set WalkPath :=
  {s | m ≤ localTime s (creationTimeNat m k s) 0}

theorem not_mem_checkerOriginShiftExceptionEvent
    {d : Tilings.CheckerDirection} {m k w : ℕ} {s : WalkPath}
    (hs : s ∉ checkerOriginShiftExceptionEvent d m k w) :
    localTime s (creationTimeNat m k s) 0 < m := by
  simpa only [checkerOriginShiftExceptionEvent, Set.mem_ofPred_eq,
    not_le] using hs

/-- Outside the origin-domino obstruction, translation injects every odd
dominant near-level endpoint into the canonical source `V₂` family of the
recentered path. -/
theorem oppositeDominant_card_le_shifted_vTwoAtCreation
    (omega : StepPath) (d : Tilings.CheckerDirection)
    {m k w N : ℕ} (hm : 2 ≤ m) (hk : 0 < k)
    (hcreation : ThresholdCreation (trajectory omega) m k N)
    (hnext : thresholdCount (trajectory omega) N (m + 1) = 0)
    (hgoodOrigin : trajectory omega ∉ checkerOriginShiftExceptionEvent d m k w) :
    (tilingOppositeDominantNearEndpointsAtCreation (.checker d) m k w
        (trajectory omega)).card ≤
      (tilingVTwoAtCreation (shiftedCheckerTiling d) m k w
        (oneStepRecenter (trajectory omega))).card := by
  classical
  have hNpos := thresholdCreation_time_pos_of_two_le omega hm hk hcreation
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
  have hclock : creationTimeNat m k (trajectory omega) = n + 1 :=
    creationTimeNat_eq_of_creation hcreation
  have horiginData := not_mem_checkerOriginShiftExceptionEvent hgoodOrigin
  have horigin : localTime (trajectory omega) (n + 1) 0 < m := by
    rw [← hclock]
    exact horiginData
  have hshiftCreation := thresholdCreation_oneStepRecenter omega n m k
    (by omega) hcreation horigin
  have hshiftClock :
      creationTimeNat m k (oneStepRecenter (trajectory omega)) = n :=
    creationTimeNat_eq_of_creation hshiftCreation
  let S := tilingOppositeDominantNearEndpointsAtCreation (.checker d) m k w
    (trajectory omega)
  let f : Point → Point := fun x ↦ x - trajectory omega 1
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h := congrArg (fun z ↦ z + trajectory omega 1) hxy
    simpa [f] using h
  have hsub : S.image f ⊆
      tilingVTwoAtCreation (shiftedCheckerTiling d) m k w
        (oneStepRecenter (trajectory omega)) := by
    intro y hy
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
    have hxS' := hxS
    dsimp only [S] at hxS'
    rw [tilingOppositeDominantNearEndpointsAtCreation,
      Finset.mem_filter] at hxS'
    rcases hxS' with ⟨hxDominantFamily, hxNotBase⟩
    rw [tilingDominantNearBasesAtCreation, Finset.mem_image] at hxDominantFamily
    obtain ⟨b, hbNear, hbx⟩ := hxDominantFamily
    have hbNear' := hbNear
    rw [tilingNearFavoriteBasesAtCreation, Finset.mem_filter] at hbNear'
    rw [hclock] at hbx hbNear'
    have hxDominance := tilingDominantEndpointAt_partner_le (.checker d)
      (trajectory omega) (n + 1) b
    rw [hbx] at hxDominance
    have hxNear : tilingXiPlusAt (.checker d) (trajectory omega) (n + 1) x ∈
        HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w ∪
          HLOZShellZeroReplacementWindows.shellZeroReplacementTotalWindow m w := by
      rw [← hbx, tilingXiPlusAt_dominantEndpoint]
      exact hbNear'.2
    have hmaxLt := (thresholdCount_eq_zero_iff_forall_lt
      (trajectory omega) (n + 1) (m + 1) (by omega)).mp hnext
    have hxSource : localTime (trajectory omega) (n + 1) x ∈
        HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w := by
      rw [tilingXiPlusAt_eq_base_of_partner_le hxDominance] at hxNear
      rw [Finset.mem_union] at hxNear
      rcases hxNear with hsource | hreplacement
      · exact hsource
      · have hge :=
          (HLOZShellZeroReplacementWindows.mem_shellZeroReplacementTotalWindow.mp
            hreplacement).1
        have hlt := hmaxLt x
        omega
    have hxZero : x ≠ 0 := by
      intro hx0
      apply hxNotBase
      rw [hx0]
      rfl
    have hxVTwo : tilingVTwoAt (.checker d)
        (HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w)
        (trajectory omega) (n + 1) x := ⟨hxDominance, hxSource⟩
    have hyVTwo := tilingVTwoAt_oneStepRecenter_of_opposite omega d n
      (HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w) x
      hxNotBase hxZero hxVTwo
    rw [tilingVTwoAtCreation, hshiftClock, tilingVTwoBases,
      Finset.mem_filter]
    refine ⟨?_, hyVTwo⟩
    rw [visitedTilingBases, Finset.mem_image]
    refine ⟨x - trajectory omega 1, ?_, ?_⟩
    · rw [mem_visitedSites_iff_localTime_pos,
        localTime_oneStepRecenter_eq_of_ne_origin omega n x hxZero]
      have hxlower :=
        (HLOZShellZeroReplacementWindows.mem_shellZeroSourceTotalWindow.mp
          hxSource).1
      omega
    · rw [tilingBase, if_pos
        ((isTilingBase_shiftedChecker_iff_not omega d x).2 hxNotBase)]
  calc
    S.card = (S.image f).card :=
      (Finset.card_image_of_injective S hfinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The shifted structural complement is kept distinct from `Theta`: it says
the recentered threshold stage does not satisfy the deterministic `D_eta`
classification. -/
def shiftedCheckerStructuralFailureEvent (d : Tilings.CheckerDirection)
    (m k w low : ℕ) : Set WalkPath :=
  oneStepRecenter ⁻¹'
    tilingStageStructuralSourceFailureEvent (thresholdReachStage m k)
      (shiftedCheckerTiling d) m k w low

/-- The shifted, `V₂`-restricted `Theta` complement.  This is not the paper's
unrestricted global `Theta`; it is exactly the screen needed by the source
product event. -/
def shiftedCheckerRestrictedThetaFailureEvent
    (d : Tilings.CheckerDirection)
    (m k w low externalLow externalHigh : ℕ) : Set WalkPath :=
  oneStepRecenter ⁻¹'
    tilingStageThetaFailureEvent (Set.univ : Set WalkPath)
      (shiftedCheckerTiling d) m k w low externalLow externalHigh

theorem simpleRandomWalk_shiftedCheckerStructuralFailureEvent
    (d : Tilings.CheckerDirection) (m k w low : ℕ) :
    simpleRandomWalk (shiftedCheckerStructuralFailureEvent d m k w low) =
      simpleRandomWalk
        (tilingStageStructuralSourceFailureEvent (thresholdReachStage m k)
          (shiftedCheckerTiling d) m k w low) := by
  apply simpleRandomWalk_preimage_oneStepRecenter
  exact measurableSet_tilingStageStructuralSourceFailureEvent
    (measurableSet_thresholdReachStage m k) (shiftedCheckerTiling d)
      m k w low

theorem simpleRandomWalk_shiftedCheckerRestrictedThetaFailureEvent
    (d : Tilings.CheckerDirection)
    (m k w low externalLow externalHigh : ℕ) :
    simpleRandomWalk
        (shiftedCheckerRestrictedThetaFailureEvent d m k w low
          externalLow externalHigh) =
      simpleRandomWalk
        (tilingStageThetaFailureEvent (Set.univ : Set WalkPath)
          (shiftedCheckerTiling d) m k w low externalLow externalHigh) := by
  apply simpleRandomWalk_preimage_oneStepRecenter
  exact measurableSet_tilingStageThetaFailureEvent MeasurableSet.univ
    (shiftedCheckerTiling d) m k w low externalLow externalHigh

/-- A large opposite class is therefore either a genuine shifted source or
one of the two named shifted profile complements.  The origin obstruction is
an explicit hypothesis here and is added as a union in the staged corollary. -/
theorem oppositeDominant_cut_mem_shifted_source_or_failure
    (omega : StepPath) (d : Tilings.CheckerDirection)
    {m k w low externalLow externalHigh cut N : ℕ}
    (hm : 2 ≤ m) (hk : 0 < k)
    (hcreation : ThresholdCreation (trajectory omega) m k N)
    (hnext : thresholdCount (trajectory omega) N (m + 1) = 0)
    (hgoodOrigin : trajectory omega ∉ checkerOriginShiftExceptionEvent d m k w)
    (hcut : cut <
      (tilingOppositeDominantNearEndpointsAtCreation (.checker d) m k w
        (trajectory omega)).card) :
    trajectory omega ∈
        shiftedCheckerSourceEvent d m k w low externalLow externalHigh cut ∪
      shiftedCheckerStructuralFailureEvent d m k w low ∪
      shiftedCheckerRestrictedThetaFailureEvent d m k w low
        externalLow externalHigh := by
  have hcard := lt_of_lt_of_le hcut
    (oppositeDominant_card_le_shifted_vTwoAtCreation omega d hm hk
      hcreation hnext hgoodOrigin)
  have hreachShift : ReachesThreshold
      (oneStepRecenter (trajectory omega)) m k := by
    have hNpos := thresholdCreation_time_pos_of_two_le omega hm hk hcreation
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
    have horiginData := not_mem_checkerOriginShiftExceptionEvent hgoodOrigin
    have horigin : localTime (trajectory omega) (n + 1) 0 < m := by
      rw [creationTimeNat_eq_of_creation hcreation] at horiginData
      simpa only [Nat.succ_eq_add_one] using horiginData
    exact ⟨n, (thresholdCreation_oneStepRecenter omega n m k (by omega)
      hcreation horigin).1⟩
  by_cases hD : tilingDEtaAtCreation (shiftedCheckerTiling d) m k w low
      (oneStepRecenter (trajectory omega))
  · by_cases htheta : tilingThetaAtCreation (shiftedCheckerTiling d) m k w
        externalLow externalHigh (oneStepRecenter (trajectory omega)) = ∅
    · exact Or.inl (Or.inl ⟨hreachShift, hD, htheta, hcard⟩)
    · exact Or.inr ⟨⟨⟨Set.mem_univ _, hreachShift⟩, hD⟩, htheta⟩
  · exact Or.inl (Or.inr ⟨hreachShift, fun h ↦ hD h.2⟩)

/-- Source-facing form: once the old threshold sites are domino-separated,
the structural branch vanishes deterministically.  Only the literal shifted
source and the shifted restricted-`Theta` complement remain. -/
theorem oppositeDominant_cut_mem_shifted_source_or_restrictedTheta
    (omega : StepPath) (d : Tilings.CheckerDirection)
    {m k w low externalLow externalHigh cut N : ℕ}
    (hm : 2 ≤ m) (hk : 0 < k) (hlow : low = m - w)
    (hcreation : ThresholdCreation (trajectory omega) m k N)
    (hnext : thresholdCount (trajectory omega) N (m + 1) = 0)
    (hsep : TilingThresholdDominoSeparated (.checker d)
      (trajectory omega) N m)
    (hgoodOrigin : trajectory omega ∉ checkerOriginShiftExceptionEvent d m k w)
    (hcut : cut <
      (tilingOppositeDominantNearEndpointsAtCreation (.checker d) m k w
        (trajectory omega)).card) :
    trajectory omega ∈
      shiftedCheckerSourceEvent d m k w low externalLow externalHigh cut ∪
        shiftedCheckerRestrictedThetaFailureEvent d m k w low
          externalLow externalHigh := by
  have horiginData := not_mem_checkerOriginShiftExceptionEvent hgoodOrigin
  have hclock : creationTimeNat m k (trajectory omega) = N :=
    creationTimeNat_eq_of_creation hcreation
  have horigin : localTime (trajectory omega) N 0 < m := by
    rw [← hclock]
    exact horiginData
  have hD := tilingDEtaAtCreation_oneStepRecenter omega d hm hk hlow
    hcreation hnext hsep horigin
  have hcard := lt_of_lt_of_le hcut
    (oppositeDominant_card_le_shifted_vTwoAtCreation omega d hm hk
      hcreation hnext hgoodOrigin)
  have hNpos := thresholdCreation_time_pos_of_two_le omega hm hk hcreation
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
  have hshiftCreation := thresholdCreation_oneStepRecenter omega n m k
    (by omega) hcreation (by simpa only [Nat.succ_eq_add_one] using horigin)
  have hreachShift : ReachesThreshold
      (oneStepRecenter (trajectory omega)) m k := ⟨n, hshiftCreation.1⟩
  by_cases htheta : tilingThetaAtCreation (shiftedCheckerTiling d) m k w
      externalLow externalHigh (oneStepRecenter (trajectory omega)) = ∅
  · exact Or.inl ⟨hreachShift, hD, htheta, hcard⟩
  · exact Or.inr ⟨⟨⟨Set.mem_univ _, hreachShift⟩, hD⟩, htheta⟩

theorem firstTransition_opposite_cut_mem_shifted_source_or_restrictedTheta
    (omega : StepPath) (d : Tilings.CheckerDirection)
    {m w low externalLow externalHigh cut : ℕ}
    (a : (GapScale × GapScale) × GapScale)
    (hm : 2 ≤ m) (hlow : low = m - w)
    (hstage : trajectory omega ∈ firstTransitionEvent (.checker d) m a)
    (hgoodOrigin : trajectory omega ∉ checkerOriginShiftExceptionEvent d m 1 w)
    (hcut : cut <
      (tilingOppositeDominantNearEndpointsAtCreation (.checker d) m 1 w
        (trajectory omega)).card) :
    trajectory omega ∈
      shiftedCheckerSourceEvent d m 1 w low externalLow externalHigh cut ∪
        shiftedCheckerRestrictedThetaFailureEvent d m 1 w low
          externalLow externalHigh := by
  simp only [firstTransitionEvent, Set.mem_iUnion] at hstage
  obtain ⟨n₁, n₂, h₁, h₂, hnext, hsep, ha⟩ := hstage
  have htime : n₁ < n₂ := creation_time_lt (by omega) (by omega)
    (by omega) h₁ h₂
  have hmono := thresholdCount_mono_time (trajectory omega) (m + 1) htime.le
  have hnext₁ : thresholdCount (trajectory omega) n₁ (m + 1) = 0 := by
    change thresholdCount (trajectory omega) n₁ (m + 1) ≤
      thresholdCount (trajectory omega) n₂ (m + 1) at hmono
    omega
  exact oppositeDominant_cut_mem_shifted_source_or_restrictedTheta
    omega d hm (by omega) hlow h₁ hnext₁
      (thresholdDominoSeparated_of_singleton
        (thresholdSites_eq_singleton_at_first_creation h₁))
      hgoodOrigin hcut

theorem secondTransition_opposite_cut_mem_shifted_source_or_restrictedTheta
    (omega : StepPath) (d : Tilings.CheckerDirection)
    {m w low externalLow externalHigh cut : ℕ}
    (a : (GapScale × GapScale) × GapScale)
    (hm : 2 ≤ m) (hlow : low = m - w)
    (hstage : trajectory omega ∈ secondTransitionEvent (.checker d) m a)
    (hgoodOrigin : trajectory omega ∉ checkerOriginShiftExceptionEvent d m 2 w)
    (hcut : cut <
      (tilingOppositeDominantNearEndpointsAtCreation (.checker d) m 2 w
        (trajectory omega)).card) :
    trajectory omega ∈
      shiftedCheckerSourceEvent d m 2 w low externalLow externalHigh cut ∪
        shiftedCheckerRestrictedThetaFailureEvent d m 2 w low
          externalLow externalHigh := by
  simp only [secondTransitionEvent, Set.mem_iUnion] at hstage
  obtain ⟨n₁, n₂, n₃, h₁, h₂, h₃, hnext, h₁₂, h₁₃, h₂₃,
    ha₁, ha₂⟩ := hstage
  have htime : n₂ < n₃ := creation_time_lt (by omega) (by omega)
    (by omega) h₂ h₃
  have hmono := thresholdCount_mono_time (trajectory omega) (m + 1) htime.le
  have hnext₂ : thresholdCount (trajectory omega) n₂ (m + 1) = 0 := by
    change thresholdCount (trajectory omega) n₂ (m + 1) ≤
      thresholdCount (trajectory omega) n₃ (m + 1) at hmono
    omega
  exact oppositeDominant_cut_mem_shifted_source_or_restrictedTheta
    omega d hm (by omega) hlow h₂ hnext₂
      (thresholdDominoSeparated_of_pair
        (thresholdSites_eq_pair_at_second_creation h₁ h₂) h₁₂)
      hgoodOrigin hcut

theorem thirdTransition_opposite_cut_mem_shifted_source_or_restrictedTheta
    (omega : StepPath) (d : Tilings.CheckerDirection)
    {m w low externalLow externalHigh cut : ℕ}
    (a : (GapScale × GapScale) × GapScale)
    (hm : 2 ≤ m) (hlow : low = m - w)
    (hstage : trajectory omega ∈ thirdTransitionEvent (.checker d) m a)
    (hgoodOrigin : trajectory omega ∉ checkerOriginShiftExceptionEvent d m 3 w)
    (hcut : cut <
      (tilingOppositeDominantNearEndpointsAtCreation (.checker d) m 3 w
        (trajectory omega)).card) :
    trajectory omega ∈
      shiftedCheckerSourceEvent d m 3 w low externalLow externalHigh cut ∪
        shiftedCheckerRestrictedThetaFailureEvent d m 3 w low
          externalLow externalHigh := by
  simp only [thirdTransitionEvent, Set.mem_iUnion] at hstage
  obtain ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep,
    ha₁, ha₂, ha₃⟩ := hstage
  have htime : n₃ < n₄ := creation_time_lt (by omega) (by omega)
    (by omega) h₃ h₄
  have hmono := thresholdCount_mono_time (trajectory omega) (m + 1) htime.le
  have hnext₃ : thresholdCount (trajectory omega) n₃ (m + 1) = 0 := by
    change thresholdCount (trajectory omega) n₃ (m + 1) ≤
      thresholdCount (trajectory omega) n₄ (m + 1) at hmono
    omega
  rcases hsep with ⟨h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄⟩
  exact oppositeDominant_cut_mem_shifted_source_or_restrictedTheta
    omega d hm (by omega) hlow h₃ hnext₃
      (thresholdDominoSeparated_of_triple
        (thresholdSites_eq_triple_at_third_creation h₁ h₂ h₃)
        h₁₂ h₁₃ h₂₃)
      hgoodOrigin hcut

/-! ## The paired column source uses reflection, not `theta_1` -/

def IsColumnTiling : DominoTiling → Prop
  | .checker _ => False
  | .evenColumns | .oddColumns => True

def reflectedColumnTiling : DominoTiling → DominoTiling
  | .checker d => .checker d
  | .evenColumns => .oddColumns
  | .oddColumns => .evenColumns

theorem isTilingBase_reflectedColumn_iff_not
    {t : DominoTiling} (ht : IsColumnTiling t) (x : Point) :
    IsTilingBase (reflectedColumnTiling t) (horizontalReflectPoint x) ↔
      ¬ IsTilingBase t x := by
  cases t with
  | checker d => contradiction
  | evenColumns =>
      rcases x with ⟨x₁, x₂⟩
      simp only [reflectedColumnTiling, IsTilingBase, horizontalReflectPoint,
        Tilings.columnEven, beq_iff_eq, Int.neg_emod_two]
      simp
  | oddColumns =>
      rcases x with ⟨x₁, x₂⟩
      simp only [reflectedColumnTiling, IsTilingBase, horizontalReflectPoint,
        Tilings.columnEven, beq_eq_false_iff_ne, beq_iff_eq,
        Int.neg_emod_two]
      simp

theorem tilingPartner_reflectedColumn
    {t : DominoTiling} (ht : IsColumnTiling t) (x : Point) :
    tilingPartner (reflectedColumnTiling t) (horizontalReflectPoint x) =
      horizontalReflectPoint (tilingPartner t x) := by
  cases t with
  | checker d => contradiction
  | evenColumns =>
      rcases x with ⟨x₁, x₂⟩
      simp only [reflectedColumnTiling, tilingPartner, IsTilingBase,
        horizontalReflectPoint, tilingDisplacement, Tilings.columnEven,
        Tilings.shift, unshift]
      split_ifs <;> simp_all <;> omega
  | oddColumns =>
      rcases x with ⟨x₁, x₂⟩
      simp only [reflectedColumnTiling, tilingPartner, IsTilingBase,
        horizontalReflectPoint, tilingDisplacement, Tilings.columnEven,
        Tilings.shift, unshift]
      split_ifs <;> simp_all <;> omega

theorem localTime_horizontalReflectPath
    (s : WalkPath) (n : ℕ) (x : Point) :
    localTime (horizontalReflectPath s) n (horizontalReflectPoint x) =
      localTime s n x := by
  induction n with
  | zero =>
      rw [localTime_zero_eq_if, localTime_zero_eq_if]
      have hinj : Function.Injective horizontalReflectPoint :=
        Function.Involutive.injective horizontalReflectPoint_involutive
      simp only [horizontalReflectPath, hinj.eq_iff]
  | succ n ih =>
      rw [localTime_succ, localTime_succ, ih]
      have hinj : Function.Injective horizontalReflectPoint :=
        Function.Involutive.injective horizontalReflectPoint_involutive
      simp only [horizontalReflectPath, hinj.eq_iff]

theorem thresholdSites_horizontalReflectPath_eq_image
    (s : WalkPath) (n m : ℕ) (hm : 0 < m) :
    thresholdSites (horizontalReflectPath s) n m =
      (thresholdSites s n m).image horizontalReflectPoint := by
  classical
  ext y
  rw [mem_thresholdSites_iff _ _ _ _ hm, Finset.mem_image]
  constructor
  · intro hy
    refine ⟨horizontalReflectPoint y, ?_, ?_⟩
    · rw [mem_thresholdSites_iff _ _ _ _ hm]
      rw [← localTime_horizontalReflectPath]
      simpa using hy
    · simp
  · rintro ⟨x, hx, rfl⟩
    rw [mem_thresholdSites_iff _ _ _ _ hm] at hx
    rw [localTime_horizontalReflectPath]
    exact hx

theorem thresholdCount_horizontalReflectPath
    (s : WalkPath) (n m : ℕ) (hm : 0 < m) :
    thresholdCount (horizontalReflectPath s) n m = thresholdCount s n m := by
  rw [thresholdCount, thresholdCount,
    thresholdSites_horizontalReflectPath_eq_image s n m hm]
  exact Finset.card_image_of_injective _
    (Function.Involutive.injective horizontalReflectPoint_involutive)

theorem thresholdCreation_horizontalReflectPath
    (s : WalkPath) (m k n : ℕ) (hm : 0 < m) :
    ThresholdCreation (horizontalReflectPath s) m k n ↔
      ThresholdCreation s m k n := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← thresholdCount_horizontalReflectPath s n m hm]
      exact h.1
    · intro q hq
      rw [← thresholdCount_horizontalReflectPath s q m hm]
      exact h.2 q hq
  · intro h
    constructor
    · rw [thresholdCount_horizontalReflectPath s n m hm]
      exact h.1
    · intro q hq
      rw [thresholdCount_horizontalReflectPath s q m hm]
      exact h.2 q hq

theorem tilingVTwoAt_horizontalReflectPath_iff
    {t : DominoTiling} (ht : IsColumnTiling t) (s : WalkPath)
    (n : ℕ) (window : Finset ℕ) (x : Point) :
    tilingVTwoAt (reflectedColumnTiling t) window
        (horizontalReflectPath s) n (horizontalReflectPoint x) ↔
      tilingVTwoAt t window s n x := by
  unfold tilingVTwoAt
  rw [tilingPartner_reflectedColumn ht,
    localTime_horizontalReflectPath, localTime_horizontalReflectPath]

theorem sameDomino_reflectedColumn_iff
    {t : DominoTiling} (ht : IsColumnTiling t) (x y : Point) :
    Tilings.sameDomino (reflectedColumnTiling t)
        (horizontalReflectPoint x) (horizontalReflectPoint y) ↔
      Tilings.sameDomino t x y := by
  rw [sameDomino_iff_partner_eq, sameDomino_iff_partner_eq,
    tilingPartner_reflectedColumn ht]
  exact (Function.Involutive.injective
    horizontalReflectPoint_involutive).eq_iff

theorem thresholdDominoSeparated_horizontalReflectPath
    {t : DominoTiling} (ht : IsColumnTiling t)
    (s : WalkPath) (n m : ℕ) (hm : 0 < m)
    (hsep : TilingThresholdDominoSeparated t s n m) :
    TilingThresholdDominoSeparated (reflectedColumnTiling t)
      (horizontalReflectPath s) n m := by
  intro a ha b hb hab hdom
  rw [thresholdSites_horizontalReflectPath_eq_image s n m hm] at ha hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hb
  subst b
  have hxy : x ≠ y := by
    intro h
    apply hab
    rw [h]
  exact hsep x hx y hy hxy
    ((sameDomino_reflectedColumn_iff ht x y).mp hdom)

/-- The deterministic source profile is preserved exactly by the column
reflection.  In particular, the reflected column branch has no analogue of
the checkerboard origin loss. -/
theorem tilingDEtaAtCreation_horizontalReflectPath
    {t : DominoTiling} (ht : IsColumnTiling t)
    (s : WalkPath) {m k w low N : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hlow : low = m - w)
    (hcreation : ThresholdCreation s m k N)
    (hnext : thresholdCount s N (m + 1) = 0)
    (hsep : TilingThresholdDominoSeparated t s N m) :
    tilingDEtaAtCreation (reflectedColumnTiling t) m k w low
      (horizontalReflectPath s) := by
  apply tilingDEtaAtCreation_of_creation_of_dominoSeparated hm hk hlow
    ((thresholdCreation_horizontalReflectPath s m k N hm).2 hcreation)
  · rw [thresholdCount_horizontalReflectPath s N (m + 1) (by omega)]
    exact hnext
  · exact thresholdDominoSeparated_horizontalReflectPath ht s N m hm hsep

/-- Reflection injects the non-base dominant half of a column pairing into
the canonical `V₂` source family for the paired column tiling. -/
theorem oppositeDominant_card_le_reflected_vTwoAtCreation
    {t : DominoTiling} (ht : IsColumnTiling t)
    (s : WalkPath) {m k w N : ℕ} (hm : 0 < m)
    (hcreation : ThresholdCreation s m k N)
    (hnext : thresholdCount s N (m + 1) = 0) :
    (tilingOppositeDominantNearEndpointsAtCreation t m k w s).card ≤
      (tilingVTwoAtCreation (reflectedColumnTiling t) m k w
        (horizontalReflectPath s)).card := by
  classical
  have hreflectCreation :=
    (thresholdCreation_horizontalReflectPath s m k N hm).2 hcreation
  have hclock : creationTimeNat m k s = N :=
    creationTimeNat_eq_of_creation hcreation
  have hreflectClock :
      creationTimeNat m k (horizontalReflectPath s) = N :=
    creationTimeNat_eq_of_creation hreflectCreation
  let S := tilingOppositeDominantNearEndpointsAtCreation t m k w s
  have hsub : S.image horizontalReflectPoint ⊆
      tilingVTwoAtCreation (reflectedColumnTiling t) m k w
        (horizontalReflectPath s) := by
    intro y hy
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
    have hxS' := hxS
    dsimp only [S] at hxS'
    rw [tilingOppositeDominantNearEndpointsAtCreation,
      Finset.mem_filter] at hxS'
    rcases hxS' with ⟨hxDominantFamily, hxNotBase⟩
    rw [tilingDominantNearBasesAtCreation, Finset.mem_image] at hxDominantFamily
    obtain ⟨b, hbNear, hbx⟩ := hxDominantFamily
    have hbNear' := hbNear
    rw [tilingNearFavoriteBasesAtCreation, Finset.mem_filter] at hbNear'
    rw [hclock] at hbx hbNear'
    have hxDominance := tilingDominantEndpointAt_partner_le t s N b
    rw [hbx] at hxDominance
    have hxNear : tilingXiPlusAt t s N x ∈
        HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w ∪
          HLOZShellZeroReplacementWindows.shellZeroReplacementTotalWindow m w := by
      rw [← hbx, tilingXiPlusAt_dominantEndpoint]
      exact hbNear'.2
    have hmaxLt := (thresholdCount_eq_zero_iff_forall_lt
      s N (m + 1) (by omega)).mp hnext
    have hxSource : localTime s N x ∈
        HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w := by
      rw [tilingXiPlusAt_eq_base_of_partner_le hxDominance] at hxNear
      rw [Finset.mem_union] at hxNear
      rcases hxNear with hsource | hreplacement
      · exact hsource
      · have hge :=
          (HLOZShellZeroReplacementWindows.mem_shellZeroReplacementTotalWindow.mp
            hreplacement).1
        have hlt := hmaxLt x
        omega
    have hxVTwo : tilingVTwoAt (reflectedColumnTiling t)
        (HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m w)
        (horizontalReflectPath s) N (horizontalReflectPoint x) := by
      rw [tilingVTwoAt_horizontalReflectPath_iff ht]
      exact ⟨hxDominance, hxSource⟩
    rw [tilingVTwoAtCreation, hreflectClock, tilingVTwoBases,
      Finset.mem_filter]
    refine ⟨?_, hxVTwo⟩
    rw [visitedTilingBases, Finset.mem_image]
    refine ⟨horizontalReflectPoint x, ?_, ?_⟩
    · rw [mem_visitedSites_iff_localTime_pos,
        localTime_horizontalReflectPath]
      have hxlower :=
        (HLOZShellZeroReplacementWindows.mem_shellZeroSourceTotalWindow.mp
          hxSource).1
      omega
    · rw [tilingBase, if_pos
        ((isTilingBase_reflectedColumn_iff_not ht x).2 hxNotBase)]
  calc
    S.card = (S.image horizontalReflectPoint).card :=
      (Finset.card_image_of_injective S
        (Function.Involutive.injective
          horizontalReflectPoint_involutive)).symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ## Reflected column source events -/

/-- The non-base half of a column source is the pullback of the paired
column source under vertical-axis reflection.  The numerical external
thresholds are explicit arguments and are therefore identical on source and
target; no cross-package threshold equality is assumed. -/
def reflectedColumnSourceEvent (t : DominoTiling)
    (m k w low externalLow externalHigh cut : ℕ) : Set WalkPath :=
  horizontalReflectPath ⁻¹'
    shellZeroSourceEvent (reflectedColumnTiling t) m k w low
      externalLow externalHigh cut

theorem measurableSet_reflectedColumnSourceEvent
    (t : DominoTiling) (m k w low externalLow externalHigh cut : ℕ) :
    MeasurableSet (reflectedColumnSourceEvent t m k w low externalLow
      externalHigh cut) :=
  (measurableSet_shellZeroSourceEvent (reflectedColumnTiling t) m k w low
    externalLow externalHigh cut).preimage measurable_horizontalReflectPath

theorem simpleRandomWalk_reflectedColumnSourceEvent
    (t : DominoTiling) (m k w low externalLow externalHigh cut : ℕ) :
    simpleRandomWalk (reflectedColumnSourceEvent t m k w low externalLow
        externalHigh cut) =
      simpleRandomWalk
        (shellZeroSourceEvent (reflectedColumnTiling t) m k w low
          externalLow externalHigh cut) := by
  exact simpleRandomWalk_preimage_horizontalReflectPath
    (measurableSet_shellZeroSourceEvent (reflectedColumnTiling t) m k w low
      externalLow externalHigh cut)

/-- The reflected `V₂`-restricted balance complement.  As in the checker
branch, this is not identified with the paper's unrestricted global
`Theta`. -/
def reflectedColumnRestrictedThetaFailureEvent (t : DominoTiling)
    (m k w low externalLow externalHigh : ℕ) : Set WalkPath :=
  horizontalReflectPath ⁻¹'
    tilingStageThetaFailureEvent (Set.univ : Set WalkPath)
      (reflectedColumnTiling t) m k w low externalLow externalHigh

theorem simpleRandomWalk_reflectedColumnRestrictedThetaFailureEvent
    (t : DominoTiling) (m k w low externalLow externalHigh : ℕ) :
    simpleRandomWalk
        (reflectedColumnRestrictedThetaFailureEvent t m k w low
          externalLow externalHigh) =
      simpleRandomWalk
        (tilingStageThetaFailureEvent (Set.univ : Set WalkPath)
          (reflectedColumnTiling t) m k w low externalLow externalHigh) := by
  apply simpleRandomWalk_preimage_horizontalReflectPath
  exact measurableSet_tilingStageThetaFailureEvent MeasurableSet.univ
    (reflectedColumnTiling t) m k w low externalLow externalHigh

theorem oppositeDominant_cut_mem_reflected_source_or_restrictedTheta
    {t : DominoTiling} (ht : IsColumnTiling t) (s : WalkPath)
    {m k w low externalLow externalHigh cut N : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hlow : low = m - w)
    (hcreation : ThresholdCreation s m k N)
    (hnext : thresholdCount s N (m + 1) = 0)
    (hsep : TilingThresholdDominoSeparated t s N m)
    (hcut : cut <
      (tilingOppositeDominantNearEndpointsAtCreation t m k w s).card) :
    s ∈ reflectedColumnSourceEvent t m k w low externalLow externalHigh cut ∪
      reflectedColumnRestrictedThetaFailureEvent t m k w low
        externalLow externalHigh := by
  have hD := tilingDEtaAtCreation_horizontalReflectPath ht s hm hk hlow
    hcreation hnext hsep
  have hcard := lt_of_lt_of_le hcut
    (oppositeDominant_card_le_reflected_vTwoAtCreation ht s hm
      hcreation hnext)
  have hreflectCreation :=
    (thresholdCreation_horizontalReflectPath s m k N hm).2 hcreation
  have hreachReflect : ReachesThreshold (horizontalReflectPath s) m k :=
    ⟨N, hreflectCreation.1⟩
  by_cases htheta : tilingThetaAtCreation (reflectedColumnTiling t) m k w
      externalLow externalHigh (horizontalReflectPath s) = ∅
  · exact Or.inl ⟨hreachReflect, hD, htheta, hcard⟩
  · exact Or.inr ⟨⟨⟨Set.mem_univ _, hreachReflect⟩, hD⟩, htheta⟩

theorem firstTransition_opposite_cut_mem_reflected_source_or_restrictedTheta
    {t : DominoTiling} (ht : IsColumnTiling t) (omega : StepPath)
    {m w low externalLow externalHigh cut : ℕ}
    (a : (GapScale × GapScale) × GapScale)
    (hm : 0 < m) (hlow : low = m - w)
    (hstage : trajectory omega ∈ firstTransitionEvent t m a)
    (hcut : cut <
      (tilingOppositeDominantNearEndpointsAtCreation t m 1 w
        (trajectory omega)).card) :
    trajectory omega ∈
      reflectedColumnSourceEvent t m 1 w low externalLow externalHigh cut ∪
        reflectedColumnRestrictedThetaFailureEvent t m 1 w low
          externalLow externalHigh := by
  simp only [firstTransitionEvent, Set.mem_iUnion] at hstage
  obtain ⟨n₁, n₂, h₁, h₂, hnext, hsep, ha⟩ := hstage
  have htime : n₁ < n₂ := creation_time_lt (by omega) (by omega)
    (by omega) h₁ h₂
  have hmono := thresholdCount_mono_time (trajectory omega) (m + 1) htime.le
  have hnext₁ : thresholdCount (trajectory omega) n₁ (m + 1) = 0 := by
    change thresholdCount (trajectory omega) n₁ (m + 1) ≤
      thresholdCount (trajectory omega) n₂ (m + 1) at hmono
    omega
  exact oppositeDominant_cut_mem_reflected_source_or_restrictedTheta
    ht (trajectory omega) hm (by omega) hlow h₁ hnext₁
      (thresholdDominoSeparated_of_singleton
        (thresholdSites_eq_singleton_at_first_creation h₁)) hcut

theorem secondTransition_opposite_cut_mem_reflected_source_or_restrictedTheta
    {t : DominoTiling} (ht : IsColumnTiling t) (omega : StepPath)
    {m w low externalLow externalHigh cut : ℕ}
    (a : (GapScale × GapScale) × GapScale)
    (hm : 0 < m) (hlow : low = m - w)
    (hstage : trajectory omega ∈ secondTransitionEvent t m a)
    (hcut : cut <
      (tilingOppositeDominantNearEndpointsAtCreation t m 2 w
        (trajectory omega)).card) :
    trajectory omega ∈
      reflectedColumnSourceEvent t m 2 w low externalLow externalHigh cut ∪
        reflectedColumnRestrictedThetaFailureEvent t m 2 w low
          externalLow externalHigh := by
  simp only [secondTransitionEvent, Set.mem_iUnion] at hstage
  obtain ⟨n₁, n₂, n₃, h₁, h₂, h₃, hnext, h₁₂, h₁₃, h₂₃,
    ha₁, ha₂⟩ := hstage
  have htime : n₂ < n₃ := creation_time_lt (by omega) (by omega)
    (by omega) h₂ h₃
  have hmono := thresholdCount_mono_time (trajectory omega) (m + 1) htime.le
  have hnext₂ : thresholdCount (trajectory omega) n₂ (m + 1) = 0 := by
    change thresholdCount (trajectory omega) n₂ (m + 1) ≤
      thresholdCount (trajectory omega) n₃ (m + 1) at hmono
    omega
  exact oppositeDominant_cut_mem_reflected_source_or_restrictedTheta
    ht (trajectory omega) hm (by omega) hlow h₂ hnext₂
      (thresholdDominoSeparated_of_pair
        (thresholdSites_eq_pair_at_second_creation h₁ h₂) h₁₂) hcut

theorem thirdTransition_opposite_cut_mem_reflected_source_or_restrictedTheta
    {t : DominoTiling} (ht : IsColumnTiling t) (omega : StepPath)
    {m w low externalLow externalHigh cut : ℕ}
    (a : (GapScale × GapScale) × GapScale)
    (hm : 0 < m) (hlow : low = m - w)
    (hstage : trajectory omega ∈ thirdTransitionEvent t m a)
    (hcut : cut <
      (tilingOppositeDominantNearEndpointsAtCreation t m 3 w
        (trajectory omega)).card) :
    trajectory omega ∈
      reflectedColumnSourceEvent t m 3 w low externalLow externalHigh cut ∪
        reflectedColumnRestrictedThetaFailureEvent t m 3 w low
          externalLow externalHigh := by
  simp only [thirdTransitionEvent, Set.mem_iUnion] at hstage
  obtain ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep,
    ha₁, ha₂, ha₃⟩ := hstage
  have htime : n₃ < n₄ := creation_time_lt (by omega) (by omega)
    (by omega) h₃ h₄
  have hmono := thresholdCount_mono_time (trajectory omega) (m + 1) htime.le
  have hnext₃ : thresholdCount (trajectory omega) n₃ (m + 1) = 0 := by
    change thresholdCount (trajectory omega) n₃ (m + 1) ≤
      thresholdCount (trajectory omega) n₄ (m + 1) at hmono
    omega
  rcases hsep with ⟨h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄⟩
  exact oppositeDominant_cut_mem_reflected_source_or_restrictedTheta
    ht (trajectory omega) hm (by omega) hlow h₃ hnext₃
      (thresholdDominoSeparated_of_triple
        (thresholdSites_eq_triple_at_third_creation h₁ h₂ h₃)
        h₁₂ h₁₃ h₂₃) hcut

end

end Erdos1165.HLOZThetaOneSourceShift
