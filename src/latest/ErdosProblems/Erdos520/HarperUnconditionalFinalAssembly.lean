import ErdosProblems.Erdos520.HarperCentralUnitAssembly
import ErdosProblems.Erdos520.HarperEconomicalLocalGeometry
import ErdosProblems.Erdos520.HarperEntropyLossArithmetic
import ErdosProblems.Erdos520.HarperMovingHeightMomentIteration
import ErdosProblems.Erdos520.HarperPositiveLogDyadicRecursion
import ErdosProblems.Erdos520.HarperTiltedPositiveLogBallot

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Final economical assembly for Harper's initial moment

This file isolates the last local-to-global step in the unconditional Harper
route.  The input is a uniform local moment estimate for every unit shell
retained by the economical vertical truncation.  The conclusion is the exact
`HarperRademacherInitialMomentStatement` consumed by the Caich part of the
formalization.

The uniformity in the shell range is essential: a separate eventual cutoff
for each fixed shell would not suffice because the Parseval truncation grows
with the ambient Euler cutoff.
-/

/-- Uniform local-moment interface at the economical truncation.  The
analytic constructions supply one absolute `J`; the schedule then makes all
unit shells below `harperAvailableLogScale y / 8` available simultaneously. -/
def HarperEconomicalLocalMomentBound (C : ℝ) (J : ℕ) : Prop :=
  ∀ y : ℕ, 8 * (J + 2) ≤ harperAvailableLogScale y → 4 ≤ y →
    ∀ positive shell, shell < harperEconomicalVerticalTruncation y →
      (∫ omega,
          harperEulerLocalEnergy y positive shell omega ^ harperTwoThird ∂μ) ≤
        (C * (1 + logLogNat y) ^ (-(1 : ℝ) / 3)) *
          harperLocalMomentLoss shell

/-- Central-unit form naturally produced by the shrinking-band assembly. -/
def HarperEconomicalCentralUnitMomentBound (C : ℝ) (J : ℕ) : Prop :=
  ∀ y : ℕ, 8 * (J + 2) ≤ harperAvailableLogScale y → 4 ≤ y →
    (∫ omega,
        harperEulerSetEnergy y harperCentralUnitSet omega ^ harperTwoThird ∂μ) ≤
      C * (1 + logLogNat y) ^ (-(1 : ℝ) / 3)

/-- Noncentral form naturally produced by the moving-height unit-shell
argument. -/
def HarperEconomicalNoncentralLocalMomentBound
    (C : ℝ) (J : ℕ) : Prop :=
  ∀ y : ℕ, 8 * (J + 2) ≤ harperAvailableLogScale y → 4 ≤ y →
    ∀ positive shell, 1 ≤ shell →
      shell < harperEconomicalVerticalTruncation y →
        (∫ omega,
            harperEulerLocalEnergy y positive shell omega ^ harperTwoThird ∂μ) ≤
          (C * (1 + logLogNat y) ^ (-(1 : ℝ) / 3)) *
            harperLocalMomentLoss shell

theorem one_add_logLogNat_pos_of_four_le
    {y : ℕ} (hy : 4 ≤ y) :
    0 < 1 + logLogNat y := by
  have hyR : (4 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogFour : (1 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    nlinarith [Real.log_two_gt_d9]
  have hlogMono : Real.log (4 : ℝ) ≤ Real.log (y : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (show (4 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (y : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        positivity)
      hyR
  have hlogY : (1 : ℝ) < Real.log (y : ℝ) := hlogFour.trans_le hlogMono
  have hloglog : 0 < Real.log (Real.log (y : ℝ)) := by
    rw [← Real.log_one]
    exact Real.strictMonoOn_log
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show Real.log (y : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        linarith)
      hlogY
  unfold logLogNat
  linarith

theorem one_le_harperLocalMomentLoss_public (shell : ℕ) :
    1 ≤ harperLocalMomentLoss shell := by
  unfold harperLocalMomentLoss harperShellScale
  exact Real.one_le_rpow (by norm_num) (by norm_num)

/-- A coarse absolute bound for the cubic Taylor allowance.  Its actual
value is much smaller; this constant is convenient in the shell entropy
bookkeeping. -/
theorem harperScheduledLogTaylorAllowance_le_four_thirds (start : ℕ) :
    harperScheduledLogTaylorAllowance start ≤ (4 / 3 : ℝ) := by
  have hendNat : 1 ≤ harperBlockEndpoint start := by
    exact (by omega : 1 ≤ 16).trans (harperBlockEndpoint_ge_sixteen start)
  have hend : (1 : ℝ) ≤ (harperBlockEndpoint start : ℝ) := by
    exact_mod_cast hendNat
  have hendPos : (0 : ℝ) < (harperBlockEndpoint start : ℝ) := by
    exact_mod_cast harperBlockEndpoint_pos start
  have hsqrtPos : 0 < Real.sqrt (harperBlockEndpoint start : ℝ) :=
    Real.sqrt_pos.2 hendPos
  have hsqrtOne : 1 ≤ Real.sqrt (harperBlockEndpoint start : ℝ) :=
    Real.one_le_sqrt.mpr hend
  have hinv :
      (Real.sqrt (harperBlockEndpoint start : ℝ))⁻¹ ≤ 1 :=
    (inv_le_one₀ hsqrtPos).2 hsqrtOne
  unfold harperScheduledLogTaylorAllowance
  nlinarith

/-- At an economical shell start, the fixed intercept in the positive-log
ballot estimate is absorbed by the existing sixth-root shell loss. -/
theorem
    harperExplicitPrefixPositiveLogOffset_economicalShellStart_zero_add_three_le
    (J shell : ℕ) {E D : ℝ} (hE : 0 ≤ E) (hD : 0 ≤ D) :
    harperExplicitPrefixPositiveLogOffset
          (harperEconomicalShellStart J shell) (shell + 1) 0 E D + 3 ≤
      (harperShellEntropyLossConstant J + E / 2 + D + 13 / 3) *
        harperLocalMomentLoss shell := by
  let L : ℝ := harperLocalMomentLoss shell
  have hbase :=
    harperExplicitPrefixEntropyBase_economicalShellStart_le_localMomentLoss
      J shell
  have htaylor :=
    harperScheduledLogTaylorAllowance_le_four_thirds
      (harperEconomicalShellStart J shell)
  have hL : 1 ≤ L := by
    simpa only [L] using! one_le_harperLocalMomentLoss_public shell
  have hfixed : 0 ≤ E / 2 + D + 13 / 3 := by positivity
  unfold harperExplicitPrefixPositiveLogOffset
  calc
    harperExplicitPrefixEntropyBase
          (harperEconomicalShellStart J shell) (shell + 1) +
        0 + E / 2 + D +
          harperScheduledLogTaylorAllowance
            (harperEconomicalShellStart J shell) + 3 ≤
        harperShellEntropyLossConstant J * L +
          (E / 2 + D + 13 / 3) := by
      dsimp only [L] at hbase ⊢
      linarith
    _ ≤ (harperShellEntropyLossConstant J + E / 2 + D + 13 / 3) *
        L := by
      have hmul := mul_nonneg hfixed (sub_nonneg.mpr hL)
      nlinarith

/-- The noncentral good coefficient is bounded by one fixed constant times
the sixth-root shell loss. -/
theorem harperPositiveLogDyadicGoodConstant_economicalShell_le
    (J shell : ℕ) {E D C : ℝ}
    (hE : 0 ≤ E) (hD : 0 ≤ D) (hC : 0 ≤ C) :
    harperPositiveLogDyadicGoodConstant 1 harperTiltedPositiveLogSlope
        (harperExplicitPrefixPositiveLogOffset
          (harperEconomicalShellStart J shell) (shell + 1) 0 E D + 3) C ≤
      max 1
          (harperExplicitMertensConstant * harperTiltedPositiveLogSlope *
            (harperShellEntropyLossConstant J + E / 2 + D + 13 / 3 + C)) *
        harperLocalMomentLoss shell := by
  let L : ℝ := harperLocalMomentLoss shell
  let X : ℝ :=
    harperExplicitPrefixPositiveLogOffset
      (harperEconomicalShellStart J shell) (shell + 1) 0 E D + 3
  let Xbound : ℝ :=
    harperShellEntropyLossConstant J + E / 2 + D + 13 / 3
  let Qbound : ℝ :=
    harperExplicitMertensConstant * harperTiltedPositiveLogSlope *
      (Xbound + C)
  have hL : 1 ≤ L := by
    simpa only [L] using! one_le_harperLocalMomentLoss_public shell
  have hX :=
    harperExplicitPrefixPositiveLogOffset_economicalShellStart_zero_add_three_le
      J shell hE hD
  have hX0 : 0 ≤ X := by
    dsimp only [X]
    have hoffset := harperExplicitPrefixPositiveLogOffset_nonneg
      (harperEconomicalShellStart J shell) (shell + 1)
      (B := 0) (E := E) (D := D) (by norm_num) hE hD
    linarith
  have hXbound0 : 0 ≤ Xbound := by
    dsimp only [Xbound]
    exact add_nonneg
      (add_nonneg
        (add_nonneg (harperShellEntropyLossConstant_nonneg J)
          (div_nonneg hE (by norm_num))) hD)
      (by norm_num)
  have hQbound0 : 0 ≤ Qbound := by
    dsimp only [Qbound]
    exact mul_nonneg
      (mul_nonneg harperExplicitMertensConstant_pos.le
        harperTiltedPositiveLogSlope_nonneg)
      (add_nonneg hXbound0 hC)
  have hQ :
      harperExplicitMertensConstant * 1 * harperTiltedPositiveLogSlope *
          (X + C) ≤ Qbound * L := by
    have hXC : X + C ≤ (Xbound + C) * L := by
      calc
        X + C ≤ Xbound * L + C := by
          dsimp only [X, Xbound, L] at hX ⊢
          linarith
        _ ≤ (Xbound + C) * L := by
          have hmul := mul_nonneg hC (sub_nonneg.mpr hL)
          nlinarith
    have hcoef :
        0 ≤ harperExplicitMertensConstant * harperTiltedPositiveLogSlope :=
      mul_nonneg harperExplicitMertensConstant_pos.le
        harperTiltedPositiveLogSlope_nonneg
    calc
      harperExplicitMertensConstant * 1 * harperTiltedPositiveLogSlope *
          (X + C) =
          (harperExplicitMertensConstant * harperTiltedPositiveLogSlope) *
            (X + C) := by ring
      _ ≤ (harperExplicitMertensConstant * harperTiltedPositiveLogSlope) *
          ((Xbound + C) * L) :=
        mul_le_mul_of_nonneg_left hXC hcoef
      _ = Qbound * L := by
        dsimp only [Qbound]
        ring
  unfold harperPositiveLogDyadicGoodConstant
  apply max_le
  · calc
      1 ≤ max 1 Qbound := le_max_left _ _
      _ ≤ max 1 Qbound * L := by
        simpa only [mul_one] using!
          mul_le_mul_of_nonneg_left hL
            (le_trans (by norm_num) (le_max_left 1 Qbound))
  · calc
      harperExplicitMertensConstant * 1 * harperTiltedPositiveLogSlope *
          (X + C) ≤ Qbound * L := hQ
      _ ≤ max 1 Qbound * L :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)

/-- The moving-height positive-log iteration supplies the noncentral part of
the economical local interface with one fixed absolute cutoff. -/
theorem exists_harperEconomicalNoncentralLocalMomentBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ J : ℕ,
      HarperEconomicalNoncentralLocalMomentBound C J := by
  obtain ⟨E, hE, D, hD, J, hiter⟩ :=
    exists_integral_harperMovingHeight_twoThird_le_iterated
  let Cballot : ℝ := Real.log 4
  let Q : ℝ :=
    max 1
      (harperExplicitMertensConstant * harperTiltedPositiveLogSlope *
        (harperShellEntropyLossConstant J + E / 2 + D + 13 / 3 + Cballot))
  let T : ℝ := max 1 harperExplicitMertensConstant
  let B : ℝ :=
    2 * (Q + 2 * Real.exp (-Cballot)) + 2 * T
  let W : ℝ :=
    (3 : ℝ) ^ (2 / 3 : ℝ) * 4 ^ ((1 : ℝ) / 3)
  let C : ℝ := W * B
  have hCballot : Real.log 4 ≤ Cballot := by rfl
  have hCballot0 : 0 ≤ Cballot := by
    dsimp only [Cballot]
    exact (Real.log_pos (by norm_num)).le
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    exact le_max_of_le_left (by norm_num)
  have hT0 : 0 ≤ T := by
    dsimp only [T]
    exact le_max_of_le_left (by norm_num)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hW0 : 0 ≤ W := by
    dsimp only [W]
    positivity
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg hW0 hB0
  refine ⟨C, hC0, J, ?_⟩
  intro y hlarge hy positive shell hshellOne hshell
  let n : ℕ := harperEconomicalShellPathLength y J shell
  let I : Set ℝ := harperEulerUnitInterval positive shell
  let scale : ℝ := 1 + logLogNat y
  let loss : ℝ := harperLocalMomentLoss shell
  have hn : 0 < n := by
    dsimp only [n]
    exact harperEconomicalShellPathLength_pos hlarge hshell
  have hnOne : 1 ≤ n := hn
  have hendpoint :
      harperBlockEndpoint (harperEconomicalShellStart J shell + n) ≤ y := by
    dsimp only [n]
    exact harperBlockEndpoint_economicalShellStart_add_path_le
      (by omega) hlarge hshell
  have hI : MeasurableSet I := by
    dsimp only [I]
    exact measurableSet_harperEulerUnitInterval positive shell
  have hIfinite : volume I ≠ ⊤ := by
    dsimp only [I]
    cases positive <;>
      simp [harperEulerUnitInterval, Real.volume_Ioc, Real.volume_Ico]
  have htLower : ∀ t ∈ I, 1 ≤ |t| := by
    intro t ht
    exact one_le_abs_of_mem_harperEulerUnitInterval positive hshellOne ht
  have htUpper : ∀ t ∈ I, |t| ≤ (shell + 1 : ℕ) := by
    intro t ht
    exact abs_le_succ_of_mem_harperEulerUnitInterval positive shell ht
  have hstop : harperDyadicMomentGap n * Real.sqrt (n : ℝ) ≤ 2 :=
    harperDyadicMomentGap_mul_sqrt_nat_le_two_at_length hnOne
  have hraw := hiter (shell + 1) (harperEconomicalShellStart J shell)
    n y (by simp [harperEconomicalShellStart, harperEconomicalStart]) hn
    hendpoint (by omega) I hI hIfinite htLower htUpper
    Cballot hCballot n hstop
  have hvolume : volume.real I = 1 := by
    dsimp only [I]
    exact volume_real_harperEulerUnitInterval_eq_one positive shell
  have hgood :
      harperPositiveLogDyadicGoodConstant 1 harperTiltedPositiveLogSlope
          (harperExplicitPrefixPositiveLogOffset
            (harperEconomicalShellStart J shell) (shell + 1) 0 E D + 3)
          Cballot ≤ Q * loss := by
    dsimp only [Q, loss]
    exact harperPositiveLogDyadicGoodConstant_economicalShell_le
      J shell hE hD hCballot0
  have hlossOne : 1 ≤ loss := by
    dsimp only [loss]
    exact one_le_harperLocalMomentLoss_public shell
  have hbracket :
      2 *
            (harperPositiveLogDyadicGoodConstant 1
                harperTiltedPositiveLogSlope
                (harperExplicitPrefixPositiveLogOffset
                  (harperEconomicalShellStart J shell) (shell + 1) 0 E D + 3)
                Cballot +
              2 * Real.exp (-Cballot)) +
          2 * max 1 harperExplicitMertensConstant ≤ B * loss := by
    have hexp0 : 0 ≤ Real.exp (-Cballot) := Real.exp_pos _ |>.le
    have htail :
        2 * Real.exp (-Cballot) ≤
          (2 * Real.exp (-Cballot)) * loss := by
      nlinarith
    have hterminal : 2 * T ≤ (2 * T) * loss := by
      nlinarith
    dsimp only [T] at hterminal
    dsimp only [B]
    nlinarith
  have hscale : 0 < scale := by
    dsimp only [scale]
    exact one_add_logLogNat_pos_of_four_le hy
  have hcompare : scale ≤ 4 * (n : ℝ) := by
    dsimp only [scale, n]
    exact one_add_logLogNat_le_four_mul_economicalShellPathLength
      hlarge hshell
  have hweight :
      harperDyadicMomentWeight (Real.sqrt (n : ℝ)) 0 ≤
        W * scale ^ (-(1 : ℝ) / 3) := by
    dsimp only [W]
    exact harperDyadicMomentWeight_sqrt_nat_initial_le_of_scale
      hscale hnOne hcompare
  have hbracket0 :
      0 ≤
        2 *
            (harperPositiveLogDyadicGoodConstant 1
                harperTiltedPositiveLogSlope
                (harperExplicitPrefixPositiveLogOffset
                  (harperEconomicalShellStart J shell) (shell + 1) 0 E D + 3)
                Cballot +
              2 * Real.exp (-Cballot)) +
          2 * max 1 harperExplicitMertensConstant := by
    unfold harperPositiveLogDyadicGoodConstant
    positivity
  have hraw' :
      (∫ omega,
          harperEulerLocalEnergy y positive shell omega ^ harperTwoThird ∂μ) ≤
        harperDyadicMomentWeight (Real.sqrt (n : ℝ)) 0 *
          (2 *
              (harperPositiveLogDyadicGoodConstant 1
                  harperTiltedPositiveLogSlope
                  (harperExplicitPrefixPositiveLogOffset
                    (harperEconomicalShellStart J shell) (shell + 1) 0 E D + 3)
                  Cballot +
                2 * Real.exp (-Cballot)) +
            2 * max 1 harperExplicitMertensConstant) := by
    simpa only [I, harperEulerLocalEnergy, harperEulerSetEnergy, hvolume,
      one_mul, mul_one] using! hraw
  calc
    (∫ omega,
        harperEulerLocalEnergy y positive shell omega ^ harperTwoThird ∂μ) ≤
        harperDyadicMomentWeight (Real.sqrt (n : ℝ)) 0 *
          (2 *
              (harperPositiveLogDyadicGoodConstant 1
                  harperTiltedPositiveLogSlope
                  (harperExplicitPrefixPositiveLogOffset
                    (harperEconomicalShellStart J shell) (shell + 1) 0 E D + 3)
                  Cballot +
                2 * Real.exp (-Cballot)) +
            2 * max 1 harperExplicitMertensConstant) := hraw'
    _ ≤ (W * scale ^ (-(1 : ℝ) / 3)) * (B * loss) := by
      exact mul_le_mul hweight hbracket hbracket0
        (mul_nonneg hW0 (Real.rpow_nonneg hscale.le _))
    _ = (C * (1 + logLogNat y) ^ (-(1 : ℝ) / 3)) *
          harperLocalMomentLoss shell := by
      dsimp only [C, scale, loss]
      ring


/-- Merge the independently proved central and noncentral estimates into the
single uniform local interface consumed by Parseval. -/
theorem harperEconomicalLocalMomentBound_of_central_noncentral
    {Ccentral Cnoncentral : ℝ} {Jcentral Jnoncentral : ℕ}
    (hCcentral : 0 ≤ Ccentral) (hCnoncentral : 0 ≤ Cnoncentral)
    (hcentral :
      HarperEconomicalCentralUnitMomentBound Ccentral Jcentral)
    (hnoncentral :
      HarperEconomicalNoncentralLocalMomentBound Cnoncentral Jnoncentral) :
    HarperEconomicalLocalMomentBound
      (Ccentral + Cnoncentral) (max Jcentral Jnoncentral) := by
  intro y hlarge hy positive shell hshell
  have hlargeCentral :
      8 * (Jcentral + 2) ≤ harperAvailableLogScale y := by
    have hJ : Jcentral ≤ max Jcentral Jnoncentral := le_max_left _ _
    omega
  have hlargeNoncentral :
      8 * (Jnoncentral + 2) ≤ harperAvailableLogScale y := by
    have hJ : Jnoncentral ≤ max Jcentral Jnoncentral := le_max_right _ _
    omega
  have hscale0 :
      0 ≤ (1 + logLogNat y) ^ (-(1 : ℝ) / 3) :=
    Real.rpow_nonneg (one_add_logLogNat_pos_of_four_le hy).le _
  cases shell with
  | zero =>
      have hzero :=
        integral_harperEulerLocalEnergy_zero_twoThird_le_of_centralUnit
          (show 2 ≤ y by omega)
          (hcentral y hlargeCentral hy) positive
      calc
        (∫ omega,
            harperEulerLocalEnergy y positive 0 omega ^ harperTwoThird ∂μ) ≤
            Ccentral * (1 + logLogNat y) ^ (-(1 : ℝ) / 3) := hzero
        _ ≤ (Ccentral + Cnoncentral) *
            (1 + logLogNat y) ^ (-(1 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right hCnoncentral) hscale0
        _ = ((Ccentral + Cnoncentral) *
              (1 + logLogNat y) ^ (-(1 : ℝ) / 3)) *
            harperLocalMomentLoss 0 := by
          simp [harperLocalMomentLoss, harperShellScale]
  | succ shell =>
      have hmain := hnoncentral y hlargeNoncentral hy positive (shell + 1)
        (by omega) hshell
      have hloss0 : 0 ≤ harperLocalMomentLoss (shell + 1) := by
        unfold harperLocalMomentLoss
        exact Real.rpow_nonneg (harperShellScale_pos _).le _
      calc
        (∫ omega,
            harperEulerLocalEnergy y positive (shell + 1) omega ^
              harperTwoThird ∂μ) ≤
            (Cnoncentral *
              (1 + logLogNat y) ^ (-(1 : ℝ) / 3)) *
                harperLocalMomentLoss (shell + 1) := hmain
        _ ≤ ((Ccentral + Cnoncentral) *
              (1 + logLogNat y) ^ (-(1 : ℝ) / 3)) *
                harperLocalMomentLoss (shell + 1) := by
          apply mul_le_mul_of_nonneg_right _ hloss0
          exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left hCcentral) hscale0

/-- At the economical truncation, the real log--log scale is at most sixteen
times the retained number of unit shells. -/
theorem one_add_logLogNat_le_sixteen_mul_economicalVerticalTruncation
    {y : ℕ} (havail : 16 ≤ harperAvailableLogScale y) :
    1 + logLogNat y ≤
      16 * (harperEconomicalVerticalTruncation y : ℝ) := by
  let A := harperAvailableLogScale y
  let M := harperEconomicalVerticalTruncation y
  have hlog := logLogNat_le_harperAvailableLogScale_add_one
    (show 1 ≤ harperAvailableLogScale y by omega)
  have hnat : A + 2 ≤ 16 * M := by
    dsimp only [A, M, harperEconomicalVerticalTruncation]
    omega
  have hnatR : (A : ℝ) + 2 ≤ 16 * (M : ℝ) := by
    exact_mod_cast hnat
  dsimp only [A, M] at hnatR ⊢
  linarith

/-- The explicit Parseval tail at the economical truncation already has the
required negative one-third power of the real log--log scale. -/
theorem economicalParsevalTail_twoThird_le_scale
    {y : ℕ} (hy : 4 ≤ y)
    (havail : 16 ≤ harperAvailableLogScale y) :
    (2 * harperExplicitMertensConstant /
        (harperEconomicalVerticalTruncation y : ℝ)) ^ harperTwoThird ≤
      (8 * harperExplicitMertensConstant) ^ harperTwoThird *
          4 ^ ((1 : ℝ) / 3) *
        (1 + logLogNat y) ^ (-(1 : ℝ) / 3) := by
  let scale : ℝ := 1 + logLogNat y
  let M : ℕ := harperEconomicalVerticalTruncation y
  have hscale : 0 < scale := by
    simpa only [scale] using! one_add_logLogNat_pos_of_four_le hy
  have hM : 1 ≤ M := by
    dsimp only [M, harperEconomicalVerticalTruncation]
    omega
  have hfourM : 1 ≤ 4 * M := by omega
  have hcompare : scale ≤ 4 * ((4 * M : ℕ) : ℝ) := by
    have h := one_add_logLogNat_le_sixteen_mul_economicalVerticalTruncation
      havail
    dsimp only [scale, M] at h ⊢
    convert! h using 1 <;> norm_num <;> ring
  have htail := rpow_div_nat_twoThird_le_of_scale_le_four_mul
    (A := 8 * harperExplicitMertensConstant) (scale := scale)
    (n := 4 * M)
    (mul_nonneg (by norm_num) harperExplicitMertensConstant_pos.le)
    hscale hfourM hcompare
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hfourM0 : ((4 * M : ℕ) : ℝ) ≠ 0 := by positivity
  convert! htail using 1 <;>
    simp only [scale, M, harperTwoThird, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hM0, hfourM0]
  <;> ring_nf

/-- A uniform economical unit-shell estimate implies the exact eventual
Harper initial-moment bound.  All finite-series and Parseval-tail constants
are chosen internally. -/
theorem harperRademacherInitialMomentStatement_of_economicalLocalMoments
    {C : ℝ} {J : ℕ} (hC : 0 ≤ C)
    (hlocal : HarperEconomicalLocalMomentBound C J) :
    HarperRademacherInitialMomentStatement := by
  let S : ℝ := ∑' n : ℕ, harperGlobalMomentSeriesTerm n
  let Ctail : ℝ :=
    (8 * harperExplicitMertensConstant) ^ harperTwoThird *
      4 ^ ((1 : ℝ) / 3)
  let Cfinal : ℝ := 1 + 2 * C * 4 ^ harperTwoThird * S + Ctail
  let threshold : ℕ := 8 * (J + 2)
  let Y : ℕ := max 4 (harperBlockEndpoint threshold)
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    exact tsum_nonneg fun n ↦
      Real.rpow_nonneg (harperShellScale_pos n).le _
  have hCtail0 : 0 ≤ Ctail := by
    dsimp only [Ctail]
    exact mul_nonneg
      (Real.rpow_nonneg
        (mul_nonneg (by norm_num) harperExplicitMertensConstant_pos.le) _)
      (Real.rpow_nonneg (by norm_num) _)
  have hCfinal : 0 < Cfinal := by
    dsimp only [Cfinal]
    positivity
  have hY : 2 ≤ Y := by
    dsimp only [Y]
    omega
  refine ⟨Cfinal, hCfinal, Y, hY, ?_⟩
  intro y hyY hy2
  have hy4 : 4 ≤ y := by
    have h4Y : 4 ≤ Y := by
      dsimp only [Y]
      exact le_max_left _ _
    exact h4Y.trans hyY
  have hendpoint : harperBlockEndpoint threshold ≤ y := by
    have hEY : harperBlockEndpoint threshold ≤ Y := by
      dsimp only [Y]
      exact le_max_right _ _
    exact hEY.trans hyY
  have hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y := by
    have h := add_four_le_harperAvailableLogScale_of_blockEndpoint_le
      hendpoint
    dsimp only [threshold] at h ⊢
    omega
  have havail : 16 ≤ harperAvailableLogScale y := by
    have : 16 ≤ 8 * (J + 2) := by omega
    exact this.trans hlarge
  let scale : ℝ := 1 + logLogNat y
  let M : ℕ := harperEconomicalVerticalTruncation y
  have hscale : 0 < scale := by
    simpa only [scale] using! one_add_logLogNat_pos_of_four_le hy4
  have hM : 1 ≤ M := by
    dsimp only [M, harperEconomicalVerticalTruncation]
    omega
  let A : ℝ := C * scale ^ (-(1 : ℝ) / 3)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg hC (Real.rpow_nonneg hscale.le _)
  have hmoment : ∀ d n, n < M →
      (∫ omega,
          harperEulerLocalEnergy y d n omega ^ harperTwoThird ∂μ) ≤
        A * harperLocalMomentLoss n := by
    intro d n hn
    simpa only [A, scale, M] using! hlocal y hlarge hy4 d n hn
  have hparseval :=
    integral_harperInitialNormalizedEnergy_twoThird_le_of_eulerLocalIntervals
      hy2 hM hmoment
  have hsum :
      (∑ n ∈ Finset.range M, harperGlobalMomentSeriesTerm n) ≤ S := by
    dsimp only [S]
    exact summable_harperGlobalMomentSeriesTerm.sum_le_tsum _
      (fun n _ ↦ Real.rpow_nonneg (harperShellScale_pos n).le _)
  have hmain :
      2 * A * 4 ^ harperTwoThird *
          (∑ n ∈ Finset.range M, harperGlobalMomentSeriesTerm n) ≤
        (2 * C * 4 ^ harperTwoThird * S) *
          scale ^ (-(1 : ℝ) / 3) := by
    have hcoef : 0 ≤ 2 * A * 4 ^ harperTwoThird := by positivity
    calc
      2 * A * 4 ^ harperTwoThird *
          (∑ n ∈ Finset.range M, harperGlobalMomentSeriesTerm n) ≤
          2 * A * 4 ^ harperTwoThird * S :=
        mul_le_mul_of_nonneg_left hsum hcoef
      _ = (2 * C * 4 ^ harperTwoThird * S) *
          scale ^ (-(1 : ℝ) / 3) := by
        dsimp only [A]
        ring
  have htail := economicalParsevalTail_twoThird_le_scale hy4 havail
  have hcombined :
      (∫ omega,
          harperInitialNormalizedEnergy y omega ^ harperTwoThird ∂μ) ≤
        (2 * C * 4 ^ harperTwoThird * S + Ctail) *
          scale ^ (-(1 : ℝ) / 3) := by
    calc
      (∫ omega,
          harperInitialNormalizedEnergy y omega ^ harperTwoThird ∂μ) ≤
          2 * A * 4 ^ harperTwoThird *
              (∑ n ∈ Finset.range M,
                harperGlobalMomentSeriesTerm n) +
            (2 * harperExplicitMertensConstant / (M : ℝ)) ^
              harperTwoThird := hparseval
      _ ≤ (2 * C * 4 ^ harperTwoThird * S) *
              scale ^ (-(1 : ℝ) / 3) +
            Ctail * scale ^ (-(1 : ℝ) / 3) := by
        exact add_le_add hmain (by simpa only [Ctail, scale, M] using! htail)
      _ = (2 * C * 4 ^ harperTwoThird * S + Ctail) *
          scale ^ (-(1 : ℝ) / 3) := by ring
  have hcoefFinal :
      2 * C * 4 ^ harperTwoThird * S + Ctail ≤ Cfinal := by
    dsimp only [Cfinal]
    linarith
  have hpow0 : 0 ≤ scale ^ (-(1 : ℝ) / 3) :=
    Real.rpow_nonneg hscale.le _
  calc
    (∫ omega,
        harperInitialNormalizedEnergy y omega ^ ((2 : ℝ) / 3) ∂μ) ≤
        (2 * C * 4 ^ harperTwoThird * S + Ctail) *
          scale ^ (-(1 : ℝ) / 3) := by
      simpa only [harperTwoThird] using! hcombined
    _ ≤ Cfinal * scale ^ (-(1 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right hcoefFinal hpow0
    _ = Cfinal / scale ^ ((1 : ℝ) / 3) := by
      rw [show (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) by ring,
        Real.rpow_neg hscale.le]
      ring
    _ = Cfinal / (1 + logLogNat y) ^ ((1 : ℝ) / 3) := rfl

end Problem520
end Erdos

#print axioms Erdos.Problem520.economicalParsevalTail_twoThird_le_scale
#print axioms Erdos.Problem520.harperPositiveLogDyadicGoodConstant_economicalShell_le
#print axioms Erdos.Problem520.exists_harperEconomicalNoncentralLocalMomentBound
#print axioms Erdos.Problem520.harperEconomicalLocalMomentBound_of_central_noncentral
#print axioms Erdos.Problem520.harperRademacherInitialMomentStatement_of_economicalLocalMoments
