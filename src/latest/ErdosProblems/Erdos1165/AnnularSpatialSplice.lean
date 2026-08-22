/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.LiteralRealAnnulusRadialExit
import ErdosProblems.Erdos1165.TerminalSpliceProfileGeometry

/-!
# Initial and final spatial factors in HLOZ Lemma A.6

The chronological radial word starts only after the walk first reaches local
profile boundary `1`, and it ends on local profile boundary `0`.  The full
successful event additionally needs an initial hit before the global exit and
a final global escape before returning to boundary `1`.

This module first proves the quantitative centered annulus estimates behind
those two pieces.  The constants are deliberately coarse: both probabilities
are bounded below by `1 / 128`.  Subsequent lemmas transport the centered
events to an arbitrary candidate point and splice them to the literal radial
word.
-/

open Filter Real Set
open scoped ENNReal

namespace Erdos1165.AnnularSpatialSplice

open Annulus AnnulusHarnack BoundaryStoppedHarnack
  LiteralRealAnnulus LiteralRealAnnulusRadialExit
  PotentialConvergence PotentialEuclideanGeometry PotentialRadialGlobal RealDiscFinite
  ThickPoint TerminalSpliceProfileGeometry

noncomputable section

private lemma realBoundaryPotentialValue_sub_eq_log_div
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    realBoundaryPotentialValue r - realBoundaryPotentialValue s =
      (2 / Real.pi) * Real.log (r / s) := by
  unfold realBoundaryPotentialValue
  rw [Real.log_div hr.ne' hs.ne']
  ring

private lemma log_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
  exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans_eq
    (by norm_num)

private lemma three_eighths_le_log_eight_fifths :
    (3 / 8 : ℝ) ≤ Real.log (8 / 5 : ℝ) := by
  have h := Real.self_sub_one_le_mul_log
    (show (0 : ℝ) ≤ 8 / 5 by norm_num)
  nlinarith

private lemma log_eight_mul_exp_one_le_four :
    Real.log (8 * Real.exp 1) ≤ (4 : ℝ) := by
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (Real.exp_ne_zero 1),
    show Real.log (8 : ℝ) = 3 * Real.log 2 by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      norm_num,
    Real.log_exp]
  linarith [log_two_le_one]

private lemma log_thirtyTwo_mul_exp_one_le_six :
    Real.log (32 * Real.exp 1) ≤ (6 : ℝ) := by
  rw [Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) (Real.exp_ne_zero 1),
    show Real.log (32 : ℝ) = 5 * Real.log 2 by
      rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
      norm_num,
    Real.log_exp]
  linarith [log_two_le_one]

private lemma realBoundaryPotentialValue_mono
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    realBoundaryPotentialValue r ≤ realBoundaryPotentialValue s := by
  unfold realBoundaryPotentialValue
  have hlog := Real.log_le_log hr hrs
  have hcoef : 0 ≤ (2 / Real.pi : ℝ) := by positivity
  nlinarith

/-- Marking the whole literal outer disc boundary gives the same exit mass
as marking the actual outer-side graph-exit piece. -/
theorem exitMass_discBoundaryFinset_eq_literalRealAnnulusOuterExit
    {rInner rOuter : ℝ} {boxRadius : ℕ} {x : Point}
    (hrOuter : 0 ≤ rOuter) (hbox : rOuter ≤ (boxRadius : ℝ))
    (hsep : rInner + 1 ≤ rOuter)
    (hx : x ∈ literalRealAnnulus rInner rOuter boxRadius) :
    exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (RealDiscFinite.discBoundaryFinset 0 rOuter) x =
      exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (literalRealAnnulusOuterExit rInner rOuter boxRadius) x := by
  let D := literalRealAnnulus rInner rOuter boxRadius
  let B := RealDiscFinite.discBoundaryFinset 0 rOuter
  let C := literalRealAnnulusOuterExit rInner rOuter boxRadius
  have hDB : Disjoint D B := by
    rw [Finset.disjoint_left]
    intro z hzD hzB
    exact (mem_literalRealAnnulus_raw.mp hzD).2.2.1
      (RealDiscFinite.mem_discBoundaryFinset.mp hzB)
  have hDC : Disjoint D C := by
    rw [Finset.disjoint_left]
    intro z hzD hzC
    exact (mem_outerBoundary D z).mp
      ((mem_literalRealAnnulusOuterExit _ _ _ z).mp hzC).1 |>.1 hzD
  apply exitMass_eq_of_agree_on_outerBoundary hx hDB hDC
  intro z hzOuter
  constructor
  · intro hzB
    apply (mem_literalRealAnnulusOuterExit _ _ _ z).mpr
    refine ⟨hzOuter, ?_⟩
    intro hzInner
    exact (not_mem_discBoundary_of_mem_disc_of_add_one_le hzInner hsep)
      (RealDiscFinite.mem_discBoundaryFinset.mp hzB)
  · intro hzC
    apply RealDiscFinite.mem_discBoundaryFinset.mpr
    exact literalRealAnnulusOuterExit_subset_discBoundary hrOuter hbox hzC

/-- Seen from the candidate center, the origin has radius between `2 r₀`
and `5 r₀`.  The upper constant is a convenient rational replacement
for the exact square-corner constant `3 √2`. -/
theorem candidate_neg_euclideanRadius_bounds
    {n : ℕ} {x : Point} (hx : x ∈ candidateBox n) :
    2 * scaleRadius n 0 ≤ euclideanRadius (-x) ∧
      euclideanRadius (-x) ≤ 5 * scaleRadius n 0 := by
  have hr0 : 0 ≤ scaleRadius n 0 := by
    simp only [scaleRadius_of_le (Nat.zero_le n), regularRadius,
      Nat.cast_zero, sub_zero]
    positivity
  have hxmem := mem_candidateBox.mp hx
  have hx1ceil : ⌈2 * regularRadius n 0⌉ ≤ x.1 :=
    (mem_candidateInterval.mp hxmem.1).1
  have hx1ceilReal : (⌈2 * regularRadius n 0⌉ : ℝ) ≤ (x.1 : ℝ) := by
    exact_mod_cast hx1ceil
  have hx1Lower : 2 * scaleRadius n 0 ≤ (x.1 : ℝ) := by
    rw [scaleRadius_of_le (Nat.zero_le n)]
    exact (Int.le_ceil _).trans hx1ceilReal
  have hxAbs :=
    TerminalExcursionPathwise.candidate_coordinate_abs_le_three_radius hx
  have hx1sq : (x.1 : ℝ) ^ 2 ≤ (3 * scaleRadius n 0) ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hr0)]
    exact hxAbs.1
  have hx2sq : (x.2 : ℝ) ^ 2 ≤ (3 * scaleRadius n 0) ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hr0)]
    exact hxAbs.2
  have hnegSq : euclideanRadius (-x) ^ 2 =
      (x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2 := by
    rw [euclideanRadius_sq]
    simp [euclideanRadiusSq]
  have hradNonneg := euclideanRadius_nonneg (-x)
  constructor
  · have hx1sqLower : (2 * scaleRadius n 0) ^ 2 ≤ (x.1 : ℝ) ^ 2 := by
      nlinarith
    nlinarith [sq_nonneg (x.2 : ℝ)]
  · nlinarith

private lemma initial_error_le_of_radius_large
    {r0 r1 rho : ℝ}
    (hC : 0 ≤ globalRadialConstant)
    (hr1 : 2 ≤ r1) (hr10 : 0 < r1) (hr10r0 : r1 ≤ r0)
    (hrho : 2 * r0 ≤ rho)
    (hlarge : 16 * (3 * globalRadialConstant + 4) ≤ r1) :
    globalRadialConstant / rho +
        max (realBoundaryPotentialError r1)
          (realBoundaryPotentialError (8 * r0)) ≤ 1 / 16 := by
  have hr0 : 0 < r0 := lt_of_lt_of_le hr10 hr10r0
  have hrho0 : 0 < rho := lt_of_lt_of_le (by positivity) hrho
  have houter : r1 ≤ 8 * r0 := by nlinarith
  have herrorOuter : realBoundaryPotentialError (8 * r0) ≤
      realBoundaryPotentialError r1 :=
    realBoundaryPotentialError_antitone (by linarith) houter
  have hmax : max (realBoundaryPotentialError r1)
      (realBoundaryPotentialError (8 * r0)) = realBoundaryPotentialError r1 :=
    max_eq_left herrorOuter
  have hglobal : globalRadialConstant / rho ≤
      globalRadialConstant / r1 :=
    div_le_div_of_nonneg_left hC hr10 (hr10r0.trans (by nlinarith))
  have hden : r1 / 2 ≤ r1 - 1 := by linarith
  have hnum : 0 ≤ globalRadialConstant + 2 := by linarith
  have hboundary : realBoundaryPotentialError r1 ≤
      2 * (globalRadialConstant + 2) / r1 := by
    unfold realBoundaryPotentialError
    have := div_le_div_of_nonneg_left hnum (by positivity : 0 < r1 / 2) hden
    calc
      (globalRadialConstant + 2) / (r1 - 1) ≤
          (globalRadialConstant + 2) / (r1 / 2) := this
      _ = 2 * (globalRadialConstant + 2) / r1 := by ring
  rw [hmax]
  have hcost : (3 * globalRadialConstant + 4) / r1 ≤ 1 / 16 := by
    rw [div_le_iff₀ hr10]
    nlinarith
  calc
    globalRadialConstant / rho + realBoundaryPotentialError r1 ≤
        globalRadialConstant / r1 +
          2 * (globalRadialConstant + 2) / r1 := add_le_add hglobal hboundary
    _ = (3 * globalRadialConstant + 4) / r1 := by ring
    _ ≤ 1 / 16 := hcost

private lemma final_error_le_of_radius_large
    {r0 r1 : ℝ}
    (hr1 : 2 ≤ r1) (hr10 : 0 < r1) (hr10r0 : r1 ≤ r0)
    (hlarge : 64 * (globalRadialConstant + 2) ≤ r1) :
    realBoundaryPotentialError r0 +
        max (realBoundaryPotentialError r1)
          (realBoundaryPotentialError (32 * r0)) ≤ 1 / 16 := by
  have hr0 : 0 < r0 := lt_of_lt_of_le hr10 hr10r0
  have herror0 : realBoundaryPotentialError r0 ≤
      realBoundaryPotentialError r1 :=
    realBoundaryPotentialError_antitone (by linarith) hr10r0
  have herrorOuter : realBoundaryPotentialError (32 * r0) ≤
      realBoundaryPotentialError r1 :=
    realBoundaryPotentialError_antitone (by linarith) (by nlinarith)
  have hmax : max (realBoundaryPotentialError r1)
      (realBoundaryPotentialError (32 * r0)) = realBoundaryPotentialError r1 :=
    max_eq_left herrorOuter
  have hden : r1 / 2 ≤ r1 - 1 := by linarith
  have hnum : 0 ≤ globalRadialConstant + 2 := by
    linarith [globalRadialConstant_pos]
  have hboundary : realBoundaryPotentialError r1 ≤
      2 * (globalRadialConstant + 2) / r1 := by
    unfold realBoundaryPotentialError
    have := div_le_div_of_nonneg_left hnum (by positivity : 0 < r1 / 2) hden
    calc
      (globalRadialConstant + 2) / (r1 - 1) ≤
          (globalRadialConstant + 2) / (r1 / 2) := this
      _ = 2 * (globalRadialConstant + 2) / r1 := by ring
  rw [hmax]
  have hcost : 4 * (globalRadialConstant + 2) / r1 ≤ 1 / 16 := by
    rw [div_le_iff₀ hr10]
    nlinarith
  calc
    realBoundaryPotentialError r0 + realBoundaryPotentialError r1 ≤
        2 * (2 * (globalRadialConstant + 2) / r1) := by
      linarith
    _ = 4 * (globalRadialConstant + 2) / r1 := by ring
    _ ≤ 1 / 16 := hcost

/-- A single explicit lower threshold discharges both potential-error
budgets and the elementary radius-separation requirements. -/
noncomputable def spatialSpliceRadiusThreshold : ℝ :=
  max 3 (max (16 * (3 * globalRadialConstant + 4))
    (64 * (globalRadialConstant + 2)))

lemma natCast_le_scaleRadius_one (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ≤ scaleRadius n 1 := by
  rw [scaleRadius_of_le hn, regularRadius]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdiff : 0 ≤ (n : ℝ) - (1 : ℝ) := by linarith
  have hexp : 1 ≤ Real.exp ((n : ℝ) - (1 : ℝ)) := Real.one_le_exp hdiff
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ 9 := by
    simpa using (pow_le_pow_right₀ hnR (show 1 ≤ 9 by omega))
  have hpow0 : 0 ≤ (n : ℝ) ^ 9 := by positivity
  calc
    (n : ℝ) ≤ (n : ℝ) ^ 9 := hpow
    _ = 1 * (n : ℝ) ^ 9 := by ring
    _ ≤ Real.exp ((n : ℝ) - (1 : ℝ)) * (n : ℝ) ^ 9 :=
      mul_le_mul_of_nonneg_right hexp hpow0
    _ = Real.exp ((n : ℝ) - ((1 : ℕ) : ℝ)) * (n : ℝ) ^ 9 := by
      norm_num

lemma scaleRadius_one_eq_zero_div_exp (n : ℕ) (hn : 1 ≤ n) :
    scaleRadius n 1 = scaleRadius n 0 / Real.exp 1 := by
  rw [scaleRadius_of_le hn, scaleRadius_of_le (Nat.zero_le n)]
  simpa using regularRadius_succ n 0

/-- Starting between radii `2 r₀` and `5 r₀`, the probability of
reaching `r₁ = r₀/e` before radius `8 r₀` is at least `1/128`, once
the explicit potential-kernel errors total at most `1/16`. -/
theorem one_div_128_le_centered_initial_innerExitMass
    {r0 r1 : ℝ} {boxRadius : ℕ} {y : Point}
    (hr0 : 2 < r0) (hr1 : r1 = r0 / Real.exp 1) (hr1two : 2 < r1)
    (hbox : 8 * r0 ≤ (boxRadius : ℝ))
    (hyLower : 2 * r0 ≤ euclideanRadius y)
    (hyUpper : euclideanRadius y ≤ 5 * r0)
    (herror : globalRadialConstant / euclideanRadius y +
        max (realBoundaryPotentialError r1)
          (realBoundaryPotentialError (8 * r0)) ≤ 1 / 16) :
    (1 / 128 : ℝ) ≤
      (exitMass (literalRealAnnulus r1 (8 * r0) boxRadius)
        (literalRealAnnulusInnerExit r1 (8 * r0) boxRadius) y).toReal := by
  have hr0pos : 0 < r0 := by linarith
  have hexp : 0 < Real.exp 1 := Real.exp_pos _
  have hr1pos : 0 < r1 := by rw [hr1]; positivity
  have houterTwo : 2 < 8 * r0 := by nlinarith
  have hyrPos : 0 < euclideanRadius y := lt_of_lt_of_le (by positivity) hyLower
  have hyne : y ≠ 0 := (euclideanRadius_pos_iff y).mp hyrPos
  have hyOuter : y ∈ disc 0 (8 * r0) := by
    simpa [disc, RadialHarnackSpecialization.latticeDistance_zero_eq_euclideanRadius]
      using hyUpper.trans (by linarith : 5 * r0 ≤ 8 * r0)
  have hyNotOuterBoundary : y ∉ discBoundary 0 (8 * r0) := by
    apply not_mem_discBoundary_of_mem_disc_of_add_one_le
      (r := 5 * r0)
    · simpa [disc, RadialHarnackSpecialization.latticeDistance_zero_eq_euclideanRadius]
        using hyUpper
    · nlinarith
  have hyNotInner : y ∉ disc 0 r1 := by
    intro hy
    have hyr1 : euclideanRadius y ≤ r1 := by
      simpa [disc, RadialHarnackSpecialization.latticeDistance_zero_eq_euclideanRadius]
        using hy
    rw [hr1] at hyr1
    have hexpTwo : 2 < Real.exp 1 := Real.exp_one_gt_two
    have : r0 / Real.exp 1 < 2 * r0 := by
      rw [div_lt_iff₀ hexp]
      nlinarith
    linarith
  have hyAnnulus : y ∈ literalRealAnnulus r1 (8 * r0) boxRadius := by
    rw [mem_literalRealAnnulus_iff (by positivity) hbox]
    exact ⟨hyOuter, hyNotOuterBoundary, hyNotInner⟩
  have hdelta : 0 < realBoundaryPotentialValue (8 * r0) -
      realBoundaryPotentialValue r1 := by
    rw [realBoundaryPotentialValue_sub_eq_log_div (by positivity) hr1pos]
    apply mul_pos (by positivity)
    apply Real.log_pos
    rw [hr1]
    have : (8 * r0) / (r0 / Real.exp 1) = 8 * Real.exp 1 := by
      field_simp
    rw [this]
    nlinarith [Real.exp_one_gt_two]
  have hratio := literalRealAnnulusInnerExit_ratio_bounds
    hr1two houterTwo hbox hyAnnulus hdelta
  have hpotentialAbs :=
    abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_global
      hyne
  have hpotentialUpper : planarPotentialKernel y ≤
      realBoundaryPotentialValue (euclideanRadius y) +
        globalRadialConstant / euclideanRadius y := by
    unfold realBoundaryPotentialValue
    rw [abs_le] at hpotentialAbs
    linarith
  have hvalueUpper : realBoundaryPotentialValue (euclideanRadius y) ≤
      realBoundaryPotentialValue (5 * r0) :=
    realBoundaryPotentialValue_mono hyrPos hyUpper
  have hmainLower : (3 / 16 : ℝ) ≤
      realBoundaryPotentialValue (8 * r0) -
        realBoundaryPotentialValue (5 * r0) := by
    rw [realBoundaryPotentialValue_sub_eq_log_div (by positivity) (by positivity)]
    have hquot : (8 * r0) / (5 * r0) = (8 / 5 : ℝ) := by field_simp
    rw [hquot]
    have hcoef : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_le_four]
    have hmul := mul_le_mul hcoef three_eighths_le_log_eight_fifths
      (by norm_num : (0 : ℝ) ≤ 3 / 8) (by positivity : (0 : ℝ) ≤ 2 / Real.pi)
    norm_num at hmul ⊢
    exact hmul
  have hdenUpper :
      realBoundaryPotentialValue (8 * r0) -
          realBoundaryPotentialValue r1 ≤ 4 := by
    rw [realBoundaryPotentialValue_sub_eq_log_div (by positivity) hr1pos,
      hr1]
    have hquot : (8 * r0) / (r0 / Real.exp 1) = 8 * Real.exp 1 := by
      field_simp
    rw [hquot]
    have hcoef : (2 / Real.pi : ℝ) ≤ 1 := by
      rw [div_le_one Real.pi_pos]
      exact Real.two_le_pi
    exact (mul_le_mul hcoef log_eight_mul_exp_one_le_four
      (Real.log_nonneg (by nlinarith [Real.exp_one_gt_two])) (by norm_num)).trans_eq
        (by ring)
  calc
    (1 / 128 : ℝ) ≤
        (realBoundaryPotentialValue (8 * r0) - planarPotentialKernel y -
            max (realBoundaryPotentialError r1)
              (realBoundaryPotentialError (8 * r0))) /
          (realBoundaryPotentialValue (8 * r0) -
            realBoundaryPotentialValue r1) := by
      rw [le_div_iff₀ hdelta]
      have hnum : (1 / 8 : ℝ) ≤
          realBoundaryPotentialValue (8 * r0) - planarPotentialKernel y -
            max (realBoundaryPotentialError r1)
              (realBoundaryPotentialError (8 * r0)) := by
        linarith
      nlinarith
    _ ≤ _ := hratio.1

/-- From boundary `r₀`, the probability of reaching radius `32 r₀` before
returning to `r₁ = r₀/e` is at least `1/128`, once the explicit boundary
errors total at most `1/16`. -/
theorem one_div_128_le_centered_final_outerExitMass
    {r0 r1 : ℝ} {boxRadius : ℕ} {y : Point}
    (hr0 : 2 < r0) (hr1 : r1 = r0 / Real.exp 1) (hr1two : 2 < r1)
    (hbox : 32 * r0 ≤ (boxRadius : ℝ))
    (hy : y ∈ discBoundary 0 r0)
    (herror : realBoundaryPotentialError r0 +
        max (realBoundaryPotentialError r1)
          (realBoundaryPotentialError (32 * r0)) ≤ 1 / 16) :
    (1 / 128 : ℝ) ≤
      (exitMass (literalRealAnnulus r1 (32 * r0) boxRadius)
        (literalRealAnnulusOuterExit r1 (32 * r0) boxRadius) y).toReal := by
  have hr0pos : 0 < r0 := by linarith
  have hexp : 0 < Real.exp 1 := Real.exp_pos _
  have hr1pos : 0 < r1 := by rw [hr1]; positivity
  have houterTwo : 2 < 32 * r0 := by nlinarith
  have hr1sep : r1 + 1 ≤ r0 := by
    rw [hr1]
    have hhalf : r0 / Real.exp 1 < r0 / 2 := by
      exact div_lt_div_of_pos_left hr0pos (by norm_num) Real.exp_one_gt_two
    linarith
  have hyOuter : y ∈ disc 0 (32 * r0) := by
    have hyDisc : y ∈ disc 0 r0 :=
      RealDiscFinite.discBoundary_subset_disc 0 r0 hy
    change latticeDistance 0 y ≤ r0 at hyDisc
    change latticeDistance 0 y ≤ 32 * r0
    exact hyDisc.trans (by nlinarith)
  have hyNotOuterBoundary : y ∉ discBoundary 0 (32 * r0) := by
    apply not_mem_discBoundary_of_mem_disc_of_add_one_le
      (RealDiscFinite.discBoundary_subset_disc 0 r0 hy)
    nlinarith
  have hyNotInner : y ∉ disc 0 r1 := by
    intro hyInner
    exact (not_mem_discBoundary_of_mem_disc_of_add_one_le hyInner hr1sep) hy
  have hyAnnulus : y ∈ literalRealAnnulus r1 (32 * r0) boxRadius := by
    rw [mem_literalRealAnnulus_iff (by positivity) hbox]
    exact ⟨hyOuter, hyNotOuterBoundary, hyNotInner⟩
  have hdelta : 0 < realBoundaryPotentialValue (32 * r0) -
      realBoundaryPotentialValue r1 := by
    rw [realBoundaryPotentialValue_sub_eq_log_div (by positivity) hr1pos]
    apply mul_pos (by positivity)
    apply Real.log_pos
    rw [hr1]
    have hquot : (32 * r0) / (r0 / Real.exp 1) = 32 * Real.exp 1 := by
      field_simp
    rw [hquot]
    nlinarith [Real.exp_one_gt_two]
  have hratio := literalRealAnnulusOuterExit_ratio_bounds
    hr1two houterTwo hbox hyAnnulus hdelta
  have hpotentialAbs :=
    abs_planarPotentialKernel_sub_realBoundaryPotentialValue_le hr0 hy
  have hpotentialLower :
      realBoundaryPotentialValue r0 - realBoundaryPotentialError r0 ≤
        planarPotentialKernel y := by
    rw [abs_le] at hpotentialAbs
    linarith
  have hmainLower : (1 / 2 : ℝ) ≤
      realBoundaryPotentialValue r0 - realBoundaryPotentialValue r1 := by
    rw [realBoundaryPotentialValue_sub_eq_log_div hr0pos hr1pos, hr1]
    have hquot : r0 / (r0 / Real.exp 1) = Real.exp 1 := by field_simp
    rw [hquot, Real.log_exp]
    have hcoef : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_le_four]
    simpa using hcoef
  have hdenUpper :
      realBoundaryPotentialValue (32 * r0) -
          realBoundaryPotentialValue r1 ≤ 6 := by
    rw [realBoundaryPotentialValue_sub_eq_log_div (by positivity) hr1pos,
      hr1]
    have hquot : (32 * r0) / (r0 / Real.exp 1) = 32 * Real.exp 1 := by
      field_simp
    rw [hquot]
    have hcoef : (2 / Real.pi : ℝ) ≤ 1 := by
      rw [div_le_one Real.pi_pos]
      exact Real.two_le_pi
    exact (mul_le_mul hcoef log_thirtyTwo_mul_exp_one_le_six
      (Real.log_nonneg (by nlinarith [Real.exp_one_gt_two])) (by norm_num)).trans_eq
        (by ring)
  calc
    (1 / 128 : ℝ) ≤
        (planarPotentialKernel y - realBoundaryPotentialValue r1 -
            max (realBoundaryPotentialError r1)
              (realBoundaryPotentialError (32 * r0))) /
          (realBoundaryPotentialValue (32 * r0) -
            realBoundaryPotentialValue r1) := by
      rw [le_div_iff₀ hdelta]
      have hnum : (7 / 16 : ℝ) ≤
          planarPotentialKernel y - realBoundaryPotentialValue r1 -
            max (realBoundaryPotentialError r1)
              (realBoundaryPotentialError (32 * r0)) := by
        linarith
      nlinarith
    _ ≤ _ := hratio.1

/-- At every scale above the explicit radius threshold, the centered
initial and final `1/128` estimates apply with natural-ceiling carriers.
The final estimate is uniform over its starting boundary point. -/
theorem centered_spatial_splice_bounds_at_scale
    (n : ℕ) (hn : 1 ≤ n)
    (hlarge : spatialSpliceRadiusThreshold ≤ (n : ℝ))
    {x : Point} (hx : x ∈ candidateBox n) :
    (1 / 128 : ℝ) ≤
        (exitMass
          (literalRealAnnulus (scaleRadius n 1) (8 * scaleRadius n 0)
            ⌈8 * scaleRadius n 0⌉₊)
          (literalRealAnnulusInnerExit (scaleRadius n 1) (8 * scaleRadius n 0)
            ⌈8 * scaleRadius n 0⌉₊) (-x)).toReal ∧
      ∀ y : Point, y ∈ discBoundary 0 (scaleRadius n 0) →
        (1 / 128 : ℝ) ≤
          (exitMass
            (literalRealAnnulus (scaleRadius n 1) (32 * scaleRadius n 0)
              ⌈32 * scaleRadius n 0⌉₊)
            (literalRealAnnulusOuterExit (scaleRadius n 1) (32 * scaleRadius n 0)
              ⌈32 * scaleRadius n 0⌉₊) y).toReal := by
  let r0 := scaleRadius n 0
  let r1 := scaleRadius n 1
  have hnRadius : (n : ℝ) ≤ r1 := by
    dsimp only [r1]
    exact natCast_le_scaleRadius_one n hn
  have hr1large : spatialSpliceRadiusThreshold ≤ r1 :=
    hlarge.trans hnRadius
  have hthresholdThree : (3 : ℝ) ≤ spatialSpliceRadiusThreshold :=
    le_max_left _ _
  have hr1three : (3 : ℝ) ≤ r1 := hthresholdThree.trans hr1large
  have hr1two : 2 < r1 := by linarith
  have hr01 : r1 = r0 / Real.exp 1 := by
    dsimp only [r0, r1]
    exact scaleRadius_one_eq_zero_div_exp n hn
  have hr1r0 : r1 ≤ r0 := by
    rw [hr01]
    have hr0nonneg : 0 ≤ r0 := by
      dsimp only [r0]
      simp only [scaleRadius_of_le (Nat.zero_le n), regularRadius,
        Nat.cast_zero, sub_zero]
      positivity
    exact div_le_self hr0nonneg (Real.one_le_exp (by norm_num))
  have hr0two : 2 < r0 := lt_of_lt_of_le hr1two hr1r0
  have hinitLarge : 16 * (3 * globalRadialConstant + 4) ≤ r1 :=
    (le_max_left _ _).trans ((le_max_right (3 : ℝ) _).trans hr1large)
  have hfinalLarge : 64 * (globalRadialConstant + 2) ≤ r1 :=
    (le_max_right _ _).trans ((le_max_right (3 : ℝ) _).trans hr1large)
  have hgeom := candidate_neg_euclideanRadius_bounds hx
  constructor
  · apply one_div_128_le_centered_initial_innerExitMass
      hr0two hr01 hr1two (Nat.le_ceil _) hgeom.1 hgeom.2
    exact initial_error_le_of_radius_large globalRadialConstant_pos.le
      (by linarith) (by linarith) hr1r0 hgeom.1 hinitLarge
  · intro y hy
    apply one_div_128_le_centered_final_outerExitMass
      hr0two hr01 hr1two (Nat.le_ceil _) hy
    exact final_error_le_of_radius_large
      (by linarith) (by linarith) hr1r0 hfinalLarge

/-- The preceding centered spatial bounds hold for all sufficiently large
HLOZ scales. -/
theorem eventually_centered_spatial_splice_bounds :
    ∀ᶠ n : ℕ in atTop, ∀ x : Point, x ∈ candidateBox n →
      (1 / 128 : ℝ) ≤
          (exitMass
            (literalRealAnnulus (scaleRadius n 1) (8 * scaleRadius n 0)
              ⌈8 * scaleRadius n 0⌉₊)
            (literalRealAnnulusInnerExit (scaleRadius n 1) (8 * scaleRadius n 0)
              ⌈8 * scaleRadius n 0⌉₊) (-x)).toReal ∧
        ∀ y : Point, y ∈ discBoundary 0 (scaleRadius n 0) →
          (1 / 128 : ℝ) ≤
            (exitMass
              (literalRealAnnulus (scaleRadius n 1) (32 * scaleRadius n 0)
                ⌈32 * scaleRadius n 0⌉₊)
              (literalRealAnnulusOuterExit (scaleRadius n 1) (32 * scaleRadius n 0)
                ⌈32 * scaleRadius n 0⌉₊) y).toReal := by
  have hlarge := tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop spatialSpliceRadiusThreshold)
  filter_upwards [hlarge, eventually_ge_atTop 1] with n hlarge hn x hx
  exact centered_spatial_splice_bounds_at_scale n hn hlarge hx

end

end Erdos1165.AnnularSpatialSplice
