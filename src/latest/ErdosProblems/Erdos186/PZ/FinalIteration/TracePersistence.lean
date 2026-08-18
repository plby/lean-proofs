/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.FinalIteration

/-!
# Source-faithful population persistence along a trace

Same-dimensional steps are aggregated into maximal runs.  Their convex
scales and structural ratios telescope before the persistence estimate is
applied, so a whole run costs one fixed power rather than one power per step.
Only the intervening dimension-changing moves incur the separate change-step
power cost.
-/

namespace Erdos186.PZ.FinalIteration.Partial.TracePersistence

open Finset
open scoped BigOperators

noncomputable section

/-- The extra estimate imposed on a same-dimensional step before it is put
into a telescoped run. -/
def SameStepAbsorbed {K : ℕ} {zeta changeGain sameGain : ℝ}
    {current : State zeta}
    (step : StepOutput (K := K) (changeGain := changeGain)
      (sameGain := sameGain) current) : Prop :=
  step.kind = .same ∧
    step.boxConstant * step.convexScale ≤
      step.convexScale ^ sameRunA current.dimension zeta

/-- A consecutive run consisting only of absorbed same-dimensional steps. -/
inductive SameRun (K : ℕ) (zeta changeGain sameGain : ℝ) :
    ℕ → State zeta → State zeta → Type
  | nil (current : State zeta) :
      SameRun K zeta changeGain sameGain 0 current current
  | snoc {length : ℕ} {first current : State zeta}
      (run : SameRun K zeta changeGain sameGain length first current)
      (step : StepOutput (K := K) (changeGain := changeGain)
        (sameGain := sameGain) current)
      (absorbed : SameStepAbsorbed step) :
      SameRun K zeta changeGain sameGain (length + 1) first step.next

namespace SameRun

variable {K : ℕ} {zeta changeGain sameGain : ℝ}
variable {length : ℕ} {first last : State zeta}

/-- Product of all convex scales in the run. -/
def U {length : ℕ} {first last : State zeta} :
    SameRun K zeta changeGain sameGain length first last → ℝ
  | .nil _ => 1
  | .snoc run step _ => U run * step.convexScale

/-- Product of all structural population ratios in the run. -/
def V {length : ℕ} {first last : State zeta} :
    SameRun K zeta changeGain sameGain length first last → ℝ
  | .nil _ => 1
  | .snoc run step _ => V run * step.structuralRatio

theorem dimension_eq
    (run : SameRun K zeta changeGain sameGain length first last) :
    last.dimension = first.dimension := by
  induction run with
  | nil => rfl
  | snoc run step absorbed ih =>
      have htransition := step.transition
      rw [absorbed.1] at htransition
      exact htransition.1.trans ih

theorem U_pos
    (run : SameRun K zeta changeGain sameGain length first last) :
    0 < run.U := by
  induction run with
  | nil =>
      change 0 < (1 : ℝ)
      norm_num
  | snoc run step absorbed ih =>
      change 0 < run.U * step.convexScale
      exact mul_pos ih step.convexScale_pos

theorem U_le_one
    (run : SameRun K zeta changeGain sameGain length first last) :
    run.U ≤ 1 := by
  induction run with
  | nil => norm_num [U]
  | snoc run step absorbed ih =>
      change run.U * step.convexScale ≤ 1
      nlinarith [run.U_pos, step.convexScale_pos,
        step.convexScale_le_one]

theorem V_pos
    (run : SameRun K zeta changeGain sameGain length first last) :
    0 < run.V := by
  induction run with
  | nil =>
      change 0 < (1 : ℝ)
      norm_num
  | snoc run step absorbed ih =>
      change 0 < run.V * step.structuralRatio
      exact mul_pos ih step.structuralRatio_pos

theorem V_le_one
    (run : SameRun K zeta changeGain sameGain length first last) :
    run.V ≤ 1 := by
  induction run with
  | nil => norm_num [V]
  | snoc run step absorbed ih =>
      change run.V * step.structuralRatio ≤ 1
      nlinarith [run.V_pos, step.structuralRatio_pos,
        step.structuralRatio_le_one]

/-- Telescoped point-retention inequality for a same-dimensional run. -/
theorem point_product
    (run : SameRun K zeta changeGain sameGain length first last) :
    run.U ^ sameRunQ first.dimension zeta * run.V * first.points.card ≤
      (last.points.card : ℝ) := by
  induction run with
  | nil => norm_num [U, V]
  | @snoc length first current run step absorbed ih =>
      have hdimension : current.dimension = first.dimension := run.dimension_eq
      have htransition := step.transition
      rw [absorbed.1] at htransition
      have hretention : step.retention =
          step.convexScale ^ sameRunQ first.dimension zeta *
            step.structuralRatio := by
        rw [htransition.2.2.1, sameRunQ, hdimension]
      have hmultNonneg : 0 ≤
          step.convexScale ^ sameRunQ first.dimension zeta *
            step.structuralRatio :=
        mul_nonneg (Real.rpow_nonneg step.convexScale_pos.le _)
          step.structuralRatio_pos.le
      calc
        (SameRun.snoc run step absorbed).U ^
              sameRunQ first.dimension zeta *
              (SameRun.snoc run step absorbed).V * first.points.card =
            (step.convexScale ^ sameRunQ first.dimension zeta *
              step.structuralRatio) *
                (run.U ^ sameRunQ first.dimension zeta * run.V *
                  first.points.card) := by
          change (run.U * step.convexScale) ^
              sameRunQ first.dimension zeta *
              (run.V * step.structuralRatio) * first.points.card = _
          rw [Real.mul_rpow run.U_pos.le step.convexScale_pos.le]
          ring
        _ ≤ (step.convexScale ^ sameRunQ first.dimension zeta *
              step.structuralRatio) * current.points.card :=
          mul_le_mul_of_nonneg_left ih hmultNonneg
        _ = step.retention * current.points.card := by rw [hretention]
        _ ≤ (step.next.points.card : ℝ) := step.population_retained

/-- Telescoped box inequality after absorbing the fixed constant at each
same-dimensional step. -/
theorem box_end_le_product
    (run : SameRun K zeta changeGain sameGain length first last) :
    (last.box.carrier.card : ℝ) ≤
      run.U ^ sameRunA first.dimension zeta * run.V ^ K *
        first.box.carrier.card := by
  induction run with
  | nil => norm_num [U, V]
  | @snoc length first current run step absorbed ih =>
      have hdimension : current.dimension = first.dimension := run.dimension_eq
      have htransition := step.transition
      rw [absorbed.1] at htransition
      have habsorb : step.boxConstant * step.convexScale ≤
          step.convexScale ^ sameRunA first.dimension zeta := by
        simpa [hdimension] using absorbed.2
      have hratioPow : 0 ≤ step.structuralRatio ^ K :=
        pow_nonneg step.structuralRatio_pos.le _
      have hcurrentBox : (0 : ℝ) ≤ current.box.carrier.card := by positivity
      have hscaleProduct : 0 ≤
          step.convexScale ^ sameRunA first.dimension zeta *
            step.structuralRatio ^ K :=
        mul_nonneg (Real.rpow_nonneg step.convexScale_pos.le _) hratioPow
      calc
        (step.next.box.carrier.card : ℝ) ≤
            step.boxConstant * step.convexScale *
              step.structuralRatio ^ K * current.box.carrier.card :=
          htransition.2.2.2
        _ ≤ step.convexScale ^ sameRunA first.dimension zeta *
              step.structuralRatio ^ K * current.box.carrier.card := by
          gcongr
        _ ≤ step.convexScale ^ sameRunA first.dimension zeta *
              step.structuralRatio ^ K *
                (run.U ^ sameRunA first.dimension zeta * run.V ^ K *
                  first.box.carrier.card) := by
          gcongr
        _ = (SameRun.snoc run step absorbed).U ^
              sameRunA first.dimension zeta *
              (SameRun.snoc run step absorbed).V ^ K *
                first.box.carrier.card := by
          change _ = (run.U * step.convexScale) ^
              sameRunA first.dimension zeta *
              (run.V * step.structuralRatio) ^ K * first.box.carrier.card
          rw [Real.mul_rpow run.U_pos.le step.convexScale_pos.le, mul_pow]
          ring

/-- The telescoped products form the numerical persistence input of the
existing `U,V` lemma. -/
def persistenceInput
    (run : SameRun K zeta changeGain sameGain length first last)
    (hK : 1 ≤ (K : ℝ) * sameRunLambda first.dimension zeta) :
    SameDimensionPersistenceInput where
  U := run.U
  V := run.V
  boxStart := first.box.carrier.card
  pointsStart := first.points.card
  pointsEnd := last.points.card
  K := K
  a := sameRunA first.dimension zeta
  q := sameRunQ first.dimension zeta
  densityExponent := boxExponent first.dimension + zeta + first.excess
  lambda := sameRunLambda first.dimension zeta
  U_pos := run.U_pos
  U_le_one := run.U_le_one
  V_pos := run.V_pos
  V_le_one := run.V_le_one
  boxStart_pos := by
    exact_mod_cast Finset.card_pos.mpr
      (first.points_nonempty.mono first.points_subset_box)
  pointsStart_pos := by exact_mod_cast first.points_nonempty.card_pos
  densityExponent_pos := by
    have hbox := boxExponent_pos first.dimension_pos
    linarith [first.zeta_pos, first.excess_nonneg]
  lambda_nonneg := by
    have hconvex : 0 ≤ convexDensityExponent first.dimension := by
      unfold convexDensityExponent
      positivity
    dsimp [sameRunLambda]
    linarith [first.zeta_pos]
  q_le_a_mul_lambda := by
    have hlambda : 0 < sameRunLambda first.dimension zeta := by
      have hconvex : 0 ≤ convexDensityExponent first.dimension := by
        unfold convexDensityExponent
        positivity
      dsimp [sameRunLambda]
      linarith [first.zeta_pos]
    dsimp [sameRunA]
    rw [div_mul_cancel₀ _ hlambda.ne']
  one_le_K_mul_lambda := hK
  lambda_lt_densityExponent := by
    have hconvex := convexDensityExponent_le_boxExponent first.dimension_pos
    dsimp [sameRunLambda]
    linarith [first.zeta_pos, first.excess_nonneg]
  start_density := by
    have hboxPos : (0 : ℝ) < first.box.carrier.card := by
      exact_mod_cast Finset.card_pos.mpr
        (first.points_nonempty.mono first.points_subset_box)
    have hpointsPos : (0 : ℝ) < first.points.card := by
      exact_mod_cast first.points_nonempty.card_pos
    by_contra hnot
    have hreverse : (first.points.card : ℝ) ≤
        (first.box.carrier.card : ℝ) ^
          (boxExponent first.dimension + zeta + first.excess) :=
      le_of_not_gt hnot
    have hlogReverse := Real.log_le_log hpointsPos hreverse
    rw [Real.log_rpow hboxPos] at hlogReverse
    linarith [first.density_certificate]
  point_product := run.point_product
  box_product := by
    have hone : (1 : ℝ) ≤ last.box.carrier.card := by
      exact_mod_cast Nat.succ_le_iff.mpr
        (last.points_nonempty.mono last.points_subset_box).card_pos
    exact hone.trans run.box_end_le_product

/-- A whole same-dimensional run incurs the single source persistence
exponent supplied by its initial state. -/
theorem points_start_rpow_runExponent_le
    (run : SameRun K zeta changeGain sameGain length first last)
    (hK : 1 ≤ (K : ℝ) * sameRunLambda first.dimension zeta) :
    (first.points.card : ℝ) ^
        (1 - sameRunLambda first.dimension zeta /
          (boxExponent first.dimension + zeta + first.excess)) ≤
      (last.points.card : ℝ) := by
  exact (run.persistenceInput hK).pointsStart_rpow_sigma_le_pointsEnd

/-- The source choice `lambda = convexDensityExponent d + 3*zeta/4`
leaves at least the fixed exponent `zeta/4` over an entire same-dimensional
run. -/
theorem zeta_div_four_le_runExponent
    (_run : SameRun K zeta changeGain sameGain length first last) :
    zeta / 4 ≤
      1 - sameRunLambda first.dimension zeta /
        (boxExponent first.dimension + zeta + first.excess) := by
  let D : ℝ := boxExponent first.dimension + zeta + first.excess
  let L : ℝ := sameRunLambda first.dimension zeta
  have hDpos : 0 < D := by
    dsimp [D]
    have hbox := boxExponent_pos first.dimension_pos
    linarith [first.zeta_pos, first.excess_nonneg]
  have hDone : D ≤ 1 := first.totalExponent_lt_one.le
  have hconvex := convexDensityExponent_le_boxExponent first.dimension_pos
  have hgap : zeta / 4 ≤ D - L := by
    dsimp [D, L, sameRunLambda]
    linarith [first.excess_nonneg]
  have hzetaQuarter : 0 ≤ zeta / 4 := by linarith [first.zeta_pos]
  have hscaled : zeta / 4 * D ≤ zeta / 4 := by
    nlinarith [mul_nonneg hzetaQuarter (sub_nonneg.mpr hDone)]
  have hdivision : 1 - L / D = (D - L) / D := by
    field_simp
  rw [hdivision, le_div_iff₀ hDpos]
  exact hscaled.trans hgap

/-- Thus every absorbed same-dimensional run, of arbitrary length, retains
the same fixed population power `zeta/4`. -/
theorem points_start_rpow_zeta_div_four_le
    (run : SameRun K zeta changeGain sameGain length first last)
    (hK : 1 ≤ (K : ℝ) * (3 * zeta / 4)) :
    (first.points.card : ℝ) ^ (zeta / 4) ≤
      (last.points.card : ℝ) := by
  have hconvex : 0 ≤ convexDensityExponent first.dimension := by
    unfold convexDensityExponent
    positivity
  have hKrun : 1 ≤
      (K : ℝ) * sameRunLambda first.dimension zeta := by
    have hKnonneg : (0 : ℝ) ≤ K := by positivity
    have hlambda : 3 * zeta / 4 ≤ sameRunLambda first.dimension zeta := by
      dsimp [sameRunLambda]
      linarith
    exact hK.trans (mul_le_mul_of_nonneg_left hlambda hKnonneg)
  have hpointsOne : (1 : ℝ) ≤ first.points.card := by
    exact_mod_cast Nat.succ_le_iff.mpr first.points_nonempty.card_pos
  exact (Real.rpow_le_rpow_of_exponent_le hpointsOne
      run.zeta_div_four_le_runExponent).trans
    (run.points_start_rpow_runExponent_le hKrun)

end SameRun

/-! ### Maximal-run decomposition of a branch-controlled trace -/

/-- Canonical decomposition into consecutive same-dimensional runs,
separated by individual dimension-changing steps.  Every internal run is
maximal by construction: a separator is inserted exactly at each non-same
step. -/
inductive SameRunDecomposition (K : ℕ)
    (zeta changeGain sameGain rhoChange : ℝ) :
    ℕ → State zeta → State zeta → ℕ → Type
  | single {runLength : ℕ} {first last : State zeta}
      (run : SameRun K zeta changeGain sameGain runLength first last) :
      SameRunDecomposition K zeta changeGain sameGain rhoChange
        runLength first last 0
  | snocChange {prefixLength runLength changes : ℕ}
      {first current last : State zeta}
      (decompPrefix : SameRunDecomposition K zeta changeGain sameGain rhoChange
        prefixLength first current changes)
      (step : BranchControlledStepOutput (K := K)
        (changeGain := changeGain) (sameGain := sameGain)
        (rhoChange := rhoChange) current)
      (hchange : step.kind ≠ .same)
      (run : SameRun K zeta changeGain sameGain
        runLength step.next last) :
      SameRunDecomposition K zeta changeGain sameGain rhoChange
        (prefixLength + 1 + runLength) first last (changes + 1)

namespace SameRunDecomposition

variable {K : ℕ} {zeta changeGain sameGain rhoChange : ℝ}

/-- Extend the final same-dimensional run by one more same step. -/
def appendSame {length changes : ℕ} {first current : State zeta}
    (decomposition : SameRunDecomposition K zeta changeGain sameGain
      rhoChange length first current changes)
    (step : BranchControlledStepOutput (K := K)
      (changeGain := changeGain) (sameGain := sameGain)
      (rhoChange := rhoChange) current)
    (hsame : step.kind = .same) :
    SameRunDecomposition K zeta changeGain sameGain rhoChange
      (length + 1) first step.next changes := by
  induction decomposition with
  | single run =>
      exact .single (.snoc run step.toStepOutput
        ⟨hsame, step.same_box_absorbed hsame⟩)
  | @snocChange prefixLength runLength changes first before current
      decompPrefix changeStep hchange run ih =>
      simpa only [Nat.add_assoc] using
        SameRunDecomposition.snocChange decompPrefix changeStep hchange
          (.snoc run step.toStepOutput
            ⟨hsame, step.same_box_absorbed hsame⟩)

end SameRunDecomposition

variable {K : ℕ} {zeta changeGain sameGain rhoChange : ℝ}
variable {length : ℕ} {first last : State zeta}

/-- Every branch-controlled trace has the canonical maximal-same-run
decomposition, indexed by its exact number of dimension changes. -/
theorem branchTrace_exists_sameRunDecomposition
    (trace : BranchTrace K zeta changeGain sameGain rhoChange
      length first last) :
    Nonempty (SameRunDecomposition K zeta changeGain sameGain rhoChange
      length first last trace.changeCount) := by
  induction trace with
  | nil current =>
      exact ⟨.single (.nil current)⟩
  | @snoc n first current tracePrefix step ih =>
      obtain ⟨decomposition⟩ := ih
      by_cases hsame : step.kind = .same
      · exact ⟨by
          simpa [BranchTrace.changeCount, hsame] using
            decomposition.appendSame step hsame⟩
      · exact ⟨by
          simpa [BranchTrace.changeCount, hsame] using
            SameRunDecomposition.snocChange decomposition step hsame
              (.nil step.next)⟩

/-! ### Uniform population exponent -/

/-- Exact initial-population exponent after `changes` dimension-changing
moves and the `changes + 1` intervening maximal same-dimensional runs. -/
def persistenceExponent (zeta rhoChange : ℝ) (changes : ℕ) : ℝ :=
  (zeta / 4) ^ (changes + 1) * (1 - rhoChange) ^ changes

theorem persistenceExponent_pos
    {zeta rhoChange : ℝ} (changes : ℕ)
    (hzeta : 0 < zeta) (hrhoChange : rhoChange < 1) :
    0 < persistenceExponent zeta rhoChange changes := by
  dsimp [persistenceExponent]
  exact mul_pos (pow_pos (by positivity) _)
    (pow_pos (sub_pos.mpr hrhoChange) _)

/-- A positive change gain has a finite source budget for all changing
moves. -/
theorem exists_changeSteps_budget {changeGain : ℝ}
    (hchangeGain : 0 < changeGain) :
    ∃ changeSteps : ℕ, 1 ≤ (changeSteps : ℝ) * changeGain := by
  obtain ⟨changeSteps, hsteps⟩ := exists_nat_gt (1 / changeGain)
  refine ⟨changeSteps, ?_⟩
  have hmul := mul_lt_mul_of_pos_right hsteps hchangeGain
  rw [div_mul_cancel₀ 1 hchangeGain.ne'] at hmul
  exact hmul.le

/-- A positive `zeta` admits an integer box exponent large enough for the
same-run persistence calculation. -/
theorem exists_K_sameRun_budget {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ K : ℕ, 1 ≤ (K : ℝ) * (3 * zeta / 4) := by
  have hcoefficient : 0 < 3 * zeta / 4 := by positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / (3 * zeta / 4))
  refine ⟨K, ?_⟩
  have hmul := mul_lt_mul_of_pos_right hK hcoefficient
  rw [div_mul_cancel₀ 1 hcoefficient.ne'] at hmul
  exact hmul.le

namespace SameRunDecomposition

variable {K : ℕ} {zeta changeGain sameGain rhoChange : ℝ}
variable {length changes : ℕ} {first last : State zeta}

/-- The exact source-faithful persistence bound: same-dimensional losses
are charged once per maximal run, and replacement power losses are charged
only at the dimension-changing separators. -/
theorem points_rpow_persistenceExponent_le
    (decomposition : SameRunDecomposition K zeta changeGain sameGain
      rhoChange length first last changes)
    (hK : 1 ≤ (K : ℝ) * (3 * zeta / 4))
    (hrho : rhoChange ≤ 1) :
    (first.points.card : ℝ) ^
        persistenceExponent zeta rhoChange changes ≤
      (last.points.card : ℝ) := by
  have hsNonneg : 0 ≤ zeta / 4 := by linarith [first.zeta_pos]
  have hsigmaNonneg : 0 ≤ 1 - rhoChange := sub_nonneg.mpr hrho
  induction decomposition with
  | single run =>
      simpa [persistenceExponent] using
        run.points_start_rpow_zeta_div_four_le hK
  | @snocChange prefixLength runLength changes first current last
      decompPrefix step hchange run ih =>
      let s : ℝ := zeta / 4
      let sigma : ℝ := 1 - rhoChange
      let E : ℝ := persistenceExponent zeta rhoChange changes
      have hraiseChange :
          ((first.points.card : ℝ) ^ E) ^ sigma ≤
            (current.points.card : ℝ) ^ sigma :=
        Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          ih hsigmaNonneg
      have hchangeRetained :
          (current.points.card : ℝ) ^ sigma ≤
            (step.next.points.card : ℝ) := by
        exact step.change_points_power_retained hchange
      have hthroughChange :
          ((first.points.card : ℝ) ^ E) ^ sigma ≤
            (step.next.points.card : ℝ) :=
        hraiseChange.trans hchangeRetained
      have hraiseRun :
          (((first.points.card : ℝ) ^ E) ^ sigma) ^ s ≤
            (step.next.points.card : ℝ) ^ s :=
        Real.rpow_le_rpow
          (Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _)
          hthroughChange hsNonneg
      have hrun := run.points_start_rpow_zeta_div_four_le hK
      have hexponent :
          persistenceExponent zeta rhoChange (changes + 1) =
            E * sigma * s := by
        dsimp [E, sigma, s, persistenceExponent]
        rw [pow_succ (zeta / 4) (changes + 1),
          pow_succ (1 - rhoChange) changes]
        ring
      calc
        (first.points.card : ℝ) ^
              persistenceExponent zeta rhoChange (changes + 1) =
            (((first.points.card : ℝ) ^ E) ^ sigma) ^ s := by
          rw [hexponent, Real.rpow_mul (Nat.cast_nonneg _)]
          congr 1
          exact Real.rpow_mul (Nat.cast_nonneg _) E sigma
        _ ≤ (step.next.points.card : ℝ) ^ s := hraiseRun
        _ ≤ (last.points.card : ℝ) := hrun

end SameRunDecomposition

/-- The exact persistence estimate directly on a branch-controlled trace. -/
theorem branchTrace_points_rpow_exact_le
    {K length : ℕ} {zeta changeGain sameGain rhoChange : ℝ}
    {first last : State zeta}
    (trace : BranchTrace (K := K) (ζ := zeta)
      (changeGain := changeGain) (sameGain := sameGain)
      (rhoChange := rhoChange) length first last)
    (hK : 1 ≤ (K : ℝ) * (3 * zeta / 4))
    (hrho : rhoChange ≤ 1) :
    (first.points.card : ℝ) ^
        persistenceExponent zeta rhoChange trace.changeCount ≤
      (last.points.card : ℝ) := by
  obtain ⟨decomposition⟩ :=
    branchTrace_exists_sameRunDecomposition trace
  exact decomposition.points_rpow_persistenceExponent_le hK hrho

/-- When both branch losses lie in `[0,1]`, the persistence exponent is
antitone in the allowed number of dimension changes. -/
theorem persistenceExponent_anti
    {zeta rhoChange : ℝ} {changes changeCap : ℕ}
    (hsNonneg : 0 ≤ zeta / 4) (hsOne : zeta / 4 ≤ 1)
    (hrhoNonneg : 0 ≤ rhoChange) (hrhoOne : rhoChange ≤ 1)
    (hchanges : changes ≤ changeCap) :
    persistenceExponent zeta rhoChange changeCap ≤
      persistenceExponent zeta rhoChange changes := by
  have hsigmaNonneg : 0 ≤ 1 - rhoChange := sub_nonneg.mpr hrhoOne
  have hsigmaOne : 1 - rhoChange ≤ 1 := by linarith
  have hsPower :
      (zeta / 4) ^ (changeCap + 1) ≤
        (zeta / 4) ^ (changes + 1) :=
    pow_le_pow_of_le_one hsNonneg hsOne (Nat.add_le_add_right hchanges 1)
  have hsigmaPower :
      (1 - rhoChange) ^ changeCap ≤
        (1 - rhoChange) ^ changes :=
    pow_le_pow_of_le_one hsigmaNonneg hsigmaOne hchanges
  dsimp [persistenceExponent]
  exact mul_le_mul hsPower hsigmaPower
    (pow_nonneg hsigmaNonneg _) (pow_nonneg hsNonneg _)

/-- Final uniform prefix lower bound.  An Archimedean change budget bounds
the number of dimension-changing moves; arbitrarily many same-dimensional
steps do not alter the fixed exponent. -/
theorem branchTrace_points_rpow_changeBudget_le
    {K length changeSteps : ℕ}
    {zeta changeGain sameGain rhoChange : ℝ}
    {first last : State zeta}
    (trace : BranchTrace (K := K) (ζ := zeta)
      (changeGain := changeGain) (sameGain := sameGain)
      (rhoChange := rhoChange) length first last)
    (hK : 1 ≤ (K : ℝ) * (3 * zeta / 4))
    (hrhoNonneg : 0 ≤ rhoChange) (hrhoOne : rhoChange ≤ 1)
    (hchangeGain : 0 < changeGain) (hsameGain : 0 ≤ sameGain)
    (hchangeBudget : 1 ≤ (changeSteps : ℝ) * changeGain) :
    (first.points.card : ℝ) ^
        persistenceExponent zeta rhoChange changeSteps ≤
      (last.points.card : ℝ) := by
  have hcount : trace.changeCount ≤ changeSteps :=
    (trace.changeCount_lt hchangeGain hsameGain hchangeBudget).le
  have hsNonneg : 0 ≤ zeta / 4 := by linarith [first.zeta_pos]
  have hzetaOne : zeta < 1 := by
    have htotal := first.totalExponent_lt_one
    have hbox := boxExponent_pos first.dimension_pos
    linarith [first.excess_nonneg]
  have hsOne : zeta / 4 ≤ 1 := by linarith
  have hexponent := persistenceExponent_anti hsNonneg hsOne
    hrhoNonneg hrhoOne hcount
  have hpointsOne : (1 : ℝ) ≤ first.points.card := by
    exact_mod_cast Nat.succ_le_iff.mpr first.points_nonempty.card_pos
  exact (Real.rpow_le_rpow_of_exponent_le hpointsOne hexponent).trans
    (branchTrace_points_rpow_exact_le trace hK hrhoOne)

end

end Erdos186.PZ.FinalIteration.Partial.TracePersistence

#print axioms
  Erdos186.PZ.FinalIteration.Partial.TracePersistence.SameRun.points_start_rpow_runExponent_le
#print axioms
  Erdos186.PZ.FinalIteration.Partial.TracePersistence.branchTrace_points_rpow_changeBudget_le

namespace Erdos186.PZ.FinalIteration.Partial

open TracePersistence

/-! ### The source-faithful frozen package -/

/-- A positive fixed persistence exponent converts the public box threshold
and the strict critical-density inequality into the initial population
budget required by the branch-controlled package. -/
theorem exists_box_threshold_persistence_budget
    (pointThreshold : ℕ) {criticalExponent persistence : ℝ}
    (hcriticalExponent : 0 < criticalExponent)
    (hpersistence : 0 < persistence) :
    ∃ boxThreshold : ℕ, 2 ≤ boxThreshold ∧
      ∀ {boxCard pointCard : ℕ}, boxThreshold ≤ boxCard →
        (boxCard : ℝ) ^ criticalExponent < (pointCard : ℝ) →
        (pointThreshold : ℝ) ≤ (pointCard : ℝ) ^ persistence := by
  have heffective : 0 < criticalExponent * persistence :=
    mul_pos hcriticalExponent hpersistence
  have heventually : ∀ᶠ boxCard : ℕ in Filter.atTop,
      (pointThreshold : ℝ) ≤
        (boxCard : ℝ) ^ (criticalExponent * persistence) := by
    exact ((tendsto_rpow_atTop heffective).comp
      tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_ge_atTop (pointThreshold : ℝ))
  obtain ⟨growthThreshold, hgrowth⟩ :=
    Filter.eventually_atTop.1 heventually
  let boxThreshold := max 2 growthThreshold
  refine ⟨boxThreshold, le_max_left _ _, ?_⟩
  intro boxCard pointCard hlarge hcritical
  have hgrowthLarge : growthThreshold ≤ boxCard :=
    (le_max_right 2 growthThreshold).trans hlarge
  have hboxNonneg : (0 : ℝ) ≤ boxCard := by positivity
  have hcriticalPow :
      ((boxCard : ℝ) ^ criticalExponent) ^ persistence <
        (pointCard : ℝ) ^ persistence :=
    Real.rpow_lt_rpow (Real.rpow_nonneg hboxNonneg _) hcritical hpersistence
  calc
    (pointThreshold : ℝ) ≤
        (boxCard : ℝ) ^ (criticalExponent * persistence) :=
      hgrowth boxCard hgrowthLarge
    _ = ((boxCard : ℝ) ^ criticalExponent) ^ persistence := by
      rw [Real.rpow_mul hboxNonneg]
    _ ≤ (pointCard : ℝ) ^ persistence := hcriticalPow.le

/-- All parameters frozen before the finite iteration.  Same-dimensional
runs are charged through `persistenceExponent`, while only the bounded
number of dimension-changing moves pay `rhoChange`. -/
structure Package {ζ : ℝ} (initial : State ζ) where
  dimensionCeiling : ℕ
  pointThreshold : ℕ
  steps : ℕ
  changeSteps : ℕ
  K : ℕ
  changeGain : ℝ
  sameGain : ℝ
  rhoChange : ℝ
  changeGain_pos : 0 < changeGain
  sameGain_pos : 0 < sameGain
  rhoChange_nonneg : 0 ≤ rhoChange
  rhoChange_le_one : rhoChange ≤ 1
  sameRun_K_budget : 1 ≤ (K : ℝ) * (3 * ζ / 4)
  change_budget : 1 ≤ (changeSteps : ℝ) * changeGain
  exponent_budget :
    1 < initial.excess + (steps : ℝ) *
      DensityIteration.Iteration.uniformGain changeGain sameGain
  dimension_persists :
    ∀ {length : ℕ} {last : State ζ}, length ≤ steps →
      Nonempty (BranchTrace (K := K) (ζ := ζ)
        (changeGain := changeGain) (sameGain := sameGain)
        (rhoChange := rhoChange) length initial last) →
      last.dimension ≤ dimensionCeiling
  initial_population_budget :
    (pointThreshold : ℝ) ≤
      (initial.points.card : ℝ) ^
        persistenceExponent ζ rhoChange changeSteps
  oneStep : BranchOneStepConstructor dimensionCeiling pointThreshold
    initial.points.card K ζ changeGain sameGain rhoChange
      ((initial.points.card : ℝ) ^
        persistenceExponent ζ rhoChange changeSteps)

namespace Package

variable {ζ : ℝ} {initial : State ζ}

/-- Every prefix retains the exact real population floor frozen from the
initial state. -/
theorem populationFloor_persists
    (P : Package initial) {length : ℕ} {last : State ζ}
    (trace : BranchTrace (K := P.K) (ζ := ζ)
      (changeGain := P.changeGain) (sameGain := P.sameGain)
      (rhoChange := P.rhoChange) length initial last) :
    (initial.points.card : ℝ) ^
        persistenceExponent ζ P.rhoChange P.changeSteps ≤
      (last.points.card : ℝ) := by
  exact
    branchTrace_points_rpow_changeBudget_le trace P.sameRun_K_budget
      P.rhoChange_nonneg P.rhoChange_le_one P.changeGain_pos
      P.sameGain_pos.le P.change_budget

/-- The maximal-run persistence theorem and the single initial budget imply
the stopping exclusion at every prefix. -/
theorem population_persists
    (P : Package initial) {length : ℕ} {last : State ζ}
    (_hlength : length ≤ P.steps)
    (trace : BranchTrace (K := P.K) (ζ := ζ)
      (changeGain := P.changeGain) (sameGain := P.sameGain)
      (rhoChange := P.rhoChange) length initial last) :
    P.pointThreshold ≤ last.points.card := by
  have hcast : (P.pointThreshold : ℝ) ≤ (last.points.card : ℝ) :=
    P.initial_population_budget.trans (P.populationFloor_persists trace)
  exact_mod_cast hcast

theorem pointThreshold_le_of_trace
    (P : Package initial) {length : ℕ} {last : State ζ}
    (hlength : length ≤ P.steps)
    (trace : BranchTrace (K := P.K) (ζ := ζ)
      (changeGain := P.changeGain) (sameGain := P.sameGain)
      (rhoChange := P.rhoChange) length initial last) :
    P.pointThreshold ≤ last.points.card :=
  P.population_persists hlength trace

/-- Every prefix is applicable: dimension and lower population persist, and
raw step containment supplies the frozen initial-population ceiling. -/
theorem applicable_of_trace
    (P : Package initial) {length : ℕ} {last : State ζ}
    (hlength : length ≤ P.steps)
    (trace : BranchTrace (K := P.K) (ζ := ζ)
      (changeGain := P.changeGain) (sameGain := P.sameGain)
      (rhoChange := P.rhoChange) length initial last) :
    BranchApplicable P.dimensionCeiling P.pointThreshold initial.points.card
      ((initial.points.card : ℝ) ^
        persistenceExponent ζ P.rhoChange P.changeSteps) last := by
  exact ⟨⟨P.dimension_persists hlength ⟨trace⟩,
      P.pointThreshold_le_of_trace hlength trace,
      trace.points_card_le_first⟩,
    P.populationFloor_persists trace⟩

/-- The partial branch-controlled one-step theorem constructs every prefix
up to the frozen contradiction horizon. -/
theorem exists_trace (P : Package initial) :
    ∀ length : ℕ, length ≤ P.steps →
      ∃ last : State ζ, Nonempty
        (BranchTrace (K := P.K) (ζ := ζ)
          (changeGain := P.changeGain) (sameGain := P.sameGain)
          (rhoChange := P.rhoChange) length initial last) := by
  intro length hlength
  induction length with
  | zero => exact ⟨initial, ⟨BranchTrace.nil initial⟩⟩
  | succ length ih =>
      obtain ⟨current, ⟨tracePrefix⟩⟩ := ih (by omega)
      have happlicable := P.applicable_of_trace (by omega) tracePrefix
      let step := Classical.choice (P.oneStep current happlicable)
      exact ⟨step.next, ⟨BranchTrace.snoc tracePrefix step⟩⟩

/-- The global finite-horizon contradiction. -/
theorem false_of_partialOneStep (P : Package initial) : False := by
  obtain ⟨last, ⟨trace⟩⟩ := P.exists_trace P.steps (le_refl _)
  have hlower := trace.excess_lower_bound
  have hupper := last.excess_le_one
  linarith [P.exponent_budget]

end Package

end Erdos186.PZ.FinalIteration.Partial

namespace Erdos186.PZ.FinalIteration

/-- The exact branch-controlled constructor proposition required by the
final box theorem.  Its public quantifier order is unchanged. -/
def OneStepPackageStatement : Prop :=
  ∀ d : ℕ, ∀ hd : 0 < d, ∀ ζ : ℝ, ∀ hζ : 0 < ζ,
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (B : IntegerBox d) (A : Finset (BoxPoint d))
        (hA : A ⊆ B.carrier) (hNA : IsBoxNonaveraging A)
        (_hlarge : M ≤ B.carrier.card)
        (hBtwo : 2 ≤ B.carrier.card)
        (hcritical :
          (B.carrier.card : ℝ) ^ (boxExponent d + ζ) < (A.card : ℝ)),
        let initial := @Partial.initialState d ζ hd hζ B A hA hNA
          hBtwo hcritical
        Nonempty (Partial.Package initial)

/-- Final Pham--Zakharov box theorem from the source-faithful partial
one-step construction. -/
theorem pzBoxBound_of_oneStep
    (oneStep : OneStepPackageStatement) : PZBoxBound := by
  intro d hd ζ hζ
  obtain ⟨M, hMtwo, hconstruct⟩ := oneStep d hd ζ hζ
  refine ⟨M, ?_⟩
  intro B A hA hNA hlarge
  by_contra hbound
  have hcritical :
      (B.carrier.card : ℝ) ^ (boxExponent d + ζ) < (A.card : ℝ) :=
    lt_of_not_ge hbound
  let initial := @Partial.initialState d ζ hd hζ B A hA hNA
    (hMtwo.trans hlarge) hcritical
  let P : Partial.Package initial :=
    Classical.choice
      (hconstruct B A hA hNA hlarge (hMtwo.trans hlarge) hcritical)
  exact P.false_of_partialOneStep

end Erdos186.PZ.FinalIteration
