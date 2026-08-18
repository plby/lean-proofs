/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# The finite density-increment iteration for Erdős Problem 186

This file isolates the bookkeeping at the end of the Pham--Zakharov
argument.  It deliberately takes the output of one density-increment step
as an explicit interface.  The additive-combinatorial and convex-geometric
parts of the proof are responsible for constructing values satisfying this
interface.

At stage `i`, `points i` and `box i` are positive real cardinalities and
`exponent i` is certified by

`(exponent i) * log (box i) < log (points i)`.

Since the point set is contained in its box, every certified exponent is at
most one.  A step either changes dimension and gains `changeGain`, or stays
in the same dimension and gains `sameGain`.  In the latter case a proportion
`ratio i` of the points is retained while the next box shrinks by its
`K`-th power.  The main results below prove:

* a uniform linear lower bound for the successive exponents;
* telescoping product bounds on every same-dimension run;
* the resulting finite upper bound on the number of steps; and
* contradiction as soon as the accumulated excess exponent is greater
  than one.

The dimension ceiling is part of the data, so a single pair of gains can be
chosen uniformly over all dimensions reached by the iteration.
-/

open scoped BigOperators

namespace Erdos186.DensityIteration

/-- The three alternatives in one Pham--Zakharov iteration step. -/
inductive StepKind where
  /-- The subset-sum dimension strictly increases. -/
  | up
  /-- The subset-sum dimension strictly decreases. -/
  | down
  /-- The subset-sum dimension stays fixed. -/
  | same
  deriving DecidableEq

/--
Finite data for the density-increment iteration.

The functions are defined on all natural numbers to make successor
bookkeeping painless; every condition is restricted to the first `steps`
transitions or the first `steps + 1` states.  The hypotheses in `step`
are exactly the three proved interfaces needed from a one-step theorem.
-/
structure Iteration (dimensionCeiling steps K : ℕ)
    (changeGain sameGain : ℝ) where
  /-- Subset-sum dimension at each stage. -/
  dimension : ℕ → ℕ
  /-- Cardinality of the retained point set, viewed in `ℝ`. -/
  points : ℕ → ℝ
  /-- Cardinality of the containing box, viewed in `ℝ`. -/
  box : ℕ → ℝ
  /-- The exponent in the current supercritical density estimate. -/
  exponent : ℕ → ℝ
  /-- The point-retention proportion used in a same-dimension step. -/
  ratio : ℕ → ℝ
  /-- Which of the three alternatives occurs at a transition. -/
  kind : ℕ → StepKind
  /-- All dimensions reached by the finite iteration are uniformly bounded. -/
  dimension_le : ∀ i, i ≤ steps → dimension i ≤ dimensionCeiling
  /-- Every point set in the iteration is nonempty. -/
  one_le_points : ∀ i, i ≤ steps → 1 ≤ points i
  /-- The point set is contained in its ambient box. -/
  points_le_box : ∀ i, i ≤ steps → points i ≤ box i
  /-- The current density estimate, expressed after taking logarithms. -/
  density_certificate :
    ∀ i, i ≤ steps → exponent i * Real.log (box i) < Real.log (points i)
  /-- Retention proportions used by transitions are strictly positive. -/
  ratio_pos : ∀ i, i < steps → 0 < ratio i
  /-- Retention proportions are at most one. -/
  ratio_le_one : ∀ i, i < steps → ratio i ≤ 1
  /-- The explicit per-step trichotomy. -/
  step : ∀ i, i < steps →
    match kind i with
    | .up =>
        dimension i < dimension (i + 1) ∧
          exponent i + changeGain ≤ exponent (i + 1)
    | .down =>
        dimension (i + 1) < dimension i ∧
          exponent i + changeGain ≤ exponent (i + 1)
    | .same =>
        dimension (i + 1) = dimension i ∧
          exponent i + sameGain ≤ exponent (i + 1) ∧
          ratio i * points i ≤ points (i + 1) ∧
          box (i + 1) ≤ ratio i ^ K * box i

namespace Iteration

variable {dimensionCeiling steps K : ℕ} {changeGain sameGain : ℝ}

/-- The common positive increment available in every branch. -/
def uniformGain (changeGain sameGain : ℝ) : ℝ := min changeGain sameGain

/-- Product of the retention proportions along a consecutive run. -/
def retentionProduct
    (X : Iteration dimensionCeiling steps K changeGain sameGain)
    (start length : ℕ) : ℝ :=
  ∏ j ∈ Finset.range length, X.ratio (start + j)

@[simp] theorem retentionProduct_zero
    (X : Iteration dimensionCeiling steps K changeGain sameGain)
    (start : ℕ) : X.retentionProduct start 0 = 1 := by
  simp [retentionProduct]

theorem retentionProduct_succ
    (X : Iteration dimensionCeiling steps K changeGain sameGain)
    (start length : ℕ) :
    X.retentionProduct start (length + 1) =
      X.retentionProduct start length * X.ratio (start + length) := by
  simp [retentionProduct, Finset.prod_range_succ]

/-- A density certificate for a contained nonempty point set can never have
exponent greater than one. -/
theorem exponent_le_one
    (X : Iteration dimensionCeiling steps K changeGain sameGain)
    {i : ℕ} (hi : i ≤ steps) : X.exponent i ≤ 1 := by
  have hp1 : 1 ≤ X.points i := X.one_le_points i hi
  have hpb : X.points i ≤ X.box i := X.points_le_box i hi
  have hb1 : 1 ≤ X.box i := hp1.trans hpb
  have hp0 : 0 < X.points i := lt_of_lt_of_le zero_lt_one hp1
  have hlog_nonneg : 0 ≤ Real.log (X.box i) := Real.log_nonneg hb1
  have hlog_le : Real.log (X.points i) ≤ Real.log (X.box i) :=
    Real.log_le_log hp0 hpb
  have hdensity := X.density_certificate i hi
  by_contra h
  have hone : 1 < X.exponent i := lt_of_not_ge h
  have hbox_le : Real.log (X.box i) ≤ X.exponent i * Real.log (X.box i) := by
    nlinarith
  linarith

/-- Both numerical gains dominate their common uniform gain. -/
theorem uniformGain_le_changeGain : uniformGain changeGain sameGain ≤ changeGain :=
  min_le_left _ _

/-- Both numerical gains dominate their common uniform gain. -/
theorem uniformGain_le_sameGain : uniformGain changeGain sameGain ≤ sameGain :=
  min_le_right _ _

/-- Every branch of the trichotomy increases the exponent by at least the
uniform gain. -/
theorem exponent_add_uniformGain_le
    (X : Iteration dimensionCeiling steps K changeGain sameGain)
    {i : ℕ} (hi : i < steps) :
    X.exponent i + uniformGain changeGain sameGain ≤ X.exponent (i + 1) := by
  have hstep := X.step i hi
  have hchangeGain : uniformGain changeGain sameGain ≤ changeGain :=
    min_le_left _ _
  have hsameGain : uniformGain changeGain sameGain ≤ sameGain :=
    min_le_right _ _
  cases hkind : X.kind i with
  | up =>
      rw [hkind] at hstep
      simp only at hstep
      linarith
  | down =>
      rw [hkind] at hstep
      simp only at hstep
      linarith
  | same =>
      rw [hkind] at hstep
      simp only at hstep
      linarith

/-- After `i` transitions, the initial exponent has gained at least `i`
copies of the uniform increment. -/
theorem exponent_lower_bound
    (X : Iteration dimensionCeiling steps K changeGain sameGain)
    {i : ℕ} (hi : i ≤ steps) :
    X.exponent 0 + (i : ℝ) * uniformGain changeGain sameGain ≤ X.exponent i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have histeps : i < steps := by omega
      have ih' : X.exponent 0 + (i : ℝ) * uniformGain changeGain sameGain ≤
          X.exponent i := ih (by omega)
      calc
        X.exponent 0 + ((i + 1 : ℕ) : ℝ) * uniformGain changeGain sameGain =
            (X.exponent 0 + (i : ℝ) * uniformGain changeGain sameGain) +
              uniformGain changeGain sameGain := by
                push_cast
                ring
        _ ≤ X.exponent i + uniformGain changeGain sameGain := by
          linarith
        _ ≤ X.exponent (i + 1) := X.exponent_add_uniformGain_le histeps

/-- The exponent budget bounds the total length of every valid iteration. -/
theorem step_budget
    (X : Iteration dimensionCeiling steps K changeGain sameGain) :
    X.exponent 0 + (steps : ℝ) * uniformGain changeGain sameGain ≤ 1 := by
  exact (X.exponent_lower_bound (le_refl steps)).trans
    (X.exponent_le_one (le_refl steps))

/-- A same-dimension transition exposes both multiplicative estimates from
the step interface. -/
theorem same_step_data
    (X : Iteration dimensionCeiling steps K changeGain sameGain)
    {i : ℕ} (hi : i < steps) (hkind : X.kind i = .same) :
    X.exponent i + sameGain ≤ X.exponent (i + 1) ∧
      X.ratio i * X.points i ≤ X.points (i + 1) ∧
      X.box (i + 1) ≤ X.ratio i ^ K * X.box i := by
  have hstep := X.step i hi
  rw [hkind] at hstep
  simp only at hstep
  exact ⟨hstep.2.1, hstep.2.2.1, hstep.2.2.2⟩

/-- Point retention telescopes along a consecutive same-dimension run. -/
theorem retentionProduct_mul_points_le
    (X : Iteration dimensionCeiling steps K changeGain sameGain)
    {start length : ℕ} (hend : start + length ≤ steps)
    (hsame : ∀ j, j < length → X.kind (start + j) = .same) :
    X.retentionProduct start length * X.points start ≤ X.points (start + length) := by
  induction length with
  | zero => simp [retentionProduct]
  | succ length ih =>
      have hprefix : start + length ≤ steps := by omega
      have hlast : start + length < steps := by omega
      have ih' := ih hprefix (fun j hj ↦ hsame j (by omega))
      have hdata := X.same_step_data hlast (hsame length (by omega))
      rw [retentionProduct_succ]
      calc
        (X.retentionProduct start length * X.ratio (start + length)) *
              X.points start =
            X.ratio (start + length) *
              (X.retentionProduct start length * X.points start) := by ring
        _ ≤ X.ratio (start + length) * X.points (start + length) :=
          mul_le_mul_of_nonneg_left ih' (le_of_lt (X.ratio_pos _ hlast))
        _ ≤ X.points (start + length + 1) := hdata.2.1
        _ = X.points (start + (length + 1)) := rfl

/-- Box shrinkage telescopes along a consecutive same-dimension run. -/
theorem box_le_retentionProduct_pow_mul
    (X : Iteration dimensionCeiling steps K changeGain sameGain)
    {start length : ℕ} (hend : start + length ≤ steps)
    (hsame : ∀ j, j < length → X.kind (start + j) = .same) :
    X.box (start + length) ≤ X.retentionProduct start length ^ K * X.box start := by
  induction length with
  | zero => simp [retentionProduct]
  | succ length ih =>
      have hprefix : start + length ≤ steps := by omega
      have hlast : start + length < steps := by omega
      have ih' := ih hprefix (fun j hj ↦ hsame j (by omega))
      have hdata := X.same_step_data hlast (hsame length (by omega))
      have hratio_pow : 0 ≤ X.ratio (start + length) ^ K :=
        pow_nonneg (le_of_lt (X.ratio_pos _ hlast)) K
      rw [retentionProduct_succ, mul_pow]
      calc
        X.box (start + (length + 1)) = X.box (start + length + 1) := rfl
        _ ≤ X.ratio (start + length) ^ K * X.box (start + length) := hdata.2.2
        _ ≤ X.ratio (start + length) ^ K *
              (X.retentionProduct start length ^ K * X.box start) :=
          mul_le_mul_of_nonneg_left ih' hratio_pow
        _ = (X.retentionProduct start length ^ K *
              X.ratio (start + length) ^ K) * X.box start := by ring

/-- Nonemptiness of the last box gives the exact product obstruction used
to show that a same-dimension run cannot discard too much mass. -/
theorem one_le_retentionProduct_pow_mul_box
    (X : Iteration dimensionCeiling steps K changeGain sameGain)
    {start length : ℕ} (hend : start + length ≤ steps)
    (hsame : ∀ j, j < length → X.kind (start + j) = .same) :
    1 ≤ X.retentionProduct start length ^ K * X.box start := by
  have hone : 1 ≤ X.box (start + length) :=
    (X.one_le_points _ hend).trans (X.points_le_box _ hend)
  exact hone.trans (X.box_le_retentionProduct_pow_mul hend hsame)

/-- The two telescoping conclusions for a same-dimension run, packaged in
the form used by the global iteration. -/
theorem same_run_product_bounds
    (X : Iteration dimensionCeiling steps K changeGain sameGain)
    {start length : ℕ} (hend : start + length ≤ steps)
    (hsame : ∀ j, j < length → X.kind (start + j) = .same) :
    X.retentionProduct start length * X.points start ≤ X.points (start + length) ∧
      1 ≤ X.retentionProduct start length ^ K * X.box start := by
  exact ⟨X.retentionProduct_mul_points_le hend hsame,
    X.one_le_retentionProduct_pow_mul_box hend hsame⟩

/-- The complete finite bookkeeping theorem: bounded-dimension trichotomy
controls the exponent budget, while every same-dimension block satisfies the
two product estimates needed to keep subsequent steps in range. -/
theorem bookkeeping
    (X : Iteration dimensionCeiling steps K changeGain sameGain) :
    X.exponent 0 + (steps : ℝ) * uniformGain changeGain sameGain ≤ 1 ∧
      ∀ start length, start + length ≤ steps →
        (∀ j, j < length → X.kind (start + j) = .same) →
          X.retentionProduct start length * X.points start ≤
              X.points (start + length) ∧
            1 ≤ X.retentionProduct start length ^ K * X.box start := by
  refine ⟨X.step_budget, ?_⟩
  intro start length hend hsame
  exact X.same_run_product_bounds hend hsame

/-- If both branch gains are positive, sufficiently many transitions force
the certified exponent past one, contradicting containment. -/
theorem no_iteration_of_one_lt_accumulated_exponent
    (X : Iteration dimensionCeiling steps K changeGain sameGain)
    (hchange : 0 < changeGain) (hsame : 0 < sameGain)
    (hbudget : 1 < X.exponent 0 +
      (steps : ℝ) * uniformGain changeGain sameGain) : False := by
  have huniform : 0 < uniformGain changeGain sameGain :=
    lt_min hchange hsame
  have := X.step_budget
  linarith [huniform]

/-- A natural-number version convenient when planning a fixed number of
iterations. -/
theorem no_iteration_of_nat_budget
    (X : Iteration dimensionCeiling steps K changeGain sameGain)
    (hchange : 0 < changeGain) (hsame : 0 < sameGain) {budget : ℕ}
    (hsteps : budget ≤ steps)
    (hbudget : 1 < X.exponent 0 +
      (budget : ℝ) * uniformGain changeGain sameGain) : False := by
  have huniform : 0 < uniformGain changeGain sameGain :=
    lt_min hchange hsame
  have hcast : (budget : ℝ) ≤ (steps : ℝ) := by exact_mod_cast hsteps
  apply X.no_iteration_of_one_lt_accumulated_exponent hchange hsame
  exact lt_of_lt_of_le hbudget (by nlinarith)

end Iteration

end Erdos186.DensityIteration
