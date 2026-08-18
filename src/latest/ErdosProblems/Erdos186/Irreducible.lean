/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# Bookkeeping for the irreducibility iteration in Erdős problem 186

This file formalizes the finite bookkeeping part of Lemma 10 of
Pham--Zakharov.  It deliberately does **not** assert that any of the moves
can be constructed.  That additive-combinatorial content belongs in the
modules which construct a move.  Here a finite run is represented by a
`MoveTrace`; its fields are precisely the one-step facts used by the
bookkeeping argument.

There are three moves.

* An `up` move strictly raises the subset-sum dimension, costs a fixed
  factor `cost` in GAP size, and has an additional saving.
* A `down` move strictly lowers the dimension and costs `cost`.
* A `shrink` move preserves the dimension and multiplies GAP size by
  `shrinkFactor`.

Every move retains at least a `retention` fraction of the current
population.  The saving in an up move is bounded by
`upBase ^ (dimension jump)`.  In the application `upBase` is the inverse
of the common lower bound for the scales `s(A_i)`.

The main conclusions are:

* population after `m` moves is at least `retention ^ m` times its initial
  value;
* the GAP-size multiplier factors exactly into the up/down cost, shrink
  factor, and product of up savings;
* the dimensions telescope, so the number of dimension-changing moves is
  at most the initial dimension plus twice the total upward jump;
* once dimension-changing moves are bounded, a sufficiently long trace
  would contain too many shrink moves and force a GAP size below one.

No choice or existence principle for moves is hidden in these statements.
-/

namespace Erdos186
namespace Irreducible

open Finset

/-- Numerical parameters used by every step of an irreducibility trace. -/
structure MoveParameters where
  /-- Fraction of the population retained in one move. -/
  retention : ℝ
  /-- Loss attached to an up or down move. -/
  cost : ℝ
  /-- Loss attached to a same-dimensional shrink move. -/
  shrinkFactor : ℝ
  /-- Uniform upper bound per unit of upward dimension jump. -/
  upBase : ℝ
  retention_nonneg : 0 ≤ retention
  one_le_cost : 1 ≤ cost
  shrinkFactor_nonneg : 0 ≤ shrinkFactor
  shrinkFactor_le_one : shrinkFactor ≤ 1
  upBase_nonneg : 0 ≤ upBase
  upBase_le_one : upBase ≤ 1

/-- The numerical data retained about one stage of the iteration. -/
structure IterationState where
  /-- Cardinality of the current set, coerced to `ℝ`. -/
  population : ℝ
  /-- Rank / subset-sum dimension at the current stage. -/
  dimension : ℕ
  /-- Cardinality of the current containing GAP, coerced to `ℝ`. -/
  gapSize : ℝ
  population_pos : 0 < population
  /-- A containing GAP is nonempty.  This is the lower bound used in the
  termination contradiction. -/
  one_le_gapSize : 1 ≤ gapSize

/-- The three kinds of move in the irreducibility reduction. -/
inductive MoveKind
  | up
  | down
  | shrink
  deriving DecidableEq, Repr

/-- The one-step multiplier in the GAP-size estimate. -/
def stepMultiplier (p : MoveParameters) (kind : MoveKind)
    (upSaving : ℝ) : ℝ :=
  match kind with
  | .up => p.cost * upSaving
  | .down => p.cost
  | .shrink => p.shrinkFactor

theorem MoveParameters.cost_nonneg (p : MoveParameters) : 0 ≤ p.cost := by
  linarith [p.one_le_cost]

/-- A finite sequence of abstract irreducibility moves.

Only values at indices below `length` (and states up through `length`) are
used.  Keeping the sequences total makes prefix sums and products easy to
state. -/
structure MoveTrace (p : MoveParameters) (length : ℕ) where
  state : ℕ → IterationState
  kind : ℕ → MoveKind
  /-- The extra multiplier belonging to an up move.  Its value is ignored
  at down and shrink moves. -/
  upSaving : ℕ → ℝ
  upSaving_nonneg : ∀ i, i < length → 0 ≤ upSaving i
  population_retained : ∀ i, i < length →
    p.retention * (state i).population ≤ (state (i + 1)).population
  dimension_rule : ∀ i, i < length →
    match kind i with
    | .up => (state i).dimension < (state (i + 1)).dimension
    | .down => (state (i + 1)).dimension < (state i).dimension
    | .shrink => (state (i + 1)).dimension = (state i).dimension
  gap_control : ∀ i, i < length →
    (state (i + 1)).gapSize ≤
      stepMultiplier p (kind i) (upSaving i) * (state i).gapSize
  upSaving_control : ∀ i, i < length → kind i = .up →
    upSaving i ≤
      p.upBase ^ ((state (i + 1)).dimension - (state i).dimension)

variable {p : MoveParameters} {length : ℕ}

/-- Number of moves of kind `kind` among the first `m` moves. -/
def kindCount (t : MoveTrace p length) (kind : MoveKind) (m : ℕ) : ℕ :=
  match m with
  | 0 => 0
  | m + 1 => kindCount t kind m + if t.kind m = kind then 1 else 0

/-- Total amount by which up moves raise the dimension in the first `m`
moves. -/
def upwardJump (t : MoveTrace p length) (m : ℕ) : ℕ :=
  match m with
  | 0 => 0
  | m + 1 =>
      upwardJump t m +
        if t.kind m = .up then
          (t.state (m + 1)).dimension - (t.state m).dimension
        else 0

/-- Total amount by which down moves lower the dimension in the first `m`
moves. -/
def downwardJump (t : MoveTrace p length) (m : ℕ) : ℕ :=
  match m with
  | 0 => 0
  | m + 1 =>
      downwardJump t m +
        if t.kind m = .down then
          (t.state m).dimension - (t.state (m + 1)).dimension
        else 0

/-- Product of the extra saving factors at the up moves in a prefix. -/
def upSavingProduct (t : MoveTrace p length) (m : ℕ) : ℝ :=
  match m with
  | 0 => 1
  | m + 1 => upSavingProduct t m *
      if t.kind m = .up then t.upSaving m else 1

/-- Product of all one-step GAP multipliers in a prefix. -/
def multiplierProduct (t : MoveTrace p length) (m : ℕ) : ℝ :=
  match m with
  | 0 => 1
  | m + 1 => multiplierProduct t m *
      stepMultiplier p (t.kind m) (t.upSaving m)

@[simp] theorem kindCount_zero (t : MoveTrace p length) (kind : MoveKind) :
    kindCount t kind 0 = 0 := by
  simp [kindCount]

@[simp] theorem upwardJump_zero (t : MoveTrace p length) :
    upwardJump t 0 = 0 := by
  simp [upwardJump]

@[simp] theorem downwardJump_zero (t : MoveTrace p length) :
    downwardJump t 0 = 0 := by
  simp [downwardJump]

@[simp] theorem upSavingProduct_zero (t : MoveTrace p length) :
    upSavingProduct t 0 = 1 := by
  simp [upSavingProduct]

@[simp] theorem multiplierProduct_zero (t : MoveTrace p length) :
    multiplierProduct t 0 = 1 := by
  simp [multiplierProduct]

/-- The three move counts partition a prefix. -/
theorem length_eq_sum_kindCount (t : MoveTrace p length) (m : ℕ) :
    m = kindCount t .up m + kindCount t .down m +
      kindCount t .shrink m := by
  induction m with
  | zero => simp
  | succ m ih =>
      cases hkind : t.kind m <;>
        simp [kindCount, hkind] at ih ⊢ <;> omega

/-- At one step, the dimension increase and decrease balance. -/
private theorem dimension_step_balance (t : MoveTrace p length) {i : ℕ}
    (hi : i < length) :
    (t.state i).dimension +
        (if t.kind i = .up then
          (t.state (i + 1)).dimension - (t.state i).dimension else 0) =
      (t.state (i + 1)).dimension +
        (if t.kind i = .down then
          (t.state i).dimension - (t.state (i + 1)).dimension else 0) := by
  have hrule := t.dimension_rule i hi
  cases hkind : t.kind i <;> simp [hkind] at hrule ⊢ <;> omega

/-- Telescoping identity for all dimension changes in a prefix. -/
theorem dimension_balance (t : MoveTrace p length) {m : ℕ}
    (hm : m ≤ length) :
    (t.state 0).dimension + upwardJump t m =
      (t.state m).dimension + downwardJump t m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm' : m ≤ length := by omega
      have hstep := dimension_step_balance t (show m < length by omega)
      specialize ih hm'
      simp only [upwardJump, downwardJump]
      rw [← Nat.add_assoc, ih]
      omega

/-- Every up move contributes at least one unit to the total upward jump. -/
theorem upCount_le_upwardJump (t : MoveTrace p length) {m : ℕ}
    (hm : m ≤ length) : kindCount t .up m ≤ upwardJump t m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm' : m ≤ length := by omega
      specialize ih hm'
      have hrule := t.dimension_rule m (show m < length by omega)
      cases hkind : t.kind m <;>
        simp [kindCount, upwardJump, hkind] at hrule ⊢ <;> omega

/-- Every down move contributes at least one unit to the total downward
jump. -/
theorem downCount_le_downwardJump (t : MoveTrace p length) {m : ℕ}
    (hm : m ≤ length) : kindCount t .down m ≤ downwardJump t m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm' : m ≤ length := by omega
      specialize ih hm'
      have hrule := t.dimension_rule m (show m < length by omega)
      cases hkind : t.kind m <;>
        simp [kindCount, downwardJump, hkind] at hrule ⊢ <;> omega

/-- Downward jump is paid for by the initial dimension and upward jump. -/
theorem downwardJump_le_initial_add_upwardJump
    (t : MoveTrace p length) {m : ℕ} (hm : m ≤ length) :
    downwardJump t m ≤ (t.state 0).dimension + upwardJump t m := by
  have hbalance := dimension_balance t hm
  omega

/-- The number of dimension-changing moves is controlled by the total
upward jump. -/
theorem changingMoveCount_le (t : MoveTrace p length) {m : ℕ}
    (hm : m ≤ length) :
    kindCount t .up m + kindCount t .down m ≤
      (t.state 0).dimension + 2 * upwardJump t m := by
  have hup := upCount_le_upwardJump t hm
  have hdown := downCount_le_downwardJump t hm
  have hfall := downwardJump_le_initial_add_upwardJump t hm
  omega

/-- A version of `changingMoveCount_le` using any externally established
upper bound for the total upward jump. -/
theorem changingMoveCount_le_of_upwardJump_le
    (t : MoveTrace p length) {m jumpBound : ℕ} (hm : m ≤ length)
    (hjump : upwardJump t m ≤ jumpBound) :
    kindCount t .up m + kindCount t .down m ≤
      (t.state 0).dimension + 2 * jumpBound := by
  exact (changingMoveCount_le t hm).trans (by omega)

/-- Iterating the retained-population inequality. -/
theorem retention_pow_mul_le_population (t : MoveTrace p length) {m : ℕ}
    (hm : m ≤ length) :
    p.retention ^ m * (t.state 0).population ≤ (t.state m).population := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm' : m ≤ length := by omega
      have hret := t.population_retained m (show m < length by omega)
      specialize ih hm'
      rw [pow_succ]
      calc
        p.retention ^ m * p.retention * (t.state 0).population =
            p.retention * (p.retention ^ m * (t.state 0).population) := by ring
        _ ≤ p.retention * (t.state m).population :=
          mul_le_mul_of_nonneg_left ih p.retention_nonneg
        _ ≤ (t.state (m + 1)).population := hret

/-- Consequently, crossing below a population threshold consumes the
corresponding multiplicative retention budget. -/
theorem retention_budget_of_population_lt (t : MoveTrace p length)
    {m : ℕ} (hm : m ≤ length) {threshold : ℝ}
    (hsmall : (t.state m).population < threshold) :
    p.retention ^ m * (t.state 0).population < threshold :=
  (retention_pow_mul_le_population t hm).trans_lt hsmall

/-- Exact algebraic factorization of the product of the one-step GAP
multipliers. -/
theorem multiplierProduct_factorization (t : MoveTrace p length) (m : ℕ) :
    multiplierProduct t m =
      p.cost ^ (kindCount t .up m + kindCount t .down m) *
        p.shrinkFactor ^ kindCount t .shrink m * upSavingProduct t m := by
  induction m with
  | zero => simp
  | succ m ih =>
      cases hkind : t.kind m <;>
        simp [multiplierProduct, upSavingProduct, kindCount,
          stepMultiplier, hkind, ih, pow_succ] <;> ring

/-- Every prefix product of up-saving factors is nonnegative. -/
theorem upSavingProduct_nonneg (t : MoveTrace p length) {m : ℕ}
    (hm : m ≤ length) : 0 ≤ upSavingProduct t m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm' : m ≤ length := by omega
      specialize ih hm'
      by_cases hkind : t.kind m = .up
      · simp [upSavingProduct, hkind,
          mul_nonneg ih (t.upSaving_nonneg m (by omega))]
      · simpa [upSavingProduct, hkind] using ih

/-- The product of all up savings is bounded just by the total upward
dimension jump. -/
theorem upSavingProduct_le_pow_upwardJump (t : MoveTrace p length) {m : ℕ}
    (hm : m ≤ length) :
    upSavingProduct t m ≤ p.upBase ^ upwardJump t m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm' : m ≤ length := by omega
      specialize ih hm'
      have hmi : m < length := by omega
      cases hkind : t.kind m with
      | up =>
          have hsave := t.upSaving_control m hmi (by simpa using hkind)
          have hold := upSavingProduct_nonneg t hm'
          have hnew := t.upSaving_nonneg m hmi
          have hpow : 0 ≤ p.upBase ^
              ((t.state (m + 1)).dimension - (t.state m).dimension) :=
            pow_nonneg p.upBase_nonneg _
          have hpow_old : 0 ≤ p.upBase ^ upwardJump t m :=
            pow_nonneg p.upBase_nonneg _
          simp only [upSavingProduct, upwardJump,
            hkind, ↓reduceIte]
          rw [pow_add]
          exact mul_le_mul ih hsave hnew hpow_old
      | down =>
          simp [upSavingProduct, upwardJump, hkind] at ih ⊢
          exact ih
      | shrink =>
          simp [upSavingProduct, upwardJump, hkind] at ih ⊢
          exact ih

/-- The product estimate obtained by iterating the one-step GAP bounds. -/
theorem gapSize_le_multiplierProduct (t : MoveTrace p length) {m : ℕ}
    (hm : m ≤ length) :
    (t.state m).gapSize ≤
      multiplierProduct t m * (t.state 0).gapSize := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm' : m ≤ length := by omega
      have hstep := t.gap_control m (show m < length by omega)
      specialize ih hm'
      have hfactor_nonneg :
          0 ≤ stepMultiplier p (t.kind m) (t.upSaving m) := by
        cases hkind : t.kind m
        · simp [stepMultiplier, hkind, mul_nonneg p.cost_nonneg
              (t.upSaving_nonneg m (by omega))]
        · simpa [stepMultiplier, hkind] using p.cost_nonneg
        · simpa [stepMultiplier, hkind] using p.shrinkFactor_nonneg
      calc
        (t.state (m + 1)).gapSize ≤
            stepMultiplier p (t.kind m) (t.upSaving m) *
              (t.state m).gapSize := hstep
        _ ≤ stepMultiplier p (t.kind m) (t.upSaving m) *
              (multiplierProduct t m * (t.state 0).gapSize) :=
          mul_le_mul_of_nonneg_left ih hfactor_nonneg
        _ = multiplierProduct t (m + 1) * (t.state 0).gapSize := by
          simp [multiplierProduct]
          ring

/-- The Pham--Zakharov product estimate in collected form. -/
theorem gapSize_le_collected_product (t : MoveTrace p length) {m : ℕ}
    (hm : m ≤ length) :
    (t.state m).gapSize ≤
      p.cost ^ (kindCount t .up m + kindCount t .down m) *
        p.shrinkFactor ^ kindCount t .shrink m * upSavingProduct t m *
          (t.state 0).gapSize := by
  rw [← multiplierProduct_factorization t m]
  exact gapSize_le_multiplierProduct t hm

/-- Uniform form of the product estimate, replacing all individual up
savings by `upBase ^ (total upward jump)`. -/
theorem gapSize_le_uniform_product (t : MoveTrace p length) {m : ℕ}
    (hm : m ≤ length) :
    (t.state m).gapSize ≤
      p.cost ^ (kindCount t .up m + kindCount t .down m) *
        p.shrinkFactor ^ kindCount t .shrink m *
          p.upBase ^ upwardJump t m * (t.state 0).gapSize := by
  have hcollected := gapSize_le_collected_product t hm
  have hsave := upSavingProduct_le_pow_upwardJump t hm
  have hcoeff : 0 ≤
      p.cost ^ (kindCount t .up m + kindCount t .down m) *
        p.shrinkFactor ^ kindCount t .shrink m :=
    mul_nonneg (pow_nonneg p.cost_nonneg _)
      (pow_nonneg p.shrinkFactor_nonneg _)
  have hgap : 0 ≤ (t.state 0).gapSize :=
    (t.state 0).one_le_gapSize.trans' (by norm_num)
  calc
    (t.state m).gapSize ≤
        (p.cost ^ (kindCount t .up m + kindCount t .down m) *
          p.shrinkFactor ^ kindCount t .shrink m) *
            upSavingProduct t m * (t.state 0).gapSize := by
      simpa [mul_assoc] using hcollected
    _ ≤ (p.cost ^ (kindCount t .up m + kindCount t .down m) *
          p.shrinkFactor ^ kindCount t .shrink m) *
            p.upBase ^ upwardJump t m * (t.state 0).gapSize :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsave hcoeff) hgap

/-- No prefix can have a uniform GAP upper bound strictly below one. -/
theorem one_le_uniform_product (t : MoveTrace p length) {m : ℕ}
    (hm : m ≤ length) :
    1 ≤ p.cost ^ (kindCount t .up m + kindCount t .down m) *
        p.shrinkFactor ^ kindCount t .shrink m *
          p.upBase ^ upwardJump t m * (t.state 0).gapSize := by
  exact (t.state m).one_le_gapSize.trans (gapSize_le_uniform_product t hm)

/-- If at most `changeBound` moves change dimension, the trace cannot
contain more than `shrinkBound` shrink moves once that many shrink factors
would force the GAP size below one. -/
theorem shrinkCount_le_of_budget (t : MoveTrace p length)
    {changeBound shrinkBound : ℕ}
    (hchange : kindCount t .up length + kindCount t .down length ≤ changeBound)
    (hbudget :
      p.cost ^ changeBound * p.shrinkFactor ^ (shrinkBound + 1) *
        (t.state 0).gapSize < 1) :
    kindCount t .shrink length ≤ shrinkBound := by
  by_contra hnot
  have hshrink : shrinkBound + 1 ≤ kindCount t .shrink length := by omega
  have hcost :
      p.cost ^ (kindCount t .up length + kindCount t .down length) ≤
        p.cost ^ changeBound := by
    exact pow_le_pow_right₀ p.one_le_cost hchange
  have hgamma :
      p.shrinkFactor ^ kindCount t .shrink length ≤
        p.shrinkFactor ^ (shrinkBound + 1) := by
    exact pow_le_pow_of_le_one p.shrinkFactor_nonneg p.shrinkFactor_le_one hshrink
  have hup : p.upBase ^ upwardJump t length ≤ 1 := by
    exact pow_le_one₀ p.upBase_nonneg p.upBase_le_one
  have hgap0 : 0 ≤ (t.state 0).gapSize := by
    linarith [(t.state 0).one_le_gapSize]
  have hgamma_nonneg : 0 ≤ p.shrinkFactor ^ kindCount t .shrink length :=
    pow_nonneg p.shrinkFactor_nonneg _
  have hcost_nonneg :
      0 ≤ p.cost ^ (kindCount t .up length + kindCount t .down length) :=
    pow_nonneg p.cost_nonneg _
  have hcost_bound_nonneg : 0 ≤ p.cost ^ changeBound :=
    pow_nonneg p.cost_nonneg _
  have hgamma_bound_nonneg :
      0 ≤ p.shrinkFactor ^ (shrinkBound + 1) :=
    pow_nonneg p.shrinkFactor_nonneg _
  have hbound :
      p.cost ^ (kindCount t .up length + kindCount t .down length) *
          p.shrinkFactor ^ kindCount t .shrink length *
            p.upBase ^ upwardJump t length * (t.state 0).gapSize ≤
        p.cost ^ changeBound * p.shrinkFactor ^ (shrinkBound + 1) *
          (t.state 0).gapSize := by
    calc
      p.cost ^ (kindCount t .up length + kindCount t .down length) *
            p.shrinkFactor ^ kindCount t .shrink length *
              p.upBase ^ upwardJump t length * (t.state 0).gapSize
          ≤ p.cost ^ (kindCount t .up length + kindCount t .down length) *
            p.shrinkFactor ^ kindCount t .shrink length * 1 *
              (t.state 0).gapSize := by
            gcongr
      _ ≤ p.cost ^ changeBound *
            p.shrinkFactor ^ (shrinkBound + 1) * 1 *
              (t.state 0).gapSize := by
            gcongr
      _ = p.cost ^ changeBound * p.shrinkFactor ^ (shrinkBound + 1) *
            (t.state 0).gapSize := by ring
  have hone := one_le_uniform_product t (show length ≤ length by rfl)
  linarith

/-- Explicit finite termination bound.  A trace whose dimension-changing
moves are bounded by `changeBound` and whose shrink budget is exhausted
has length at most `changeBound + shrinkBound`. -/
theorem length_le_of_budgets (t : MoveTrace p length)
    {changeBound shrinkBound : ℕ}
    (hchange : kindCount t .up length + kindCount t .down length ≤ changeBound)
    (hbudget :
      p.cost ^ changeBound * p.shrinkFactor ^ (shrinkBound + 1) *
        (t.state 0).gapSize < 1) :
    length ≤ changeBound + shrinkBound := by
  have hshrink := shrinkCount_le_of_budget t hchange hbudget
  rw [length_eq_sum_kindCount t length]
  omega

/-- The preceding stopping bound with the dimension-changing estimate
discharged from a bound on total upward jump. -/
theorem length_le_of_upwardJump_and_budget (t : MoveTrace p length)
    {jumpBound shrinkBound : ℕ}
    (hjump : upwardJump t length ≤ jumpBound)
    (hbudget :
      p.cost ^ ((t.state 0).dimension + 2 * jumpBound) *
          p.shrinkFactor ^ (shrinkBound + 1) * (t.state 0).gapSize < 1) :
    length ≤ (t.state 0).dimension + 2 * jumpBound + shrinkBound := by
  apply length_le_of_budgets t
  · exact changingMoveCount_le_of_upwardJump_le t (le_refl length) hjump
  · exact hbudget

end Irreducible
end Erdos186
