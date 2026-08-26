import ErdosProblems.Erdos520.CaichConcentration
import ErdosProblems.Erdos520.IntegerThinSchedule
import ErdosProblems.Erdos520.SmoothScheduleBudget
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Complex.ExponentialBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos
namespace Problem520

/-!
# Aligned integer macro scales and thin blocks

The first exact schedule in `IntegerThinSchedule` gives excellent geometry
inside one scale, but it is not aligned across consecutive outer scales:
its new initial endpoint is larger than the preceding final endpoint.  That
also prevents it from supplying the large `log x / log y₀` saving needed for
the smooth contribution.

This file gives a gap-free replacement.  Put

`X_ell = 2 ^ (2 ^ (ell ^ K))`.

At outer scale `ell` the thin schedule starts at `X_(ell-2)`, below every
test point in `(X_(ell-1), X_ell]`.  Its logarithmic exponents are generated
by the exact natural recurrence

`E_(j+1) = E_j + ceil(E_j / ell)`.

There are `ell^(K+1)` blocks.  Every `ell` steps at least double the
exponent, so the last endpoint reaches `X_ell`; on the other hand a single
step has `log log` width at most `2 / ell`.  Thus the block-count degree is
`K+1`, while the entropy of the usual root-exponential test mesh still has
degree `K`.
-/

/-- Exponent of `2` in the logarithm of the outer endpoint. -/
def alignedOuterExponent (K ell : ℕ) : ℕ := 2 ^ (ell ^ K)

/-- Exact double-exponential outer endpoint. -/
def alignedOuterEndpoint (K ell : ℕ) : ℕ :=
  2 ^ alignedOuterExponent K ell

/-- Number of thin blocks used at outer scale `ell`. -/
def alignedThinBlockCount (K ell : ℕ) : ℕ := ell ^ (K + 1)

/-- One exact multiplicative step, with upward rounding. -/
def ceilThinStep (ell E : ℕ) : ℕ := E + E ⌈/⌉ ell

/-- Iteration of the exact thin step. -/
def ceilThinGrow (ell E : ℕ) : ℕ → ℕ
  | 0 => E
  | j + 1 => ceilThinStep ell (ceilThinGrow ell E j)

/-- The aligned schedule starts two outer scales below the current one. -/
def alignedThinExponent (K ell j : ℕ) : ℕ :=
  ceilThinGrow ell (alignedOuterExponent K (ell - 2)) j

/-- Exact natural thin-block endpoint. -/
def alignedThinEndpoint (K ell j : ℕ) : ℕ :=
  2 ^ alignedThinExponent K ell j

@[simp] theorem ceilThinGrow_zero (ell E : ℕ) :
    ceilThinGrow ell E 0 = E := rfl

@[simp] theorem ceilThinGrow_succ (ell E j : ℕ) :
    ceilThinGrow ell E (j + 1) =
      ceilThinStep ell (ceilThinGrow ell E j) := rfl

theorem ceilThinGrow_seed_le (ell E j : ℕ) :
    E ≤ ceilThinGrow ell E j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      exact ih.trans (Nat.le_add_right _ _)

theorem ceilThinGrow_pos {ell E j : ℕ} (hE : 0 < E) :
    0 < ceilThinGrow ell E j :=
  hE.trans_le (ceilThinGrow_seed_le ell E j)

private theorem ceilDiv_mono_left {ell E F : ℕ} (hell : 0 < ell)
    (hEF : E ≤ F) : E ⌈/⌉ ell ≤ F ⌈/⌉ ell := by
  exact (gc_mul_ceilDiv hell).monotone_l hEF

theorem ceilThinGrow_mono_seed (ell j : ℕ) :
    Monotone fun E => ceilThinGrow ell E j := by
  intro E F hEF
  induction j with
  | zero => exact hEF
  | succ j ih =>
      simp only [ceilThinGrow_succ, ceilThinStep]
      by_cases hell : ell = 0
      · subst ell
        simpa using! ih
      · exact Nat.add_le_add ih
          (ceilDiv_mono_left (Nat.pos_of_ne_zero hell) ih)

theorem ceilThinGrow_mono_index (ell E : ℕ) :
    Monotone fun j => ceilThinGrow ell E j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => rfl
  | @succ j hij ih =>
      exact ih.trans (Nat.le_add_right _ _)

theorem alignedThinExponent_mono (K ell : ℕ) :
    Monotone (alignedThinExponent K ell) :=
  ceilThinGrow_mono_index _ _

theorem alignedThinEndpoint_mono (K ell : ℕ) :
    Monotone (alignedThinEndpoint K ell) := by
  intro i j hij
  exact Nat.pow_le_pow_right (by norm_num)
    (alignedThinExponent_mono K ell hij)

theorem ceilDiv_le_div_add_one {E ell : ℕ} (hell : 0 < ell) :
    E ⌈/⌉ ell ≤ E / ell + 1 := by
  rw [ceilDiv_le_iff_le_mul hell]
  have hmod := Nat.mod_lt E hell
  calc
    E = ell * (E / ell) + E % ell := (Nat.div_add_mod E ell).symm
    _ ≤ ell * (E / ell) + ell := by omega
    _ = ell * (E / ell + 1) := by ring

/-- If the current exponent is at least the scale, one rounded step is at
most a relative `2 / ell` increase. -/
theorem cast_ceilDiv_le_two_mul_div {E ell : ℕ}
    (hell : 0 < ell) (hle : ell ≤ E) :
    ((E ⌈/⌉ ell : ℕ) : ℝ) ≤ 2 * (E : ℝ) / (ell : ℝ) := by
  have h₁ : ((E ⌈/⌉ ell : ℕ) : ℝ) ≤ ((E / ell + 1 : ℕ) : ℝ) := by
    exact_mod_cast ceilDiv_le_div_add_one hell
  have h₂ : (((E / ell + 1 : ℕ) : ℝ)) ≤ (E : ℝ) / (ell : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
    linarith [Nat.cast_div_le (α := ℝ) (m := E) (n := ell)]
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hratio : (1 : ℝ) ≤ (E : ℝ) / (ell : ℝ) := by
    rw [le_div_iff₀ hellR]
    simpa using! (show (ell : ℝ) ≤ E by exact_mod_cast hle)
  calc
    ((E ⌈/⌉ ell : ℕ) : ℝ) ≤ ((E / ell + 1 : ℕ) : ℝ) := h₁
    _ ≤ (E : ℝ) / (ell : ℝ) + 1 := h₂
    _ ≤ 2 * (E : ℝ) / (ell : ℝ) := by
      rw [show 2 * (E : ℝ) / (ell : ℝ) =
        2 * ((E : ℝ) / (ell : ℝ)) by ring]
      linarith

/-- One step has relative size at most `1 + 2/ell`. -/
theorem cast_ceilThinStep_div_le {E ell : ℕ}
    (hell : 0 < ell) (hE : 0 < E) (hle : ell ≤ E) :
    (ceilThinStep ell E : ℝ) / (E : ℝ) ≤
      1 + 2 / (ell : ℝ) := by
  have hER : (0 : ℝ) < E := by exact_mod_cast hE
  have hinc := cast_ceilDiv_le_two_mul_div hell hle
  unfold ceilThinStep
  apply (div_le_iff₀ hER).2
  calc
    ((E + E ⌈/⌉ ell : ℕ) : ℝ) =
        (E : ℝ) + (E ⌈/⌉ ell : ℕ) := by norm_cast
    _ ≤ (E : ℝ) + 2 * (E : ℝ) / (ell : ℝ) := by linarith
    _ = (1 + 2 / (ell : ℝ)) * (E : ℝ) := by ring

private theorem add_two_le_two_pow {n : ℕ} (hn : 2 ≤ n) :
    n + 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | @succ n hn ih =>
      rw [pow_succ]
      omega

private theorem three_mul_add_two_le_two_mul_two_pow {n : ℕ}
    (hn : 3 ≤ n) : 3 * (n + 2) ≤ 2 * 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | @succ n hn ih =>
      rw [pow_succ]
      omega

/-- The initial exponent is already at least the current scale. -/
theorem scale_le_alignedInitialExponent {K ell : ℕ}
    (hK : 1 ≤ K) (hell : 4 ≤ ell) :
    ell ≤ alignedOuterExponent K (ell - 2) := by
  have hbase : 2 ≤ ell - 2 := by omega
  have hpow : ell - 2 ≤ (ell - 2) ^ K := by
    exact le_self_pow₀ (by omega) (by omega : K ≠ 0)
  calc
    ell = (ell - 2) + 2 := by omega
    _ ≤ 2 ^ (ell - 2) := add_two_le_two_pow hbase
    _ ≤ 2 ^ ((ell - 2) ^ K) :=
      Nat.pow_le_pow_right (by norm_num) hpow
    _ = alignedOuterExponent K (ell - 2) := rfl

/-- A slightly stronger lower bound used to absorb the Chebyshev endpoint
error uniformly. -/
theorem three_mul_scale_le_two_mul_alignedInitialExponent {K ell : ℕ}
    (hK : 1 ≤ K) (hell : 5 ≤ ell) :
    3 * ell ≤ 2 * alignedOuterExponent K (ell - 2) := by
  have hbase : 3 ≤ ell - 2 := by omega
  have hpow : ell - 2 ≤ (ell - 2) ^ K := by
    exact le_self_pow₀ (by omega) (by omega : K ≠ 0)
  calc
    3 * ell = 3 * ((ell - 2) + 2) := by omega
    _ ≤ 2 * 2 ^ (ell - 2) :=
      three_mul_add_two_le_two_mul_two_pow hbase
    _ ≤ 2 * 2 ^ ((ell - 2) ^ K) :=
      Nat.mul_le_mul_left 2
        (Nat.pow_le_pow_right (by norm_num) hpow)
    _ = 2 * alignedOuterExponent K (ell - 2) := rfl

theorem log_alignedThinEndpoint (K ell j : ℕ) :
    Real.log (alignedThinEndpoint K ell j : ℝ) =
      (alignedThinExponent K ell j : ℝ) * Real.log 2 := by
  unfold alignedThinEndpoint
  rw [show ((2 ^ alignedThinExponent K ell j : ℕ) : ℝ) =
      (2 : ℝ) ^ alignedThinExponent K ell j by norm_cast,
    Real.log_pow]

theorem alignedThinExponent_pos (K ell j : ℕ) :
    0 < alignedThinExponent K ell j := by
  apply ceilThinGrow_pos
  unfold alignedOuterExponent
  positivity

theorem two_le_alignedThinEndpoint (K ell j : ℕ) :
    2 ≤ alignedThinEndpoint K ell j := by
  change 2 ^ 1 ≤ 2 ^ alignedThinExponent K ell j
  exact Nat.pow_le_pow_right (by norm_num)
    (alignedThinExponent_pos K ell j)

/-- Exact `log log` width of one rounded thin step. -/
theorem alignedThinEndpoint_logLog_width {K ell j : ℕ}
    (hK : 1 ≤ K) (hell : 4 ≤ ell) :
    logLogNat (alignedThinEndpoint K ell (j + 1)) -
        logLogNat (alignedThinEndpoint K ell j) ≤
      2 / (ell : ℝ) := by
  let E := alignedThinExponent K ell j
  have hEpos : 0 < E := alignedThinExponent_pos K ell j
  have hseed : ell ≤ alignedOuterExponent K (ell - 2) :=
    scale_le_alignedInitialExponent hK hell
  have hElarge : ell ≤ E :=
    hseed.trans (ceilThinGrow_seed_le ell
      (alignedOuterExponent K (ell - 2)) j)
  have hratio := cast_ceilThinStep_div_le
    (show 0 < ell by omega) hEpos hElarge
  have hnext : alignedThinExponent K ell (j + 1) =
      ceilThinStep ell E := rfl
  have hnextpos : 0 < ceilThinStep ell E :=
    hEpos.trans_le (Nat.le_add_right _ _)
  rw [alignedThinEndpoint, alignedThinEndpoint,
    logLogNat_two_pow_eq (by simpa [hnext] using! hnextpos),
    logLogNat_two_pow_eq hEpos]
  rw [hnext]
  rw [show Real.log (ceilThinStep ell E : ℝ) + Real.log (Real.log 2) -
      (Real.log (E : ℝ) + Real.log (Real.log 2)) =
      Real.log (ceilThinStep ell E : ℝ) - Real.log (E : ℝ) by ring]
  rw [← Real.log_div
    (by positivity : ((ceilThinStep ell E : ℕ) : ℝ) ≠ 0)
    (by positivity : (E : ℝ) ≠ 0)]
  have hratioPos : (0 : ℝ) <
      (ceilThinStep ell E : ℝ) / (E : ℝ) := by positivity
  calc
    Real.log ((ceilThinStep ell E : ℝ) / (E : ℝ)) ≤
        (ceilThinStep ell E : ℝ) / (E : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hratioPos
    _ ≤ (1 + 2 / (ell : ℝ)) - 1 := sub_le_sub_right hratio 1
    _ = 2 / (ell : ℝ) := by ring

/-! ## The schedule reaches the current macro endpoint -/

theorem ceilThinGrow_linear_lower {ell E t : ℕ} (hell : 0 < ell) :
    E + t * (E ⌈/⌉ ell) ≤ ceilThinGrow ell E t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hseed : E ≤ ceilThinGrow ell E t :=
        ceilThinGrow_seed_le ell E t
      have hceil : E ⌈/⌉ ell ≤
          ceilThinGrow ell E t ⌈/⌉ ell :=
        ceilDiv_mono_left hell hseed
      simp only [ceilThinGrow_succ, ceilThinStep]
      calc
        E + (t + 1) * (E ⌈/⌉ ell) =
            (E + t * (E ⌈/⌉ ell)) + (E ⌈/⌉ ell) := by ring
        _ ≤ ceilThinGrow ell E t +
              (ceilThinGrow ell E t ⌈/⌉ ell) :=
          Nat.add_le_add ih hceil

/-- During any `ell` successive steps the exponent at least doubles. -/
theorem two_mul_le_ceilThinGrow_scale {ell E : ℕ} (hell : 0 < ell) :
    2 * E ≤ ceilThinGrow ell E ell := by
  have hround : E ≤ ell * (E ⌈/⌉ ell) := by
    simpa [nsmul_eq_mul] using!
      (le_smul_ceilDiv (a := ell) (b := E) hell)
  calc
    2 * E = E + E := by ring
    _ ≤ E + ell * (E ⌈/⌉ ell) := Nat.add_le_add_left hround E
    _ ≤ ceilThinGrow ell E ell := ceilThinGrow_linear_lower hell

theorem ceilThinGrow_add (ell E a b : ℕ) :
    ceilThinGrow ell E (a + b) =
      ceilThinGrow ell (ceilThinGrow ell E a) b := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Nat.add_succ, ceilThinGrow_succ, ih, ceilThinGrow_succ]

/-- Repeating the preceding doubling estimate `d` times. -/
theorem pow_two_mul_le_ceilThinGrow_mul
    {ell E d : ℕ} (hell : 0 < ell) :
    2 ^ d * E ≤ ceilThinGrow ell E (d * ell) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hdbl := two_mul_le_ceilThinGrow_scale
        (ell := ell) (E := ceilThinGrow ell E (d * ell)) hell
      calc
        2 ^ (d + 1) * E = 2 * (2 ^ d * E) := by
          rw [pow_succ]
          ring
        _ ≤ 2 * ceilThinGrow ell E (d * ell) :=
          Nat.mul_le_mul_left 2 ih
        _ ≤ ceilThinGrow ell (ceilThinGrow ell E (d * ell)) ell := hdbl
        _ = ceilThinGrow ell E (d * ell + ell) :=
          (ceilThinGrow_add ell E (d * ell) ell).symm
        _ = ceilThinGrow ell E ((d + 1) * ell) := by
          congr 1
          ring

/-- The final thin endpoint covers the whole current outer block. -/
theorem alignedOuterExponent_le_finalThinExponent
    {K ell : ℕ} (hell : 0 < ell) :
    alignedOuterExponent K ell ≤
      alignedThinExponent K ell (alignedThinBlockCount K ell) := by
  have hgrow := pow_two_mul_le_ceilThinGrow_mul
    (ell := ell) (E := alignedOuterExponent K (ell - 2))
    (d := ell ^ K) hell
  have hE : 1 ≤ alignedOuterExponent K (ell - 2) := by
    unfold alignedOuterExponent
    exact one_le_pow₀ (by norm_num)
  have hmul : 2 ^ (ell ^ K) ≤
      2 ^ (ell ^ K) * alignedOuterExponent K (ell - 2) := by
    simpa only [mul_one] using! Nat.mul_le_mul_left (2 ^ (ell ^ K)) hE
  unfold alignedThinExponent alignedThinBlockCount alignedOuterExponent
  rw [pow_succ]
  exact hmul.trans hgrow

theorem alignedOuterEndpoint_le_finalThinEndpoint
    {K ell : ℕ} (hell : 0 < ell) :
    alignedOuterEndpoint K ell ≤
      alignedThinEndpoint K ell (alignedThinBlockCount K ell) := by
  exact Nat.pow_le_pow_right (by norm_num)
    (alignedOuterExponent_le_finalThinExponent hell)

@[simp] theorem alignedThinExponent_zero (K ell : ℕ) :
    alignedThinExponent K ell 0 = alignedOuterExponent K (ell - 2) := rfl

@[simp] theorem alignedThinEndpoint_zero (K ell : ℕ) :
    alignedThinEndpoint K ell 0 = alignedOuterEndpoint K (ell - 2) := rfl

theorem alignedOuterExponent_mono (K : ℕ) :
    Monotone (alignedOuterExponent K) := by
  intro i j hij
  exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left hij K)

theorem alignedOuterEndpoint_mono (K : ℕ) :
    Monotone (alignedOuterEndpoint K) := by
  intro i j hij
  exact Nat.pow_le_pow_right (by norm_num) (alignedOuterExponent_mono K hij)

/-- The initial thin cutoff is below the lower endpoint of the current test
block. -/
theorem alignedThinInitial_le_previousOuter (K ell : ℕ) :
    alignedThinEndpoint K ell 0 ≤ alignedOuterEndpoint K (ell - 1) := by
  rw [alignedThinEndpoint_zero]
  exact alignedOuterEndpoint_mono K (by omega)

theorem alignedThinInitial_lt_of_mem_outerBlock
    {K ell x : ℕ} (hx : alignedOuterEndpoint K (ell - 1) < x) :
    alignedThinEndpoint K ell 0 < x :=
  (alignedThinInitial_le_previousOuter K ell).trans_lt hx

/-- Exact polynomial block-count identity, in the form consumed by the
finite thin-block union. -/
theorem alignedThinBlockCount_cast_le (K ell : ℕ) :
    (alignedThinBlockCount K ell : ℝ) ≤
      1 * (ell : ℝ) ^ (K + 1 : ℕ) := by
  simp [alignedThinBlockCount]

/-! ## Exact logarithmic size of the macro blocks -/

theorem alignedOuterExponent_pos (K ell : ℕ) :
    0 < alignedOuterExponent K ell := by
  unfold alignedOuterExponent
  positivity

theorem logLog_alignedOuterEndpoint (K ell : ℕ) :
    logLogNat (alignedOuterEndpoint K ell) =
      (ell : ℝ) ^ K * Real.log 2 + Real.log (Real.log 2) := by
  unfold alignedOuterEndpoint
  rw [logLogNat_two_pow_eq (alignedOuterExponent_pos K ell)]
  unfold alignedOuterExponent
  rw [show ((2 ^ ell ^ K : ℕ) : ℝ) = (2 : ℝ) ^ (ell ^ K) by norm_cast,
    Real.log_pow]
  norm_cast

/-! ## Uniform damping and reciprocal-prime geometry -/

/-- Summing the exact one-step widths from the initial cutoff. -/
theorem alignedThinEndpoint_logLog_diff_zero_le
    {K ell j : ℕ} (hK : 1 ≤ K) (hell : 4 ≤ ell) :
    logLogNat (alignedThinEndpoint K ell j) -
        logLogNat (alignedThinEndpoint K ell 0) ≤
      (j : ℝ) * (2 / (ell : ℝ)) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep := alignedThinEndpoint_logLog_width
        (K := K) (ell := ell) (j := j) hK hell
      calc
        logLogNat (alignedThinEndpoint K ell (j + 1)) -
            logLogNat (alignedThinEndpoint K ell 0) =
          (logLogNat (alignedThinEndpoint K ell (j + 1)) -
              logLogNat (alignedThinEndpoint K ell j)) +
            (logLogNat (alignedThinEndpoint K ell j) -
              logLogNat (alignedThinEndpoint K ell 0)) := by ring
        _ ≤ 2 / (ell : ℝ) + (j : ℝ) * (2 / (ell : ℝ)) :=
          add_le_add hstep ih
        _ = ((j + 1 : ℕ) : ℝ) * (2 / (ell : ℝ)) := by
          norm_num
          ring

/-- Throughout the valid block range, recovery of Caich's damping costs an
exponent of at most `2`. -/
theorem alignedThinEndpoint_dampingExponent_le_two
    {K ell j : ℕ} (hK : 1 ≤ K) (hell : 4 ≤ ell)
    (hj : j ≤ alignedThinBlockCount K ell) :
    Real.log
          (Real.log (alignedThinEndpoint K ell j : ℝ) /
            Real.log (alignedThinEndpoint K ell 0 : ℝ)) /
        ((ell : ℝ) ^ K) ≤ 2 := by
  have hdiff := alignedThinEndpoint_logLog_diff_zero_le
    (K := K) (ell := ell) (j := j) hK hell
  have hjR : (j : ℝ) ≤ (alignedThinBlockCount K ell : ℝ) := by
    exact_mod_cast hj
  have hdenom : (0 : ℝ) < (ell : ℝ) ^ K := by positivity
  have hlogj : 0 < Real.log (alignedThinEndpoint K ell j : ℝ) := by
    apply Real.log_pos
    exact_mod_cast lt_of_lt_of_le Nat.one_lt_two
      (two_le_alignedThinEndpoint K ell j)
  have hlog0 : 0 < Real.log (alignedThinEndpoint K ell 0 : ℝ) := by
    apply Real.log_pos
    exact_mod_cast lt_of_lt_of_le Nat.one_lt_two
      (two_le_alignedThinEndpoint K ell 0)
  have hrewrite :
      Real.log
          (Real.log (alignedThinEndpoint K ell j : ℝ) /
            Real.log (alignedThinEndpoint K ell 0 : ℝ)) =
        logLogNat (alignedThinEndpoint K ell j) -
          logLogNat (alignedThinEndpoint K ell 0) := by
    unfold logLogNat
    exact Real.log_div hlogj.ne' hlog0.ne'
  rw [hrewrite]
  apply (div_le_iff₀ hdenom).2
  calc
    logLogNat (alignedThinEndpoint K ell j) -
        logLogNat (alignedThinEndpoint K ell 0) ≤
      (j : ℝ) * (2 / (ell : ℝ)) := hdiff
    _ ≤ (alignedThinBlockCount K ell : ℝ) *
        (2 / (ell : ℝ)) := by gcongr
    _ = ((ell : ℝ) ^ (K + 1)) * (2 / (ell : ℝ)) := by
      rw [alignedThinBlockCount]
      norm_cast
    _ = 2 * (ell : ℝ) ^ K := by
      rw [pow_succ]
      field_simp

/-- A numerical damping bound in exactly the form required by
`smoothEnergy_div_log_le_caichNormalizedEnergy`, with `Cparseval = 2`. -/
theorem alignedThinEndpoint_caichDamping_le_four_pi
    {K ell j : ℕ} (hK : 1 ≤ K) (hell : 4 ≤ ell)
    (hj : j ≤ alignedThinBlockCount K ell) :
    Real.exp
        (Real.log
            (Real.log (alignedThinEndpoint K ell j : ℝ) /
              Real.log (alignedThinEndpoint K ell 0 : ℝ)) /
          ((ell : ℝ) ^ K)) ≤
      (2 * Real.pi) * 2 := by
  have hexponent := alignedThinEndpoint_dampingExponent_le_two
    hK hell hj
  calc
    Real.exp
        (Real.log
            (Real.log (alignedThinEndpoint K ell j : ℝ) /
              Real.log (alignedThinEndpoint K ell 0 : ℝ)) /
          ((ell : ℝ) ^ K)) ≤ Real.exp 2 :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    _ ≤ 3 * 3 := mul_le_mul Real.exp_one_lt_three.le
      Real.exp_one_lt_three.le (Real.exp_pos _).le (by norm_num)
    _ ≤ (2 * Real.pi) * 2 := by nlinarith [Real.pi_gt_three]

/-- Every lower endpoint is large enough to absorb the endpoint term in the
Chebyshev reciprocal-prime estimate. -/
theorem scale_le_log_alignedThinEndpoint
    {K ell j : ℕ} (hK : 1 ≤ K) (hell : 5 ≤ ell) :
    (ell : ℝ) ≤ Real.log (alignedThinEndpoint K ell j : ℝ) := by
  let E₀ := alignedOuterExponent K (ell - 2)
  have hthree : 3 * ell ≤ 2 * E₀ := by
    exact three_mul_scale_le_two_mul_alignedInitialExponent hK hell
  have hlogTwo : (2 / 3 : ℝ) < Real.log 2 :=
    (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hE₀pos : (0 : ℝ) < E₀ := by
    exact_mod_cast alignedOuterExponent_pos K (ell - 2)
  have hbase : (ell : ℝ) ≤ (E₀ : ℝ) * Real.log 2 := by
    have hthreeR : (3 : ℝ) * ell ≤ 2 * E₀ := by exact_mod_cast hthree
    nlinarith
  rw [log_alignedThinEndpoint]
  have hmono : E₀ ≤ alignedThinExponent K ell j := by
    exact ceilThinGrow_seed_le ell E₀ j
  have hmonoR : (E₀ : ℝ) ≤ alignedThinExponent K ell j := by
    exact_mod_cast hmono
  exact hbase.trans (mul_le_mul_of_nonneg_right hmonoR
    (Real.log_pos (by norm_num)).le)

theorem scale_le_alignedThinEndpoint
    {K ell j : ℕ} (hK : 1 ≤ K) (hell : 4 ≤ ell) :
    ell ≤ alignedThinEndpoint K ell j := by
  have hseed : ell ≤ alignedOuterExponent K (ell - 2) :=
    scale_le_alignedInitialExponent hK hell
  have hexp : alignedOuterExponent K (ell - 2) ≤
      alignedThinExponent K ell j :=
    ceilThinGrow_seed_le ell (alignedOuterExponent K (ell - 2)) j
  calc
    ell ≤ alignedThinExponent K ell j := hseed.trans hexp
    _ ≤ 2 ^ alignedThinExponent K ell j :=
      Nat.le_of_lt (alignedThinExponent K ell j).lt_two_pow_self
    _ = alignedThinEndpoint K ell j := rfl

/-! ## Initial cutoff versus Harper's logarithmic scale -/

private theorem neg_one_lt_log_log_two_aligned :
    (-1 : ℝ) < Real.log (Real.log 2) := by
  have hexpLog : Real.exp (-1) < Real.log 2 :=
    Real.exp_neg_one_lt_half.trans
      ((by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
        Real.log_two_gt_d9)
  exact (Real.lt_log_iff_exp_lt (Real.log_pos (by norm_num))).mpr hexpLog

/-- Exact initial `log log` identity for the aligned schedule. -/
theorem one_add_logLog_alignedThinInitial (K ell : ℕ) :
    1 + logLogNat (alignedThinEndpoint K ell 0) =
      1 + (ell - 2 : ℕ) ^ K * Real.log 2 + Real.log (Real.log 2) := by
  rw [alignedThinEndpoint_zero, logLog_alignedOuterEndpoint]
  norm_cast
  ring

/-- Although the aligned cutoff starts at `X_(ell-2)`, its logarithmic scale
is still a fixed positive `K`-dependent multiple of `ell^K`. -/
theorem alignedThinInitial_harperScale_lower
    {K ell : ℕ} (hK : 1 ≤ K) (hell : 5 ≤ ell) :
    (1 / (3 * (2 : ℝ) ^ K)) * (ell : ℝ) ^ K ≤
      1 + logLogNat (alignedThinEndpoint K ell 0) := by
  let A : ℕ := (ell - 2) ^ K
  have hhalf : (ell : ℝ) / 2 ≤ (ell - 2 : ℕ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ ell)]
    norm_num
    have hellR : (5 : ℝ) ≤ ell := by exact_mod_cast hell
    linarith
  have hpowHalf : ((ell : ℝ) / 2) ^ K ≤ (A : ℝ) := by
    dsimp [A]
    simpa only [Nat.cast_pow] using!
      (pow_le_pow_left₀ (by positivity) hhalf K)
  have hpowDiv : (ell : ℝ) ^ K / (2 : ℝ) ^ K ≤ (A : ℝ) := by
    simpa only [div_pow] using! hpowHalf
  have hAthree : (3 : ℝ) ≤ A := by
    have hbase : 3 ≤ ell - 2 := by omega
    have hnat : ell - 2 ≤ (ell - 2) ^ K :=
      le_self_pow₀ (by omega) (by omega : K ≠ 0)
    exact_mod_cast hbase.trans hnat
  have hlogTwo : (2 / 3 : ℝ) < Real.log 2 :=
    (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hloglog := neg_one_lt_log_log_two_aligned
  rw [one_add_logLog_alignedThinInitial]
  have hleft :
      (1 / (3 * (2 : ℝ) ^ K)) * (ell : ℝ) ^ K ≤ (A : ℝ) / 3 := by
    have htwoPow : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
    calc
      (1 / (3 * (2 : ℝ) ^ K)) * (ell : ℝ) ^ K =
          ((ell : ℝ) ^ K / (2 : ℝ) ^ K) / 3 := by field_simp
      _ ≤ (A : ℝ) / 3 := div_le_div_of_nonneg_right hpowDiv (by norm_num)
  apply hleft.trans
  rw [← Nat.cast_pow]
  change (A : ℝ) / 3 ≤
    1 + (A : ℝ) * Real.log 2 + Real.log (Real.log 2)
  nlinarith

/-! ## Fixed-shift comparison for the repaired block threshold -/

/-- The scalar level appearing in the maximal block-energy event. -/
noncomputable def alignedCaichBlockLevel (K n : ℕ) : ℝ :=
  Real.sqrt
      ((n : ℝ) ^ 10 / ((n : ℝ) * Real.log (n : ℝ))) /
    (n : ℝ) ^ ((K : ℝ) / 2)

theorem alignedCaichBlockLevel_nonneg (K n : ℕ) :
    0 ≤ alignedCaichBlockLevel K n := by
  unfold alignedCaichBlockLevel
  positivity

/-- For `K ≥ 9`, squaring the block level leaves the elementary decreasing
function `1 / (n^(K-9) log n)`. -/
theorem alignedCaichBlockLevel_sq
    {K n : ℕ} (hK : 9 ≤ K) (hn : 2 ≤ n) :
    alignedCaichBlockLevel K n ^ 2 =
      1 / ((n : ℝ) ^ (K - 9) * Real.log (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hQ : 0 ≤ (n : ℝ) ^ 10 /
      ((n : ℝ) * Real.log (n : ℝ)) := by positivity
  have hrpowSq : ((n : ℝ) ^ ((K : ℝ) / 2)) ^ 2 =
      (n : ℝ) ^ K := by
    calc
      ((n : ℝ) ^ ((K : ℝ) / 2)) ^ 2 =
          ((n : ℝ) ^ ((K : ℝ) / 2)) ^ (2 : ℝ) :=
        (Real.rpow_two _).symm
      _ = (n : ℝ) ^ (((K : ℝ) / 2) * 2) :=
        (Real.rpow_mul hnR.le _ _).symm
      _ = (n : ℝ) ^ (K : ℝ) := by congr 1 <;> ring
      _ = (n : ℝ) ^ K := Real.rpow_natCast _ _
  unfold alignedCaichBlockLevel
  rw [div_pow, Real.sq_sqrt hQ, hrpowSq]
  have hsplit : K = 9 + (K - 9) := by omega
  rw [hsplit]
  simp only [Nat.add_sub_cancel_left]
  rw [pow_add, pow_succ]
  field_simp

/-- The block threshold decreases with the scale once `K ≥ 9`. -/
theorem alignedCaichBlockLevel_antitone
    {K n N : ℕ} (hK : 9 ≤ K) (hn : 2 ≤ n) (hnN : n ≤ N) :
    alignedCaichBlockLevel K N ≤ alignedCaichBlockLevel K n := by
  have hN : 2 ≤ N := hn.trans hnN
  have hnR : (0 : ℝ) < n := by positivity
  have hNR : (0 : ℝ) < N := by positivity
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpow : (n : ℝ) ^ (K - 9) ≤ (N : ℝ) ^ (K - 9) := by
    exact pow_le_pow_left₀ hnR.le (by exact_mod_cast hnN) _
  have hlog : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hnR (by exact_mod_cast hnN)
  have hdenom : (n : ℝ) ^ (K - 9) * Real.log (n : ℝ) ≤
      (N : ℝ) ^ (K - 9) * Real.log (N : ℝ) := by
    exact mul_le_mul hpow hlog (by positivity) (by positivity)
  have hsquare : alignedCaichBlockLevel K N ^ 2 ≤
      alignedCaichBlockLevel K n ^ 2 := by
    rw [alignedCaichBlockLevel_sq hK hN,
      alignedCaichBlockLevel_sq hK hn]
    exact one_div_le_one_div_of_le (by positivity) hdenom
  exact (sq_le_sq₀ (alignedCaichBlockLevel_nonneg K N)
    (alignedCaichBlockLevel_nonneg K n)).mp hsquare

/-- The fixed analytic shift used in the concrete schedule costs no constant
at all at the block-energy level when `K ≥ 9`. -/
theorem alignedCaichBlockLevel_add_le
    {K S ell : ℕ} (hK : 9 ≤ K) (hell : 2 ≤ ell) :
    alignedCaichBlockLevel K (ell + S) ≤
      alignedCaichBlockLevel K ell :=
  alignedCaichBlockLevel_antitone hK hell (Nat.le_add_right ell S)

theorem mul_alignedCaichBlockLevel_add_le
    {K S ell : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hK : 9 ≤ K) (hell : 2 ≤ ell) :
    B * alignedCaichBlockLevel K (ell + S) ≤
      B * alignedCaichBlockLevel K ell :=
  mul_le_mul_of_nonneg_left (alignedCaichBlockLevel_add_le hK hell) hB

/-- A fixed shift turns all finite-scale side conditions into total fields
of `ConcreteThinBlockSchedule`. -/
def alignedScheduleShift (N : ℕ) : ℕ := max 5 N

/-- The shifted concrete schedule suppresses the irrelevant zeroth scale so
that a bound by a positive power of `ell` is literally valid for all `ell`. -/
def shiftedAlignedThinBlockCount (K S ell : ℕ) : ℕ :=
  if ell = 0 then 0 else alignedThinBlockCount K (ell + S)

theorem five_le_alignedScheduleShift (N : ℕ) :
    5 ≤ alignedScheduleShift N := le_max_left _ _

theorem self_le_alignedScheduleShift (N : ℕ) :
    N ≤ alignedScheduleShift N := le_max_right _ _

/-- The shifted block count is still polynomial of degree `K+1`. -/
theorem shifted_alignedThinBlockCount_le
    {K S ell : ℕ} (hell : 1 ≤ ell) :
    ((alignedThinBlockCount K (ell + S) : ℕ) : ℝ) ≤
      (((S + 1) ^ (K + 1) : ℕ) : ℝ) *
        (ell : ℝ) ^ (K + 1 : ℕ) := by
  have hbase : ell + S ≤ (S + 1) * ell := by
    nlinarith [Nat.mul_le_mul_left S hell]
  have hpow := Nat.pow_le_pow_left hbase (K + 1)
  rw [alignedThinBlockCount]
  exact_mod_cast (hpow.trans_eq (mul_pow (S + 1) ell (K + 1)))

theorem shiftedAlignedThinBlockCount_cast_le_all
    (K S ell : ℕ) :
    (shiftedAlignedThinBlockCount K S ell : ℝ) ≤
      (((S + 1) ^ (K + 1) : ℕ) : ℝ) *
        (ell : ℝ) ^ (K + 1 : ℕ) := by
  by_cases hell : ell = 0
  · subst ell
    simp [shiftedAlignedThinBlockCount]
  rw [shiftedAlignedThinBlockCount, if_neg hell]
  exact shifted_alignedThinBlockCount_le (Nat.one_le_iff_ne_zero.mpr hell)

/-! ## Concrete thin-block packaging -/

/-- The aligned schedule supplies a genuine concrete thin-block schedule.
The only parameter restriction is `K ≥ 1`; all analytic constants and the
finite initial shift are chosen unconditionally from Chebyshev's theorem. -/
theorem exists_alignedIntegerConcreteThinBlockSchedule
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ s : ConcreteThinBlockSchedule, ∃ S : ℕ, 5 ≤ S ∧
      s.J = shiftedAlignedThinBlockCount K S ∧
      s.y = (fun ell j => alignedThinEndpoint K (ell + S) j) ∧
      s.I = (fun ell j =>
        caichNormalizedEnergy (ell + S) K
          (alignedThinEndpoint K (ell + S) 0)
          (alignedThinEndpoint K (ell + S) j)) := by
  obtain ⟨C, hC, N, hN, hP⟩ := exists_primeCountingUpperBound
  let S : ℕ := alignedScheduleShift N
  have hS5 : 5 ≤ S := five_le_alignedScheduleShift N
  have hNS : N ≤ S := self_le_alignedScheduleShift N
  let s : ConcreteThinBlockSchedule :=
    { J := shiftedAlignedThinBlockCount K S
      y := fun ell j => alignedThinEndpoint K (ell + S) j
      y_monotone := fun ell => alignedThinEndpoint_mono K (ell + S)
      two_le_y := fun ell j => two_le_alignedThinEndpoint K (ell + S) j
      I := fun ell j =>
        caichNormalizedEnergy (ell + S) K
          (alignedThinEndpoint K (ell + S) 0)
          (alignedThinEndpoint K (ell + S) j)
      I_nonneg := by
        intro ell j old
        apply caichNormalizedEnergy_nonneg
        exact lt_of_lt_of_le Nat.one_lt_two
          (two_le_alignedThinEndpoint K (ell + S) j)
      Cparseval := 2
      Cparseval_nonneg := by norm_num
      Crecip := 4 * C
      Crecip_nonneg := by positivity
      parseval_le := by
        intro ell _hell j hj hjJ old
        have hellne : ell ≠ 0 := by
          intro hell0
          subst ell
          simp [shiftedAlignedThinBlockCount] at hjJ
          omega
        rw [shiftedAlignedThinBlockCount, if_neg hellne] at hjJ
        let L : ℕ := ell + S
        let a : ℕ := alignedThinEndpoint K L (j - 1)
        let b : ℕ := alignedThinEndpoint K L j
        have hL5 : 5 ≤ L := by dsimp [L]; omega
        have ha : 1 < a := by
          exact lt_of_lt_of_le Nat.one_lt_two
            (two_le_alignedThinEndpoint K L (j - 1))
        have hab : a ≤ b := by
          exact alignedThinEndpoint_mono K L (Nat.sub_le j 1)
        have hjprev : j - 1 ≤ alignedThinBlockCount K L :=
          (Nat.sub_le j 1).trans hjJ
        have hdamp :
            Real.exp
                (Real.log
                    (Real.log (a : ℝ) /
                      Real.log (alignedThinEndpoint K L 0 : ℝ)) /
                  ((L : ℝ) ^ K)) ≤
              (2 * Real.pi) * 2 := by
          simpa only [a] using!
            (alignedThinEndpoint_caichDamping_le_four_pi
              hK (show 4 ≤ L by omega) hjprev)
        change smoothEnergy old a / Real.log (b : ℝ) ≤
          (2 : ℝ) *
            caichNormalizedEnergy L K
              (alignedThinEndpoint K L 0) a old
        exact smoothEnergy_div_log_le_caichNormalizedEnergy
          ha hab hdamp old
      reciprocal_le := by
        intro ell hell j hj hjJ
        have hellne : ell ≠ 0 := Nat.one_le_iff_ne_zero.mp hell
        rw [shiftedAlignedThinBlockCount, if_neg hellne] at hjJ
        let L : ℕ := ell + S
        let a : ℕ := alignedThinEndpoint K L (j - 1)
        let b : ℕ := alignedThinEndpoint K L j
        have hL5 : 5 ≤ L := by dsimp [L]; omega
        have hNL : N ≤ L := hNS.trans (by dsimp [L]; omega)
        have hLa : L ≤ a := by
          exact scale_le_alignedThinEndpoint hK (show 4 ≤ L by omega)
        have hNa : N ≤ a := hNL.trans hLa
        have ha : 2 ≤ a := two_le_alignedThinEndpoint K L (j - 1)
        have hab : a ≤ b :=
          alignedThinEndpoint_mono K L (Nat.sub_le j 1)
        have hwidth : logLogNat b - logLogNat a ≤ 2 / (L : ℝ) := by
          have hstep := alignedThinEndpoint_logLog_width
            (K := K) (ell := L) (j := j - 1) hK (show 4 ≤ L by omega)
          simpa only [a, b, Nat.sub_add_cancel hj] using! hstep
        have hlarge : (L : ℝ) ≤ Real.log (a : ℝ) :=
          scale_le_log_alignedThinEndpoint hK hL5
        have hraw := freshReciprocalSum_le_of_primeCountingUpperBound
          hC.le hP hNa ha hab
        have hLR : (0 : ℝ) < L := by positivity
        have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
        have hellL : (ell : ℝ) ≤ L := by exact_mod_cast (Nat.le_add_right ell S)
        calc
          freshReciprocalSum a b ≤
              C * (logLogNat b - logLogNat a) +
                2 * C / Real.log (a : ℝ) := hraw
          _ ≤ C * (2 / (L : ℝ)) + 2 * C / (L : ℝ) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hwidth hC.le
            · exact div_le_div_of_nonneg_left (by positivity) hLR hlarge
          _ = 4 * C / (L : ℝ) := by ring
          _ ≤ 4 * C / (ell : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hellR hellL }
  exact ⟨s, S, hS5, rfl, rfl, rfl⟩

/-- Hence the complete equation-(16) moment bound is available on the
aligned, gap-free schedule. -/
theorem exists_alignedIntegerThinPrimeBlockMomentBound
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ s : ConcreteThinBlockSchedule, ∃ S : ℕ, 5 ≤ S ∧
      s.J = shiftedAlignedThinBlockCount K S ∧
      ThinPrimeBlockMomentBound μ s.toThinBlockData := by
  obtain ⟨s, S, hS, hJ, _hy, _hI⟩ :=
    exists_alignedIntegerConcreteThinBlockSchedule K hK
  exact ⟨s, S, hS, hJ, s.thinPrimeBlockMomentBound⟩

/-! ## The exact root-exponential test mesh -/

/-- Caich--Lau--Tenenbaum--Wu test point with `c₀ = 1/m`. -/
noncomputable def alignedRootExpTestPoint (m i : ℕ) : ℕ :=
  Nat.floor (Real.exp ((i : ℝ) ^ (1 / (m : ℝ))))

/-- A safe finite index cutoff.  At this index the real test point has
already passed the upper macro endpoint. -/
def alignedRootExpTestIndexBound (K m ell : ℕ) : ℕ :=
  (2 * alignedOuterExponent K ell) ^ m

/-- Exactly the root-exponential test indices in the current outer block.
The finite range is proved below to contain every global index whose test
point is at most `X_ell`. -/
noncomputable def alignedRootExpTests (K m ell : ℕ) : Finset ℕ :=
  if ell < 5 then ∅
  else
    (Finset.range (alignedRootExpTestIndexBound K m ell + 1)).filter
      (fun i =>
        alignedOuterEndpoint K (ell - 1) < alignedRootExpTestPoint m i ∧
          alignedRootExpTestPoint m i ≤ alignedOuterEndpoint K ell)

theorem alignedRootExpTestPoint_mono (m : ℕ) :
    Monotone (alignedRootExpTestPoint m) := by
  intro i j hij
  unfold alignedRootExpTestPoint
  apply Nat.floor_mono
  apply Real.exp_monotone
  apply Real.rpow_le_rpow
  · positivity
  · exact_mod_cast hij
  · positivity

private theorem alignedRootExpTestIndexBound_root
    {K m ell : ℕ} (hm : 0 < m) :
    ((alignedRootExpTestIndexBound K m ell : ℝ) ^
        (1 / (m : ℝ))) =
      (2 * alignedOuterExponent K ell : ℕ) := by
  rw [alignedRootExpTestIndexBound, Nat.cast_pow, one_div]
  exact Real.pow_rpow_inv_natCast (by positivity) hm.ne'

private theorem outerEndpoint_add_one_le_exp_two_mul_outerExponent
    (K ell : ℕ) :
    (alignedOuterEndpoint K ell + 1 : ℕ) ≤
      Real.exp (2 * alignedOuterExponent K ell : ℕ) := by
  let E := alignedOuterExponent K ell
  let X := alignedOuterEndpoint K ell
  have hEpos : 0 < E := alignedOuterExponent_pos K ell
  have hXtwo : 2 ≤ X := by
    dsimp [X, alignedOuterEndpoint]
    change 2 ^ 1 ≤ 2 ^ E
    exact Nat.pow_le_pow_right (by norm_num) hEpos
  have hXsq : X + 1 ≤ X * X := by nlinarith
  have hExpOne : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hExpE : (X : ℝ) ≤ Real.exp (E : ℝ) := by
    have hexp : Real.exp (E : ℝ) = Real.exp 1 ^ E := by
      simpa using! Real.exp_nat_mul 1 E
    rw [hexp]
    change ((2 ^ E : ℕ) : ℝ) ≤ Real.exp 1 ^ E
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_left₀ (by norm_num) hExpOne E
  have hExpSq : (X : ℝ) * X ≤
      Real.exp (E : ℝ) * Real.exp (E : ℝ) := by
    exact mul_le_mul hExpE hExpE (Nat.cast_nonneg X)
      (Real.exp_pos _).le
  calc
    ((X + 1 : ℕ) : ℝ) ≤ (X * X : ℕ) := by exact_mod_cast hXsq
    _ = (X : ℝ) * X := by norm_cast
    _ ≤ Real.exp (E : ℝ) * Real.exp (E : ℝ) := hExpSq
    _ = Real.exp (2 * E : ℕ) := by
      rw [← Real.exp_add]
      congr 1
      norm_cast
      ring

/-- The safe cutoff index has test point strictly beyond `X_ell`. -/
theorem alignedOuterEndpoint_lt_testPoint_indexBound
    {K m ell : ℕ} (hm : 0 < m) :
    alignedOuterEndpoint K ell <
      alignedRootExpTestPoint m (alignedRootExpTestIndexBound K m ell) := by
  have hroot := alignedRootExpTestIndexBound_root
    (K := K) (ell := ell) hm
  have hfloor : alignedOuterEndpoint K ell + 1 ≤
      Nat.floor (Real.exp
        ((alignedRootExpTestIndexBound K m ell : ℝ) ^
          (1 / (m : ℝ)))) := by
    apply Nat.le_floor
    rw [hroot]
    exact outerEndpoint_add_one_le_exp_two_mul_outerExponent K ell
  exact Nat.lt_of_succ_le hfloor

/-- Every global test index whose point lies in the macro block belongs to
the finite family `alignedRootExpTests`. -/
theorem mem_alignedRootExpTests_of_mem_outerBlock
    {K m ell i : ℕ} (hm : 0 < m) (hell : 5 ≤ ell)
    (hlower : alignedOuterEndpoint K (ell - 1) <
      alignedRootExpTestPoint m i)
    (hupper : alignedRootExpTestPoint m i ≤ alignedOuterEndpoint K ell) :
    i ∈ alignedRootExpTests K m ell := by
  rw [alignedRootExpTests, if_neg (not_lt_of_ge hell), Finset.mem_filter,
    Finset.mem_range]
  refine ⟨?_, hlower, hupper⟩
  apply Nat.lt_succ_iff.mpr
  by_contra hnot
  have hbound : alignedRootExpTestIndexBound K m ell ≤ i :=
    le_of_not_ge hnot
  have hmono := alignedRootExpTestPoint_mono m hbound
  have hpast := alignedOuterEndpoint_lt_testPoint_indexBound
    (K := K) (ell := ell) hm
  exact (not_lt_of_ge hupper) (hpast.trans_le hmono)

theorem alignedThinInitial_lt_testPoint_of_mem
    {K m ell i : ℕ} (hi : i ∈ alignedRootExpTests K m ell) :
    alignedThinEndpoint K ell 0 < alignedRootExpTestPoint m i := by
  rw [alignedRootExpTests] at hi
  split at hi
  · simp at hi
  · exact alignedThinInitial_lt_of_mem_outerBlock
      (Finset.mem_filter.mp hi).2.1

theorem five_le_of_mem_alignedRootExpTests
    {K m ell i : ℕ} (hi : i ∈ alignedRootExpTests K m ell) :
    5 ≤ ell := by
  by_contra hnot
  have hsmall : ell < 5 := by omega
  simp [alignedRootExpTests, hsmall] at hi

/-- Exact lower macro-scale formula at every selected test point. -/
theorem previousOuter_log₂_lt_testPoint
    {K m ell i : ℕ} (hi : i ∈ alignedRootExpTests K m ell) :
    (ell - 1 : ℕ) ^ K * Real.log 2 + Real.log (Real.log 2) <
      log₂ (alignedRootExpTestPoint m i) := by
  have hx : alignedOuterEndpoint K (ell - 1) <
      alignedRootExpTestPoint m i := by
    unfold alignedRootExpTests at hi
    split at hi
    · simp at hi
    · exact (Finset.mem_filter.mp hi).2.1
  have ha : 2 ≤ alignedOuterEndpoint K (ell - 1) := by
    unfold alignedOuterEndpoint
    change 2 ^ 1 ≤ 2 ^ alignedOuterExponent K (ell - 1)
    exact Nat.pow_le_pow_right (by norm_num)
      (alignedOuterExponent_pos K (ell - 1))
  have hloga : 0 < Real.log (alignedOuterEndpoint K (ell - 1) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < alignedOuterEndpoint K (ell - 1) by omega)
  have hlogx : 0 < Real.log (alignedRootExpTestPoint m i : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < alignedRootExpTestPoint m i by omega)
  have htestPos : (0 : ℝ) < alignedRootExpTestPoint m i := by
    exact_mod_cast (show 0 < alignedRootExpTestPoint m i by omega)
  have hfirst : Real.log (alignedOuterEndpoint K (ell - 1) : ℝ) <
      Real.log (alignedRootExpTestPoint m i : ℝ) :=
    Real.strictMonoOn_log
      (show (0 : ℝ) < alignedOuterEndpoint K (ell - 1) by positivity)
      htestPos
      (by exact_mod_cast hx)
  have hsecond :
      Real.log (Real.log (alignedOuterEndpoint K (ell - 1) : ℝ)) <
        Real.log (Real.log (alignedRootExpTestPoint m i : ℝ)) :=
    Real.strictMonoOn_log hloga hlogx hfirst
  rw [← logLog_alignedOuterEndpoint K (ell - 1)]
  simpa [log₂, logLogNat] using! hsecond

/-- Coarse power lower bound for the selected test-point scale.  The
constant is explicit and depends only on `K`. -/
theorem alignedRootExpTestPoint_log₂_scale_lower
    {K m ell i : ℕ} (hK : 1 ≤ K)
    (hi : i ∈ alignedRootExpTests K m ell) :
    (1 / (3 * (2 : ℝ) ^ K)) * (ell : ℝ) ^ K ≤
      log₂ (alignedRootExpTestPoint m i) := by
  have hell : 5 ≤ ell := five_le_of_mem_alignedRootExpTests hi
  let A : ℕ := (ell - 1) ^ K
  have hhalf : (ell : ℝ) / 2 ≤ (ell - 1 : ℕ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ ell)]
    norm_num
    have hellR : (5 : ℝ) ≤ ell := by exact_mod_cast hell
    linarith
  have hpowHalf : ((ell : ℝ) / 2) ^ K ≤ (A : ℝ) := by
    dsimp [A]
    simpa only [Nat.cast_pow] using!
      (pow_le_pow_left₀ (by positivity) hhalf K)
  have hpowDiv : (ell : ℝ) ^ K / (2 : ℝ) ^ K ≤ (A : ℝ) := by
    simpa only [div_pow] using! hpowHalf
  have hAthree : (3 : ℝ) ≤ A := by
    have hbase : 4 ≤ ell - 1 := by omega
    have hnat : ell - 1 ≤ (ell - 1) ^ K :=
      le_self_pow₀ (by omega) (by omega : K ≠ 0)
    exact_mod_cast (show 3 ≤ A by dsimp [A]; omega)
  have hlogTwo : (2 / 3 : ℝ) < Real.log 2 :=
    (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hloglog := neg_one_lt_log_log_two_aligned
  have hmacro := previousOuter_log₂_lt_testPoint hi
  have hmacro' : (A : ℝ) * Real.log 2 + Real.log (Real.log 2) <
      log₂ (alignedRootExpTestPoint m i) := by
    simpa only [A, Nat.cast_pow] using! hmacro
  have hleft :
      (1 / (3 * (2 : ℝ) ^ K)) * (ell : ℝ) ^ K ≤ (A : ℝ) / 3 := by
    calc
      (1 / (3 * (2 : ℝ) ^ K)) * (ell : ℝ) ^ K =
          ((ell : ℝ) ^ K / (2 : ℝ) ^ K) / 3 := by field_simp
      _ ≤ (A : ℝ) / 3 := div_le_div_of_nonneg_right hpowDiv (by norm_num)
  apply hleft.trans
  have hcoarse : (A : ℝ) / 3 ≤
      (A : ℝ) * Real.log 2 + Real.log (Real.log 2) := by
    nlinarith
  exact hcoarse.trans hmacro'.le

theorem card_alignedRootExpTests_le_indexBound (K m ell : ℕ) :
    (alignedRootExpTests K m ell).card ≤
      alignedRootExpTestIndexBound K m ell + 1 := by
  unfold alignedRootExpTests
  split
  · simp
  · exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

private theorem alignedRootExpTestIndexBound_add_one_le_entropyPow
    {K m ell : ℕ} (hell : 0 < ell) :
    alignedRootExpTestIndexBound K m ell + 1 ≤
      2 ^ ((2 * m + 2) * ell ^ K) := by
  let A : ℕ := ell ^ K
  have hA : 1 ≤ A := by
    dsimp [A]
    exact Nat.one_le_pow K ell hell
  have hbound : alignedRootExpTestIndexBound K m ell =
      2 ^ ((A + 1) * m) := by
    unfold alignedRootExpTestIndexBound alignedOuterExponent
    change (2 * 2 ^ A) ^ m = _
    rw [show 2 * 2 ^ A = 2 ^ (A + 1) by rw [pow_succ]; ring,
      pow_mul]
  have hboundOne : 1 ≤ alignedRootExpTestIndexBound K m ell := by
    rw [hbound]
    exact one_le_pow₀ (by norm_num)
  have hexponent : 1 + (A + 1) * m ≤ (2 * m + 2) * A := by
    have hm : m ≤ m * A := by
      simpa only [mul_one] using! Nat.mul_le_mul_left m hA
    nlinarith
  calc
    alignedRootExpTestIndexBound K m ell + 1 ≤
        2 * alignedRootExpTestIndexBound K m ell := by omega
    _ = 2 ^ (1 + (A + 1) * m) := by
      rw [hbound, show 2 * 2 ^ ((A + 1) * m) =
        2 ^ (1 + (A + 1) * m) by
          rw [show 1 + (A + 1) * m = (A + 1) * m + 1 by omega,
            pow_succ]
          ring]
    _ ≤ 2 ^ ((2 * m + 2) * A) :=
      Nat.pow_le_pow_right (by norm_num) hexponent
    _ = 2 ^ ((2 * m + 2) * ell ^ K) := rfl

/-- Exact finite-test entropy.  The root-exponential mesh has degree `K`,
even though the aligned thin schedule has block-count degree `K+1`. -/
theorem card_alignedRootExpTests_le_exp_entropy
    (K m ell : ℕ) :
    ((alignedRootExpTests K m ell).card : ℝ) ≤
      Real.exp (((2 * m + 2 : ℕ) : ℝ) * (ell : ℝ) ^ (K : ℝ)) := by
  by_cases hellSmall : ell < 5
  · simp [alignedRootExpTests, hellSmall, Real.exp_nonneg]
  have hellpos : 0 < ell := by omega
  let n : ℕ := (2 * m + 2) * ell ^ K
  have hbound := alignedRootExpTestIndexBound_add_one_le_entropyPow
    (K := K) (m := m) (ell := ell) hellpos
  have hbound' : alignedRootExpTestIndexBound K m ell + 1 ≤ 2 ^ n := by
    simpa only [n] using! hbound
  have hcardNat : (alignedRootExpTests K m ell).card ≤ 2 ^ n :=
    (card_alignedRootExpTests_le_indexBound K m ell).trans hbound'
  have hbase : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hpow : ((2 : ℝ) ^ n) ≤ Real.exp 1 ^ n :=
    pow_le_pow_left₀ (by norm_num) hbase n
  have hexpEq : Real.exp 1 ^ n = Real.exp (n : ℝ) := by
    simpa using! (Real.exp_nat_mul 1 n).symm
  calc
    ((alignedRootExpTests K m ell).card : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    _ = (2 : ℝ) ^ n := by norm_cast
    _ ≤ Real.exp 1 ^ n := hpow
    _ = Real.exp (n : ℝ) := hexpEq
    _ = Real.exp (((2 * m + 2 : ℕ) : ℝ) *
        (ell : ℝ) ^ (K : ℝ)) := by
      congr 1
      dsimp [n]
      rw [Real.rpow_natCast]
      norm_cast

/-! ## Concentration with separate entropy and block degrees -/

/-- General stopped-Hoeffding summability with an entropy degree `P`
independent of every thin-block count. -/
theorem summable_largestPrimeStoppedBudget_of_entropyDegree
    (tests : ℕ → Finset ℕ) (u T : ℕ → ℕ → ℝ)
    {C c q : ℝ} {P : ℕ} (hC : 0 ≤ C) (hc : 0 < c)
    (hPq : (P : ℝ) < q) (hq : 1 < q)
    (hcard : ∀ ell,
      ((tests ell).card : ℝ) ≤ Real.exp (C * (ell : ℝ) ^ (P : ℝ)))
    (hexponent : ∀ ell r, r ∈ tests ell →
      c * (ell : ℝ) ^ q ≤ (u ell r) ^ 2 / (2 * T ell r)) :
    Summable fun ell => largestPrimeStoppedBudget tests u T ell := by
  apply Summable.of_nonneg_of_le
  · intro ell
    unfold largestPrimeStoppedBudget
    positivity
  · intro ell
    exact largestPrimeStoppedBudget_le_caichExponent
      tests u T hcard hexponent ell
  · exact (summable_exp_rpow_sub_rpow hC hc hPq hq).mul_left 2

/-- The exact aligned root-exponential mesh can be inserted directly in the
generalized concentration theorem.  Its entropy degree is `K`; the aligned
thin-block degree `K+1` is absent from the exponent comparison. -/
theorem summable_largestPrimeStoppedBudget_alignedRootExpTests
    (K m : ℕ) (u T : ℕ → ℕ → ℝ)
    {c q : ℝ} (hc : 0 < c) (hKq : (K : ℝ) < q) (hq : 1 < q)
    (hexponent : ∀ ell r, r ∈ alignedRootExpTests K m ell →
      c * (ell : ℝ) ^ q ≤ (u ell r) ^ 2 / (2 * T ell r)) :
    Summable fun ell =>
      largestPrimeStoppedBudget (alignedRootExpTests K m) u T ell := by
  apply summable_largestPrimeStoppedBudget_of_entropyDegree
    (tests := alignedRootExpTests K m) (u := u) (T := T)
    (C := (2 * m + 2 : ℕ)) (P := K)
    (by positivity) hc hKq hq
  · exact card_alignedRootExpTests_le_exp_entropy K m
  · exact hexponent

/-- Numerical comparison for a concentration power `q`: only the entropy
degree `P`, not the block-count degree, must lie below `q`. -/
theorem concentrationPower_gt_entropyDegree
    {P K : ℕ} {η : ℝ}
    (hgap : (P : ℝ) + 10 < (K : ℝ) + 2 * (K : ℝ) * η) :
    (P : ℝ) < (K : ℝ) + 2 * (K : ℝ) * η - 10 := by
  linarith

/-- Caich's usual condition `2 K η > 10` therefore handles the exact test
mesh, despite the aligned block count having degree `K+1`. -/
theorem summable_largestPrimeStoppedBudget_alignedRootExpTests_caich
    (K m : ℕ) (hK : 1 ≤ K) (u T : ℕ → ℕ → ℝ)
    {c η : ℝ} (hc : 0 < c) (hgap : 10 < 2 * (K : ℝ) * η)
    (hexponent : ∀ ell r, r ∈ alignedRootExpTests K m ell →
      c * (ell : ℝ) ^
          ((K : ℝ) + 2 * (K : ℝ) * η - 10) ≤
        (u ell r) ^ 2 / (2 * T ell r)) :
    Summable fun ell =>
      largestPrimeStoppedBudget (alignedRootExpTests K m) u T ell := by
  apply summable_largestPrimeStoppedBudget_alignedRootExpTests
    K m u T hc (caich_concentration_exponent_gap hgap)
  · have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
    exact hKR.trans_lt (caich_concentration_exponent_gap hgap)
  · exact hexponent

end Problem520
end Erdos
