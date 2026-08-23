/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma2Concrete
import ErdosProblems.Erdos240.BakerLemma3Instantiation

/-!
# Closed-form majorants for the source auxiliary function

The canonical majorants in `BakerLemma3Instantiation` are exact finite
sums.  This file bounds the parts of those sums which do not involve the
Delta polynomials by explicit expressions independent of the coefficient
state.

The exponential-rate estimate records a mathematically necessary source
normalization: the distinguished last logarithmic coefficient dominates
the old coefficients.  Without this hypothesis the rate contains
`b_r / b_last`, and no bound exponential in `log Bsrc` can hold uniformly.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceMajorantClosedForm

open Finset
open Erdos240
open BakerAuxiliary
open BakerLemma2Concrete
open BakerLemma3
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceState
open DeltaPower
open Polynomial

/-! ## Complex evaluation of nonnegative rational polynomials -/

/-- Evaluation in `ℂ` is bounded by evaluation at the norm in `ℝ` when all
rational coefficients are nonnegative. -/
theorem norm_eval₂_le_real_eval₂_of_coeffNonneg (p : ℚ[X])
    (hp : CoeffNonneg p) (z : ℂ) :
    ‖Polynomial.eval₂ (algebraMap ℚ ℂ) z p‖ ≤
      Polynomial.eval₂ (algebraMap ℚ ℝ) ‖z‖ p := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.eval₂_eq_sum]
  calc
    ‖∑ i ∈ p.support, algebraMap ℚ ℂ (p.coeff i) * z ^ i‖ ≤
        ∑ i ∈ p.support,
          ‖algebraMap ℚ ℂ (p.coeff i) * z ^ i‖ := norm_sum_le _ _
    _ = ∑ i ∈ p.support,
          algebraMap ℚ ℝ (p.coeff i) * ‖z‖ ^ i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [norm_mul, norm_pow]
      have hcoeff : 0 ≤ (p.coeff i : ℝ) := by exact_mod_cast hp i
      change ‖((p.coeff i : ℚ) : ℂ)‖ * ‖z‖ ^ i =
        ((p.coeff i : ℚ) : ℝ) * ‖z‖ ^ i
      rw [Complex.norm_ratCast, abs_of_nonneg hcoeff]
    _ = _ := by rfl

/-- Real evaluation of a nonnegative rational polynomial is monotone on
the nonnegative half-line. -/
theorem real_eval₂_mono_of_coeffNonneg (p : ℚ[X]) (hp : CoeffNonneg p)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Polynomial.eval₂ (algebraMap ℚ ℝ) x p ≤
      Polynomial.eval₂ (algebraMap ℚ ℝ) y p := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.eval₂_eq_sum]
  apply Finset.sum_le_sum
  intro i _hi
  have hcoeff : 0 ≤ (p.coeff i : ℝ) := by exact_mod_cast hp i
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy i) hcoeff

/-- A nonnegative-coefficient polynomial at an arbitrary complex point is
bounded by its value at the natural ceiling of the norm. -/
theorem norm_eval₂_le_eval_nat_of_coeffNonneg (p : ℚ[X])
    (hp : CoeffNonneg p) (z : ℂ) :
    ‖Polynomial.eval₂ (algebraMap ℚ ℂ) z p‖ ≤
      algebraMap ℚ ℝ (p.eval (Nat.ceil ‖z‖ : ℚ)) := by
  calc
    ‖Polynomial.eval₂ (algebraMap ℚ ℂ) z p‖ ≤
        Polynomial.eval₂ (algebraMap ℚ ℝ) ‖z‖ p :=
      norm_eval₂_le_real_eval₂_of_coeffNonneg p hp z
    _ ≤ Polynomial.eval₂ (algebraMap ℚ ℝ) (Nat.ceil ‖z‖ : ℝ) p :=
      real_eval₂_mono_of_coeffNonneg p hp (norm_nonneg z) (Nat.le_ceil ‖z‖)
    _ = algebraMap ℚ ℝ (p.eval (Nat.ceil ‖z‖ : ℚ)) := by
      rw [show ((Nat.ceil ‖z‖ : ℕ) : ℝ) =
          algebraMap ℚ ℝ (Nat.ceil ‖z‖ : ℚ) by norm_num,
        Polynomial.eval₂_at_apply]

/-- Complex powered-Delta derivatives have a fixed-base ceiling bound. -/
theorem norm_poweredDeltaHasseEval_le_two_pow
    (h lambda m : ℕ) (z : ℂ) :
    ‖poweredDeltaHasseEval h lambda m z‖ ≤
      (2 : ℝ) ^ ((Nat.ceil ‖z‖ + 1 + h) * lambda) := by
  refine (norm_eval₂_le_eval_nat_of_coeffNonneg
    (poweredDeltaHasse h lambda m)
    ((coeffNonneg_poweredDelta h lambda).hasseDeriv m) z).trans ?_
  have hraw := poweredDeltaHasse_eval_nat_le_two_pow
    h lambda m (Nat.ceil ‖z‖)
  change (((poweredDeltaHasse h lambda m).eval
      ((Nat.ceil ‖z‖ : ℕ) : ℚ) : ℚ) : ℝ) ≤
    (2 : ℝ) ^ ((Nat.ceil ‖z‖ + 1 + h) * lambda)
  exact_mod_cast hraw

/-- Complex ordinary Delta values have a ceiling bound retaining their
true degree `m`. -/
theorem norm_simpleDeltaEval_le_pow (m : ℕ) (z : ℂ) :
    ‖simpleDeltaEval m z‖ ≤ ((Nat.ceil ‖z‖ + 1 : ℕ) : ℝ) ^ m := by
  refine (norm_eval₂_le_eval_nat_of_coeffNonneg
    (Erdos240Delta.delta m) (coeffNonneg_delta m) z).trans ?_
  have hraw := Erdos240Delta.eval_delta_nat_le_pow m (Nat.ceil ‖z‖)
  change (((Erdos240Delta.delta m).eval
      ((Nat.ceil ‖z‖ : ℕ) : ℚ) : ℚ) : ℝ) ≤
    ((Nat.ceil ‖z‖ + 1 : ℕ) : ℝ) ^ m
  exact_mod_cast hraw

/-- The initial coefficient-box cardinality, used as a uniform cardinality
bound at every later level. -/
def initialSupportBound {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℕ :=
  Fintype.card (LambdaBox (BakerSourceState.initialBoxShape P))

/-- A closed-form bound for every modified exponential rate after the last
coefficient has been chosen dominant. -/
def sourceRateBound {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  ∑ r : Fin oldRank,
    ((P.LiZero r + P.LlastZero : ℕ) : ℝ) * ‖oldLog P r‖

theorem levelIndex_card_le_initialSupportBound {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) :
    Fintype.card (LevelIndex P J) ≤ initialSupportBound P := by
  unfold initialSupportBound
  rw [card_lambdaBox, card_lambdaBox]
  unfold unknownCount BakerSourceState.initialBoxShape
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul le_rfl le_rfl
  · apply Nat.mul_le_mul
    · apply Finset.prod_le_prod'
      intro r _hr
      rw [show (levelBoxShape P 0).oldMax r = P.LiZero r from
        BakerSourceState.initialBoxShape_oldMax P r]
      exact Nat.add_le_add_right (levelBoxShape_oldMax_le_initial P J r) 1
    · rw [show (levelBoxShape P 0).lastMax = P.LlastZero from
        BakerSourceState.initialBoxShape_lastMax P]
      exact Nat.add_le_add_right (levelBoxShape_lastMax_le_initial P J) 1

theorem state_support_card_le_initialSupportBound {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J) :
    state.support.card ≤ initialSupportBound P := by
  simpa [LevelState.support] using levelIndex_card_le_initialSupportBound P J

theorem state_support_card_le_exp_heightScale {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (hreq : initialUnknownRequirement P ∈ P.kRequirements) :
    (state.support.card : ℝ) ≤
      Real.exp ((1 / 6 : ℝ) * P.h * P.k * P.Omega *
        Real.log P.OmegaOld) := by
  calc
    (state.support.card : ℝ) ≤ (initialSupportBound P : ℕ) := by
      exact_mod_cast state_support_card_le_initialSupportBound P state
    _ = Fintype.card
        (LambdaBox (BakerLemma2Concrete.initialBoxShape P)) := by rfl
    _ ≤ Real.exp ((1 / 6 : ℝ) * P.h * P.k * P.Omega *
          Real.log P.OmegaOld) :=
      initial_unknownCount_le_exp_heightScale P hreq

theorem norm_intCast_div_intCast_le_one_of_dominates
    {a b : ℤ} (hb : b ≠ 0) (hab : a.natAbs ≤ b.natAbs) :
    ‖(a : ℂ) / (b : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_intCast, Complex.norm_intCast]
  have hbabs : 0 < |(b : ℝ)| := abs_pos.mpr (by exact_mod_cast hb)
  rw [div_le_one hbabs]
  have habR : (a.natAbs : ℝ) ≤ b.natAbs := by exact_mod_cast hab
  simpa only [Nat.cast_natAbs, Int.cast_abs] using habR

theorem state_lastExponent_le_initial {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (lambda : LevelIndex P J) :
    (coordinatesForState state).lastExponent lambda ≤ P.LlastZero := by
  change lambda.lastExponentFin.val ≤ P.LlastZero
  exact (Nat.le_of_lt_succ lambda.lastExponentFin.isLt).trans
    (levelBoxShape_lastMax_le_initial P J)

/-- The last exponent retains the exact `q^{-J}` decay of the level box. -/
theorem state_lastExponent_cast_le_scaled {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (lambda : LevelIndex P J) :
    ((coordinatesForState state).lastExponent lambda : ℝ) ≤
      P.qInvPow J * P.LlastZero := by
  have hnat :
      (coordinatesForState state).lastExponent lambda ≤
        scaledExponentMax P J P.LlastZero := by
    change lambda.lastExponentFin.val ≤
      (levelBoxShape P J).lastMax
    exact Nat.le_of_lt_succ lambda.lastExponentFin.isLt
  have hcast :
      ((coordinatesForState state).lastExponent lambda : ℝ) ≤
        scaledExponentMax P J P.LlastZero := by
    exact_mod_cast hnat
  exact hcast.trans (scaledExponentMax_cast_le P J P.LlastZero)

theorem state_oldExponent_le_initial {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (lambda : LevelIndex P J) (r : Fin oldRank) :
    (coordinatesForState state).oldExponent lambda r ≤ P.LiZero r := by
  change (lambda.oldExponentFin r).val ≤ P.LiZero r
  exact (Nat.le_of_lt_succ (lambda.oldExponentFin r).isLt).trans
    (levelBoxShape_oldMax_le_initial P J r)

/-- The shift coordinate has the same fixed source range at every level. -/
theorem state_shift_lt_h {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (lambda : LevelIndex P J) :
    (coordinatesForState state).shift lambda < P.h := by
  change lambda.shiftIndex.val < P.h
  simpa only [levelBoxShape_shiftMax, P.LminusOne_add_one_eq_h] using
    lambda.shiftIndex.isLt

/-- The signed argument of every old-coordinate Delta factor is controlled
uniformly by the source coefficient cutoff and the initial exponent sides. -/
theorem state_old_delta_argument_natAbs_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc)
    (lambda : LevelIndex P J) (r : Fin oldRank) :
    (bLast * (coordinatesForState state).oldExponent lambda r -
        b r * (coordinatesForState state).lastExponent lambda).natAbs ≤
      P.Bsrc * (P.LiZero r + P.LlastZero) := by
  calc
    (bLast * (coordinatesForState state).oldExponent lambda r -
          b r * (coordinatesForState state).lastExponent lambda).natAbs ≤
        (bLast * (coordinatesForState state).oldExponent lambda r).natAbs +
          (b r * (coordinatesForState state).lastExponent lambda).natAbs :=
      Int.natAbs_sub_le _ _
    _ = bLast.natAbs * (coordinatesForState state).oldExponent lambda r +
          (b r).natAbs * (coordinatesForState state).lastExponent lambda := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ P.Bsrc * P.LiZero r + P.Bsrc * P.LlastZero := by
      exact Nat.add_le_add
        (Nat.mul_le_mul hbLast
          (state_oldExponent_le_initial P state lambda r))
        (Nat.mul_le_mul (hb r)
          (state_lastExponent_le_initial P state lambda))
    _ = P.Bsrc * (P.LiZero r + P.LlastZero) := by
      rw [Nat.mul_add]

/-- A single common natural base for every old-coordinate Delta factor at
every induction level. -/
def sourceOldDeltaBaseNat {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℕ :=
  P.Bsrc * ((∑ r : Fin oldRank, P.LiZero r) + P.LlastZero) + 1

theorem ceil_norm_intCast (a : ℤ) :
    Nat.ceil ‖(a : ℂ)‖ = a.natAbs := by
  rw [Complex.norm_intCast]
  have habs : |(a : ℝ)| = (a.natAbs : ℝ) := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
  rw [habs, Nat.ceil_natCast]

/-- Uniform bound for one old-coordinate Delta factor in a corrected source
state. -/
theorem norm_state_simpleDeltaEval_le_sourceOldDeltaBase_pow
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc)
    (lambda : LevelIndex P J) (m : VDPLMultiIndex (oldRank + 1))
    (r : Fin oldRank) :
    ‖simpleDeltaEval (m r.succ)
        ((bLast : ℂ) * (coordinatesForState state).oldExponent lambda r -
          (b r : ℂ) * (coordinatesForState state).lastExponent lambda)‖ ≤
      (sourceOldDeltaBaseNat P : ℝ) ^ (m r.succ) := by
  let a : ℤ := bLast * (coordinatesForState state).oldExponent lambda r -
    b r * (coordinatesForState state).lastExponent lambda
  have harg :
      (bLast : ℂ) * (coordinatesForState state).oldExponent lambda r -
          (b r : ℂ) * (coordinatesForState state).lastExponent lambda =
        (a : ℂ) := by
    dsimp only [a]
    push_cast
    rfl
  rw [harg]
  refine (norm_simpleDeltaEval_le_pow (m r.succ) (a : ℂ)).trans ?_
  rw [ceil_norm_intCast]
  apply pow_le_pow_left₀ (by positivity)
  unfold sourceOldDeltaBaseNat
  have hLi : P.LiZero r ≤ ∑ i : Fin oldRank, P.LiZero i :=
    Finset.single_le_sum (fun i _hi ↦ Nat.zero_le (P.LiZero i))
      (Finset.mem_univ r)
  have ha := state_old_delta_argument_natAbs_le
    P state b bLast hb hbLast lambda r
  exact_mod_cast Nat.add_le_add_right
    (ha.trans (Nat.mul_le_mul_left P.Bsrc
      (Nat.add_le_add_right hLi P.LlastZero))) 1

/-- Uniform head-Delta envelope at level `J`; it depends on the evaluation
point only through the norm of the scaled head argument. -/
def sourceHeadDeltaMajorant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (z : ℂ) : ℝ :=
  (2 : ℝ) ^
    ((Nat.ceil (‖scaledArgument P.q J z‖ + P.h) + 1 + P.h) *
      P.LzeroPlusOne)

/-- Monotonicity wrapper for replacing the scaled argument by a convenient
real grid-radius bound. -/
theorem sourceHeadDeltaMajorant_le_of_scaledNorm_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (z : ℂ) {x : ℝ}
    (hz : ‖scaledArgument P.q J z‖ ≤ x) :
    sourceHeadDeltaMajorant P J z ≤
      (2 : ℝ) ^
        ((Nat.ceil (x + P.h) + 1 + P.h) * P.LzeroPlusOne) := by
  unfold sourceHeadDeltaMajorant
  have hceil :
      Nat.ceil (‖scaledArgument P.q J z‖ + P.h) ≤
        Nat.ceil (x + P.h) :=
    Nat.ceil_mono (add_le_add_left hz P.h)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (Nat.mul_le_mul_right P.LzeroPlusOne
      (Nat.add_le_add_right (Nat.add_le_add_right hceil 1) P.h))

/-- The powered head Delta factor of every corrected state is bounded by the
uniform head envelope. -/
theorem norm_state_poweredDeltaHasseEval_le_sourceHeadDeltaMajorant
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (lambda : LevelIndex P J) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    ‖poweredDeltaHasseEval P.h
        ((coordinatesForState state).deltaIndex lambda + 1) (m 0)
        (scaledArgument P.q J z + (coordinatesForState state).shift lambda)‖ ≤
      sourceHeadDeltaMajorant P J z := by
  refine (norm_poweredDeltaHasseEval_le_two_pow P.h
    ((coordinatesForState state).deltaIndex lambda + 1) (m 0)
    (scaledArgument P.q J z +
      (coordinatesForState state).shift lambda)).trans ?_
  unfold sourceHeadDeltaMajorant
  have hnorm :
      ‖scaledArgument P.q J z +
          ((coordinatesForState state).shift lambda : ℂ)‖ ≤
        ‖scaledArgument P.q J z‖ + P.h := by
    calc
      ‖scaledArgument P.q J z +
          ((coordinatesForState state).shift lambda : ℂ)‖ ≤
          ‖scaledArgument P.q J z‖ +
            ‖((coordinatesForState state).shift lambda : ℂ)‖ :=
        norm_add_le _ _
      _ = ‖scaledArgument P.q J z‖ +
            (coordinatesForState state).shift lambda := by
        rw [Complex.norm_natCast]
      _ ≤ ‖scaledArgument P.q J z‖ + P.h := by
        have hs :
            ((coordinatesForState state).shift lambda : ℝ) ≤ P.h := by
          exact_mod_cast Nat.le_of_lt (state_shift_lt_h P state lambda)
        exact add_le_add_right hs _
  have hceil :
      Nat.ceil ‖scaledArgument P.q J z +
          ((coordinatesForState state).shift lambda : ℂ)‖ ≤
        Nat.ceil (‖scaledArgument P.q J z‖ + P.h) :=
    Nat.ceil_mono hnorm
  have hpower := state_deltaPower_le P state lambda
  have hexp :
      (Nat.ceil ‖scaledArgument P.q J z +
          ((coordinatesForState state).shift lambda : ℂ)‖ + 1 + P.h) *
          ((coordinatesForState state).deltaIndex lambda + 1) ≤
        (Nat.ceil (‖scaledArgument P.q J z‖ + P.h) + 1 + P.h) *
          P.LzeroPlusOne :=
    Nat.mul_le_mul (Nat.add_le_add_right (Nat.add_le_add_right hceil 1) P.h)
      hpower
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp

/-- A closed Delta-factor envelope for every multi-index of total weight at
most `S`. -/
def sourceDeltaFactorMajorant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (z : ℂ) (S : ℕ) : ℝ :=
  sourceHeadDeltaMajorant P J z * (sourceOldDeltaBaseNat P : ℝ) ^ S

theorem sourceDeltaFactorMajorant_le_of_scaledNorm_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (z : ℂ) (S : ℕ) {x : ℝ}
    (hz : ‖scaledArgument P.q J z‖ ≤ x) :
    sourceDeltaFactorMajorant P J z S ≤
      (2 : ℝ) ^
          ((Nat.ceil (x + P.h) + 1 + P.h) * P.LzeroPlusOne) *
        (sourceOldDeltaBaseNat P : ℝ) ^ S := by
  unfold sourceDeltaFactorMajorant
  exact mul_le_mul_of_nonneg_right
    (sourceHeadDeltaMajorant_le_of_scaledNorm_le P J z hz)
    (pow_nonneg (by positivity) _)

theorem sourceOldDeltaBaseNat_one_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    (1 : ℝ) ≤ sourceOldDeltaBaseNat P := by
  unfold sourceOldDeltaBaseNat
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le
    (P.Bsrc * ((∑ r : Fin oldRank, P.LiZero r) + P.LlastZero)))

/-- The product of all ordinary old-coordinate Delta factors consumes only
the total derivative budget, not one copy of the budget per coordinate. -/
theorem norm_state_oldDeltaProduct_le_sourceOldDeltaBase_pow
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc)
    (lambda : LevelIndex P J) (m : VDPLMultiIndex (oldRank + 1))
    {S : ℕ} (hm : VDPLMultiIndex.weight m ≤ S) :
    ‖∏ r : Fin oldRank, simpleDeltaEval (m r.succ)
        ((bLast : ℂ) * (coordinatesForState state).oldExponent lambda r -
          (b r : ℂ) * (coordinatesForState state).lastExponent lambda)‖ ≤
      (sourceOldDeltaBaseNat P : ℝ) ^ S := by
  have hsum : (∑ r : Fin oldRank, m r.succ) ≤ S := by
    have hdecomp :
        VDPLMultiIndex.weight m = m 0 + ∑ r : Fin oldRank, m r.succ := by
      simp only [VDPLMultiIndex.weight, Fin.sum_univ_succ]
    omega
  calc
    ‖∏ r : Fin oldRank, simpleDeltaEval (m r.succ)
        ((bLast : ℂ) * (coordinatesForState state).oldExponent lambda r -
          (b r : ℂ) * (coordinatesForState state).lastExponent lambda)‖ =
        ∏ r : Fin oldRank, ‖simpleDeltaEval (m r.succ)
          ((bLast : ℂ) * (coordinatesForState state).oldExponent lambda r -
            (b r : ℂ) * (coordinatesForState state).lastExponent lambda)‖ := by
      rw [norm_prod]
    _ ≤ ∏ r : Fin oldRank,
          (sourceOldDeltaBaseNat P : ℝ) ^ (m r.succ) := by
      exact Finset.prod_le_prod
        (fun r _hr ↦ norm_nonneg (simpleDeltaEval (m r.succ)
          ((bLast : ℂ) * (coordinatesForState state).oldExponent lambda r -
            (b r : ℂ) * (coordinatesForState state).lastExponent lambda)))
        (fun r _hr ↦ norm_state_simpleDeltaEval_le_sourceOldDeltaBase_pow
          P state b bLast hb hbLast lambda m r)
    _ = (sourceOldDeltaBaseNat P : ℝ) ^
          (∑ r : Fin oldRank, m r.succ) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ (sourceOldDeltaBaseNat P : ℝ) ^ S :=
      pow_le_pow_right₀ (sourceOldDeltaBaseNat_one_le P) hsum

/-- Every individual source Delta factor is bounded by the closed envelope. -/
theorem norm_state_auxiliaryFactor_le_sourceDeltaFactorMajorant
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc)
    (lambda : LevelIndex P J) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) {S : ℕ}
    (hm : VDPLMultiIndex.weight m ≤ S) :
    ‖auxiliaryFactor (coordinatesForState state) P.h b bLast lambda
        (scaledArgument P.q J z) m‖ ≤
      sourceDeltaFactorMajorant P J z S := by
  unfold auxiliaryFactor sourceDeltaFactorMajorant
  rw [norm_mul]
  exact mul_le_mul
    (norm_state_poweredDeltaHasseEval_le_sourceHeadDeltaMajorant
      P state lambda z m)
    (norm_state_oldDeltaProduct_le_sourceOldDeltaBase_pow
      P state b bLast hb hbLast lambda m hm)
    (norm_nonneg _)
    (pow_nonneg (by norm_num) _)

theorem sourceDeltaFactorMajorant_nonneg {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (z : ℂ) (S : ℕ) :
    0 ≤ sourceDeltaFactorMajorant P J z S := by
  unfold sourceDeltaFactorMajorant sourceHeadDeltaMajorant
  exact mul_nonneg (pow_nonneg (by norm_num) _)
    (pow_nonneg (by positivity) _)

/-- The exact finite-sum Delta majorant of the canonical corrected-state
majorants is bounded by a completely explicit closed form. -/
theorem deltaMajorant_le_closedForm {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) {S : ℕ}
    (hm : VDPLMultiIndex.weight m ≤ S) :
    (stateSourceMajorants P state b bLast z m).deltaMajorant ≤
      (initialSupportBound P : ℝ) * sourceDeltaFactorMajorant P J z S := by
  unfold stateSourceMajorants exactSourceMajorants
  dsimp only
  calc
    ∑ lambda ∈ state.support,
        ‖auxiliaryFactor (coordinatesForState state) P.h b bLast lambda
          (scaledArgument P.q J z) m‖ ≤
        ∑ _lambda ∈ state.support, sourceDeltaFactorMajorant P J z S := by
      apply Finset.sum_le_sum
      intro lambda _hlambda
      exact norm_state_auxiliaryFactor_le_sourceDeltaFactorMajorant
        P state b bLast hb hbLast lambda z m hm
    _ = (state.support.card : ℝ) * sourceDeltaFactorMajorant P J z S := by
      simp
    _ ≤ (initialSupportBound P : ℝ) * sourceDeltaFactorMajorant P J z S := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast state_support_card_le_initialSupportBound P state)
        (sourceDeltaFactorMajorant_nonneg P J z S)

theorem norm_gamma_le_initialSides {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hdominant : ∀ r, (b r).natAbs ≤ bLast.natAbs)
    (lambda : LevelIndex P J) (r : Fin oldRank) :
    ‖gamma (coordinatesForState state) b bLast lambda r‖ ≤
      (P.LiZero r + P.LlastZero : ℕ) := by
  unfold gamma
  calc
    ‖((coordinatesForState state).oldExponent lambda r : ℂ) -
        (b r : ℂ) * ((coordinatesForState state).lastExponent lambda : ℂ) /
          (bLast : ℂ)‖ ≤
        ‖((coordinatesForState state).oldExponent lambda r : ℂ)‖ +
          ‖(b r : ℂ) *
            ((coordinatesForState state).lastExponent lambda : ℂ) /
              (bLast : ℂ)‖ := norm_sub_le _ _
    _ = ((coordinatesForState state).oldExponent lambda r : ℝ) +
          (‖(b r : ℂ) / (bLast : ℂ)‖ *
            (coordinatesForState state).lastExponent lambda) := by
      rw [show (b r : ℂ) *
          ((coordinatesForState state).lastExponent lambda : ℂ) /
            (bLast : ℂ) =
          ((b r : ℂ) / (bLast : ℂ)) *
            (coordinatesForState state).lastExponent lambda by ring]
      rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    _ ≤ (P.LiZero r : ℝ) + P.LlastZero := by
      have hratio := norm_intCast_div_intCast_le_one_of_dominates
        hbLast (hdominant r)
      have hlast0 : 0 ≤
          ((coordinatesForState state).lastExponent lambda : ℝ) := by positivity
      have hprod :
          ‖(b r : ℂ) / (bLast : ℂ)‖ *
              ((coordinatesForState state).lastExponent lambda : ℝ) ≤
            1 * P.LlastZero := by
        exact mul_le_mul hratio (by exact_mod_cast
          state_lastExponent_le_initial P state lambda) hlast0 (by norm_num)
      have hold :
          ((coordinatesForState state).oldExponent lambda r : ℝ) ≤
            P.LiZero r := by
        exact_mod_cast state_oldExponent_le_initial P state lambda r
      linarith
    _ = ((P.LiZero r + P.LlastZero : ℕ) : ℝ) := by norm_num

theorem norm_modifiedRate_le_sourceRateBound {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hdominant : ∀ r, (b r).natAbs ≤ bLast.natAbs)
    (lambda : LevelIndex P J) :
    ‖modifiedRate (coordinatesForState state) b bLast (oldLog P) lambda‖ ≤
      sourceRateBound P := by
  unfold modifiedRate sourceRateBound
  calc
    ‖∑ r, gamma (coordinatesForState state) b bLast lambda r * oldLog P r‖ ≤
        ∑ r, ‖gamma (coordinatesForState state) b bLast lambda r *
          oldLog P r‖ := norm_sum_le _ _
    _ ≤ ∑ r, ((P.LiZero r + P.LlastZero : ℕ) : ℝ) *
          ‖oldLog P r‖ := by
      apply Finset.sum_le_sum
      intro r _hr
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_gamma_le_initialSides P state b hbLast hdominant lambda r)
        (norm_nonneg _)

/-- The amplification sum has the same `q^{-J}` decay as the last side of
the level box.  This is the form needed on contours whose radii grow like
`q^J`. -/
theorem amplificationMajorant_le_scaledClosedForm {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    (stateSourceMajorants P state b bLast z m).amplificationMajorant ≤
      (initialSupportBound P : ℝ) *
        (P.qInvPow J * P.LlastZero) * ‖z‖ := by
  unfold stateSourceMajorants exactSourceMajorants
  dsimp only
  calc
    ∑ lambda ∈ state.support,
        ‖((coordinatesForState state).lastExponent lambda : ℂ) /
          (bLast : ℂ)‖ * ‖z‖ ≤
        ∑ _lambda ∈ state.support,
          ((P.qInvPow J * P.LlastZero) * ‖z‖) := by
      apply Finset.sum_le_sum
      intro lambda _hlambda
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
      rw [norm_div, Complex.norm_natCast, Complex.norm_intCast]
      have hb : (1 : ℝ) ≤ |(bLast : ℝ)| := by
        have hbNat : 0 < bLast.natAbs := Int.natAbs_pos.mpr hbLast
        have hbCast : (1 : ℝ) ≤ bLast.natAbs := by exact_mod_cast hbNat
        simpa only [Nat.cast_natAbs, Int.cast_abs] using hbCast
      exact (div_le_self (by positivity) hb).trans
        (state_lastExponent_cast_le_scaled P state lambda)
    _ = (state.support.card : ℝ) *
          ((P.qInvPow J * P.LlastZero) * ‖z‖) := by simp
    _ ≤ (initialSupportBound P : ℝ) *
          (P.qInvPow J * P.LlastZero) * ‖z‖ := by
      have hcard : (state.support.card : ℝ) ≤ initialSupportBound P := by
        exact_mod_cast state_support_card_le_initialSupportBound P state
      calc
        (state.support.card : ℝ) *
            ((P.qInvPow J * P.LlastZero) * ‖z‖) ≤
          (initialSupportBound P : ℝ) *
            ((P.qInvPow J * P.LlastZero) * ‖z‖) :=
          mul_le_mul_of_nonneg_right hcard
            (mul_nonneg
              (mul_nonneg (P.qInvPow_pos J).le (by positivity))
              (norm_nonneg z))
        _ = (initialSupportBound P : ℝ) *
            (P.qInvPow J * P.LlastZero) * ‖z‖ := by ring

theorem amplificationMajorant_le_closedForm {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    (stateSourceMajorants P state b bLast z m).amplificationMajorant ≤
      (initialSupportBound P : ℝ) * P.LlastZero * ‖z‖ := by
  unfold stateSourceMajorants exactSourceMajorants
  dsimp only
  calc
    ∑ lambda ∈ state.support,
        ‖((coordinatesForState state).lastExponent lambda : ℂ) /
          (bLast : ℂ)‖ * ‖z‖ ≤
        ∑ _lambda ∈ state.support,
          ((P.LlastZero : ℝ) * ‖z‖) := by
      apply Finset.sum_le_sum
      intro lambda _hlambda
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
      rw [norm_div, Complex.norm_natCast, Complex.norm_intCast]
      have hb : (1 : ℝ) ≤ |(bLast : ℝ)| := by
        have hbNat : 0 < bLast.natAbs := Int.natAbs_pos.mpr hbLast
        have hbCast : (1 : ℝ) ≤ bLast.natAbs := by exact_mod_cast hbNat
        simpa only [Nat.cast_natAbs, Int.cast_abs] using hbCast
      have hbpos : 0 < |(bLast : ℝ)| := lt_of_lt_of_le zero_lt_one hb
      rw [div_le_iff₀ hbpos]
      have hlast :
          ((coordinatesForState state).lastExponent lambda : ℝ) ≤
            P.LlastZero := by
        exact_mod_cast state_lastExponent_le_initial P state lambda
      nlinarith [abs_nonneg (bLast : ℝ)]
    _ = (state.support.card : ℝ) *
          ((P.LlastZero : ℝ) * ‖z‖) := by simp
    _ ≤ (initialSupportBound P : ℝ) * P.LlastZero * ‖z‖ := by
      have hcard : (state.support.card : ℝ) ≤ initialSupportBound P := by
        exact_mod_cast state_support_card_le_initialSupportBound P state
      calc
        (state.support.card : ℝ) * ((P.LlastZero : ℝ) * ‖z‖) ≤
            (initialSupportBound P : ℝ) *
              ((P.LlastZero : ℝ) * ‖z‖) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg (by positivity)
            (norm_nonneg z))
        _ = (initialSupportBound P : ℝ) * P.LlastZero * ‖z‖ := by ring

theorem exponentialMajorant_le_closedForm {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hdominant : ∀ r, (b r).natAbs ≤ bLast.natAbs)
    (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) :
    (stateSourceMajorants P state b bLast z m).exponentialMajorant ≤
      (initialSupportBound P : ℝ) *
        Real.exp (sourceRateBound P * ‖z‖) := by
  unfold stateSourceMajorants exactSourceMajorants
  dsimp only
  calc
    ∑ lambda ∈ state.support,
        Real.exp
          (‖modifiedRate (coordinatesForState state) b bLast (oldLog P) lambda‖ *
            ‖z‖) ≤
        ∑ _lambda ∈ state.support,
          Real.exp (sourceRateBound P * ‖z‖) := by
      apply Finset.sum_le_sum
      intro lambda _hlambda
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right
        (norm_modifiedRate_le_sourceRateBound P state b hbLast hdominant lambda)
        (norm_nonneg z)
    _ = (state.support.card : ℝ) *
          Real.exp (sourceRateBound P * ‖z‖) := by simp
    _ ≤ (initialSupportBound P : ℝ) *
          Real.exp (sourceRateBound P * ‖z‖) := by
      exact mul_le_mul_of_nonneg_right (by
        exact_mod_cast state_support_card_le_initialSupportBound P state)
        (Real.exp_pos _).le

#print axioms levelIndex_card_le_initialSupportBound
#print axioms deltaMajorant_le_closedForm
#print axioms norm_modifiedRate_le_sourceRateBound
#print axioms amplificationMajorant_le_scaledClosedForm
#print axioms amplificationMajorant_le_closedForm
#print axioms exponentialMajorant_le_closedForm

end Erdos240.BakerSourceMajorantClosedForm
