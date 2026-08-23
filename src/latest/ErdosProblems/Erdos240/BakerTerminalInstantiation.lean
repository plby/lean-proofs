/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerFinalZeroCount
import ErdosProblems.Erdos240.BakerInduction
import ErdosProblems.Erdos240.BakerSourceState

/-!
# Instantiating the terminal van der Poorten--Loxton equation

This file is the type-level bridge between the coefficient state propagated by
source Lemma 6 and the final equation-(13) zero count.  In the rational-prime
specialization the old logarithms are already indexed by `Fin oldRank`, so the
`Fintype.equivFin` reindexing in `BakerFinalZeroCount.terminalBox` is the
identity.  Consequently its terminal box is exactly
`BakerSourceState.levelBoxShape`.

The source chooses the last level with the *real* side
`LlastZeroScale < q^N`.  This is not a cosmetic endpoint: it makes the
distinguished last exponent side a singleton, which is why equation (13) on
p. 53 has no remaining sum over `lambda_n`.  The lemmas below expose that fact
and restrict the padded Lemma-6 state to its genuine active side lengths before
the analytic vanishing equations are identified with `TerminalEquation13`.
-/

noncomputable section

namespace Erdos240.BakerTerminalInstantiation

open Erdos240
open Erdos240.BakerAuxiliary
open Erdos240.BakerSourceState
open Erdos240.BakerFinalZeroCount

private theorem lambdaBox_ext {oldRank : ℕ} {L : BoxShape oldRank}
    {a b : LambdaBox L}
    (hshift : a.shiftIndex = b.shiftIndex)
    (hdelta : a.deltaIndexFin = b.deltaIndexFin)
    (hold : a.oldExponentFin = b.oldExponentFin)
    (hlast : a.lastExponentFin = b.lastExponentFin) : a = b := by
  cases a
  cases b
  simp_all

/-- The exact active coefficient box carried by a Lemma-6 state.  The state
is stored in a canonical padded box, but its Delta powers and nonzero support
use these genuine (possibly smaller) sides. -/
def activeBox {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) : BoxShape oldRank where
  shiftMax := P.LminusOne
  deltaMax := P.Lzero
  oldMax := state.oldSide
  lastMax := state.lastSide

/-- Inclusion of the genuine active box into the canonical padded level box. -/
def activeIndexToLevel {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) :
    LambdaBox (activeBox state) → LevelIndex P N :=
  fun lambda ↦
    { shiftIndex := lambda.shiftIndex
      deltaIndexFin := lambda.deltaIndexFin
      oldExponentFin := fun r ↦
        ⟨lambda.oldExponent r,
          lt_of_lt_of_le (lambda.oldExponentFin r).isLt
            (Nat.succ_le_succ (state.oldSide_le r))⟩
      lastExponentFin :=
        ⟨lambda.lastExponent,
          lt_of_lt_of_le lambda.lastExponentFin.isLt
            (Nat.succ_le_succ state.lastSide_le)⟩ }

@[simp] theorem activeIndexToLevel_shift {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (lambda : LambdaBox (activeBox state)) :
    (activeIndexToLevel state lambda).shift = lambda.shift := rfl

@[simp] theorem activeIndexToLevel_deltaIndex {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (lambda : LambdaBox (activeBox state)) :
    (activeIndexToLevel state lambda).deltaIndex = lambda.deltaIndex := rfl

@[simp] theorem activeIndexToLevel_oldExponent {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (lambda : LambdaBox (activeBox state))
    (r : Fin oldRank) :
    (activeIndexToLevel state lambda).oldExponent r =
      lambda.oldExponent r := rfl

@[simp] theorem activeIndexToLevel_lastExponent {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (lambda : LambdaBox (activeBox state)) :
    (activeIndexToLevel state lambda).lastExponent =
      lambda.lastExponent := rfl

/-- Restrict the padded integral coefficients to the actual state box. -/
def activeCoefficient {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) : LambdaBox (activeBox state) → ℂ :=
  fun lambda ↦ (state.coeff (activeIndexToLevel state lambda) : ℂ)

/-- Every nonzero padded coefficient is inside the actual state box, so
restriction to that box preserves nontriviality. -/
theorem activeCoefficient_ne_zero {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) : activeCoefficient state ≠ 0 := by
  obtain ⟨lambda, hlambda⟩ := state.exists_coeff_ne_zero
  obtain ⟨hold, hlast⟩ := state.coeff_ne_zero_inside lambda hlambda
  let active : LambdaBox (activeBox state) :=
    { shiftIndex := lambda.shiftIndex
      deltaIndexFin := lambda.deltaIndexFin
      oldExponentFin := fun r ↦
        ⟨lambda.oldExponent r, Nat.lt_succ_of_le (hold r)⟩
      lastExponentFin :=
        ⟨lambda.lastExponent, Nat.lt_succ_of_le hlast⟩ }
  intro hzero
  have hentry := congrFun hzero active
  have hinclusion : activeIndexToLevel state active = lambda := by
    rcases lambda with ⟨shift, delta, old, last⟩
    rfl
  simp only [activeCoefficient, Pi.zero_apply, hinclusion] at hentry
  exact hlambda (by exact_mod_cast hentry)

/-- The source old sides, reindexed by the canonical `Fintype.equivFin`
used by the generic final-zero module. -/
def terminalOldSide {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) :
    Fin (Fintype.card (Fin oldRank)) → ℕ :=
  fun r ↦ state.oldSide ((Fintype.equivFin (Fin oldRank)).symm r)

/-- Inclusion of the terminal active box (whose last side is definitionally
zero) into the padded Lemma-6 level box. -/
def terminalActiveIndexToLevel {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) :
    LambdaBox (activeTerminalBox P (terminalOldSide state)) → LevelIndex P N :=
  fun lambda ↦
    { shiftIndex := lambda.shiftIndex
      deltaIndexFin := lambda.deltaIndexFin
      oldExponentFin := fun r ↦
        ⟨lambda.oldExponent (Fintype.equivFin (Fin oldRank) r), by
          have hlt :=
            (lambda.oldExponentFin (Fintype.equivFin (Fin oldRank) r)).isLt
          have hs : terminalOldSide state
              (Fintype.equivFin (Fin oldRank) r) = state.oldSide r := by
            exact congrArg state.oldSide
              ((Fintype.equivFin (Fin oldRank)).symm_apply_apply r)
          apply lt_of_lt_of_le hlt
          change terminalOldSide state (Fintype.equivFin (Fin oldRank) r) + 1 ≤
            (levelBoxShape P N).oldMax r + 1
          rw [hs]
          exact Nat.succ_le_succ (state.oldSide_le r)⟩
      lastExponentFin :=
        ⟨0, by simpa using Nat.succ_pos (levelBoxShape P N).lastMax⟩ }

@[simp] theorem terminalActiveIndexToLevel_shift {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N)
    (lambda : LambdaBox (activeTerminalBox P (terminalOldSide state))) :
    (terminalActiveIndexToLevel state lambda).shift = lambda.shift := rfl

@[simp] theorem terminalActiveIndexToLevel_deltaIndex {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N)
    (lambda : LambdaBox (activeTerminalBox P (terminalOldSide state))) :
    (terminalActiveIndexToLevel state lambda).deltaIndex =
      lambda.deltaIndex := rfl

@[simp] theorem terminalActiveIndexToLevel_oldExponent {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N)
    (lambda : LambdaBox (activeTerminalBox P (terminalOldSide state)))
    (r : Fin oldRank) :
    (terminalActiveIndexToLevel state lambda).oldExponent r =
      lambda.oldExponent (Fintype.equivFin (Fin oldRank) r) := rfl

@[simp] theorem terminalActiveIndexToLevel_lastExponent {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N)
    (lambda : LambdaBox (activeTerminalBox P (terminalOldSide state))) :
    (terminalActiveIndexToLevel state lambda).lastExponent = 0 := rfl

/-- The actual coefficient family consumed by the final zero count. -/
def terminalActiveCoefficient {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) :
    LambdaBox (activeTerminalBox P (terminalOldSide state)) → ℂ :=
  fun lambda ↦
    (state.coeff (terminalActiveIndexToLevel state lambda) : ℂ)

/-- The strict real terminal endpoint collapses the actual last side of any
terminal Lemma-6 state. -/
theorem activeLastSide_eq_zero {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N)
    (hterminal : P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ)) :
    state.lastSide = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc
    state.lastSide ≤ (levelBoxShape P N).lastMax := state.lastSide_le
    _ = 0 := levelBoxShape_lastMax_eq_zero_of_scale_lt_qpow P N hterminal

/-- Restricting a terminal state to its actual old sides and singleton last
side preserves its nonzero coefficient. -/
theorem terminalActiveCoefficient_ne_zero {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N)
    (hterminal : P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ)) :
    terminalActiveCoefficient state ≠ 0 := by
  obtain ⟨lambda, hlambda⟩ := state.exists_coeff_ne_zero
  obtain ⟨hold, hlast⟩ := state.coeff_ne_zero_inside lambda hlambda
  have hlastSide := activeLastSide_eq_zero state hterminal
  have hlambdaLast : lambda.lastExponent = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa only [hlastSide] using hlast
  let active : LambdaBox (activeTerminalBox P (terminalOldSide state)) :=
    { shiftIndex := lambda.shiftIndex
      deltaIndexFin := lambda.deltaIndexFin
      oldExponentFin := fun r ↦
        ⟨lambda.oldExponent ((Fintype.equivFin (Fin oldRank)).symm r), by
          simpa only [activeTerminalBox, terminalOldSide] using
            Nat.lt_succ_of_le (hold ((Fintype.equivFin (Fin oldRank)).symm r))⟩
      lastExponentFin := activeTerminalLastZero P (terminalOldSide state) }
  intro hzero
  have hentry := congrFun hzero active
  have hinclusion : terminalActiveIndexToLevel state active = lambda := by
    rcases lambda with ⟨shift, delta, old, last⟩
    simp only [LambdaBox.lastExponent] at hlambdaLast
    apply @lambdaBox_ext oldRank (levelBoxShape P N)
      (terminalActiveIndexToLevel state active)
      ⟨shift, delta, old, last⟩ rfl rfl
    · funext r
      apply Fin.ext
      exact congrArg (fun s : Fin oldRank ↦ (old s : ℕ))
        ((Fintype.equivFin (Fin oldRank)).symm_apply_apply r)
    · apply Fin.ext
      exact hlambdaLast.symm
  simp only [terminalActiveCoefficient, Pi.zero_apply, hinclusion] at hentry
  exact hlambda (by exact_mod_cast hentry)

/-! ## Polynomial identities in the terminal equation -/

/-- Hasse differentiation commutes with translation.  This is the precise
identity which turns the first Delta factor in source equation (13) into a
Hasse derivative of the shifted one-variable terminal polynomial. -/
theorem hasseDeriv_taylor_eval (Q : Polynomial ℂ) (s z : ℂ) (m : ℕ) :
    (Polynomial.hasseDeriv m (Polynomial.taylor s Q)).eval z =
      (Polynomial.hasseDeriv m Q).eval (z + s) := by
  rw [← Polynomial.taylor_coeff, ← Polynomial.taylor_coeff,
    Polynomial.taylor_taylor]

/-- Mapping the rational powered Delta polynomial to `ℂ` commutes with its
normalized derivative and evaluation. -/
theorem poweredDeltaComplex_hasseDeriv_eval (h L m : ℕ) (z : ℂ) :
    ((poweredDeltaComplex h L).hasseDeriv m).eval z =
      Erdos240.BakerLemma3.poweredDeltaHasseEval h L m z := by
  have hmap :
      Polynomial.hasseDeriv m
          ((DeltaPower.poweredDelta h L).map (algebraMap ℚ ℂ)) =
        (Polynomial.hasseDeriv m (DeltaPower.poweredDelta h L)).map
          (algebraMap ℚ ℂ) := by
    ext n
    simp [Polynomial.hasseDeriv_coeff]
  rw [poweredDeltaComplex, hmap]
  exact Polynomial.eval_map (algebraMap ℚ ℂ) z

/-! ## Restricting the padded state to its genuine terminal support -/

/-- The support predicate represented by the active terminal box. -/
def TerminalInside {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (lambda : LevelIndex P N) : Prop :=
  (∀ r, lambda.oldExponent r ≤ state.oldSide r) ∧
    lambda.lastExponent = 0

/-- The active terminal box is equivalent to the part of the padded source
box inside the genuine old sides and with last exponent zero. -/
def terminalActiveEquivInside {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) :
    LambdaBox (activeTerminalBox P (terminalOldSide state)) ≃
      {lambda : LevelIndex P N // TerminalInside state lambda} where
  toFun lambda := ⟨terminalActiveIndexToLevel state lambda, by
    constructor
    · intro r
      change lambda.oldExponent (Fintype.equivFin (Fin oldRank) r) ≤
        state.oldSide r
      apply Nat.le_of_lt_succ
      have hs : terminalOldSide state
          (Fintype.equivFin (Fin oldRank) r) = state.oldSide r :=
        congrArg state.oldSide
          ((Fintype.equivFin (Fin oldRank)).symm_apply_apply r)
      rw [← hs]
      exact (lambda.oldExponentFin
        (Fintype.equivFin (Fin oldRank) r)).isLt
    · rfl⟩
  invFun lambda :=
    { shiftIndex := lambda.1.shiftIndex
      deltaIndexFin := lambda.1.deltaIndexFin
      oldExponentFin := fun r ↦
        ⟨lambda.1.oldExponent ((Fintype.equivFin (Fin oldRank)).symm r), by
          simpa only [activeTerminalBox, terminalOldSide] using Nat.lt_succ_of_le
            (lambda.2.1 ((Fintype.equivFin (Fin oldRank)).symm r))⟩
      lastExponentFin := activeTerminalLastZero P (terminalOldSide state) }
  left_inv lambda := by
    apply @lambdaBox_ext (Fintype.card (Fin oldRank))
      (activeTerminalBox P (terminalOldSide state))
    · rfl
    · rfl
    · funext r
      apply Fin.ext
      exact congrArg (fun s : Fin (Fintype.card (Fin oldRank)) ↦
        (lambda.oldExponent s : ℕ))
        ((Fintype.equivFin (Fin oldRank)).apply_symm_apply r)
    · apply Fin.ext
      have hlast := lambda.lastExponentFin.isLt
      simp only [activeTerminalBox, Nat.zero_add, Nat.lt_one_iff] at hlast
      exact hlast.symm
  right_inv lambda := by
    apply Subtype.ext
    apply @lambdaBox_ext oldRank (levelBoxShape P N)
    · rfl
    · rfl
    · funext r
      apply Fin.ext
      exact congrArg (fun s : Fin oldRank ↦
        (lambda.1.oldExponent s : ℕ))
        ((Fintype.equivFin (Fin oldRank)).symm_apply_apply r)
    · apply Fin.ext
      exact lambda.2.2.symm

/-- A terminal source sum may be evaluated on the active box: every omitted
padded coefficient is zero, and `terminalActiveEquivInside` accounts for all
remaining indices exactly once. -/
theorem sum_level_eq_sum_terminalActive {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N)
    (hterminal : P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ))
    (F : LevelIndex P N → ℂ) :
    ∑ lambda, (state.coeff lambda : ℂ) * F lambda =
      ∑ lambda : LambdaBox
          (activeTerminalBox P (terminalOldSide state)),
        (state.coeff (terminalActiveIndexToLevel state lambda) : ℂ) *
          F (terminalActiveIndexToLevel state lambda) := by
  classical
  let inside : Finset (LevelIndex P N) :=
    Finset.univ.filter (TerminalInside state)
  have hrestrict :
      (∑ lambda : LevelIndex P N,
          (state.coeff lambda : ℂ) * F lambda) =
        ∑ lambda ∈ inside, (state.coeff lambda : ℂ) * F lambda := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro lambda _ hnot
    have hcoeff : state.coeff lambda = 0 := by
      by_contra hne
      obtain ⟨hold, hlast⟩ := state.coeff_ne_zero_inside lambda hne
      have hlastSide := activeLastSide_eq_zero state hterminal
      have hin : TerminalInside state lambda := by
        refine ⟨hold, ?_⟩
        apply Nat.eq_zero_of_le_zero
        simpa only [hlastSide] using hlast
      exact hnot (by simp only [inside, Finset.mem_filter,
        Finset.mem_univ, true_and]; exact hin)
    simp only [hcoeff, Int.cast_zero, zero_mul]
  rw [hrestrict]
  have hsubtype :
      (∑ lambda ∈ inside, (state.coeff lambda : ℂ) * F lambda) =
        ∑ lambda : {lambda : LevelIndex P N // TerminalInside state lambda},
          (state.coeff lambda.1 : ℂ) * F lambda.1 := by
    apply Finset.sum_subtype inside
    intro lambda
    simp only [inside, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hsubtype]
  exact Fintype.sum_equiv (terminalActiveEquivInside state)
    (fun lambda : LambdaBox
        (activeTerminalBox P (terminalOldSide state)) ↦
      (state.coeff (terminalActiveIndexToLevel state lambda) : ℂ) *
        F (terminalActiveIndexToLevel state lambda))
    (fun lambda : {lambda : LevelIndex P N // TerminalInside state lambda} ↦
      (state.coeff lambda.1 : ℂ) * F lambda.1)
    (fun _ ↦ rfl) |>.symm

/-! ## The source multi-index used in equation (13) -/

/-- The remaining Hasse order is the head coordinate; the selected row of
each equation-(14) matrix supplies the corresponding old coordinate. -/
def terminalSourceMultiIndex {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (m : ℕ)
    (row : ActiveTerminalOldExponent (terminalOldSide state)) :
    VDPLMultiIndex (oldRank + 1) :=
  Fin.cases m (fun r ↦ row (Fintype.equivFin (Fin oldRank) r))

@[simp] theorem terminalSourceMultiIndex_zero {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (m : ℕ)
    (row : ActiveTerminalOldExponent (terminalOldSide state)) :
    terminalSourceMultiIndex state m row 0 = m := rfl

@[simp] theorem terminalSourceMultiIndex_succ {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (m : ℕ)
    (row : ActiveTerminalOldExponent (terminalOldSide state))
    (r : Fin oldRank) :
    terminalSourceMultiIndex state m row r.succ =
      row (Fintype.equivFin (Fin oldRank) r) := rfl

theorem weight_terminalSourceMultiIndex {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (m : ℕ)
    (row : ActiveTerminalOldExponent (terminalOldSide state)) :
    VDPLMultiIndex.weight (terminalSourceMultiIndex state m row) =
      m + ∑ r : Fin oldRank,
        (row (Fintype.equivFin (Fin oldRank) r) : ℕ) := by
  simp only [VDPLMultiIndex.weight, Fin.sum_univ_succ,
    terminalSourceMultiIndex_zero, terminalSourceMultiIndex_succ]

/-- Every row used in the terminal tensor equation stays within the
source derivative budget.  The head order uses at most one eighth of the
level scale, and the sum of all old-coordinate rows uses at most another
one eighth. -/
theorem weight_terminalSourceMultiIndex_le {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (m : ℕ)
    (hm : m < terminalMultiplicity P N)
    (row : ActiveTerminalOldExponent (terminalOldSide state)) :
    VDPLMultiIndex.weight (terminalSourceMultiIndex state m row) ≤
      P.Slevel N := by
  have hmNat : m ≤ ⌊P.levelScale N / 8⌋₊ := by
    simpa only [terminalMultiplicity] using Nat.le_of_lt_succ hm
  have hmReal : (m : ℝ) ≤ P.levelScale N / 8 := by
    calc
      (m : ℝ) ≤ (⌊P.levelScale N / 8⌋₊ : ℕ) := by exact_mod_cast hmNat
      _ ≤ P.levelScale N / 8 :=
        Nat.floor_le (div_nonneg (P.levelScale_pos N).le (by norm_num))
  let unit : ℝ :=
    (8 * P.rank : ℝ)⁻¹ * P.k ^ (1 - P.sigma) *
      P.Omega * Real.log P.OmegaOld
  have hunit : 0 ≤ unit := by
    dsimp only [unit]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (by positivity))
          (Real.rpow_pos_of_pos P.k_pos _).le)
        P.Omega_pos.le)
      P.log_OmegaOld_pos.le
  have hside (r : Fin oldRank) :
      (((row (Fintype.equivFin (Fin oldRank) r) : ℕ) : ℝ)) ≤
        P.qInvPow N * unit := by
    have hterminalSide : terminalOldSide state
        (Fintype.equivFin (Fin oldRank) r) = state.oldSide r := by
      exact congrArg state.oldSide
        ((Fintype.equivFin (Fin oldRank)).symm_apply_apply r)
    have hrowNat :
        (row (Fintype.equivFin (Fin oldRank) r) : ℕ) ≤ state.oldSide r := by
      rw [← hterminalSide]
      exact Nat.le_of_lt_succ
        (row (Fintype.equivFin (Fin oldRank) r)).isLt
    have hscale : P.LiZeroScale r ≤ unit := by
      unfold VDPLParameters.LiZeroScale
      change unit / Real.log (P.oldHeight r) ≤ unit
      exact div_le_self hunit (by
        exact (by norm_num : (1 : ℝ) ≤ 2).trans
          (P.two_le_log_oldHeight r))
    calc
      (((row (Fintype.equivFin (Fin oldRank) r) : ℕ) : ℝ)) ≤
          (state.oldSide r : ℝ) := by exact_mod_cast hrowNat
      _ ≤ (scaledExponentMax P N (P.LiZero r) : ℝ) := by
        exact_mod_cast state.oldSide_le r
      _ ≤ P.qInvPow N * (P.LiZero r : ℝ) :=
        scaledExponentMax_cast_le P N (P.LiZero r)
      _ ≤ P.qInvPow N * P.LiZeroScale r :=
        mul_le_mul_of_nonneg_left (P.LiZero_cast_le r)
          (P.qInvPow_pos N).le
      _ ≤ P.qInvPow N * unit :=
        mul_le_mul_of_nonneg_left hscale (P.qInvPow_pos N).le
  have hkpow : P.k ^ (1 - P.sigma) ≤ P.k := by
    calc
      P.k ^ (1 - P.sigma) ≤ P.k ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le P.one_le_k (by
          linarith [P.sigma_pos])
      _ = P.k := Real.rpow_one _
  have hsumReal :
      (∑ r : Fin oldRank,
        ((row (Fintype.equivFin (Fin oldRank) r) : ℕ) : ℝ)) ≤
          P.levelScale N / 8 := by
    calc
      (∑ r : Fin oldRank,
          ((row (Fintype.equivFin (Fin oldRank) r) : ℕ) : ℝ)) ≤
          ∑ _r : Fin oldRank, P.qInvPow N * unit :=
        Finset.sum_le_sum (fun r _ ↦ hside r)
      _ = (oldRank : ℝ) * (P.qInvPow N * unit) := by simp
      _ ≤ (P.rank : ℝ) * (P.qInvPow N * unit) := by
        apply mul_le_mul_of_nonneg_right
        · simp only [VDPLParameters.rank, Fintype.card_fin]
          norm_num
        · exact mul_nonneg (P.qInvPow_pos N).le hunit
      _ = P.qInvPow N * P.k ^ (1 - P.sigma) *
            P.Omega * Real.log P.OmegaOld / 8 := by
        dsimp only [unit]
        have hrank : (P.rank : ℝ) ≠ 0 := by
          exact_mod_cast P.rank_pos.ne'
        field_simp [hrank]
      _ ≤ P.qInvPow N * P.k * P.Omega *
            Real.log P.OmegaOld / 8 := by
        have hnonneg :
            0 ≤ P.qInvPow N * P.Omega * Real.log P.OmegaOld := by
          exact mul_nonneg
            (mul_nonneg (P.qInvPow_pos N).le P.Omega_pos.le)
            P.log_OmegaOld_pos.le
        nlinarith
      _ = P.levelScale N / 8 := by
        unfold VDPLParameters.levelScale
        ring
  rw [weight_terminalSourceMultiIndex]
  unfold VDPLParameters.Slevel
  apply Nat.le_floor
  push_cast
  calc
    (m : ℝ) +
        ∑ r : Fin oldRank,
          ((row (Fintype.equivFin (Fin oldRank) r) : ℕ) : ℝ) ≤
        P.levelScale N / 8 + P.levelScale N / 8 :=
      add_le_add hmReal hsumReal
    _ ≤ P.levelScale N := by
      nlinarith [P.levelScale_pos N]

/-- The terminal node and an allowed source multi-index are among the
integral-grid equations propagated by Lemma 6. -/
theorem terminal_gSource_eq_zero {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hN : 0 < N)
    (hseed : BakerInduction.IntegralSeedAtLevel P (g state b bLast) N)
    (x : TerminalNode P N) (m : ℕ)
    (row : ActiveTerminalOldExponent (terminalOldSide state))
    (hweight : VDPLMultiIndex.weight
        (terminalSourceMultiIndex state m row) ≤ P.Slevel N) :
    gSource state b bLast (terminalNodeNumerator P x : ℂ)
      (terminalSourceMultiIndex state m row) = 0 := by
  let sourceIndex := terminalSourceMultiIndex state m row
  let rankIndex := fromSourceMultiIndex P sourceIndex
  have hrankWeight : VDPLMultiIndex.weight rankIndex ≤ P.Slevel N := by
    simpa only [rankIndex, sourceIndex, weight_fromSourceMultiIndex] using
      hweight
  have hz := hseed (terminalNodeNumerator P x)
    (terminalNodeNumerator_pos P x)
    (terminalNodeNumerator_le_radius P hN x) rankIndex hrankWeight
  simpa only [g, rankIndex, sourceIndex,
    toSourceMultiIndex_fromSourceMultiIndex, Nat.cast_one, div_one] using hz

/-- Sum form of the same equation, restricted to the genuine terminal
support.  This is equation (13) before its exponential monomials and Delta
factors are separated into tensor coordinates. -/
theorem terminal_active_source_sum_eq_zero {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hN : 0 < N)
    (hterminal : P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ))
    (hseed : BakerInduction.IntegralSeedAtLevel P (g state b bLast) N)
    (x : TerminalNode P N) (m : ℕ)
    (row : ActiveTerminalOldExponent (terminalOldSide state))
    (hweight : VDPLMultiIndex.weight
        (terminalSourceMultiIndex state m row) ≤ P.Slevel N) :
    ∑ lambda : LambdaBox
        (activeTerminalBox P (terminalOldSide state)),
      (state.coeff (terminalActiveIndexToLevel state lambda) : ℂ) *
        A state b bLast (terminalActiveIndexToLevel state lambda)
          (terminalNodeNumerator P x : ℂ)
          (terminalSourceMultiIndex state m row) *
        Complex.exp
          (Erdos240.BakerLemma3.algebraicRate coordinates (oldLog P) (lastLog P)
            (terminalActiveIndexToLevel state lambda) *
              (terminalNodeNumerator P x : ℂ)) = 0 := by
  have hz := terminal_gSource_eq_zero state b bLast hN hseed x m row hweight
  rw [gSource, gWithLogs_eq_sum] at hz
  have hwhole :
      ∑ lambda : LevelIndex P N,
        (state.coeff lambda : ℂ) *
          (A state b bLast lambda (terminalNodeNumerator P x : ℂ)
              (terminalSourceMultiIndex state m row) *
            Complex.exp
              (Erdos240.BakerLemma3.algebraicRate coordinates
                (oldLog P) (lastLog P) lambda *
                  (terminalNodeNumerator P x : ℂ))) = 0 := by
    simpa only [mul_assoc] using hz
  rw [sum_level_eq_sum_terminalActive state hterminal
    (fun lambda ↦
      A state b bLast lambda (terminalNodeNumerator P x : ℂ)
          (terminalSourceMultiIndex state m row) *
        Complex.exp
          (Erdos240.BakerLemma3.algebraicRate coordinates (oldLog P) (lastLog P) lambda *
            (terminalNodeNumerator P x : ℂ)))] at hwhole
  simpa only [mul_assoc] using hwhole

/-! ## The ordinary-Delta matrices in equation (14) -/

/-- The prime-power monomial attached to one old exponent column. -/
def terminalColumnScale {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (x : TerminalNode P N)
    (r : Fin (Fintype.card (Fin oldRank)))
    (j : Fin (terminalOldSide state r + 1)) : ℂ :=
  (P.old ((Fintype.equivFin (Fin oldRank)).symm r) : ℂ) ^
    ((j : ℕ) * terminalNodeNumerator P x)

theorem terminalColumnScale_ne_zero {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (x : TerminalNode P N)
    (r : Fin (Fintype.card (Fin oldRank)))
    (j : Fin (terminalOldSide state r + 1)) :
    terminalColumnScale state x r j ≠ 0 := by
  apply pow_ne_zero
  exact_mod_cast
    (P.old_prime ((Fintype.equivFin (Fin oldRank)).symm r)).ne_zero

/-- The literal ordinary-Delta coordinate matrix from source equation (14),
including its nonzero prime-power column scaling. -/
def terminalEliminationFamily {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (bLast : ℤ) (hbLast : bLast ≠ 0)
    (x : TerminalNode P N)
    (r : Fin (Fintype.card (Fin oldRank))) :
    EliminationFamily (terminalOldSide state r) :=
  EliminationFamily.ofOrdinaryDelta (terminalOldSide state r) (bLast : ℂ)
    (by exact_mod_cast hbLast) (terminalColumnScale state x r)
    (terminalColumnScale_ne_zero state x r)

@[simp] theorem terminalEliminationFamily_matrix_apply {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (bLast : ℤ) (hbLast : bLast ≠ 0)
    (x : TerminalNode P N)
    (r : Fin (Fintype.card (Fin oldRank)))
    (i j : Fin (terminalOldSide state r + 1)) :
    (terminalEliminationFamily state bLast hbLast x r).matrix i j =
      (ordinaryDeltaComplex (i : ℕ)).eval ((bLast : ℂ) * (j : ℕ)) *
        terminalColumnScale state x r j := by
  exact EliminationFamily.ofOrdinaryDelta_matrix_apply
    (terminalOldSide state r) (bLast : ℂ) (by exact_mod_cast hbLast)
      (terminalColumnScale state x r)
      (terminalColumnScale_ne_zero state x r) i j

/-- Complex evaluation of the ordinary Delta polynomial is the source's
`simpleDeltaEval`. -/
theorem ordinaryDeltaComplex_eval (m : ℕ) (z : ℂ) :
    (ordinaryDeltaComplex m).eval z =
      Erdos240.BakerLemma3.simpleDeltaEval m z := by
  exact Polynomial.eval_map (algebraMap ℚ ℂ) z

/-- Expanding the terminal polynomial and then taking its normalized
derivative gives exactly the head Delta factors in source equation (13). -/
theorem hasseDeriv_activeTerminalPolynomial_eval
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N)
    (old : ActiveTerminalOldExponent (terminalOldSide state))
    (m : ℕ) (z : ℂ) :
    (Polynomial.hasseDeriv m
        (activeTerminalPolynomial P (terminalOldSide state)
          (terminalActiveCoefficient state) old)).eval z =
      ∑ d : Fin (P.Lzero + 1), ∑ s : Fin (P.LminusOne + 1),
        terminalActiveCoefficient state
            ⟨s, d, old,
              activeTerminalLastZero P (terminalOldSide state)⟩ *
          Erdos240.BakerLemma3.poweredDeltaHasseEval P.h (d + 1) m
            (z + (s : ℂ)) := by
  rw [activeTerminalPolynomial, map_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_smul, Polynomial.eval_smul, smul_eq_mul,
    hasseDeriv_taylor_eval,
    poweredDeltaComplex_hasseDeriv_eval]

/-! ## Identifying the literal source summand with the tensor summand -/

/-- At a terminal active index, the source Delta factor is the head Hasse
factor at `l/q^N` times the ordinary-Delta factors in the old coordinates.
The distinguished last exponent is zero, so all coefficients `b_r` vanish
from the latter factors. -/
theorem terminal_A_eq {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (x : TerminalNode P N) (m : ℕ)
    (row : ActiveTerminalOldExponent (terminalOldSide state))
    (lambda : LambdaBox
      (activeTerminalBox P (terminalOldSide state))) :
    A state b bLast (terminalActiveIndexToLevel state lambda)
        (terminalNodeNumerator P x : ℂ)
        (terminalSourceMultiIndex state m row) =
      Erdos240.BakerLemma3.poweredDeltaHasseEval P.h
          (lambda.deltaIndex + 1) m
          (terminalNodeValue P x + (lambda.shift : ℂ)) *
        ∏ r : Fin oldRank,
          Erdos240.BakerLemma3.simpleDeltaEval
            (row (Fintype.equivFin (Fin oldRank) r))
            ((bLast : ℂ) *
              lambda.oldExponent (Fintype.equivFin (Fin oldRank) r)) := by
  simp only [A, Erdos240.BakerLemma3.auxiliaryFactor,
    coordinatesForState, coordinates, terminalSourceMultiIndex_zero,
    terminalSourceMultiIndex_succ, terminalActiveIndexToLevel_deltaIndex,
    terminalActiveIndexToLevel_shift,
    terminalActiveIndexToLevel_oldExponent,
    terminalActiveIndexToLevel_lastExponent, Nat.cast_zero, mul_zero,
    sub_zero, Erdos240.BakerLemma3.scaledArgument, terminalNodeValue]
  push_cast
  rfl

/-- The algebraic exponential monomial at an active terminal index is
exactly the product of the prime-power column scalings used in (14). -/
theorem terminal_exp_eq_columnScale_prod {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (x : TerminalNode P N)
    (lambda : LambdaBox
      (activeTerminalBox P (terminalOldSide state))) :
    Complex.exp
        (Erdos240.BakerLemma3.algebraicRate coordinates (oldLog P)
            (lastLog P) (terminalActiveIndexToLevel state lambda) *
          (terminalNodeNumerator P x : ℂ)) =
      ∏ r : Fin (Fintype.card (Fin oldRank)),
        terminalColumnScale state x r (lambda.oldExponentFin r) := by
  rw [show oldLog P =
    (fun r ↦ (Real.log (P.old r : ℝ) : ℂ)) from rfl]
  rw [show lastLog P =
    (Real.log (P.newPrime : ℝ) : ℂ) from rfl]
  rw [Erdos240.BakerSourceState.exp_algebraicRate_mul_nat_eq coordinates
    P.old P.newPrime (fun r ↦ (P.old_prime r).pos)
      P.new_prime.pos (terminalActiveIndexToLevel state lambda)
      (terminalNodeNumerator P x)]
  simp only [coordinates, terminalActiveIndexToLevel_oldExponent,
    terminalActiveIndexToLevel_lastExponent, zero_mul, pow_zero, mul_one,
    terminalColumnScale]
  simpa only [LambdaBox.oldExponent, Equiv.symm_apply_apply] using
    (Fintype.equivFin (Fin oldRank)).prod_comp
      (fun r : Fin (Fintype.card (Fin oldRank)) ↦
        (P.old ((Fintype.equivFin (Fin oldRank)).symm r) : ℂ) ^
          (lambda.oldExponent r * terminalNodeNumerator P x))

/-- The tensor entry is the product of the source's ordinary Delta factors
and the exponential prime-power column scalings. -/
theorem terminal_tensorMatrix_eq {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (bLast : ℤ) (hbLast : bLast ≠ 0)
    (x : TerminalNode P N)
    (row old : ActiveTerminalOldExponent (terminalOldSide state)) :
    tensorMatrix
        (fun r ↦ (terminalEliminationFamily state bLast hbLast x r).matrix)
        row old =
      (∏ r : Fin oldRank,
        Erdos240.BakerLemma3.simpleDeltaEval
          (row (Fintype.equivFin (Fin oldRank) r))
          ((bLast : ℂ) * old (Fintype.equivFin (Fin oldRank) r))) *
        ∏ r : Fin (Fintype.card (Fin oldRank)),
          terminalColumnScale state x r (old r) := by
  simp only [tensorMatrix, terminalEliminationFamily_matrix_apply,
    ordinaryDeltaComplex_eval, Finset.prod_mul_distrib]
  congr 1
  simpa only [Equiv.symm_apply_apply] using
    ((Fintype.equivFin (Fin oldRank)).prod_comp
      (fun r : Fin (Fintype.card (Fin oldRank)) ↦
        Erdos240.BakerLemma3.simpleDeltaEval (row r)
          ((bLast : ℂ) * old r))).symm

/-- Coordinate decomposition of the active terminal box.  Its last
coordinate is a singleton, leaving the old exponents, Delta power, and shift
as the three genuine summation coordinates. -/
def terminalActiveEquivCoordinates {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) :
    LambdaBox (activeTerminalBox P (terminalOldSide state)) ≃
      ActiveTerminalOldExponent (terminalOldSide state) ×
        (Fin (P.Lzero + 1) × Fin (P.LminusOne + 1)) where
  toFun lambda :=
    ⟨lambda.oldExponentFin, lambda.deltaIndexFin, lambda.shiftIndex⟩
  invFun coordinates :=
    ⟨coordinates.2.2, coordinates.2.1, coordinates.1,
      activeTerminalLastZero P (terminalOldSide state)⟩
  left_inv lambda := by
    rcases lambda with ⟨shift, delta, old, last⟩
    change (⟨shift, delta, old,
      activeTerminalLastZero P (terminalOldSide state)⟩ :
        LambdaBox (activeTerminalBox P (terminalOldSide state))) =
      ⟨shift, delta, old, last⟩
    apply lambdaBox_ext (a := ⟨shift, delta, old,
      activeTerminalLastZero P (terminalOldSide state)⟩)
      (b := ⟨shift, delta, old, last⟩) rfl rfl rfl
    apply Fin.ext
    have hlast := last.isLt
    simp only [activeTerminalBox, Nat.zero_add, Nat.lt_one_iff] at hlast
    exact hlast.symm
  right_inv coordinates := rfl

/-- Fubini decomposition of a sum over the active terminal box. -/
theorem sum_terminalActive_eq_sum_coordinates {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N)
    (F : LambdaBox (activeTerminalBox P (terminalOldSide state)) → ℂ) :
    ∑ lambda, F lambda =
      ∑ old : ActiveTerminalOldExponent (terminalOldSide state),
        ∑ d : Fin (P.Lzero + 1), ∑ s : Fin (P.LminusOne + 1),
          F ⟨s, d, old,
            activeTerminalLastZero P (terminalOldSide state)⟩ := by
  classical
  have h := Fintype.sum_equiv (terminalActiveEquivCoordinates state) F
    (fun coordinates ↦
      F ⟨coordinates.2.2, coordinates.2.1, coordinates.1,
        activeTerminalLastZero P (terminalOldSide state)⟩)
    (fun lambda ↦ congrArg F
      ((terminalActiveEquivCoordinates state).left_inv lambda).symm)
  simpa only [Fintype.sum_prod_type] using h

/-- Pointwise form of equation (13): a restricted source summand is the
corresponding tensor-matrix entry times its head-polynomial summand. -/
theorem terminal_source_summand_eq_tensor {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ)
    (bLast : ℤ) (hbLast : bLast ≠ 0)
    (x : TerminalNode P N) (m : ℕ)
    (row : ActiveTerminalOldExponent (terminalOldSide state))
    (lambda : LambdaBox
      (activeTerminalBox P (terminalOldSide state))) :
    (state.coeff (terminalActiveIndexToLevel state lambda) : ℂ) *
        A state b bLast (terminalActiveIndexToLevel state lambda)
          (terminalNodeNumerator P x : ℂ)
          (terminalSourceMultiIndex state m row) *
        Complex.exp
          (Erdos240.BakerLemma3.algebraicRate coordinates (oldLog P)
              (lastLog P) (terminalActiveIndexToLevel state lambda) *
            (terminalNodeNumerator P x : ℂ)) =
      tensorMatrix
          (fun r ↦
            (terminalEliminationFamily state bLast hbLast x r).matrix)
          row lambda.oldExponentFin *
        (terminalActiveCoefficient state lambda *
          Erdos240.BakerLemma3.poweredDeltaHasseEval P.h
            (lambda.deltaIndex + 1) m
            (terminalNodeValue P x + (lambda.shift : ℂ))) := by
  rw [terminal_A_eq state b bLast x m row lambda,
    terminal_exp_eq_columnScale_prod state x lambda,
    terminal_tensorMatrix_eq state bLast hbLast x row
      lambda.oldExponentFin]
  simp only [terminalActiveCoefficient, LambdaBox.oldExponent]
  ring

/-- The restricted source vanishing equation is exactly the tensor relation
required by `TerminalEquation13.ofTensor`. -/
theorem terminal_tensor_relation {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ)
    (bLast : ℤ) (hbLast : bLast ≠ 0)
    (hN : 0 < N)
    (hterminal : P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ))
    (hseed : BakerInduction.IntegralSeedAtLevel P (g state b bLast) N)
    (x : TerminalNode P N) (m : ℕ)
    (hm : m < terminalMultiplicity P N)
    (row : ActiveTerminalOldExponent (terminalOldSide state)) :
    ∑ old : ActiveTerminalOldExponent (terminalOldSide state),
      tensorMatrix
          (fun r ↦
            (terminalEliminationFamily state bLast hbLast x r).matrix)
          row old *
        (Polynomial.hasseDeriv m
          (activeTerminalPolynomial P (terminalOldSide state)
            (terminalActiveCoefficient state) old)).eval
              (terminalNodeValue P x) = 0 := by
  have hz := terminal_active_source_sum_eq_zero state b bLast hN hterminal
    hseed x m row (weight_terminalSourceMultiIndex_le state m hm row)
  let G : LambdaBox
      (activeTerminalBox P (terminalOldSide state)) → ℂ :=
    fun lambda ↦
      tensorMatrix
          (fun r ↦
            (terminalEliminationFamily state bLast hbLast x r).matrix)
          row lambda.oldExponentFin *
        (terminalActiveCoefficient state lambda *
          Erdos240.BakerLemma3.poweredDeltaHasseEval P.h
            (lambda.deltaIndex + 1) m
            (terminalNodeValue P x + (lambda.shift : ℂ)))
  calc
    (∑ old : ActiveTerminalOldExponent (terminalOldSide state),
        tensorMatrix
            (fun r ↦
              (terminalEliminationFamily state bLast hbLast x r).matrix)
            row old *
          (Polynomial.hasseDeriv m
            (activeTerminalPolynomial P (terminalOldSide state)
              (terminalActiveCoefficient state) old)).eval
                (terminalNodeValue P x)) =
        ∑ old : ActiveTerminalOldExponent (terminalOldSide state),
          tensorMatrix
              (fun r ↦
                (terminalEliminationFamily state bLast hbLast x r).matrix)
              row old *
            (∑ d : Fin (P.Lzero + 1),
              ∑ s : Fin (P.LminusOne + 1),
                terminalActiveCoefficient state
                    ⟨s, d, old,
                      activeTerminalLastZero P (terminalOldSide state)⟩ *
                  Erdos240.BakerLemma3.poweredDeltaHasseEval P.h
                    (d + 1) m (terminalNodeValue P x + (s : ℂ))) := by
      apply Finset.sum_congr rfl
      intro old _
      rw [hasseDeriv_activeTerminalPolynomial_eval]
    _ = ∑ old : ActiveTerminalOldExponent (terminalOldSide state),
          ∑ d : Fin (P.Lzero + 1),
            ∑ s : Fin (P.LminusOne + 1),
              tensorMatrix
                  (fun r ↦
                    (terminalEliminationFamily state bLast hbLast x r).matrix)
                  row old *
                (terminalActiveCoefficient state
                    ⟨s, d, old,
                      activeTerminalLastZero P (terminalOldSide state)⟩ *
                  Erdos240.BakerLemma3.poweredDeltaHasseEval P.h
                    (d + 1) m (terminalNodeValue P x + (s : ℂ))) := by
      simp only [Finset.mul_sum]
    _ = ∑ lambda : LambdaBox
            (activeTerminalBox P (terminalOldSide state)), G lambda := by
      symm
      simpa only [G, LambdaBox.deltaIndex, LambdaBox.shift] using
        sum_terminalActive_eq_sum_coordinates state G
    _ = ∑ lambda : LambdaBox
            (activeTerminalBox P (terminalOldSide state)),
          (state.coeff (terminalActiveIndexToLevel state lambda) : ℂ) *
            A state b bLast (terminalActiveIndexToLevel state lambda)
              (terminalNodeNumerator P x : ℂ)
              (terminalSourceMultiIndex state m row) *
            Complex.exp
              (Erdos240.BakerLemma3.algebraicRate coordinates (oldLog P)
                  (lastLog P) (terminalActiveIndexToLevel state lambda) *
                (terminalNodeNumerator P x : ℂ)) := by
      apply Finset.sum_congr rfl
      intro lambda _
      exact (terminal_source_summand_eq_tensor state b bLast hbLast
        x m row lambda).symm
    _ = 0 := hz

/-- Actual source construction of equation (13) after Lemma 6.  No terminal
zero-count assumption remains: the coordinate matrices are the checked
ordinary-Delta Vandermonde families, and their tensor relations are the
integral source equations supplied by `hseed`. -/
def terminalEquation13_of_source {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ)
    (bLast : ℤ) (hbLast : bLast ≠ 0)
    (hN : 0 < N)
    (hterminal : P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ))
    (hseed : BakerInduction.IntegralSeedAtLevel P (g state b bLast) N) :
    TerminalEquation13 P N (terminalOldSide state)
      (terminalActiveCoefficient state) :=
  TerminalEquation13.ofTensor hN hterminal
    (fun x _m _hm r ↦
      terminalEliminationFamily state bLast hbLast x r)
    (fun x m hm row ↦
      terminal_tensor_relation state b bLast hbLast hN hterminal
        hseed x m hm row)

/-- The genuine terminal Lemma-6 state is impossible: restriction preserves
a nonzero coefficient, whereas the checked equation-(13)--(16) zero count
forces every restricted coefficient to vanish. -/
theorem false_of_terminal_source {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ)
    (bLast : ℤ) (hbLast : bLast ≠ 0)
    (hN : 0 < N)
    (hterminal : P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ))
    (hseed : BakerInduction.IntegralSeedAtLevel P (g state b bLast) N) :
    False :=
  TerminalEquation13.false_of_nonzero
    (terminalActiveCoefficient_ne_zero state hterminal)
    (terminalEquation13_of_source state b bLast hbLast hN hterminal hseed)

/-- The same endpoint collapses the canonical terminal box consumed by the
generic final zero count. -/
theorem terminalBox_lastMax_eq_zero {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) {N : ℕ}
    (hterminal : P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ)) :
    (terminalBox P N).lastMax = 0 :=
  terminalBox_lastMax_eq_zero_of_scale_lt_qpow P hterminal

/-- Accordingly there is exactly one canonical terminal last exponent. -/
theorem terminalLastExponent_eq_zero {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) {N : ℕ}
    (hterminal : P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ))
    (last : TerminalLastExponent P N) :
    last = terminalLastZero P N :=
  terminalLastExponent_eq_zero_of_scale_lt_qpow P hterminal last

end Erdos240.BakerTerminalInstantiation

#print axioms Erdos240.BakerTerminalInstantiation.activeCoefficient_ne_zero
#print axioms Erdos240.BakerTerminalInstantiation.activeLastSide_eq_zero
#print axioms Erdos240.BakerTerminalInstantiation.terminalActiveCoefficient_ne_zero
#print axioms Erdos240.BakerTerminalInstantiation.weight_terminalSourceMultiIndex_le
#print axioms Erdos240.BakerTerminalInstantiation.terminal_tensor_relation
#print axioms Erdos240.BakerTerminalInstantiation.terminalEquation13_of_source
#print axioms Erdos240.BakerTerminalInstantiation.false_of_terminal_source
#print axioms Erdos240.BakerTerminalInstantiation.terminalBox_lastMax_eq_zero
