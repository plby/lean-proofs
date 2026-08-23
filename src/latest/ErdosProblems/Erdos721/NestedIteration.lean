/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos721.NestedScaleConstruction

/-!
# Finite termination of the nested density iteration

The error term is largest at the initial density.  Restricting the abstract
state space to states whose density is at least that initial value therefore
allows the uniform density-increment termination lemma to be applied
directly.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ENNReal Indicator mu NNReal Pointwise

namespace CyclicNestedIteration

variable {N : ℕ} [NeZero N]

private lemma error_anti {m : ℕ} {alpha beta : ℝ}
    (hm : 0 < m) (halpha : 0 < alpha) (hab : alpha ≤ beta)
    (herror : 3 * (1 / ((5 * m : ℕ) * alpha)) ≤ (1 / 16 : ℝ) / 4) :
    3 * (1 / ((5 * m : ℕ) * beta)) ≤ (1 / 16 : ℝ) / 4 := by
  have hmR : (0 : ℝ) < ((5 * m : ℕ) : ℝ) := by positivity
  have hden0 : 0 < ((5 * m : ℕ) : ℝ) * alpha := mul_pos hmR halpha
  have hden : ((5 * m : ℕ) : ℝ) * alpha ≤
      ((5 * m : ℕ) : ℝ) * beta :=
    mul_le_mul_of_nonneg_left hab hmR.le
  have hinv : 1 / (((5 * m : ℕ) : ℝ) * beta) ≤
      1 / (((5 * m : ℕ) : ℝ) * alpha) :=
    one_div_le_one_div_of_le hden0 hden
  exact (mul_le_mul_of_nonneg_left hinv (by norm_num)).trans herror

/-- A finite chain of genuine density increments.  The terminal step is kept
separate, because it may replace the final regular scale without increasing
the density. -/
inductive Reach {m : ℕ} : CyclicNestedDensityStep.State N m →
    ℕ → CyclicNestedDensityStep.State N m → Prop
  | refl (s : CyclicNestedDensityStep.State N m) : Reach s 0 s
  | step {s s' t : CyclicNestedDensityStep.State N m} {j : ℕ}
      (hinc : CyclicNestedDensityStep.IncrementOutcome s s')
      (hrest : Reach s' j t) : Reach s (j + 1) t

lemma Reach.trans {m i j : ℕ}
    {s u t : CyclicNestedDensityStep.State N m}
    (h₁ : Reach s i u) (h₂ : Reach u j t) : Reach s (i + j) t := by
  induction h₁ with
  | refl => simpa using h₂
  | @step s₀ s' u k hinc hrest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Reach.step hinc (ih h₂)

lemma Reach.beta_lower {m j : ℕ}
    {s t : CyclicNestedDensityStep.State N m} (h : Reach s j t) :
    (1 + 1 / 32768 : ℝ) ^ j * s.beta ≤ t.beta := by
  induction h with
  | refl => simp
  | @step s₀ s' t j hinc hrest ih =>
      calc
        (1 + 1 / 32768 : ℝ) ^ (j + 1) * s₀.beta =
            (1 + 1 / 32768 : ℝ) ^ j *
              ((1 + 1 / 32768 : ℝ) * s₀.beta) := by ring
        _ ≤ (1 + 1 / 32768 : ℝ) ^ j * s'.beta := by
          exact mul_le_mul_of_nonneg_left hinc.density_gain (by positivity)
        _ ≤ t.beta := ih

lemma Reach.initial_beta_le {m j : ℕ}
    {s t : CyclicNestedDensityStep.State N m} (h : Reach s j t) :
    s.beta ≤ t.beta := by
  have hpow : (1 : ℝ) ≤ (1 + 1 / 32768 : ℝ) ^ j := by
    exact one_le_pow₀ (by norm_num)
  exact (calc
    s.beta ≤ (1 + 1 / 32768 : ℝ) ^ j * s.beta := by
      nlinarith [s.beta_pos, mul_nonneg (sub_nonneg.mpr hpow) s.beta_pos.le]
    _ ≤ t.beta := h.beta_lower)

lemma Reach.rank_bound {m j : ℕ}
    {s t : CyclicNestedDensityStep.State N m} (h : Reach s j t) :
    (t.B.rank : ℝ) ≤ (s.B.rank : ℝ) +
      j * (2 ^ 140 * CyclicQuantitativeBounds.curLog s.beta ^ 6) := by
  induction h with
  | refl => simp
  | @step s₀ s' t j hinc hrest ih =>
      have hss' : s₀.beta ≤ s'.beta := by
        calc
          s₀.beta ≤ (1 + 1 / 32768 : ℝ) * s₀.beta := by
            nlinarith [s₀.beta_pos]
          _ ≤ s'.beta := hinc.density_gain
      have hlog : CyclicQuantitativeBounds.curLog s'.beta ≤
          CyclicQuantitativeBounds.curLog s₀.beta :=
        CyclicQuantitativeBounds.curLog_anti s₀.beta_pos hss'
      have hcost :
          2 ^ 140 * CyclicQuantitativeBounds.curLog s'.beta ^ 6 ≤
            2 ^ 140 * CyclicQuantitativeBounds.curLog s₀.beta ^ 6 := by
        have hslog0 : 0 ≤ CyclicQuantitativeBounds.curLog s₀.beta :=
          (by positivity : (0 : ℝ) ≤ 1).trans
            (CyclicQuantitativeBounds.one_le_curLog
              s₀.beta_pos s₀.beta_le_one)
        have hs'log0 : 0 ≤ CyclicQuantitativeBounds.curLog s'.beta :=
          (by positivity : (0 : ℝ) ≤ 1).trans
            (CyclicQuantitativeBounds.one_le_curLog
              s'.beta_pos s'.beta_le_one)
        gcongr
      push_cast
      calc
        (t.B.rank : ℝ) ≤ (s'.B.rank : ℝ) +
            j * (2 ^ 140 * CyclicQuantitativeBounds.curLog s'.beta ^ 6) := ih
        _ ≤ (s'.B.rank : ℝ) +
            j * (2 ^ 140 * CyclicQuantitativeBounds.curLog s₀.beta ^ 6) := by
          have hj0 : (0 : ℝ) ≤ j := by positivity
          exact add_le_add_right (mul_le_mul_of_nonneg_left hcost hj0) _
        _ ≤ ((s₀.B.rank : ℝ) +
              2 ^ 140 * CyclicQuantitativeBounds.curLog s₀.beta ^ 6) +
            j * (2 ^ 140 * CyclicQuantitativeBounds.curLog s₀.beta ^ 6) := by
          exact add_le_add_left hinc.rank_bound
            (j * (2 ^ 140 * CyclicQuantitativeBounds.curLog s₀.beta ^ 6))
        _ = (s₀.B.rank : ℝ) +
            (j + 1) *
              (2 ^ 140 * CyclicQuantitativeBounds.curLog s₀.beta ^ 6) := by
          ring

lemma Reach.radius_lower_of_uniform {m j : ℕ}
    {s t : CyclicNestedDensityStep.State N m} (h : Reach s j t)
    {q : ℝ} (hq0 : 0 ≤ q)
    (hfactor : ∀ u : CyclicNestedDensityStep.State N m,
      q ≤ CyclicNestedDensityStep.State.oneStepRadiusFactor u) :
    q ^ j * min 1 s.B.radius ≤ min 1 t.B.radius := by
  induction h with
  | refl => simp
  | @step s₀ s' t j hinc hrest ih =>
      calc
        q ^ (j + 1) * min 1 s₀.B.radius =
            q ^ j * (q * min 1 s₀.B.radius) := by ring
        _ ≤ q ^ j *
            (s₀.oneStepRadiusFactor * min 1 s₀.B.radius) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq0 j)
          exact mul_le_mul_of_nonneg_right (hfactor s₀)
            (le_min zero_le_one s₀.B.radius_nonneg)
        _ ≤ q ^ j * min 1 s'.B.radius := by
          exact mul_le_mul_of_nonneg_left hinc.radius_retained (by positivity)
        _ ≤ min 1 t.B.radius := ih

/-- A logarithmic number of increments already forces the density above one. -/
noncomputable def iterationBudget (beta : ℝ) : ℕ :=
  ⌈2 ^ 17 * CyclicQuantitativeBounds.curLog beta⌉₊

/-- Uniform rank ceiling over the whole logarithmic iteration. -/
noncomputable def rankCeiling {m : ℕ}
    (s : CyclicNestedDensityStep.State N m) : ℝ :=
  (s.B.rank : ℝ) + (iterationBudget s.beta : ℝ) *
    (2 ^ 140 * CyclicQuantitativeBounds.curLog s.beta ^ 6)

/-- Uniform polynomial radius factor valid at every state reached before the
iteration budget is exhausted. -/
noncomputable def uniformRadiusFactor {m : ℕ}
    (s : CyclicNestedDensityStep.State N m) : ℝ :=
  ((1 - 1 / 8192 : ℝ) * s.beta) /
    (2 ^ 51 * 400 ^ 5 * (m : ℝ) ^ 3 *
      (s.entropyBudget + 1 : ℝ) * rankCeiling s ^ 7)

lemma rankCeiling_pos {m : ℕ}
    (s : CyclicNestedDensityStep.State N m) : 0 < rankCeiling s := by
  unfold rankCeiling
  have hr : (0 : ℝ) < s.B.rank := by exact_mod_cast s.rank_pos
  positivity

lemma uniformRadiusFactor_pos {m : ℕ}
    (s : CyclicNestedDensityStep.State N m) :
    0 < uniformRadiusFactor s := by
  unfold uniformRadiusFactor
  have hm : (0 : ℝ) < m := by
    have hmNat : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      have hzero : s.delta = 0 := by
        simpa only [hm0, Nat.cast_zero, mul_zero, zero_mul, inv_zero] using
          s.delta_formula
      linarith [s.delta_pos]
    exact_mod_cast hmNat
  have hM : (0 : ℝ) < s.entropyBudget + 1 := by positivity
  have hR : 0 < rankCeiling s := rankCeiling_pos s
  exact div_pos (mul_pos (by norm_num) s.beta_pos) (by positivity)

lemma Reach.rank_le_rankCeiling {m j : ℕ}
    {s u : CyclicNestedDensityStep.State N m} (h : Reach s j u)
    (hj : j ≤ iterationBudget s.beta) :
    (u.B.rank : ℝ) ≤ rankCeiling s := by
  refine h.rank_bound.trans ?_
  unfold rankCeiling
  have hjR : (j : ℝ) ≤ iterationBudget s.beta := by exact_mod_cast hj
  have hcost : 0 ≤
      2 ^ 140 * CyclicQuantitativeBounds.curLog s.beta ^ 6 := by positivity
  gcongr

lemma Reach.entropyBudget_le {m j : ℕ}
    {s u : CyclicNestedDensityStep.State N m} (h : Reach s j u) :
    u.entropyBudget ≤ s.entropyBudget := by
  have hbeta := h.initial_beta_le
  have hlog : CyclicQuantitativeBounds.curLog u.beta ≤
      CyclicQuantitativeBounds.curLog s.beta :=
    CyclicQuantitativeBounds.curLog_anti s.beta_pos hbeta
  unfold CyclicNestedDensityStep.State.entropyBudget
  apply Nat.ceil_le_ceil
  have hu0 : 0 ≤ CyclicQuantitativeBounds.curLog u.beta :=
    (by norm_num : (0 : ℝ) ≤ 1).trans
      (CyclicQuantitativeBounds.one_le_curLog u.beta_pos u.beta_le_one)
  have hs0 : 0 ≤ CyclicQuantitativeBounds.curLog s.beta :=
    (by norm_num : (0 : ℝ) ≤ 1).trans
      (CyclicQuantitativeBounds.one_le_curLog s.beta_pos s.beta_le_one)
  gcongr

lemma Reach.uniformRadiusFactor_le_oneStep {m j : ℕ}
    {s u : CyclicNestedDensityStep.State N m} (h : Reach s j u)
    (hj : j ≤ iterationBudget s.beta) :
    uniformRadiusFactor s ≤ u.oneStepRadiusFactor := by
  let numS : ℝ := (1 - 1 / 8192 : ℝ) * s.beta
  let numU : ℝ := (1 - 1 / 8192 : ℝ) * u.beta
  let denU : ℝ :=
    2 ^ 51 * 400 ^ 5 * (m : ℝ) ^ 3 *
      (u.entropyBudget + 1 : ℝ) * (u.B.rank : ℝ) ^ 7
  let denMax : ℝ :=
    2 ^ 51 * 400 ^ 5 * (m : ℝ) ^ 3 *
      (s.entropyBudget + 1 : ℝ) * rankCeiling s ^ 7
  have hm : (0 : ℝ) < m := by
    have hmNat : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      have hzero : s.delta = 0 := by
        simpa only [hm0, Nat.cast_zero, mul_zero, zero_mul, inv_zero] using
          s.delta_formula
      linarith [s.delta_pos]
    exact_mod_cast hmNat
  have huRank : (0 : ℝ) < u.B.rank := by exact_mod_cast u.rank_pos
  have hdenU : 0 < denU := by
    dsimp only [denU]
    positivity
  have hdenMax : 0 < denMax := by
    dsimp only [denMax]
    have := rankCeiling_pos s
    positivity
  have hnumS : 0 ≤ numS := by
    dsimp only [numS]
    exact mul_nonneg (by norm_num) s.beta_pos.le
  have hnum : numS ≤ numU := by
    dsimp only [numS, numU]
    exact mul_le_mul_of_nonneg_left h.initial_beta_le (by norm_num)
  have hden : denU ≤ denMax := by
    dsimp only [denU, denMax]
    have hEntropy : (u.entropyBudget + 1 : ℝ) ≤
        (s.entropyBudget + 1 : ℝ) := by
      exact_mod_cast Nat.add_le_add_right h.entropyBudget_le 1
    have hRank := h.rank_le_rankCeiling hj
    have hRankCeiling0 := (rankCeiling_pos s).le
    gcongr
  rw [u.oneStepRadiusFactor_eq]
  change numS / denMax ≤ numU / denU
  calc
    numS / denMax ≤ numS / denU :=
      div_le_div_of_nonneg_left hnumS hdenU hden
    _ ≤ numU / denU :=
      (div_le_div_iff_of_pos_right hdenU).2 hnum

lemma Reach.radius_lower_from_root {m i j : ℕ}
    {root s t : CyclicNestedDensityStep.State N m}
    (hprefix : Reach root i s) (h : Reach s j t)
    (hij : i + j ≤ iterationBudget root.beta) :
    uniformRadiusFactor root ^ j * min 1 s.B.radius ≤
      min 1 t.B.radius := by
  induction h generalizing i with
  | refl => simp
  | @step s₀ s' t j hinc hrest ih =>
      have hi : i ≤ iterationBudget root.beta := by omega
      have hfactor := hprefix.uniformRadiusFactor_le_oneStep hi
      have hone : Reach s₀ 1 s' := by
        simpa using Reach.step hinc (Reach.refl s')
      have hprefix' : Reach root (i + 1) s' := hprefix.trans hone
      have hsum : (i + 1) + j ≤ iterationBudget root.beta := by omega
      calc
        uniformRadiusFactor root ^ (j + 1) * min 1 s₀.B.radius =
            uniformRadiusFactor root ^ j *
              (uniformRadiusFactor root * min 1 s₀.B.radius) := by ring
        _ ≤ uniformRadiusFactor root ^ j *
            (s₀.oneStepRadiusFactor * min 1 s₀.B.radius) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg
            (uniformRadiusFactor_pos root).le j)
          exact mul_le_mul_of_nonneg_right hfactor
            (le_min zero_le_one s₀.B.radius_nonneg)
        _ ≤ uniformRadiusFactor root ^ j * min 1 s'.B.radius := by
          exact mul_le_mul_of_nonneg_left hinc.radius_retained
            (pow_nonneg (uniformRadiusFactor_pos root).le j)
        _ ≤ min 1 t.B.radius := ih hprefix' hsum

lemma iterationBudget_cast_lower {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    2 ^ 17 * CyclicQuantitativeBounds.curLog beta ≤
      (iterationBudget beta : ℝ) := by
  unfold iterationBudget
  exact Nat.le_ceil _

lemma iterationBudget_cast_lt {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    (iterationBudget beta : ℝ) <
      2 ^ 17 * CyclicQuantitativeBounds.curLog beta + 1 := by
  unfold iterationBudget
  apply Nat.ceil_lt_add_one
  exact mul_nonneg (by positivity)
    ((by norm_num : (0 : ℝ) ≤ 1).trans
      (CyclicQuantitativeBounds.one_le_curLog hbeta0 hbeta1))

private lemma log_density_growth_factor_lower :
    (1 / 65536 : ℝ) ≤ Real.log (1 + 1 / 32768) := by
  calc
    (1 / 65536 : ℝ) ≤
        2 * (1 / 32768 : ℝ) / (1 / 32768 + 2) := by norm_num
    _ ≤ Real.log (1 + 1 / 32768) :=
      Real.le_log_one_add_of_nonneg (by norm_num)

lemma one_lt_pow_iterationBudget_mul (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    1 < (1 + 1 / 32768 : ℝ) ^ iterationBudget beta * beta := by
  let L := CyclicQuantitativeBounds.curLog beta
  have hL1 : (1 : ℝ) ≤ L := by
    exact CyclicQuantitativeBounds.one_le_curLog hbeta0 hbeta1
  have hJ := iterationBudget_cast_lower hbeta0 hbeta1
  have hlog := log_density_growth_factor_lower
  have hgrowth : 2 * L ≤
      (iterationBudget beta : ℝ) *
        Real.log (1 + 1 / 32768) := by
    have hJ0 : (0 : ℝ) ≤ (iterationBudget beta : ℝ) := by positivity
    have hmul := mul_le_mul hJ hlog (by norm_num) hJ0
    calc
      2 * L = (2 ^ 17 * L) * (1 / 65536 : ℝ) := by ring
      _ ≤ (iterationBudget beta : ℝ) *
          Real.log (1 + 1 / 32768) := hmul
  have hlogbeta : Real.log beta = 1 - L := by
    dsimp only [L, CyclicQuantitativeBounds.curLog]
    rw [Real.log_inv]
    ring
  have hlogprod : 0 < Real.log
      ((1 + 1 / 32768 : ℝ) ^ iterationBudget beta * beta) := by
    rw [Real.log_mul (pow_ne_zero _ (by norm_num)) hbeta0.ne',
      Real.log_pow, hlogbeta]
    nlinarith
  exact (Real.log_pos_iff
    (mul_nonneg (pow_nonneg (by norm_num) _) hbeta0.le)).mp hlogprod

private theorem exists_terminal_run_aux
    (hN : Odd N) (m : ℕ) (hm : 8192 ≤ m)
    (s : CyclicNestedDensityStep.State N m)
    (herror :
      3 * (1 / ((5 * m : ℕ) * ((1 - 1 / 8192 : ℝ) * s.beta))) ≤
        (1 / 16 : ℝ) / 4)
    (J : ℕ)
    (hlarge : 1 < (1 + 1 / 32768 : ℝ) ^ J * s.beta) :
    ∃ j < J, ∃ u st : CyclicNestedDensityStep.State N m,
      Reach s j u ∧ CyclicNestedDensityStep.TerminalOutcome u st := by
  induction J generalizing s with
  | zero =>
      simp only [pow_zero, one_mul] at hlarge
      exact (not_lt_of_ge s.beta_le_one hlarge).elim
  | succ J ih =>
      obtain hinc | hterminal :=
        CyclicNestedScaleConstruction.exists_increment_or_terminal
          hN m hm s herror
      · obtain ⟨s', hs'⟩ := hinc
        have hss' : s.beta ≤ s'.beta := by
          calc
            s.beta ≤ (1 + 1 / 32768 : ℝ) * s.beta := by
              nlinarith [s.beta_pos]
            _ ≤ s'.beta := hs'.density_gain
        have herror' := error_anti (m := m) (by omega)
          (mul_pos (by norm_num) s.beta_pos)
          (mul_le_mul_of_nonneg_left hss' (by norm_num)) herror
        have hlarge' :
            1 < (1 + 1 / 32768 : ℝ) ^ J * s'.beta := by
          have hlargeReassoc :
              1 < (1 + 1 / 32768 : ℝ) *
                ((1 + 1 / 32768 : ℝ) ^ J * s.beta) := by
            simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hlarge
          calc
            1 < (1 + 1 / 32768 : ℝ) *
                ((1 + 1 / 32768 : ℝ) ^ J * s.beta) := hlargeReassoc
            _ = (1 + 1 / 32768 : ℝ) ^ J *
                ((1 + 1 / 32768 : ℝ) * s.beta) := by ring
            _ ≤ (1 + 1 / 32768 : ℝ) ^ J * s'.beta := by
              exact mul_le_mul_of_nonneg_left hs'.density_gain (by positivity)
        obtain ⟨j, hj, u, st, hreach, hterm⟩ :=
          ih s' herror' hlarge'
        exact ⟨j + 1, by omega, u, st, Reach.step hs' hreach, hterm⟩
      · obtain ⟨st, hst⟩ := hterminal
        exact ⟨0, by omega, s, st, Reach.refl s, hst⟩

/-- Quantitative form of finite termination: if the prescribed number of
increments would force density above one, a terminal state is reached strictly
before that many increments. -/
theorem exists_terminal_run_of_pow_mul_gt_one
    (hN : Odd N) (m : ℕ) (hm : 8192 ≤ m)
    (s : CyclicNestedDensityStep.State N m)
    (herror :
      3 * (1 / ((5 * m : ℕ) * ((1 - 1 / 8192 : ℝ) * s.beta))) ≤
        (1 / 16 : ℝ) / 4)
    (J : ℕ)
    (hlarge : 1 < (1 + 1 / 32768 : ℝ) ^ J * s.beta) :
    ∃ j < J, ∃ u st : CyclicNestedDensityStep.State N m,
      Reach s j u ∧ CyclicNestedDensityStep.TerminalOutcome u st :=
  exists_terminal_run_aux hN m hm s herror J hlarge

/-- Terminal state with all three quantitative invariants needed by the
cyclic Roth endpoint. -/
theorem exists_quantitative_terminal_state
    (hN : Odd N) (m : ℕ) (hm : 8192 ≤ m)
    (s : CyclicNestedDensityStep.State N m)
    (herror :
      3 * (1 / ((5 * m : ℕ) * ((1 - 1 / 8192 : ℝ) * s.beta))) ≤
        (1 / 16 : ℝ) / 4) :
    ∃ st : CyclicNestedDensityStep.State N m,
      (1 - 1 / 8192 : ℝ) * s.beta ≤ st.beta ∧
      st.A.card ^ 2 < 2 * st.carrier.card ∧
      (st.B.rank : ℝ) ≤ rankCeiling s ∧
      uniformRadiusFactor s ^ iterationBudget s.beta *
          min 1 s.B.radius ≤ min 1 st.B.radius := by
  obtain ⟨j, hj, u, st, hreach, hterm⟩ :=
    exists_terminal_run_of_pow_mul_gt_one hN m hm s herror
      (iterationBudget s.beta)
      (one_lt_pow_iterationBudget_mul s.beta s.beta_pos s.beta_le_one)
  have hjle : j ≤ iterationBudget s.beta := hj.le
  have hbeta : (1 - 1 / 8192 : ℝ) * s.beta ≤ st.beta := by
    exact (mul_le_mul_of_nonneg_left hreach.initial_beta_le (by norm_num)).trans
      hterm.density_lower
  let cost : ℝ :=
    2 ^ 140 * CyclicQuantitativeBounds.curLog s.beta ^ 6
  have hlog : CyclicQuantitativeBounds.curLog u.beta ≤
      CyclicQuantitativeBounds.curLog s.beta :=
    CyclicQuantitativeBounds.curLog_anti s.beta_pos hreach.initial_beta_le
  have huLog0 : 0 ≤ CyclicQuantitativeBounds.curLog u.beta :=
    (by norm_num : (0 : ℝ) ≤ 1).trans
      (CyclicQuantitativeBounds.one_le_curLog u.beta_pos u.beta_le_one)
  have hsLog0 : 0 ≤ CyclicQuantitativeBounds.curLog s.beta :=
    (by norm_num : (0 : ℝ) ≤ 1).trans
      (CyclicQuantitativeBounds.one_le_curLog s.beta_pos s.beta_le_one)
  have hcost :
      2 ^ 140 * CyclicQuantitativeBounds.curLog u.beta ^ 6 ≤ cost := by
    dsimp only [cost]
    gcongr
  have hrank : (st.B.rank : ℝ) ≤ rankCeiling s := by
    have hjR : (j + 1 : ℕ) ≤ iterationBudget s.beta := by omega
    have hjRR : ((j + 1 : ℕ) : ℝ) ≤
        (iterationBudget s.beta : ℝ) := by exact_mod_cast hjR
    have hcost0 : 0 ≤ cost := by dsimp only [cost]; positivity
    calc
      (st.B.rank : ℝ) ≤ (u.B.rank : ℝ) +
          2 ^ 140 * CyclicQuantitativeBounds.curLog u.beta ^ 6 :=
        hterm.rank_bound
      _ ≤ (u.B.rank : ℝ) + cost := by gcongr
      _ ≤ ((s.B.rank : ℝ) + j * cost) + cost := by
        exact add_le_add_left (by simpa only [cost] using hreach.rank_bound) cost
      _ = (s.B.rank : ℝ) + (j + 1) * cost := by push_cast; ring
      _ ≤ (s.B.rank : ℝ) +
          (iterationBudget s.beta : ℝ) * cost := by
        have hdiff : 0 ≤
            ((iterationBudget s.beta : ℝ) - ((j : ℝ) + 1)) * cost :=
          mul_nonneg (sub_nonneg.mpr (by simpa using hjRR)) hcost0
        nlinarith
      _ = rankCeiling s := by rfl
  let q := uniformRadiusFactor s
  have hq0 : 0 ≤ q := (uniformRadiusFactor_pos s).le
  have hqStep : q ≤ s.oneStepRadiusFactor := by
    exact (Reach.refl s).uniformRadiusFactor_le_oneStep (Nat.zero_le _)
  have hq1 : q ≤ 1 := hqStep.trans s.oneStepRadiusFactor_le_one
  have hreachRadius : q ^ j * min 1 s.B.radius ≤ min 1 u.B.radius := by
    simpa only [q] using Reach.radius_lower_from_root (Reach.refl s) hreach
      (by simpa using hjle)
  have hfactorU : q ≤ u.oneStepRadiusFactor := by
    simpa only [q] using hreach.uniformRadiusFactor_le_oneStep hjle
  have hterminalRadius :
      q ^ (j + 1) * min 1 s.B.radius ≤ min 1 st.B.radius := by
    calc
      q ^ (j + 1) * min 1 s.B.radius =
          q * (q ^ j * min 1 s.B.radius) := by ring
      _ ≤ q * min 1 u.B.radius :=
        mul_le_mul_of_nonneg_left hreachRadius hq0
      _ ≤ u.oneStepRadiusFactor * min 1 u.B.radius :=
        mul_le_mul_of_nonneg_right hfactorU
          (le_min zero_le_one u.B.radius_nonneg)
      _ ≤ min 1 st.B.radius := hterm.radius_retained
  have hpow : q ^ iterationBudget s.beta ≤ q ^ (j + 1) :=
    pow_le_pow_of_le_one hq0 hq1 (by omega)
  refine ⟨st, hbeta, hterm.terminal, hrank, ?_⟩
  exact (mul_le_mul_of_nonneg_right hpow
    (le_min zero_le_one s.B.radius_nonneg)).trans hterminalRadius

/-- Starting from any state satisfying the initial numerical error budget,
the canonical nested iteration reaches a state whose carrier is terminally
small compared with its progression-free subset.  The terminal density is
at least the initial density. -/
theorem exists_terminal_state
    (hN : Odd N) (m : ℕ) (hm : 8192 ≤ m)
    (s0 : CyclicNestedDensityStep.State N m)
    (herror0 :
      3 * (1 / ((5 * m : ℕ) * ((1 - 1 / 8192 : ℝ) * s0.beta))) ≤
        (1 / 16 : ℝ) / 4) :
    ∃ st : CyclicNestedDensityStep.State N m,
      (1 - 1 / 8192 : ℝ) * s0.beta ≤ st.beta ∧
        st.A.card ^ 2 < 2 * st.carrier.card := by
  let S := {s : CyclicNestedDensityStep.State N m // s0.beta ≤ s.beta}
  let terminal : S → Prop := fun s ↦
    s.1.A.card ^ 2 < 2 * s.1.carrier.card
  let density : S → ℝ := fun s ↦ s.1.beta
  let sInitial : S := ⟨s0, le_rfl⟩
  letI : Nonempty S := ⟨sInitial⟩
  by_cases hex : ∃ st : CyclicNestedDensityStep.State N m,
      (1 - 1 / 8192 : ℝ) * s0.beta ≤ st.beta ∧
        st.A.card ^ 2 < 2 * st.carrier.card
  · exact hex
  push Not at hex
  have hstep : ∀ s : S, ¬ terminal s →
      ∃ s' : S, (1 + (1 / 32768 : ℝ)) * density s ≤ density s' := by
    intro s _hnot
    have hlow : (1 - 1 / 8192 : ℝ) * s0.beta ≤
        (1 - 1 / 8192 : ℝ) * s.1.beta := by
      exact mul_le_mul_of_nonneg_left s.2 (by norm_num)
    have hlow0 : 0 < (1 - 1 / 8192 : ℝ) * s0.beta :=
      mul_pos (by norm_num) s0.beta_pos
    have herror := error_anti (m := m) (by omega) hlow0 hlow herror0
    rcases CyclicNestedScaleConstruction.exists_increment_or_terminal
        hN m hm s.1 herror with hinc | hterminal
    · obtain ⟨s', hs'⟩ := hinc
      refine ⟨⟨s', ?_⟩, ?_⟩
      · calc
          s0.beta ≤ s.1.beta := s.2
          _ ≤ (1 + 1 / 32768 : ℝ) * s.1.beta := by
            nlinarith [s.1.beta_pos]
          _ ≤ s'.beta := hs'.density_gain
      · exact hs'.density_gain
    · obtain ⟨st, hst⟩ := hterminal
      exfalso
      have hlower : (1 - 1 / 8192 : ℝ) * s0.beta ≤ st.beta :=
        (mul_le_mul_of_nonneg_left s.2 (by norm_num)).trans hst.density_lower
      exact (not_lt_of_ge (hex st hlower)) hst.terminal
  obtain ⟨st, hterminal⟩ :=
    exists_terminal_of_uniform_density_increment terminal density
      (by norm_num : (0 : ℝ) < 1 / 32768)
      (fun s ↦ s.1.beta_pos) (fun s ↦ s.1.beta_le_one) hstep
  refine ⟨st.1, ?_, hterminal⟩
  exact (by nlinarith [s0.beta_pos] :
    (1 - 1 / 8192 : ℝ) * s0.beta ≤ s0.beta).trans st.2

end CyclicNestedIteration
end Erdos721
