/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerInduction
import ErdosProblems.Erdos240.BakerLemma3Instantiation
import ErdosProblems.Erdos240.BakerLemma4InnerInduction
import ErdosProblems.Erdos240.BakerSourceJetTransport
import ErdosProblems.Erdos240.BakerSourceLogFormNormalization
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic

/-!
# Moment cancellation for the source auxiliary function

This file packages the algebraic content of equations (7)--(8) in the
van der Poorten--Loxton proof.  Multiplication of an ordinary old-Delta
factor by its argument is the finite difference of two consecutive Delta
factors; this is the identity proved as
`BakerSourceJetTransport.simpleDeltaEval_mul_variable`.  Consequently one
ordinary `z`-derivative of the analytic auxiliary function is the finite row
operation `jetStep`.

The results below iterate that row operation.  They make the weight
bookkeeping explicit: an order-`j` moment based at a multi-index `m` uses
only rows of weight at most `weight m + j`.  Thus an integral seed with
budget `S` kills every algebraic-rate moment for which
`weight m + j <= S`.  The final theorems include the exact reindexing between
the parameter-rank multiindices used by `VanishesOn` and the explicit
`oldRank + 1` source multiindices.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceMomentCancellation

open Finset
open Erdos240
open Erdos240.BakerInduction
open Erdos240.BakerLemma3
open Erdos240.BakerLemma3Concrete
open Erdos240.BakerLemma3Instantiation
open Erdos240.BakerSourceState
open Erdos240.BakerSourceJetTransport
open Erdos240.BakerSourceLogFormNormalization

/-- Iterate the source row operation.  At a fixed point this is the exact
algebraic-rate moment operator occurring after repeated differentiation of
the analytic auxiliary function. -/
def jetIterate {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) (bLast : ℤ) :
    ℕ → (VDPLMultiIndex (oldRank + 1) → ℂ) →
      VDPLMultiIndex (oldRank + 1) → ℂ
  | 0, F => F
  | j + 1, F => jetStep P N bLast (jetIterate P N bLast j F)

@[simp] theorem jetIterate_zero {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) (bLast : ℤ)
    (F : VDPLMultiIndex (oldRank + 1) → ℂ) :
    jetIterate P N bLast 0 F = F := rfl

@[simp] theorem jetIterate_succ {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N j : ℕ) (bLast : ℤ)
    (F : VDPLMultiIndex (oldRank + 1) → ℂ) :
    jetIterate P N bLast (j + 1) F =
      jetStep P N bLast (jetIterate P N bLast j F) := rfl

/-- `jetStep` preserves pointwise zero. -/
theorem jetStep_eq_zero_of_eq_zero {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) (bLast : ℤ)
    (F : VDPLMultiIndex (oldRank + 1) → ℂ)
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : F m = 0)
    (hbump : ∀ i, F (bump m i) = 0) :
    jetStep P N bLast F m = 0 := by
  simp [jetStep, hm, hbump]

/-- An order-`j` row moment vanishes as soon as all source rows through
weight `weight m + j` vanish.  This is the precise triangular support
statement behind equation (8). -/
theorem jetIterate_eq_zero_of_weight {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) (bLast : ℤ)
    (F : VDPLMultiIndex (oldRank + 1) → ℂ) (S j : ℕ)
    (hzero : ∀ m, VDPLMultiIndex.weight m ≤ S → F m = 0) :
    ∀ m, VDPLMultiIndex.weight m + j ≤ S →
      jetIterate P N bLast j F m = 0 := by
  induction j with
  | zero =>
      intro m hm
      exact hzero m (by simpa using hm)
  | succ j ih =>
      intro m hm
      rw [jetIterate_succ]
      apply jetStep_eq_zero_of_eq_zero
      · apply ih
        omega
      · intro i
        apply ih
        rw [weight_bump]
        omega

/-- Differentiating a pointwise source row operation applies the same row
operation to the derivatives. -/
theorem hasDerivAt_jetStep {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) (bLast : ℤ)
    (F D : ℂ → VDPLMultiIndex (oldRank + 1) → ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) (z : ℂ)
    (hderiv : ∀ m', HasDerivAt (fun w ↦ F w m') (D z m') z) :
    HasDerivAt (fun w ↦ jetStep P N bLast (F w) m)
      (jetStep P N bLast (D z) m) z := by
  unfold jetStep
  apply HasDerivAt.add
  · exact (hderiv (bump m 0)).const_mul _
  · exact HasDerivAt.fun_sum fun (r : Fin oldRank) _ ↦
      ((hderiv (bump m r.succ)).sub (hderiv m)).const_mul
        (oldJetCoefficient P bLast m r)

/-- Every iterated source moment has as derivative the next moment. -/
theorem hasDerivAt_jetIterate_fSource {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (j : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) (z : ℂ) :
    HasDerivAt
      (fun w ↦ jetIterate P N bLast j
        (fun m' ↦ fSource state b bLast w m') m)
      (jetIterate P N bLast (j + 1)
        (fun m' ↦ fSource state b bLast z m') m) z := by
  induction j generalizing m with
  | zero =>
      simpa using hasDerivAt_fSource state b hbLast m z
  | succ j ih =>
      change HasDerivAt
        (fun w ↦ jetStep P N bLast
          (jetIterate P N bLast j
            (fun m' ↦ fSource state b bLast w m')) m)
        (jetStep P N bLast
          (jetIterate P N bLast (j + 1)
            (fun m' ↦ fSource state b bLast z m')) m) z
      exact hasDerivAt_jetStep P N bLast
        (fun w ↦ jetIterate P N bLast j
          (fun m' ↦ fSource state b bLast w m'))
        (fun w ↦ jetIterate P N bLast (j + 1)
          (fun m' ↦ fSource state b bLast w m')) m z
        (fun m' ↦ ih m')

/-- Exact equation (7) iterated `j` times. -/
theorem iteratedDeriv_fSource_eq_jetIterate {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (j : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) (z : ℂ) :
    iteratedDeriv j (fun w ↦ fSource state b bLast w m) z =
      jetIterate P N bLast j
        (fun m' ↦ fSource state b bLast z m') m := by
  induction j generalizing m z with
  | zero => simp
  | succ j ih =>
      rw [iteratedDeriv_succ]
      have hfun :
          iteratedDeriv j (fun w ↦ fSource state b bLast w m) =
            fun w ↦ jetIterate P N bLast j
              (fun m' ↦ fSource state b bLast w m') m := by
        funext w
        exact ih m w
      rw [hfun]
      exact (hasDerivAt_jetIterate_fSource state b hbLast j m z).deriv

/-- The normalized analytic jet has the same finite row expansion. -/
theorem normalizedIteratedDeriv_fSource_eq_jetIterate {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (j : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) (z : ℂ) :
    iteratedDeriv j (fun w ↦ fSource state b bLast w m) z /
        (j.factorial : ℂ) =
      jetIterate P N bLast j
        (fun m' ↦ fSource state b bLast z m') m /
          (j.factorial : ℂ) := by
  rw [iteratedDeriv_fSource_eq_jetIterate state b hbLast]

/-- Parameter-rank form of the exact normalized-jet expansion. -/
theorem normalizedIteratedDeriv_f_eq_jetIterate {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (j : ℕ)
    (m : VDPLMultiIndex P.rank) (z : ℂ) :
    iteratedDeriv j (fun w ↦ f state b bLast w m) z /
        (j.factorial : ℂ) =
      jetIterate P N bLast j
          (fun m' ↦ fSource state b bLast z m')
          (toSourceMultiIndex P m) /
        (j.factorial : ℂ) := by
  exact normalizedIteratedDeriv_fSource_eq_jetIterate state b hbLast j
    (toSourceMultiIndex P m) z

/-! ## Quantitative comparison with the killed algebraic-rate moment -/

/-- The nonnegative majorant obtained by replacing all coefficients in one
source row operation by their norms. -/
def jetErrorStep {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) (bLast : ℤ)
    (E : VDPLMultiIndex (oldRank + 1) → ℝ)
    (m : VDPLMultiIndex (oldRank + 1)) : ℝ :=
  ‖headJetCoefficient P N m‖ * E (bump m 0) +
    ∑ r, ‖oldJetCoefficient P bLast m r‖ *
      (E (bump m r.succ) + E m)

/-- Iteration of the coefficient-norm majorant. -/
def jetErrorIterate {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) (bLast : ℤ) :
    ℕ → (VDPLMultiIndex (oldRank + 1) → ℝ) →
      VDPLMultiIndex (oldRank + 1) → ℝ
  | 0, E => E
  | j + 1, E => jetErrorStep P N bLast (jetErrorIterate P N bLast j E)

/-- Total coefficient mass in one source row operation. -/
def jetCoefficientMass {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) (bLast : ℤ)
    (m : VDPLMultiIndex (oldRank + 1)) : ℝ :=
  ‖headJetCoefficient P N m‖ +
    ∑ r, 2 * ‖oldJetCoefficient P bLast m r‖

/-- A uniform source-parameter bound for the mass of every row of weight at
most `S`.  It is independent of the active coefficient sides. -/
def sourceJetCoefficientBound {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (S : ℕ) : ℝ :=
  (S + 1 : ℝ) * (1 + 2 * ∑ r, ‖oldLog P r‖)

/-- The head coefficient spends at most one unit of the current
multi-index budget. -/
theorem norm_headJetCoefficient_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N S : ℕ)
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ S) :
    ‖headJetCoefficient P N m‖ ≤ (S + 1 : ℝ) := by
  have hcomponent : m 0 + 1 ≤ S + 1 := by
    exact Nat.add_le_add_right
      ((VDPLMultiIndex.component_le_weight m 0).trans hm) 1
  have hden : 1 ≤ ‖((P.q : ℂ) ^ N)‖ := by
    rw [norm_pow, Complex.norm_natCast]
    exact one_le_pow₀ (by exact_mod_cast (Nat.one_le_of_lt P.one_lt_q))
  rw [headJetCoefficient, norm_div]
  have hcast : ((m 0 : ℂ) + 1) = ((m 0 + 1 : ℕ) : ℂ) := by norm_num
  rw [hcast, Complex.norm_natCast]
  calc
    ((m 0 + 1 : ℕ) : ℝ) / ‖((P.q : ℂ) ^ N)‖ ≤
        ((m 0 + 1 : ℕ) : ℝ) / 1 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = ((m 0 + 1 : ℕ) : ℝ) := by ring
    _ ≤ (S + 1 : ℝ) := by exact_mod_cast hcomponent

/-- Each old-coordinate finite-difference coefficient is bounded by the
corresponding logarithm times the available multi-index budget. -/
theorem norm_oldJetCoefficient_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (bLast : ℤ) (hbLast : bLast ≠ 0)
    (S : ℕ) (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ S) (r : Fin oldRank) :
    ‖oldJetCoefficient P bLast m r‖ ≤
      ‖oldLog P r‖ * (S + 1 : ℝ) := by
  have hcomponent : m r.succ + 1 ≤ S + 1 := by
    exact Nat.add_le_add_right
      ((VDPLMultiIndex.component_le_weight m r.succ).trans hm) 1
  have hb : 1 ≤ ‖(bLast : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hbLast
  rw [oldJetCoefficient, norm_mul, norm_div]
  have hcast : ((m r.succ : ℂ) + 1) =
      ((m r.succ + 1 : ℕ) : ℂ) := by norm_num
  rw [hcast, Complex.norm_natCast]
  calc
    ‖oldLog P r‖ / ‖(bLast : ℂ)‖ * ((m r.succ + 1 : ℕ) : ℝ) ≤
        ‖oldLog P r‖ / 1 * ((m r.succ + 1 : ℕ) : ℝ) := by
      gcongr
    _ = ‖oldLog P r‖ * ((m r.succ + 1 : ℕ) : ℝ) := by ring
    _ ≤ ‖oldLog P r‖ * (S + 1 : ℝ) := by
      gcongr
      exact_mod_cast hcomponent

theorem jetCoefficientMass_le_sourceJetCoefficientBound {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ)
    (bLast : ℤ) (hbLast : bLast ≠ 0) (S : ℕ)
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ S) :
    jetCoefficientMass P N bLast m ≤ sourceJetCoefficientBound P S := by
  unfold jetCoefficientMass sourceJetCoefficientBound
  calc
    ‖headJetCoefficient P N m‖ +
        ∑ r, 2 * ‖oldJetCoefficient P bLast m r‖ ≤
      (S + 1 : ℝ) +
        ∑ r, 2 * (‖oldLog P r‖ * (S + 1 : ℝ)) := by
      gcongr with r
      · exact norm_headJetCoefficient_le P N S m hm
      · exact norm_oldJetCoefficient_le P bLast hbLast S m hm r
    _ = (S + 1 : ℝ) * (1 + 2 * ∑ r, ‖oldLog P r‖) := by
      rw [mul_add, mul_one, Finset.mul_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      ring

/-- If all errors queried by one row operation are bounded by `x`, its
output is bounded by the coefficient mass times `x`. -/
theorem jetErrorStep_le_mass_mul {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) (bLast : ℤ)
    (E : VDPLMultiIndex (oldRank + 1) → ℝ)
    (m : VDPLMultiIndex (oldRank + 1)) {x : ℝ}
    (hx : 0 ≤ x) (hm : E m ≤ x)
    (hbump : ∀ i, E (bump m i) ≤ x) :
    jetErrorStep P N bLast E m ≤
      jetCoefficientMass P N bLast m * x := by
  unfold jetErrorStep jetCoefficientMass
  calc
    ‖headJetCoefficient P N m‖ * E (bump m 0) +
        ∑ r, ‖oldJetCoefficient P bLast m r‖ *
          (E (bump m r.succ) + E m) ≤
      ‖headJetCoefficient P N m‖ * x +
        ∑ r, ‖oldJetCoefficient P bLast m r‖ * (x + x) := by
      gcongr with r
      · exact hbump 0
      · exact hbump r.succ
    _ = (‖headJetCoefficient P N m‖ +
        ∑ r, 2 * ‖oldJetCoefficient P bLast m r‖) * x := by
      rw [add_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      ring

theorem jetErrorStep_nonneg {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) (bLast : ℤ)
    (E : VDPLMultiIndex (oldRank + 1) → ℝ)
    (hE : ∀ m, 0 ≤ E m) (m : VDPLMultiIndex (oldRank + 1)) :
    0 ≤ jetErrorStep P N bLast E m := by
  unfold jetErrorStep
  apply add_nonneg
  · exact mul_nonneg (norm_nonneg _) (hE _)
  · exact Finset.sum_nonneg fun r _ ↦
      mul_nonneg (norm_nonneg _) (add_nonneg (hE _) (hE _))

theorem jetErrorIterate_nonneg {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) (bLast : ℤ)
    (E : VDPLMultiIndex (oldRank + 1) → ℝ)
    (hE : ∀ m, 0 ≤ E m) (j : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    0 ≤ jetErrorIterate P N bLast j E m := by
  induction j generalizing m with
  | zero => exact hE m
  | succ j ih =>
      exact jetErrorStep_nonneg P N bLast _ (fun m' ↦ ih m') m

theorem sourceJetCoefficientBound_nonneg {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (S : ℕ) :
    0 ≤ sourceJetCoefficientBound P S := by
  unfold sourceJetCoefficientBound
  positivity

/-- A constant pointwise row error grows by at most the uniform coefficient
mass at each differentiated moment.  This is the algebraic-rate estimate
used after equation (8). -/
theorem jetErrorIterate_const_le_pow {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ)
    (bLast : ℤ) (hbLast : bLast ≠ 0) (S j : ℕ)
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    ∀ m : VDPLMultiIndex (oldRank + 1),
      VDPLMultiIndex.weight m + j ≤ S →
      jetErrorIterate P N bLast j (fun _ ↦ delta) m ≤
        (sourceJetCoefficientBound P S) ^ j * delta := by
  induction j with
  | zero =>
      intro m _hm
      simp [jetErrorIterate]
  | succ j ih =>
      intro m hm
      rw [jetErrorIterate]
      have hbound :
          0 ≤ (sourceJetCoefficientBound P S) ^ j * delta :=
        mul_nonneg (pow_nonneg (sourceJetCoefficientBound_nonneg P S) j) hdelta
      calc
        jetErrorStep P N bLast
            (jetErrorIterate P N bLast j (fun _ ↦ delta)) m ≤
            jetCoefficientMass P N bLast m *
              ((sourceJetCoefficientBound P S) ^ j * delta) := by
          apply jetErrorStep_le_mass_mul P N bLast _ m hbound
          · exact ih m (by omega)
          · intro i
            apply ih (bump m i)
            rw [weight_bump]
            omega
        _ ≤ sourceJetCoefficientBound P S *
              ((sourceJetCoefficientBound P S) ^ j * delta) := by
          apply mul_le_mul_of_nonneg_right _ hbound
          apply jetCoefficientMass_le_sourceJetCoefficientBound
            P N bLast hbLast S m
          omega
        _ = (sourceJetCoefficientBound P S) ^ (j + 1) * delta := by
          rw [pow_succ]
          ring

/-- Division by the normalizing factorial can only improve the preceding
uniform estimate. -/
theorem jetErrorIterate_const_div_factorial_le_pow {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ)
    (bLast : ℤ) (hbLast : bLast ≠ 0) (S j : ℕ)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (m : VDPLMultiIndex (oldRank + 1))
    (hmj : VDPLMultiIndex.weight m + j ≤ S) :
    jetErrorIterate P N bLast j (fun _ ↦ delta) m /
        ‖(j.factorial : ℂ)‖ ≤
      (sourceJetCoefficientBound P S) ^ j * delta := by
  have hfactorial : 1 ≤ ‖(j.factorial : ℂ)‖ := by
    rw [Complex.norm_natCast]
    exact_mod_cast Nat.factorial_pos j
  calc
    jetErrorIterate P N bLast j (fun _ ↦ delta) m /
        ‖(j.factorial : ℂ)‖ ≤
        jetErrorIterate P N bLast j (fun _ ↦ delta) m := by
      exact div_le_self
        (jetErrorIterate_nonneg P N bLast (fun _ ↦ delta)
          (fun _ ↦ hdelta) j m)
        hfactorial
    _ ≤ (sourceJetCoefficientBound P S) ^ j * delta :=
      jetErrorIterate_const_le_pow P N bLast hbLast S j hdelta m hmj

/-- One row operation is Lipschitz for the explicit coefficient-norm
majorant.  Only the base row and its one-coordinate bumps are needed. -/
theorem norm_jetStep_sub_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) (bLast : ℤ)
    (F G : VDPLMultiIndex (oldRank + 1) → ℂ)
    (E : VDPLMultiIndex (oldRank + 1) → ℝ)
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : ‖F m - G m‖ ≤ E m)
    (hbump : ∀ i, ‖F (bump m i) - G (bump m i)‖ ≤ E (bump m i)) :
    ‖jetStep P N bLast F m - jetStep P N bLast G m‖ ≤
      jetErrorStep P N bLast E m := by
  have hrearrange :
      jetStep P N bLast F m - jetStep P N bLast G m =
        headJetCoefficient P N m * (F (bump m 0) - G (bump m 0)) +
          ∑ r, oldJetCoefficient P bLast m r *
            ((F (bump m r.succ) - G (bump m r.succ)) - (F m - G m)) := by
    unfold jetStep
    calc
      headJetCoefficient P N m * F (bump m 0) +
            ∑ r, oldJetCoefficient P bLast m r *
              (F (bump m r.succ) - F m) -
          (headJetCoefficient P N m * G (bump m 0) +
            ∑ r, oldJetCoefficient P bLast m r *
              (G (bump m r.succ) - G m)) =
          (headJetCoefficient P N m * F (bump m 0) -
            headJetCoefficient P N m * G (bump m 0)) +
          ((∑ r, oldJetCoefficient P bLast m r *
              (F (bump m r.succ) - F m)) -
            ∑ r, oldJetCoefficient P bLast m r *
              (G (bump m r.succ) - G m)) := by ring
      _ = headJetCoefficient P N m * (F (bump m 0) - G (bump m 0)) +
          ∑ r, (oldJetCoefficient P bLast m r *
              (F (bump m r.succ) - F m) -
            oldJetCoefficient P bLast m r *
              (G (bump m r.succ) - G m)) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        ring
      _ = headJetCoefficient P N m * (F (bump m 0) - G (bump m 0)) +
          ∑ r, oldJetCoefficient P bLast m r *
            ((F (bump m r.succ) - G (bump m r.succ)) - (F m - G m)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        ring
  rw [hrearrange]
  calc
    ‖headJetCoefficient P N m * (F (bump m 0) - G (bump m 0)) +
        ∑ r, oldJetCoefficient P bLast m r *
          ((F (bump m r.succ) - G (bump m r.succ)) - (F m - G m))‖ ≤
        ‖headJetCoefficient P N m * (F (bump m 0) - G (bump m 0))‖ +
          ‖∑ r, oldJetCoefficient P bLast m r *
            ((F (bump m r.succ) - G (bump m r.succ)) - (F m - G m))‖ :=
      norm_add_le _ _
    _ ≤ ‖headJetCoefficient P N m‖ * E (bump m 0) +
          ∑ r, ‖oldJetCoefficient P bLast m r‖ *
            (E (bump m r.succ) + E m) := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbump 0) (norm_nonneg _)
      · calc
          ‖∑ r, oldJetCoefficient P bLast m r *
              ((F (bump m r.succ) - G (bump m r.succ)) - (F m - G m))‖ ≤
              ∑ r, ‖oldJetCoefficient P bLast m r *
                ((F (bump m r.succ) - G (bump m r.succ)) - (F m - G m))‖ :=
            norm_sum_le _ _
          _ ≤ ∑ r, ‖oldJetCoefficient P bLast m r‖ *
              (E (bump m r.succ) + E m) := by
            apply Finset.sum_le_sum
            intro r _
            rw [norm_mul]
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact (norm_sub_le _ _).trans
              (add_le_add (hbump r.succ) hm)
    _ = jetErrorStep P N bLast E m := rfl

/-- Repeated source row operations preserve a pointwise error estimate on
the same weight simplex. -/
theorem norm_jetIterate_sub_le_of_weight {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) (bLast : ℤ)
    (F G : VDPLMultiIndex (oldRank + 1) → ℂ)
    (E : VDPLMultiIndex (oldRank + 1) → ℝ) (S j : ℕ)
    (hE : ∀ m, 0 ≤ E m)
    (hpoint : ∀ m, VDPLMultiIndex.weight m ≤ S →
      ‖F m - G m‖ ≤ E m) :
    ∀ m, VDPLMultiIndex.weight m + j ≤ S →
      ‖jetIterate P N bLast j F m - jetIterate P N bLast j G m‖ ≤
        jetErrorIterate P N bLast j E m := by
  induction j with
  | zero =>
      intro m hm
      exact hpoint m (by simpa using hm)
  | succ j ih =>
      intro m hm
      rw [jetIterate_succ, jetIterate_succ]
      apply norm_jetStep_sub_le
      · apply ih
        omega
      · intro i
        apply ih
        rw [weight_bump]
        omega

/-- A level seed kills the algebraic-rate source moment on every old grid
node whenever the base weight plus moment order stays inside the seed
budget. -/
theorem jetIterate_gSource_eq_zero_of_vanishesOn {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N R S : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hseed : VanishesOn (g state b bLast) 1 R S)
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ R)
    (m : VDPLMultiIndex (oldRank + 1))
    (hmj : VDPLMultiIndex.weight m + j ≤ S) :
    jetIterate P N bLast j
      (fun m' ↦ gSource state b bLast (l : ℂ) m') m = 0 := by
  apply jetIterate_eq_zero_of_weight P N bLast _ S j
    (fun m' hm' ↦ ?_) m hmj
  have hz := hseed l hl hlR (fromSourceMultiIndex P m')
    (by rw [weight_fromSourceMultiIndex]; exact hm')
  simpa [g, toSourceMultiIndex_fromSourceMultiIndex] using hz

/-- The same cancellation statement when the integral seed has already
been reindexed to literal source multiindices. -/
theorem jetIterate_gSource_eq_zero_of_sourceVanishesOn {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N R S : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hseed : VanishesOn (gSource state b bLast) 1 R S)
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ R)
    (m : VDPLMultiIndex (oldRank + 1))
    (hmj : VDPLMultiIndex.weight m + j ≤ S) :
    jetIterate P N bLast j
      (fun m' ↦ gSource state b bLast (l : ℂ) m') m = 0 := by
  apply jetIterate_eq_zero_of_weight P N bLast _ S j
    (fun m' hm' ↦ ?_) m hmj
  simpa using hseed l hl hlR m' hm'

/-- Source-parameter-rank version of algebraic-rate moment cancellation.
This is the shape consumed by the concrete Lemma 4 interpolation wrapper. -/
theorem jetIterate_g_eq_zero_of_vanishesOn {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N R S : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hseed : VanishesOn (g state b bLast) 1 R S)
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ R)
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ S) :
    jetIterate P N bLast j
      (fun m' ↦ gSource state b bLast (l : ℂ) m')
      (toSourceMultiIndex P m) = 0 := by
  apply jetIterate_gSource_eq_zero_of_vanishesOn state b bLast hseed hl hlR
  simpa [weight_toSourceMultiIndex] using hmj

/-- The normalized algebraic-rate moment also vanishes. -/
theorem normalized_jetIterate_g_eq_zero_of_vanishesOn {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N R S : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hseed : VanishesOn (g state b bLast) 1 R S)
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ R)
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ S) :
    jetIterate P N bLast j
        (fun m' ↦ gSource state b bLast (l : ℂ) m')
        (toSourceMultiIndex P m) /
      (j.factorial : ℂ) = 0 := by
  rw [jetIterate_g_eq_zero_of_vanishesOn state b bLast hseed hl hlR m hmj,
    zero_div]

/-- Equations (7)--(8) in their quantitative consumer form.  The analytic
jet is compared with the algebraic-rate moment having the same row
operation; the latter is zero by the integral seed. -/
theorem norm_normalizedIteratedDeriv_f_le_jetErrorIterate_of_vanishesOn
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {N R S : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : VanishesOn (g state b bLast) 1 R S)
    (E : VDPLMultiIndex (oldRank + 1) → ℝ) (hE : ∀ m, 0 ≤ E m)
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ R)
    (hpoint : ∀ m', VDPLMultiIndex.weight m' ≤ S →
      ‖fSource state b bLast (l : ℂ) m' -
        gSource state b bLast (l : ℂ) m'‖ ≤ E m')
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ S) :
    ‖iteratedDeriv j (fun w ↦ f state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      jetErrorIterate P N bLast j E (toSourceMultiIndex P m) /
        ‖(j.factorial : ℂ)‖ := by
  rw [normalizedIteratedDeriv_f_eq_jetIterate state b hbLast]
  have hzero := jetIterate_g_eq_zero_of_vanishesOn
    state b bLast hseed hl hlR m hmj
  have hdiff := norm_jetIterate_sub_le_of_weight P N bLast
    (fun m' ↦ fSource state b bLast (l : ℂ) m')
    (fun m' ↦ gSource state b bLast (l : ℂ) m') E S j hE hpoint
    (toSourceMultiIndex P m) (by simpa [weight_toSourceMultiIndex] using hmj)
  rw [hzero, sub_zero] at hdiff
  rw [norm_div]
  exact div_le_div_of_nonneg_right hdiff (norm_nonneg _)

/-- Literal-source-index form of the quantitative moment comparison. -/
theorem
    norm_normalizedIteratedDeriv_fSource_le_jetErrorIterate_of_sourceVanishesOn
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {N R S : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : VanishesOn (gSource state b bLast) 1 R S)
    (E : VDPLMultiIndex (oldRank + 1) → ℝ) (hE : ∀ m, 0 ≤ E m)
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ R)
    (hpoint : ∀ m', VDPLMultiIndex.weight m' ≤ S →
      ‖fSource state b bLast (l : ℂ) m' -
        gSource state b bLast (l : ℂ) m'‖ ≤ E m')
    (m : VDPLMultiIndex (oldRank + 1))
    (hmj : VDPLMultiIndex.weight m + j ≤ S) :
    ‖iteratedDeriv j (fun w ↦ fSource state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      jetErrorIterate P N bLast j E m / ‖(j.factorial : ℂ)‖ := by
  rw [normalizedIteratedDeriv_fSource_eq_jetIterate state b hbLast]
  have hzero := jetIterate_gSource_eq_zero_of_sourceVanishesOn
    state b bLast hseed hl hlR m hmj
  have hdiff := norm_jetIterate_sub_le_of_weight P N bLast
    (fun m' ↦ fSource state b bLast (l : ℂ) m')
    (fun m' ↦ gSource state b bLast (l : ℂ) m') E S j hE hpoint m hmj
  rw [hzero, sub_zero] at hdiff
  rw [norm_div]
  exact div_le_div_of_nonneg_right hdiff (norm_nonneg _)

/-- Uniform normalized-jet estimate obtained from a constant pointwise
`f-g` comparison on the source weight simplex. -/
theorem
    norm_normalizedIteratedDeriv_f_le_sourceJetCoefficientBound_pow_mul
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {N R S : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : VanishesOn (g state b bLast) 1 R S)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ R)
    (hpoint : ∀ m', VDPLMultiIndex.weight m' ≤ S →
      ‖fSource state b bLast (l : ℂ) m' -
        gSource state b bLast (l : ℂ) m'‖ ≤ delta)
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ S) :
    ‖iteratedDeriv j (fun w ↦ f state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      (sourceJetCoefficientBound P S) ^ j * delta := by
  apply (norm_normalizedIteratedDeriv_f_le_jetErrorIterate_of_vanishesOn
    state b hbLast hseed (fun _ ↦ delta) (fun _ ↦ hdelta)
    hl hlR hpoint m hmj).trans
  apply jetErrorIterate_const_div_factorial_le_pow
    P N bLast hbLast S j hdelta
  simpa [weight_toSourceMultiIndex] using hmj

/-- Literal-source-index version of the uniform normalized-jet estimate. -/
theorem
    norm_normalizedIteratedDeriv_fSource_le_sourceJetCoefficientBound_pow_mul
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {N R S : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : VanishesOn (gSource state b bLast) 1 R S)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ R)
    (hpoint : ∀ m', VDPLMultiIndex.weight m' ≤ S →
      ‖fSource state b bLast (l : ℂ) m' -
        gSource state b bLast (l : ℂ) m'‖ ≤ delta)
    (m : VDPLMultiIndex (oldRank + 1))
    (hmj : VDPLMultiIndex.weight m + j ≤ S) :
    ‖iteratedDeriv j (fun w ↦ fSource state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      (sourceJetCoefficientBound P S) ^ j * delta := by
  apply
    (norm_normalizedIteratedDeriv_fSource_le_jetErrorIterate_of_sourceVanishesOn
      state b hbLast hseed (fun _ ↦ delta) (fun _ ↦ hdelta)
      hl hlR hpoint m hmj).trans
  exact jetErrorIterate_const_div_factorial_le_pow
    P N bLast hbLast S j hdelta m hmj

/-- The concrete pointwise comparison error used in equations (7)--(8).
The coefficient-height input is not a new hypothesis: it is the
`LevelState.coeff_height` field used by `stateSourceMajorants`. -/
def sourceRowError {oldRank : ℕ} (P : VDPLParameters (Fin oldRank))
    {N : ℕ} (state : LevelState P N) (b : Fin oldRank → ℤ)
    (bLast : ℤ) (z : ℂ) (linearFormBound : ℝ)
    (m : VDPLMultiIndex (oldRank + 1)) : ℝ :=
  (stateSourceMajorants P state b bLast z m).error linearFormBound

theorem sourceRowError_nonneg {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (z : ℂ) {linearFormBound : ℝ} (hbound : 0 ≤ linearFormBound)
    (m : VDPLMultiIndex (oldRank + 1)) :
    0 ≤ sourceRowError P state b bLast z linearFormBound m := by
  let M := stateSourceMajorants P state b bLast z m
  change 0 ≤ M.growth *
    (Real.exp (M.amplificationMajorant * linearFormBound) *
      (M.amplificationMajorant * linearFormBound))
  apply mul_nonneg
  · unfold SourceMajorants.growth
    exact mul_nonneg
      (mul_nonneg M.supportMajorant_nonneg
        (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg))
      M.exponentialMajorant_nonneg
  · exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg M.amplificationMajorant_nonneg hbound)

/-- Fully concrete equations (7)--(8).  An `IntegralSeedAtLevel` for the
actual algebraic source family kills the transported `g`-moment.  The
normalized strict smallness of the rational logarithmic form, together with
the coefficient-height invariant of `state`, bounds every surviving `f-g`
row by the explicit iterated error majorant.  The budget hypothesis is sharp:
the base weight plus the jet order need only fit in `Slevel N`. -/
theorem norm_normalizedIteratedDeriv_f_le_sourceError_of_integralSeed
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : IntegralSeedAtLevel P (g state b bLast) N)
    (C₀ : ℝ)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ P.R N)
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ P.Slevel N) :
    ‖iteratedDeriv j (fun w ↦ f state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      jetErrorIterate P N bLast j
          (sourceRowError P state b bLast (l : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
          (toSourceMultiIndex P m) /
        ‖(j.factorial : ℂ)‖ := by
  apply norm_normalizedIteratedDeriv_f_le_jetErrorIterate_of_vanishesOn
    state b hbLast
    (by simpa only [IntegralSeedAtLevel] using hseed)
    (sourceRowError P state b bLast (l : ℂ)
      (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
  · intro m'
    exact sourceRowError_nonneg P state b bLast (l : ℂ)
      (by unfold smallLinearFormBound; positivity) m'
  · exact hl
  · exact hlR
  · intro m' _hm'
    have hform := norm_logForm_le_smallLinearFormBound_of_normalized
      P C₀ b bLast hsmall
    have hcomparison :=
      (stateSourceMajorants P state b bLast (l : ℂ) m').norm_vdplG_sub_vdplF_le_error
        (lastLog P) hbLast (by unfold smallLinearFormBound; positivity) hform
    change
      ‖gSource state b bLast (l : ℂ) m' -
          fSource state b bLast (l : ℂ) m'‖ ≤
        sourceRowError P state b bLast (l : ℂ)
          (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) m'
      at hcomparison
    simpa only [norm_sub_rev] using hcomparison
  · exact hmj

/-- The literal inner-step budget bookkeeping used by concrete Lemma 4.
For every old integral node and every normalized derivative below the lost
budget, the corresponding algebraic-rate moment is zero. -/
theorem innerStep_algebraicMoment_eq_zero {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N t : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hseed : VanishesOn (g state b bLast) 1
      (P.lemmaFourRadius N t) (P.lemmaFourBudget N t))
    (m : VDPLMultiIndex P.rank)
    (hm : VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1))
    (i : Fin (P.lemmaFourRadius N t))
    (j : Fin (P.lemmaFourBudget N t -
      P.lemmaFourBudget N (t + 1) + 1)) :
    jetIterate P N bLast j.1
      (fun m' ↦ gSource state b bLast ((i.1 + 1 : ℕ) : ℂ) m')
      (toSourceMultiIndex P m) = 0 := by
  apply jetIterate_g_eq_zero_of_vanishesOn state b bLast hseed
  · omega
  · omega
  · have hj : j.1 ≤ P.lemmaFourBudget N t -
        P.lemmaFourBudget N (t + 1) := by omega
    have hbudget := Nat.add_le_add hm hj
    exact hbudget.trans (by
      have hmono : P.lemmaFourBudget N (t + 1) ≤
          P.lemmaFourBudget N t :=
        Erdos240.BakerLemma4InnerInduction.lemmaFourBudget_succ_le P N t
      omega)

end Erdos240.BakerSourceMomentCancellation

#print axioms Erdos240.BakerSourceMomentCancellation.jetIterate_eq_zero_of_weight
#print axioms Erdos240.BakerSourceMomentCancellation.iteratedDeriv_fSource_eq_jetIterate
#print axioms Erdos240.BakerSourceMomentCancellation.jetIterate_g_eq_zero_of_vanishesOn
#print axioms
  Erdos240.BakerSourceMomentCancellation.norm_normalizedIteratedDeriv_f_le_jetErrorIterate_of_vanishesOn
#print axioms
  Erdos240.BakerSourceMomentCancellation.norm_normalizedIteratedDeriv_f_le_sourceJetCoefficientBound_pow_mul
#print axioms
  Erdos240.BakerSourceMomentCancellation.norm_normalizedIteratedDeriv_f_le_sourceError_of_integralSeed
#print axioms
  Erdos240.BakerSourceMomentCancellation.jetErrorIterate_const_div_factorial_le_pow
#print axioms
  Erdos240.BakerSourceMomentCancellation.norm_normalizedIteratedDeriv_fSource_le_sourceJetCoefficientBound_pow_mul
