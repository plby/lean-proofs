/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceState
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Source jet transport for the van der Poorten--Loxton induction

This file formalizes equations (7)--(8) in the source proof.  Differentiating
the auxiliary function `f` once raises either the head Hasse-derivative order
or one of the ordinary old-Delta orders.  The latter assertion uses the exact
identity

`x * Delta(x;m) = (m+1) * (Delta(x;m+1) - Delta(x;m))`.

Iteration gives an exact finite transport for every normalized analytic jet.
Combining it with an integral vanishing seed for `g` and the exact logarithmic
perturbation estimate gives the small normalized jets consumed by Lemmas 4
and 5.
-/

open scoped BigOperators Polynomial

noncomputable section

namespace Erdos240.BakerSourceJetTransport

open Finset Polynomial
open Erdos240
open Erdos240.BakerLemma3
open Erdos240.BakerSourceState
open Erdos240.DeltaPower

/-- Increase one coordinate of a source multi-index by one. -/
def bump {n : ℕ} (m : VDPLMultiIndex n) (i : Fin n) : VDPLMultiIndex n :=
  Function.update m i (m i + 1)

@[simp] theorem bump_same {n : ℕ} (m : VDPLMultiIndex n) (i : Fin n) :
    bump m i i = m i + 1 := by
  simp [bump]

@[simp] theorem bump_ne {n : ℕ} (m : VDPLMultiIndex n) {i j : Fin n}
    (hij : j ≠ i) : bump m i j = m j := by
  simp [bump, hij]

theorem weight_bump {n : ℕ} (m : VDPLMultiIndex n) (i : Fin n) :
    VDPLMultiIndex.weight (bump m i) = VDPLMultiIndex.weight m + 1 := by
  classical
  simp only [VDPLMultiIndex.weight, bump]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [Finset.erase_eq]
  omega

/-- The exact ordinary-Delta recurrence used when a derivative hits an old
exponential factor. -/
theorem simpleDeltaEval_mul_variable (m : ℕ) (x : ℂ) :
    x * simpleDeltaEval m x =
      (m + 1 : ℂ) * (simpleDeltaEval (m + 1) x - simpleDeltaEval m x) := by
  have hpoly :
      Polynomial.C (m + 1 : ℚ) * Erdos240Delta.delta (m + 1) =
        (Polynomial.X + Polynomial.C (m + 1 : ℚ)) *
          Erdos240Delta.delta m := by
    have hm1 : (m + 1 : ℚ) ≠ 0 := by positivity
    have hfac : ((m + 1).factorial : ℚ) =
        (m + 1 : ℚ) * (m.factorial : ℚ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hmf : (m.factorial : ℚ) ≠ 0 := by positivity
    have hscalar : (m + 1 : ℚ) *
        (((m + 1).factorial : ℚ))⁻¹ = ((m.factorial : ℚ))⁻¹ := by
      rw [hfac]
      field_simp [hm1, hmf]
    calc
      Polynomial.C (m + 1 : ℚ) * Erdos240Delta.delta (m + 1) =
          Polynomial.C (m + 1 : ℚ) *
            (Polynomial.C (((m + 1).factorial : ℚ)⁻¹) *
              (Erdos240Delta.deltaNumerator m *
                (Polynomial.X + Polynomial.C (m + 1 : ℚ)))) := by
            rw [Erdos240Delta.delta,
              Erdos240Delta.deltaNumerator_succ]
      _ = Polynomial.C (((m.factorial : ℚ))⁻¹) *
            (Erdos240Delta.deltaNumerator m *
              (Polynomial.X + Polynomial.C (m + 1 : ℚ))) := by
            rw [← mul_assoc, ← Polynomial.C_mul, hscalar]
      _ = (Polynomial.X + Polynomial.C (m + 1 : ℚ)) *
            Erdos240Delta.delta m := by
          rw [Erdos240Delta.delta]
          ring
  have heval := congrArg
    (fun p : ℚ[X] ↦ Polynomial.eval₂ (algebraMap ℚ ℂ) x p) hpoly
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_add,
    Polynomial.eval₂_X] at heval
  change x * Polynomial.eval₂ (algebraMap ℚ ℂ) x (Erdos240Delta.delta m) =
    (m + 1 : ℂ) *
      (Polynomial.eval₂ (algebraMap ℚ ℂ) x (Erdos240Delta.delta (m + 1)) -
        Polynomial.eval₂ (algebraMap ℚ ℂ) x (Erdos240Delta.delta m))
  push_cast at heval
  calc
    x * Polynomial.eval₂ (algebraMap ℚ ℂ) x (Erdos240Delta.delta m) =
        (x + (m + 1 : ℂ)) *
            Polynomial.eval₂ (algebraMap ℚ ℂ) x (Erdos240Delta.delta m) -
          (m + 1 : ℂ) *
            Polynomial.eval₂ (algebraMap ℚ ℂ) x (Erdos240Delta.delta m) := by
          ring
    _ = (m + 1 : ℂ) *
          Polynomial.eval₂ (algebraMap ℚ ℂ) x
            (Erdos240Delta.delta (m + 1)) -
          (m + 1 : ℂ) *
            Polynomial.eval₂ (algebraMap ℚ ℂ) x
              (Erdos240Delta.delta m) := by
        rw [heval]
    _ = _ := by ring

/-- Differentiating a normalized head Hasse derivative raises its order by
one and contributes the factor `m+1`. -/
theorem hasDerivAt_poweredDeltaHasseEval (h power m : ℕ) (z : ℂ) :
    HasDerivAt (poweredDeltaHasseEval h power m)
      ((m + 1 : ℂ) * poweredDeltaHasseEval h power (m + 1) z) z := by
  have hcomp := congrArg
    (fun D : ℚ[X] →ₗ[ℚ] ℚ[X] ↦ D (poweredDelta h power))
    (Polynomial.hasseDeriv_comp (R := ℚ) 1 m)
  have hderiv :
      (poweredDeltaHasse h power m).derivative =
        (m + 1) • poweredDeltaHasse h power (m + 1) := by
    simpa only [LinearMap.comp_apply, Polynomial.hasseDeriv_one',
      LinearMap.smul_apply, Nat.choose_one_right, poweredDeltaHasse,
      Nat.add_comm] using hcomp
  have hderivC :
      (poweredDeltaHasse h power m).derivative =
        Polynomial.C (m + 1 : ℚ) *
          poweredDeltaHasse h power (m + 1) := by
    simpa [nsmul_eq_mul] using hderiv
  let pC : ℂ[X] :=
    (poweredDeltaHasse h power m).map (algebraMap ℚ ℂ)
  have hp := pC.hasDerivAt z
  have hfun : (fun w ↦ pC.eval w) = poweredDeltaHasseEval h power m := by
    funext w
    rw [poweredDeltaHasseEval, Polynomial.eval₂_eq_eval_map]
  have hvalue : pC.derivative.eval z =
      (m + 1 : ℂ) * poweredDeltaHasseEval h power (m + 1) z := by
    simp only [pC, Polynomial.derivative_map, hderivC,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
      Polynomial.eval_C, poweredDeltaHasseEval,
      Polynomial.eval₂_eq_eval_map]
    push_cast
    rfl
  rw [hfun] at hp
  simpa [hvalue] using hp

/-! ## One-step source recurrence -/

/-- Coefficient of the head shift in one analytic differentiation. -/
def headJetCoefficient {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) : ℂ :=
  (m 0 + 1 : ℂ) / (P.q : ℂ) ^ N

/-- Coefficient of the `r`th ordinary-Delta finite difference in one
analytic differentiation. -/
def oldJetCoefficient {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (bLast : ℤ)
    (m : VDPLMultiIndex (oldRank + 1)) (r : Fin oldRank) : ℂ :=
  (oldLog P r / (bLast : ℂ)) * (m r.succ + 1 : ℂ)

/-- The exact first-order row operation on a family indexed by source
multiindices. -/
def jetStep {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) (bLast : ℤ)
    (F : VDPLMultiIndex (oldRank + 1) → ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) : ℂ :=
  headJetCoefficient P N m * F (bump m 0) +
    ∑ r, oldJetCoefficient P bLast m r *
      (F (bump m r.succ) - F m)

/-- Differentiating the source Delta factor raises only its head Hasse
order. -/
theorem hasDerivAt_A {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (lambda : LevelIndex P N) (m : VDPLMultiIndex (oldRank + 1))
    (z : ℂ) :
    HasDerivAt (fun w ↦ A state b bLast lambda w m)
      (headJetCoefficient P N m *
        A state b bLast lambda z (bump m 0)) z := by
  let Cprod : ℂ :=
    ∏ r, simpleDeltaEval (m r.succ)
      ((bLast : ℂ) * coordinates.oldExponent lambda r -
        (b r : ℂ) * coordinates.lastExponent lambda)
  have harg : HasDerivAt
      (fun w : ℂ ↦ scaledArgument P.q N w + coordinates.shift lambda)
      (((P.q : ℂ) ^ N)⁻¹) z := by
    simpa [scaledArgument] using
      ((hasDerivAt_id z).div_const ((P.q : ℂ) ^ N)).add_const
        (coordinates.shift lambda : ℂ)
  have hhead :=
    (hasDerivAt_poweredDeltaHasseEval P.h
      (coordinates.deltaIndex lambda + 1) (m 0)
      (scaledArgument P.q N z + coordinates.shift lambda)).comp z harg
  have hmul := hhead.mul_const Cprod
  have hAfun :
      (fun w ↦ A state b bLast lambda w m) =
        fun w ↦
          poweredDeltaHasseEval P.h
              (coordinates.deltaIndex lambda + 1) (m 0)
              (scaledArgument P.q N w + coordinates.shift lambda) * Cprod := by
    rfl
  rw [hAfun]
  apply hmul.congr_deriv
  dsimp [A, auxiliaryFactor, coordinatesForState, Cprod,
    headJetCoefficient]
  simp only [bump_same]
  simp_rw [bump_ne m (Fin.succ_ne_zero _)]
  rw [div_eq_mul_inv]
  ring

/-- A rate contribution in an old coordinate is exactly the corresponding
ordinary-Delta finite difference.  This is the termwise algebraic heart of
source equation (7). -/
theorem oldJetCoefficient_mul_A_sub_eq_gamma_mul_oldLog_mul_A
    {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (lambda : LevelIndex P N)
    (m : VDPLMultiIndex (oldRank + 1)) (z : ℂ) (r : Fin oldRank) :
    oldJetCoefficient P bLast m r *
        (A state b bLast lambda z (bump m r.succ) -
          A state b bLast lambda z m) =
      gamma coordinates b bLast lambda r * oldLog P r *
        A state b bLast lambda z m := by
  classical
  let x : Fin oldRank → ℂ := fun s ↦
    (bLast : ℂ) * coordinates.oldExponent lambda s -
      (b s : ℂ) * coordinates.lastExponent lambda
  let D : VDPLMultiIndex (oldRank + 1) → Fin oldRank → ℂ :=
    fun m' s ↦ simpleDeltaEval (m' s.succ) (x s)
  let H : ℂ := poweredDeltaHasseEval P.h
    (coordinates.deltaIndex lambda + 1) (m 0)
    (scaledArgument P.q N z + coordinates.shift lambda)
  let R : ℂ := ∏ s ∈ Finset.univ.erase r, D m s
  have hprod_m : (∏ s, D m s) = R * D m r := by
    exact (Finset.prod_erase_mul Finset.univ (D m)
      (Finset.mem_univ r)).symm
  have hprod_bump : (∏ s, D (bump m r.succ) s) =
      R * D (bump m r.succ) r := by
    rw [← Finset.prod_erase_mul Finset.univ (D (bump m r.succ))
      (Finset.mem_univ r)]
    congr 1
    apply Finset.prod_congr rfl
    intro s hs
    have hsr : s ≠ r := Finset.ne_of_mem_erase hs
    simp [D, bump, hsr]
  have hD_bump : D (bump m r.succ) r =
      simpleDeltaEval (m r.succ + 1) (x r) := by
    simp [D, bump]
  have hD : D m r = simpleDeltaEval (m r.succ) (x r) := rfl
  have hx : x r = (bLast : ℂ) * gamma coordinates b bLast lambda r := by
    have hbLastC : (bLast : ℂ) ≠ 0 := by exact_mod_cast hbLast
    dsimp [x, gamma]
    field_simp [hbLastC]
  dsimp [A, auxiliaryFactor, coordinatesForState, oldJetCoefficient]
  change (oldLog P r / (bLast : ℂ)) * (m r.succ + 1 : ℂ) *
      (H * (∏ s, D (bump m r.succ) s) - H * (∏ s, D m s)) =
    gamma coordinates b bLast lambda r * oldLog P r *
      (H * (∏ s, D m s))
  rw [hprod_bump, hprod_m, hD_bump, hD]
  have hbLastC : (bLast : ℂ) ≠ 0 := by exact_mod_cast hbLast
  calc
    (oldLog P r / (bLast : ℂ)) * (m r.succ + 1 : ℂ) *
        (H * (R * simpleDeltaEval (m r.succ + 1) (x r)) -
          H * (R * simpleDeltaEval (m r.succ) (x r))) =
      (oldLog P r / (bLast : ℂ)) * H * R *
        ((m r.succ + 1 : ℂ) *
          (simpleDeltaEval (m r.succ + 1) (x r) -
            simpleDeltaEval (m r.succ) (x r))) := by ring
    _ = (oldLog P r / (bLast : ℂ)) * H * R *
        (x r * simpleDeltaEval (m r.succ) (x r)) := by
      rw [← simpleDeltaEval_mul_variable]
    _ = gamma coordinates b bLast lambda r * oldLog P r *
        (H * (R * simpleDeltaEval (m r.succ) (x r))) := by
      rw [hx]
      field_simp [hbLastC]

/-- Summing the coordinate identities identifies the full modified
exponential rate with the old-coordinate part of `jetStep`. -/
theorem modifiedRate_mul_A_eq_sum_oldJet {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (lambda : LevelIndex P N)
    (m : VDPLMultiIndex (oldRank + 1)) (z : ℂ) :
    modifiedRate coordinates b bLast (oldLog P) lambda *
        A state b bLast lambda z m =
      ∑ r, oldJetCoefficient P bLast m r *
        (A state b bLast lambda z (bump m r.succ) -
          A state b bLast lambda z m) := by
  classical
  rw [modifiedRate, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  exact (oldJetCoefficient_mul_A_sub_eq_gamma_mul_oldLog_mul_A
    state b hbLast lambda m z r).symm

/-- Exact source equation (7): one analytic derivative is the head Hasse
shift plus the ordinary-Delta finite differences. -/
theorem hasDerivAt_fSource {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (m : VDPLMultiIndex (oldRank + 1)) (z : ℂ) :
    HasDerivAt (fun w ↦ fSource state b bLast w m)
      (jetStep P N bLast (fun m' ↦ fSource state b bLast z m') m) z := by
  classical
  let rate : LevelIndex P N → ℂ :=
    modifiedRate coordinates b bLast (oldLog P)
  let raw : LevelIndex P N → ℂ := fun lambda ↦
    (state.coeff lambda : ℂ) *
      (headJetCoefficient P N m *
          A state b bLast lambda z (bump m 0) +
        rate lambda * A state b bLast lambda z m) *
      Complex.exp (rate lambda * z)
  have hterm (lambda : LevelIndex P N) :
      HasDerivAt
        (fun w ↦ (state.coeff lambda : ℂ) *
          A state b bLast lambda w m *
            Complex.exp (rate lambda * w))
        (raw lambda) z := by
    have hlin : HasDerivAt (fun w : ℂ ↦ rate lambda * w)
        (rate lambda) z := by
      simpa using (hasDerivAt_id z).const_mul (rate lambda)
    have hexp : HasDerivAt (fun w : ℂ ↦ Complex.exp (rate lambda * w))
        (rate lambda * Complex.exp (rate lambda * z)) z := by
      simpa [Function.comp_def, mul_comm] using
        (Complex.hasDerivAt_exp (rate lambda * z)).comp z hlin
    have hmul :=
      ((hasDerivAt_A state b bLast lambda m z).const_mul
        (state.coeff lambda : ℂ)).mul hexp
    apply hmul.congr_deriv
    dsimp [raw, rate]
    ring
  have hraw : HasDerivAt
      (fun w ↦ ∑ lambda, (state.coeff lambda : ℂ) *
        A state b bLast lambda w m *
          Complex.exp (rate lambda * w))
      (∑ lambda, raw lambda) z := by
    exact HasDerivAt.fun_sum fun lambda _ ↦ hterm lambda
  have hfun :
      (fun w ↦ fSource state b bLast w m) =
        (fun w ↦ ∑ lambda, (state.coeff lambda : ℂ) *
          A state b bLast lambda w m *
            Complex.exp (rate lambda * w)) := by
    funext w
    rw [fSource, fWithLogs_eq_sum]
  rw [hfun]
  apply hraw.congr_deriv
  dsimp [raw, rate, jetStep]
  rw [fSource, fWithLogs_eq_sum]
  simp_rw [modifiedRate_mul_A_eq_sum_oldJet state b hbLast]
  simp_rw [fWithLogs_eq_sum]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  have hbase :
      (∑ r, ∑ lambda, oldJetCoefficient P bLast m r *
        ((state.coeff lambda : ℂ) * A state b bLast lambda z m *
          Complex.exp
            (modifiedRate coordinates b bLast (oldLog P) lambda * z))) =
      (∑ lambda, ∑ r, oldJetCoefficient P bLast m r *
        ((state.coeff lambda : ℂ) * A state b bLast lambda z m *
          Complex.exp
            (modifiedRate coordinates b bLast (oldLog P) lambda * z))) := by
    rw [Finset.sum_comm]
  rw [hbase]
  ring_nf
  apply congrArg₂ (fun x y : ℂ ↦ x - y)
  · apply congrArg₂ (fun x y : ℂ ↦ x + y)
    · apply Finset.sum_congr rfl
      intro lambda _
      ring_nf
    · apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro lambda _
      ring
  · apply Finset.sum_congr rfl
    intro lambda _
    apply Finset.sum_congr rfl
    intro r _
    ring

end Erdos240.BakerSourceJetTransport

#print axioms Erdos240.BakerSourceJetTransport.hasDerivAt_fSource
