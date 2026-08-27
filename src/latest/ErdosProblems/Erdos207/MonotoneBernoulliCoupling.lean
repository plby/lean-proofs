/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteProbability

/-! # Exact finite coupling of an accepted bit below an independent proposal bit -/

namespace Erdos207.FiniteLaw

open Finset
open scoped NNReal

noncomputable section

def monotoneBitMass (p q : ℝ≥0) : Bool × Bool → ℝ≥0
  | (false, false) => 1 - q
  | (false, true) => 0
  | (true, false) => q - p
  | (true, true) => p

theorem monotoneBitMass_first_sum (p q : ℝ≥0) (hpq : p ≤ q) (a : Bool) :
    ∑ b : Bool, monotoneBitMass p q (a, b) = bernoulliBitMass q a := by
  cases a
  · simp [monotoneBitMass, bernoulliBitMass]
  · simpa [monotoneBitMass, bernoulliBitMass] using add_tsub_cancel_of_le hpq

theorem monotoneBitMass_second_sum (p q : ℝ≥0) (hpq : p ≤ q) (hq : q ≤ 1) (b : Bool) :
    ∑ a : Bool, monotoneBitMass p q (a, b) = bernoulliBitMass p b := by
  cases b
  · simp only [Fintype.sum_bool, monotoneBitMass, bernoulliBitMass, Bool.false_eq_true, ite_false]
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, NNReal.coe_sub hpq, NNReal.coe_sub hq, NNReal.coe_sub (hpq.trans hq), NNReal.coe_one]
    ring
  · simp [monotoneBitMass, bernoulliBitMass]

def bernoulliBitLaw (p : ℝ≥0) (hp : p ≤ 1) : FiniteLaw Bool where
  mass := bernoulliBitMass p
  sum_mass := sum_bernoulliBitMass hp

def monotoneBitCoupling (p q : ℝ≥0) (hpq : p ≤ q) (hq : q ≤ 1) : FiniteLaw (Bool × Bool) where
  mass := monotoneBitMass p q
  sum_mass := by
    rw [Fintype.sum_prod_type]
    simp_rw [monotoneBitMass_first_sum p q hpq]
    exact sum_bernoulliBitMass hq

theorem monotoneBitCoupling_first (p q : ℝ≥0) (hpq : p ≤ q) (hq : q ≤ 1) :
    map Prod.fst (monotoneBitCoupling p q hpq hq) = bernoulliBitLaw q hq := by
  apply FiniteLaw.ext
  intro a
  change (∑ x : Bool × Bool, if x.1 = a then monotoneBitMass p q x else 0) = bernoulliBitMass q a
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ b : Bool, monotoneBitMass p q (a, b) := by cases a <;> simp [Fintype.sum_bool]
    _ = _ := monotoneBitMass_first_sum p q hpq a

theorem monotoneBitCoupling_second (p q : ℝ≥0) (hpq : p ≤ q) (hq : q ≤ 1) :
    map Prod.snd (monotoneBitCoupling p q hpq hq) = bernoulliBitLaw p (hpq.trans hq) := by
  apply FiniteLaw.ext
  intro b
  change (∑ x : Bool × Bool, if x.2 = b then monotoneBitMass p q x else 0) = bernoulliBitMass p b
  rw [Fintype.sum_prod_type, sum_comm]
  calc
    _ = ∑ a : Bool, monotoneBitMass p q (a, b) := by cases b <;> simp [Fintype.sum_bool]
    _ = _ := monotoneBitMass_second_sum p q hpq hq b

theorem monotoneBitCoupling_supported (p q : ℝ≥0) (hpq : p ≤ q) (hq : q ≤ 1) :
    (monotoneBitCoupling p q hpq hq).SupportedOn (fun x ↦ x.2 = true → x.1 = true) := by
  intro x hx
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> simp_all [monotoneBitCoupling, monotoneBitMass]

end

end Erdos207.FiniteLaw
