/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite Newton approximation with a fixed inverse derivative modulo a parameter.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Counting

open Polynomial

variable {R : Type*} [CommRing R]

/-- One fixed-derivative Newton step improves the congruence by one order.
Only an inverse modulo the parameter is needed; no completeness is assumed. -/
theorem pow_dvd_newton_error (p : R[X]) (q y z v : R) (N : ℕ) (hN : 1 ≤ N)
    (hroot : p.eval y = 0) (hder : q ∣ v * p.derivative.eval y - 1)
    (herr : q ^ N ∣ y - z) : q ^ (N + 1) ∣ y - (z - v * p.eval z) := by
  obtain ⟨r, hr⟩ := p.exists_mul_sq_add_linear_part_eq_eval_add y (z - y)
  have hz : p.eval z = r * (z - y) ^ 2 + p.derivative.eval y * (z - y) := by
    simpa only [hroot, add_zero, add_sub_cancel] using hr.symm
  have hdiff : q ^ N ∣ z - y := by simpa only [neg_sub] using dvd_neg.mpr herr
  have hlinear : q ^ (N + 1) ∣ (z - y) * (v * p.derivative.eval y - 1) := by
    rw [pow_succ]
    exact mul_dvd_mul hdiff hder
  have hsq : q ^ (2 * N) ∣ (z - y) ^ 2 := by
    simpa only [← pow_mul, Nat.mul_comm N 2] using pow_dvd_pow_of_dvd hdiff 2
  have hquadratic : q ^ (N + 1) ∣ v * r * (z - y) ^ 2 :=
    dvd_mul_of_dvd_right ((pow_dvd_pow q (by omega : N + 1 ≤ 2 * N)).trans hsq) _
  convert dvd_add hlinear hquadratic using 1
  rw [hz]
  ring

noncomputable def newtonApproximation (p : R[X]) (v b : R) : ℕ → R
  | 0 => b
  | n + 1 => newtonApproximation p v b n - v * p.eval (newtonApproximation p v b n)

lemma map_newtonApproximation {S : Type*} [CommRing S] (φ : R →+* S)
    (p : R[X]) (v b : R) (N : ℕ) :
    φ (newtonApproximation p v b N) = newtonApproximation (p.map φ) (φ v) (φ b) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simp only [newtonApproximation, map_sub, map_mul, ← Polynomial.eval_map_apply, ih]

lemma newtonApproximation_eq_of_root (p : R[X]) (v b : R) (hb : p.eval b = 0) (N : ℕ) :
    newtonApproximation p v b N = b := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [newtonApproximation, ih, hb, mul_zero, sub_zero]

/-- The finite iteration approximates every root in the specified residue
class to any prescribed order. -/
theorem pow_dvd_newtonApproximation_error (p : R[X]) (q y v b : R)
    (hroot : p.eval y = 0) (hder : q ∣ v * p.derivative.eval y - 1)
    (hbase : q ∣ y - b) (N : ℕ) : q ^ (N + 1) ∣ y - newtonApproximation p v b N := by
  induction N with
  | zero => simpa only [newtonApproximation, Nat.zero_add, pow_one] using hbase
  | succ N ih =>
      exact pow_dvd_newton_error p q y (newtonApproximation p v b N) v (N + 1)
        (Nat.le_add_left 1 N) hroot hder ih

#print axioms pow_dvd_newtonApproximation_error
-- 'Erdos477.Counting.pow_dvd_newtonApproximation_error' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
