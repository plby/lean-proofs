/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Specializing rational functions at a point where a denominator is nonzero.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

/-- A denominator certificate for a rational function's value. -/
def EvaluatesAt (t : K) (r : RatFunc K) (v : K) : Prop :=
  ∃ p q : K[X], q.eval t ≠ 0 ∧
    algebraMap K[X] (RatFunc K) q * r = algebraMap K[X] (RatFunc K) p ∧
    p.eval t = v * q.eval t

theorem evaluatesAt_polynomial (t : K) (p : K[X]) :
    EvaluatesAt t (algebraMap K[X] (RatFunc K) p) (p.eval t) := by
  exact ⟨p, 1, by simp, by simp, by simp⟩

theorem evaluatesAt_constant (t c : K) : EvaluatesAt t (RatFunc.C c) c := by
  simpa only [RatFunc.algebraMap_C, eval_C] using evaluatesAt_polynomial t (C c)

theorem EvaluatesAt.unique {t : K} {r : RatFunc K} {v w : K}
    (hv : EvaluatesAt t r v) (hw : EvaluatesAt t r w) : v = w := by
  obtain ⟨p, q, hq, hp, hv⟩ := hv
  obtain ⟨p', q', hq', hp', hw⟩ := hw
  have hcross : p * q' = p' * q := by
    apply IsFractionRing.injective K[X] (RatFunc K)
    simp only [map_mul]
    rw [← hp, ← hp']
    ring
  have heval := congrArg (Polynomial.eval t) hcross
  simp only [eval_mul, hv, hw] at heval
  apply mul_right_cancel₀ (mul_ne_zero hq hq')
  linear_combination heval

theorem EvaluatesAt.ne_zero {t : K} {r : RatFunc K} {v : K}
    (h : EvaluatesAt t r v) (hv : v ≠ 0) : r ≠ 0 := by
  intro hr
  have hz : EvaluatesAt t (0 : RatFunc K) 0 := by
    simpa only [map_zero] using evaluatesAt_constant t 0
  exact hv (h.unique (hr ▸ hz))

theorem EvaluatesAt.add {t : K} {r s : RatFunc K} {v w : K}
    (hr : EvaluatesAt t r v) (hs : EvaluatesAt t s w) : EvaluatesAt t (r + s) (v + w) := by
  obtain ⟨p, q, hq, hp, hv⟩ := hr
  obtain ⟨p', q', hq', hp', hw⟩ := hs
  refine ⟨p * q' + p' * q, q * q', ?_, ?_, ?_⟩
  · simpa only [eval_mul] using mul_ne_zero hq hq'
  · simp only [map_mul, map_add]
    linear_combination algebraMap K[X] (RatFunc K) q' * hp +
      algebraMap K[X] (RatFunc K) q * hp'
  · simp only [eval_add, eval_mul, hv, hw]
    ring

theorem EvaluatesAt.neg {t : K} {r : RatFunc K} {v : K}
    (hr : EvaluatesAt t r v) : EvaluatesAt t (-r) (-v) := by
  obtain ⟨p, q, hq, hp, hv⟩ := hr
  refine ⟨-p, q, hq, ?_, ?_⟩
  · rw [map_neg, mul_neg, hp]
  · rw [eval_neg, hv]
    ring

theorem EvaluatesAt.sub {t : K} {r s : RatFunc K} {v w : K}
    (hr : EvaluatesAt t r v) (hs : EvaluatesAt t s w) : EvaluatesAt t (r - s) (v - w) := by
  simpa only [sub_eq_add_neg] using hr.add hs.neg

theorem EvaluatesAt.mul {t : K} {r s : RatFunc K} {v w : K}
    (hr : EvaluatesAt t r v) (hs : EvaluatesAt t s w) : EvaluatesAt t (r * s) (v * w) := by
  obtain ⟨p, q, hq, hp, hv⟩ := hr
  obtain ⟨p', q', hq', hp', hw⟩ := hs
  refine ⟨p * p', q * q', ?_, ?_, ?_⟩
  · simpa only [eval_mul] using mul_ne_zero hq hq'
  · simp only [map_mul]
    calc
      _ = (algebraMap K[X] (RatFunc K) q * r) *
          (algebraMap K[X] (RatFunc K) q' * s) := by ring
      _ = _ := by rw [hp, hp']
  · simp only [eval_mul, hv, hw]
    ring

theorem EvaluatesAt.inv {t : K} {r : RatFunc K} {v : K}
    (hr : EvaluatesAt t r v) (hv : v ≠ 0) : EvaluatesAt t r⁻¹ v⁻¹ := by
  have hr0 := hr.ne_zero hv
  obtain ⟨p, q, hq, hp, hpval⟩ := hr
  refine ⟨q, p, ?_, ?_, ?_⟩
  · rw [hpval]
    exact mul_ne_zero hv hq
  · rw [← hp, mul_assoc, mul_inv_cancel₀ hr0, mul_one]
  · rw [hpval, ← mul_assoc, inv_mul_cancel₀ hv, one_mul]

theorem EvaluatesAt.div {t : K} {r s : RatFunc K} {v w : K}
    (hr : EvaluatesAt t r v) (hs : EvaluatesAt t s w) (hw : w ≠ 0) :
    EvaluatesAt t (r / s) (v / w) := by
  simpa only [div_eq_mul_inv] using hr.mul (hs.inv hw)

theorem EvaluatesAt.pow {t : K} {r : RatFunc K} {v : K}
    (hr : EvaluatesAt t r v) (n : ℕ) : EvaluatesAt t (r ^ n) (v ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using evaluatesAt_constant t 1
  | succ n ih => simpa only [pow_succ] using ih.mul hr

theorem evaluatesAt_mvPolynomial {σ : Type*} (t : K) (x : σ → RatFunc K) (v : σ → K)
    (hx : ∀ i, EvaluatesAt t (x i) (v i)) (P : MvPolynomial σ K) :
    EvaluatesAt t (MvPolynomial.eval₂Hom RatFunc.C x P) (MvPolynomial.eval v P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using evaluatesAt_constant t a
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
      simpa using hp.mul (hx i)

#print axioms evaluatesAt_mvPolynomial
-- 'Erdos477.Geometry.evaluatesAt_mvPolynomial' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
