/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
At most one integer point lies on any affine line in a non-sixth-power level.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.RealLines

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

lemma integer_sextic_line_identity_transfer (c : ℤ) (a b : Fin 3 → ℤ)
    (h : ∀ t : K, ((a 0 : K) * t + b 0) ^ 6 + ((a 1 : K) * t + b 1) ^ 6 -
      ((a 2 : K) * t + b 2) ^ 6 = c) :
    ∀ t : ℝ, ((a 0 : ℝ) * t + b 0) ^ 6 + ((a 1 : ℝ) * t + b 1) ^ 6 -
      ((a 2 : ℝ) * t + b 2) ^ 6 = c := by
  have hpoly : (C (a 0) * X + C (b 0)) ^ 6 + (C (a 1) * X + C (b 1)) ^ 6 -
      (C (a 2) * X + C (b 2)) ^ 6 = C c := by
    apply Polynomial.funext
    intro t
    apply Int.cast_injective (α := K)
    simpa using h (t : K)
  intro t
  have heval := congrArg (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t) hpoly
  simpa only [Polynomial.coe_eval₂RingHom, eval₂_add, eval₂_sub, eval₂_pow,
    eval₂_mul, eval₂_C, eval₂_X, Int.coe_castRingHom] using heval

/-- This includes lines not defined over the reals: two integer points would
give a real direction, contradicting the real coefficient calculation. -/
theorem integer_points_on_sextic_line_unique (c : ℤ) (hc : c ∉ PowerValues 6)
    (v a : Fin 3 → K)
    (hline : ∀ t : K, (v 0 + t * a 0) ^ 6 + (v 1 + t * a 1) ^ 6 -
      (v 2 + t * a 2) ^ 6 = c)
    (z w : Fin 3 → ℤ) (s t : K)
    (hz : ∀ k, (z k : K) = v k + s * a k)
    (hw : ∀ k, (w k : K) = v k + t * a k) : z = w := by
  let dir : Fin 3 → ℤ := fun k => w k - z k
  have hid : ∀ q : K, ((dir 0 : K) * q + z 0) ^ 6 + ((dir 1 : K) * q + z 1) ^ 6 -
      ((dir 2 : K) * q + z 2) ^ 6 = c := by
    intro q
    have hcoord (k) : (dir k : K) * q + z k = v k + (s + q * (t - s)) * a k := by
      simp only [dir, Int.cast_sub, hz k, hw k]
      ring
    simp only [hcoord]
    exact hline (s + q * (t - s))
  have hreal := integer_sextic_line_identity_transfer c dir z hid
  have hzero := no_real_sextic_line_through_integer_point c hc (fun k => (dir k : ℝ)) z hreal
  ext k
  have hk : (dir k : ℝ) = 0 := congrFun hzero k
  have hk' : dir k = 0 := Int.cast_eq_zero.mp hk
  exact (sub_eq_zero.mp hk').symm

theorem card_integer_points_on_sextic_line_le_one (c : ℤ) (hc : c ∉ PowerValues 6)
    (v a : Fin 3 → K)
    (hline : ∀ t : K, (v 0 + t * a 0) ^ 6 + (v 1 + t * a 1) ^ 6 -
      (v 2 + t * a 2) ^ 6 = c)
    (S : Finset (Fin 3 → ℤ)) (hS : ∀ z ∈ S, ∃ t : K, ∀ k, (z k : K) = v k + t * a k) :
    S.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro z hz w hw
  obtain ⟨s, hs⟩ := hS z hz
  obtain ⟨t, ht⟩ := hS w hw
  exact integer_points_on_sextic_line_unique c hc v a hline z w s t hs ht

#print axioms card_integer_points_on_sextic_line_le_one
-- 'Erdos477.Geometry.card_integer_points_on_sextic_line_le_one' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
