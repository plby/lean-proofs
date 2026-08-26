/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Excluding the selected integer points from quadratic parametrizations.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.WeightedQuadratics
import ErdosProblems.Erdos477.Diagonal

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

lemma three_weighted_sixth_degrees_zero (p q r : K[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hroot : ∀ x, p.eval x = 0 → q.eval x = 0 → r.eval x = 0 → False)
    (a b c : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hsum : C a * p ^ 6 + C b * q ^ 6 + C c * r ^ 6 = 0) :
    p.natDegree = 0 ∧ q.natDegree = 0 ∧ r.natDegree = 0 := by
  have hcop : IsCoprime p q := isCoprime_of_no_common_root p q (by
    intro x hpx hqx
    have heval := congrArg (Polynomial.eval x) hsum
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_zero, hpx, hqx,
      zero_pow (by decide : 6 ≠ 0), mul_zero, zero_add] at heval
    exact hroot x hpx hqx ((pow_eq_zero_iff (by decide)).mp
      ((mul_eq_zero.mp heval).resolve_left hc)))
  exact Polynomial.flt_catalan (by decide : 6 ≠ 0) (by decide : 6 ≠ 0)
    (by decide : 6 ≠ 0) (by decide) (by norm_num : (6 : K) ≠ 0)
    (by norm_num : (6 : K) ≠ 0) (by norm_num : (6 : K) ≠ 0)
    hp hq hr hcop ha hb hc hsum

/-- Coordinates one and two may vanish identically. The first and last
coordinates suffice to rule out constant parametrizations and handle these cases. -/
theorem diagonal_quadratic_cancellation_of_outer_ne_zero (c : K) (hc : c ≠ 0)
    (f : Fin 4 → K[X]) (hf : ∀ i, (f i).natDegree ≤ 2)
    (hf0 : f 0 ≠ 0) (hf3 : f 3 ≠ 0) (hinfty : ∃ i, (f i).natDegree = 2)
    (hroot : ∀ x : K, ∃ i, (f i).eval x ≠ 0)
    (hsum : f 0 ^ 6 + f 1 ^ 6 - f 2 ^ 6 - C c * f 3 ^ 6 = 0) :
    f 0 ^ 6 + f 1 ^ 6 = 0 ∨ f 0 ^ 6 - f 2 ^ 6 = 0 ∨ f 1 ^ 6 - f 2 ^ 6 = 0 := by
  have hnone (x) (h0 : (f 0).eval x = 0) (h1 : (f 1).eval x = 0)
      (h2 : (f 2).eval x = 0) (h3 : (f 3).eval x = 0) : False := by
    obtain ⟨i, hi⟩ := hroot x
    fin_cases i
    · exact hi h0
    · exact hi h1
    · exact hi h2
    · exact hi h3
  have hnonconstant : ¬ (∀ i, (f i).natDegree = 0) := by
    intro h
    obtain ⟨i, hi⟩ := hinfty
    rw [h i] at hi
    omega
  by_cases hf1 : f 1 = 0
  · by_cases hf2 : f 2 = 0
    · exact Or.inr (Or.inr (by simp [hf1, hf2]))
    · have hsum' : C (1 : K) * f 0 ^ 6 + C (-1) * f 2 ^ 6 + C (-c) * f 3 ^ 6 = 0 := by
        simpa [hf1, sub_eq_add_neg] using hsum
      have hd := three_weighted_sixth_degrees_zero (f 0) (f 2) (f 3) hf0 hf2 hf3
        (fun x h0 h2 h3 => hnone x h0 (by simp [hf1]) h2 h3)
        1 (-1) (-c) one_ne_zero (by norm_num) (neg_ne_zero.mpr hc) hsum'
      exact (hnonconstant (by intro i; fin_cases i <;> simp [hf1, hd.1, hd.2.1, hd.2.2])).elim
  by_cases hf2 : f 2 = 0
  · have hsum' : C (1 : K) * f 0 ^ 6 + C 1 * f 1 ^ 6 + C (-c) * f 3 ^ 6 = 0 := by
      simpa [hf2, sub_eq_add_neg] using hsum
    have hd := three_weighted_sixth_degrees_zero (f 0) (f 1) (f 3) hf0 hf1 hf3
      (fun x h0 h1 h3 => hnone x h0 h1 (by simp [hf2]) h3)
      1 1 (-c) one_ne_zero one_ne_zero (neg_ne_zero.mpr hc) hsum'
    exact (hnonconstant (by intro i; fin_cases i <;> simp [hf2, hd.1, hd.2.1, hd.2.2])).elim
  apply diagonal_quadratic_sixth_pair_cancellation c hc f hf _ hinfty hroot hsum
  intro i
  fin_cases i
  · exact hf0
  · exact hf1
  · exact hf2
  · exact hf3

/-- The integer points selected in the bad-shift argument cannot occur on a
base-point-free quadratic parametrization of the projective sextic. -/
theorem no_selected_point_on_quadratic_parametrization (c : ℤ) (hc : c ∉ PowerValues 6)
    (u x y : ℕ) (hu : 1 ≤ u) (hpoint : DiagonalPoint c u x y)
    (f : Fin 4 → K[X]) (hf : ∀ i, (f i).natDegree ≤ 2)
    (hinfty : ∃ i, (f i).natDegree = 2)
    (hroot : ∀ z : K, ∃ i, (f i).eval z ≠ 0)
    (hsum : f 0 ^ 6 + f 1 ^ 6 - f 2 ^ 6 - C (c : K) * f 3 ^ 6 = 0)
    (t d : K) (hd : d ≠ 0)
    (hval : (f 0).eval t = d * u ∧ (f 1).eval t = d * y ∧
      (f 2).eval t = d * x ∧ (f 3).eval t = d) : False := by
  have hc0 : c ≠ 0 := by
    intro h
    apply hc
    exact ⟨0, by simp [h]⟩
  have hf0 : f 0 ≠ 0 := by
    intro h
    have heq := hval.1
    rw [h, eval_zero] at heq
    have huK : (u : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact mul_ne_zero hd huK heq.symm
  have hf3 : f 3 ≠ 0 := by
    intro h
    have heq := hval.2.2.2
    rw [h, eval_zero] at heq
    exact hd heq.symm
  have hcancel := diagonal_quadratic_cancellation_of_outer_ne_zero (c : K)
    (by exact_mod_cast hc0) f hf hf0 hf3 hinfty hroot hsum
  have hno := diagonalPoint_no_cancellation hc hu hpoint
  rcases hcancel with h | h | h
  · have heq := congrArg (Polynomial.eval t) h
    simp only [eval_add, eval_pow, eval_zero, hval.1, hval.2.1, mul_pow, ← mul_add] at heq
    have hK := (mul_eq_zero.mp heq).resolve_left (pow_ne_zero 6 hd)
    apply hno.1
    exact_mod_cast hK
  · have heq := congrArg (Polynomial.eval t) h
    simp only [eval_sub, eval_pow, eval_zero, hval.1, hval.2.2.1, mul_pow, ← mul_sub] at heq
    have hK := (mul_eq_zero.mp heq).resolve_left (pow_ne_zero 6 hd)
    apply hno.2.1
    exact_mod_cast hK
  · have heq := congrArg (Polynomial.eval t) h
    simp only [eval_sub, eval_pow, eval_zero, hval.2.1, hval.2.2.1, mul_pow, ← mul_sub] at heq
    have hK := (mul_eq_zero.mp heq).resolve_left (pow_ne_zero 6 hd)
    apply hno.2.2.2.1
    exact_mod_cast hK

#print axioms no_selected_point_on_quadratic_parametrization
-- 'Erdos477.Geometry.no_selected_point_on_quadratic_parametrization' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
