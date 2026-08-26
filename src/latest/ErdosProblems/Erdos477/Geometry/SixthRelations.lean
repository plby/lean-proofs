/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Mason--Stothers consequences for linear relations between sixth powers.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.PolynomialBezout

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

omit [CharZero K] in
lemma isCoprime_of_no_common_root (p q : K[X])
    (h : ∀ x, p.eval x = 0 → q.eval x = 0 → False) : IsCoprime p q := by
  obtain ⟨a, ha⟩ := exists_bezout_of_no_common_root ![p, q] (by
    intro x
    by_cases hp : p.eval x = 0
    · exact ⟨1, h x hp⟩
    · exact ⟨0, hp⟩)
  exact ⟨a 0, a 1, by simpa [Fin.sum_univ_two] using ha⟩

/-- With no common zero, a second relation involving three nonzero
coefficients forces the first polynomial to be constant. -/
theorem weighted_triple_sixth_degree_zero (p q r s : K[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hroot : ∀ x, p.eval x = 0 → q.eval x = 0 → r.eval x = 0 → s.eval x = 0 → False)
    (hsum : p ^ 6 + q ^ 6 + r ^ 6 + s ^ 6 = 0)
    (a b c : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hrel : C a * p ^ 6 + C b * q ^ 6 + C c * r ^ 6 = 0) : p.natDegree = 0 := by
  have hcop : IsCoprime p q := isCoprime_of_no_common_root p q (by
    intro x hpx hqx
    have heval := congrArg (Polynomial.eval x) hrel
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_zero, hpx, hqx,
      zero_pow (by decide : 6 ≠ 0), mul_zero, zero_add] at heval
    have hrx : r.eval x = 0 := (pow_eq_zero_iff (by decide)).mp
      ((mul_eq_zero.mp heval).resolve_left hc)
    have hseval := congrArg (Polynomial.eval x) hsum
    simp only [eval_add, eval_pow, eval_zero, hpx, hqx, hrx,
      zero_pow (by decide : 6 ≠ 0), zero_add] at hseval
    exact hroot x hpx hqx hrx ((pow_eq_zero_iff (by decide)).mp hseval))
  exact (Polynomial.flt_catalan (by decide : 6 ≠ 0) (by decide : 6 ≠ 0)
    (by decide : 6 ≠ 0) (by decide) (by norm_num : (6 : K) ≠ 0)
    (by norm_num : (6 : K) ≠ 0) (by norm_num : (6 : K) ≠ 0)
    hp hq hr hcop ha hb hc hrel).1

/-- In a nonconstant base-point-free four-term identity, a proportional pair
of sixth powers must cancel, rather than contributing a nonzero third term. -/
theorem pair_sixth_relation_cancels (p q r s : K[X])
    (hpdeg : 0 < p.natDegree) (hr : r ≠ 0) (hs : s ≠ 0)
    (hroot : ∀ x, p.eval x = 0 → q.eval x = 0 → r.eval x = 0 → s.eval x = 0 → False)
    (hsum : p ^ 6 + q ^ 6 + r ^ 6 + s ^ 6 = 0)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrel : C a * p ^ 6 + C b * q ^ 6 = 0) : p ^ 6 + q ^ 6 = 0 := by
  have hp : p ≠ 0 := by intro h; simp [h] at hpdeg
  have hab : b - a = 0 := by
    by_contra hne
    have hrel' : C (b - a) * p ^ 6 + C b * r ^ 6 + C b * s ^ 6 = 0 := by
      simp only [map_sub]
      linear_combination C b * hsum - hrel
    have hroot' : ∀ x, p.eval x = 0 → r.eval x = 0 → s.eval x = 0 → q.eval x = 0 → False :=
      fun x hp hr hs hq => hroot x hp hq hr hs
    have hsum' : p ^ 6 + r ^ 6 + s ^ 6 + q ^ 6 = 0 := by linear_combination hsum
    have hdeg := weighted_triple_sixth_degree_zero p r s q hp hr hs hroot'
      hsum' (b - a) b b hne hb hb hrel'
    omega
  have hab' : b = a := sub_eq_zero.mp hab
  rw [hab', ← mul_add] at hrel
  exact (mul_eq_zero.mp hrel).resolve_left (C_ne_zero.mpr ha)

#print axioms pair_sixth_relation_cancels
-- 'Erdos477.Geometry.pair_sixth_relation_cancels' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
