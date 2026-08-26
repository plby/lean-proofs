/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Moving a quadratic parametrization's parameter at infinity away from its coordinate zeroes.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.QuadraticCancellation

namespace Erdos477.Geometry

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

lemma reflect_pow_of_natDegree_le (D n : ℕ) (p : K[X]) (hp : p.natDegree ≤ D) :
    reflect (D * n) (p ^ n) = (reflect D p) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, pow_succ,
        reflect_mul (p ^ n) p (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hp) hp,
        ih, pow_succ]

variable [IsAlgClosed K] [CharZero K]

/-- The degree-two cancellation argument is unchanged if some nonzero
coordinates have smaller affine degree, provided there is no common zero
at the parameter's point at infinity. -/
theorem quadratic_sixth_pair_cancellation_of_le (f : Fin 4 → K[X])
    (hf : ∀ i, (f i).natDegree ≤ 2) (hf0 : ∀ i, f i ≠ 0)
    (hinfty : ∃ i, (f i).natDegree = 2)
    (hroot : ∀ x : K, ∃ i, (f i).eval x ≠ 0)
    (hsum : f 0 ^ 6 + f 1 ^ 6 + f 2 ^ 6 + f 3 ^ 6 = 0) :
    f 0 ^ 6 + f 1 ^ 6 = 0 ∨ f 0 ^ 6 + f 2 ^ 6 = 0 ∨ f 1 ^ 6 + f 2 ^ 6 = 0 := by
  classical
  have hprod : (∏ i, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hf0 i)
  obtain ⟨a, ha⟩ : ∃ a : K, (∏ i, f i).eval a ≠ 0 := by
    by_contra h
    push Not at h
    apply hprod
    apply Polynomial.funext
    intro a
    simpa using h a
  have hfa (i) : (f i).eval a ≠ 0 := by
    rw [eval_prod] at ha
    exact Finset.prod_ne_zero_iff.mp ha i (Finset.mem_univ i)
  let F : Fin 4 → K[X] := fun i => reflect 2 (taylor a (f i))
  have htdeg (i) : (taylor a (f i)).natDegree ≤ 2 := by rw [natDegree_taylor]; exact hf i
  have hFdeg (i) : (F i).natDegree = 2 := by
    have hupper : (F i).natDegree ≤ 2 :=
      natDegree_reflect_le.trans (max_le le_rfl (htdeg i))
    have hcoeff : (F i).coeff 2 ≠ 0 := by
      change (reflect 2 (taylor a (f i))).coeff 2 ≠ 0
      rw [coeff_reflect, show revAt 2 2 = 0 from rfl, taylor_coeff_zero]
      exact hfa i
    exact hupper.antisymm (le_natDegree_of_ne_zero hcoeff)
  have hFroot (x : K) : ∃ i, (F i).eval x ≠ 0 := by
    by_cases hx : x = 0
    · obtain ⟨i, hi⟩ := hinfty
      refine ⟨i, ?_⟩
      have hcoeff : (F i).eval 0 = (f i).leadingCoeff := by
        change (reflect 2 (taylor a (f i))).eval 0 = _
        rw [← coeff_zero_eq_eval_zero, coeff_reflect, revAt_zero, ← hi, coeff_taylor_natDegree]
      rw [hx, hcoeff]
      exact leadingCoeff_ne_zero.mpr (hf0 i)
    · obtain ⟨i, hi⟩ := hroot (x⁻¹ + a)
      refine ⟨i, ?_⟩
      let : Invertible (x⁻¹) := invertibleOfNonzero (inv_ne_zero hx)
      have heq := eval₂_reflect_eq_zero_iff (RingHom.id K) (x⁻¹) 2 (taylor a (f i)) (htdeg i)
      simp only [invOf_eq_inv, inv_inv, eval₂_id, taylor_eval] at heq
      exact heq.not.mpr hi
  have hpow (i) : reflect 12 ((taylor a (f i)) ^ 6) = (F i) ^ 6 :=
    reflect_pow_of_natDegree_le 2 6 _ (htdeg i)
  have hFsum : F 0 ^ 6 + F 1 ^ 6 + F 2 ^ 6 + F 3 ^ 6 = 0 := by
    have h := congrArg (fun p : K[X] => reflect 12 (taylor a p)) hsum
    simpa only [map_add, taylor_pow, map_zero, reflect_add, hpow, reflect_zero] using h
  have hback (i j : Fin 4) (h : F i ^ 6 + F j ^ 6 = 0) : f i ^ 6 + f j ^ 6 = 0 := by
    apply (taylor_eq_zero a _).mp
    apply (reflect_eq_zero_iff (N := 12)).mp
    simpa only [map_add, taylor_pow, reflect_add, hpow] using h
  rcases quadratic_sixth_pair_cancellation F hFdeg hFroot hFsum with h | h | h
  · exact Or.inl (hback 0 1 h)
  · exact Or.inr (Or.inl (hback 0 2 h))
  · exact Or.inr (Or.inr (hback 1 2 h))

#print axioms quadratic_sixth_pair_cancellation_of_le
-- 'Erdos477.Geometry.quadratic_sixth_pair_cancellation_of_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
