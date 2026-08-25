import ErdosProblems.Erdos1141.StepanovConditions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Root counting for the quadratic Stepanov polynomial
-/

namespace Pollack17.Stepanov

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

theorem le_rootMultiplicity_of_derivatives {p D : ℕ} [Fact p.Prime] [CharP K p]
    {P : K[X]} {x : K} (hP : P ≠ 0) (hDp : D ≤ p)
    (hvanish : ∀ k : ℕ, k < D → (derivative^[k] P).eval x = 0) :
    D ≤ P.rootMultiplicity x := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  apply Polynomial.le_natTrailingDegree
  · exact (Polynomial.taylor_eq_zero x P).not.mpr hP
  · intro k hk
    change (Polynomial.taylor x P).coeff k = 0
    rw [Polynomial.taylor_coeff]
    have hfact : (k.factorial : K) ≠ 0 := by
      rw [ne_eq, CharP.cast_eq_zero_iff K p, (Fact.out : p.Prime).dvd_factorial, not_le]
      exact hk.trans_le hDp
    have hscaled := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) k) P
    have heval := congrArg (fun Q : K[X] => Q.eval x) hscaled
    simp only [nsmul_eq_mul, Module.End.mul_apply, Module.End.natCast_apply,
      nsmul_eq_mul, eval_mul, eval_natCast] at heval
    rw [hvanish k hk] at heval
    exact (mul_eq_zero.mp heval).resolve_left hfact

theorem mul_card_le_natDegree_of_derivatives {p D : ℕ} [Fact p.Prime] [CharP K p]
    {P : K[X]} (hP : P ≠ 0) (hDp : D ≤ p) (S : Finset K)
    (hvanish : ∀ x ∈ S, ∀ k : ℕ, k < D → (derivative^[k] P).eval x = 0) :
    D * S.card ≤ P.natDegree := by
  classical
  by_cases hD : D = 0
  · simp [hD]
  have hmult (x : K) (hx : x ∈ S) : D ≤ P.rootMultiplicity x :=
    le_rootMultiplicity_of_derivatives hP hDp (hvanish x hx)
  have hsubset : S ⊆ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, ← Multiset.count_pos, Polynomial.count_roots]
    exact (Nat.pos_of_ne_zero hD).trans_le (hmult x hx)
  calc
    D * S.card = ∑ _x ∈ S, D := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ S, P.rootMultiplicity x := Finset.sum_le_sum hmult
    _ = ∑ x ∈ S, P.roots.count x := by simp only [Polynomial.count_roots]
    _ ≤ ∑ x ∈ P.roots.toFinset, P.roots.count x := Finset.sum_le_sum_of_subset hsubset
    _ = P.roots.card := Multiset.toFinset_sum_count_eq P.roots
    _ ≤ P.natDegree := Polynomial.card_roots' P

theorem boxPolynomial_natDegree_le {p A B : ℕ} (a : Fin A × Fin B → K) :
    (boxPolynomial (p := p) a).natDegree ≤ A + p * B := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply (Polynomial.natDegree_monomial_le (a i)).trans
  dsimp [boxExponent]
  have hmul := Nat.mul_le_mul_left p i.2.isLt.le
  have ha := i.1.isLt.le
  omega

/-- The finite Stepanov fiber inequality before choosing numerical parameters. -/
theorem quadratic_fiber_card_bound {p A B D t : ℕ} [Fact p.Prime] [CharP K p]
    (f : K[X]) {x₀ : K} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hAt : A ≤ t) (htA : t + A ≤ p) (hDp : D ≤ p)
    (hdim : D * (A + B + D * f.natDegree + 1) < 2 * A * B)
    (S : Finset K)
    (hS : ∀ x ∈ S, x ^ p = x ∧ f.eval x ≠ 0 ∧ f.eval x ^ t = 1) :
    D * S.card ≤ A + p * B + t * f.natDegree := by
  classical
  obtain ⟨a, ha, hcond⟩ := exists_nonzero_vanishing_conditions f (t : K) A B D hdim
  have hpair : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (Prod.ext h.1 h.2)
  let F := boxPolynomial (p := p) a.1 + f ^ t * boxPolynomial (p := p) a.2
  have hF : F ≠ 0 := box_auxiliary_ne_zero hpair hf hroot hAt htA
  have hdeg : F.natDegree ≤ A + p * B + t * f.natDegree := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact (boxPolynomial_natDegree_le a.1).trans (Nat.le_add_right _ _)
    · have hmul := Polynomial.natDegree_mul_le
        (p := f ^ t) (q := boxPolynomial (p := p) a.2)
      rw [Polynomial.natDegree_pow] at hmul
      have hb := boxPolynomial_natDegree_le (p := p) a.2
      omega
  apply (mul_card_le_natDegree_of_derivatives hF hDp S ?_).trans hdeg
  intro x hx k hk
  obtain ⟨hxp, hfx, hft⟩ := hS x hx
  have heval := eval_conditionPolynomial f t k a x hxp hft
  rw [hcond k hk, eval_zero] at heval
  exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hfx)

end Pollack17.Stepanov
