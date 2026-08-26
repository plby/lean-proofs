/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Bounded integer equations through finite sets of plane points.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.BoundedKernel
import ErdosProblems.Erdos477.Counting.PolynomialHeight
import ErdosProblems.Erdos477.Geometry.FieldExtension

namespace Erdos477.Counting

open scoped BigOperators Matrix

variable {K : Type*} [Field K] [CharZero K]

theorem exists_bounded_polynomial_with_support
    (P : MvPolynomial (Fin 2) K) (hP : P ≠ 0)
    (E : Finset (Fin 2 →₀ ℕ)) (hE : P.support ⊆ E)
    (S : Finset (Fin 2 → ℤ))
    (hS : ∀ z ∈ S, MvPolynomial.eval (fun k => (z k : K)) P = 0)
    (A : ℝ) (hA : 1 ≤ A)
    (hentry : ∀ z ∈ S, ∀ e ∈ E,
      |(MvPolynomial.eval z (MvPolynomial.monomial e (1 : ℤ)) : ℝ)| ≤ A) :
    ∃ Q : MvPolynomial (Fin 2) ℤ, Q ≠ 0 ∧ Q.support ⊆ E ∧
      (∀ z ∈ S, MvPolynomial.eval z Q = 0) ∧
      ∀ e, |((Q.coeff e : ℤ) : ℝ)| ≤ ((E.card : ℝ) * A) ^ E.card := by
  classical
  let m := E.card
  let e : Fin m ≃ E := (Finset.equivFin E).symm
  have heinj : Function.Injective (fun i : Fin m => (e i : Fin 2 →₀ ℕ)) :=
    Subtype.val_injective.comp e.injective
  have hPsum : P = ∑ i : Fin m, MvPolynomial.monomial (e i) (P.coeff (e i)) := by
    calc
      P = ∑ a ∈ P.support, MvPolynomial.monomial a (P.coeff a) := P.as_sum
      _ = ∑ a ∈ E, MvPolynomial.monomial a (P.coeff a) := by
        apply Finset.sum_subset hE
        intro a _ ha
        simp only [MvPolynomial.notMem_support_iff.mp ha, map_zero]
      _ = _ := by
        rw [← Finset.sum_coe_sort]
        exact (e.sum_comp _).symm
  have hvP : ∃ i : Fin m, P.coeff (e i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hP
    rw [hPsum]
    simp [h]
  have hm : 0 < m := by obtain ⟨i, _⟩ := hvP; exact (Nat.zero_le i.val).trans_lt i.isLt
  let V : S → Fin m → ℤ := fun z i =>
    MvPolynomial.eval z.val (MvPolynomial.monomial (e i) 1)
  have hdet (f : Fin m → S) : (Matrix.of fun i j => V (f i) j).det = 0 := by
    let M : Matrix (Fin m) (Fin m) K := Matrix.of fun i j => (V (f i) j : K)
    have hmul : M *ᵥ (fun j => P.coeff (e j)) = 0 := by
      ext i
      have h := hS (f i).val (f i).property
      rw [hPsum, map_sum] at h
      change ∑ j, (V (f i) j : K) * P.coeff (e j) = 0
      simp only [V, MvPolynomial.eval_monomial, one_mul] at h ⊢
      simp_rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two] at h ⊢
      push_cast
      simpa only [mul_comm] using h
    have hM : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp
      ⟨fun j => P.coeff (e j), by simpa only [ne_eq, funext_iff, Pi.zero_apply,
        not_forall] using hvP, hmul⟩
    have hmap := (Int.castRingHom K).map_det (Matrix.of fun i j => V (f i) j)
    change ((Matrix.of fun i j => V (f i) j).det : K) = M.det at hmap
    rw [hM] at hmap
    exact_mod_cast hmap
  obtain ⟨v, hv, hvan, hbound⟩ := exists_bounded_integer_kernel m hm V A hA
    (fun z i => hentry z.val z.property (e i) (e i).property) hdet
  let Q : MvPolynomial (Fin 2) ℤ := ∑ i : Fin m, MvPolynomial.monomial (e i) (v i)
  have hcoeff (i : Fin m) : Q.coeff (e i) = v i := by
    simp [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, heinj.eq_iff]
  have hcoeffzero (a : Fin 2 →₀ ℕ) (ha : a ∉ E) : Q.coeff a = 0 := by
    simp only [Q, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro i _
    have hne : (e i : Fin 2 →₀ ℕ) ≠ a := by
      intro h
      exact ha (h ▸ (e i).property)
    simp [MvPolynomial.coeff_monomial, hne]
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hv
    intro hQ
    have h := hcoeff i
    rw [hQ, MvPolynomial.coeff_zero] at h
    exact hi h.symm
  · intro a ha
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp ha) (hcoeffzero a h)
  · intro z hz
    have h := hvan ⟨z, hz⟩
    simpa only [Q, map_sum, MvPolynomial.eval_monomial, V, one_mul] using h
  · intro a
    by_cases ha : a ∈ E
    · obtain ⟨i, hi⟩ := e.surjective ⟨a, ha⟩
      have hei : (e i : Fin 2 →₀ ℕ) = a := congrArg Subtype.val hi
      rw [← hei, hcoeff]
      exact hbound i
    · rw [hcoeffzero a ha, Int.cast_zero, abs_zero]
      exact pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one hA)) _

#print axioms exists_bounded_polynomial_with_support
-- 'Erdos477.Counting.exists_bounded_polynomial_with_support' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
