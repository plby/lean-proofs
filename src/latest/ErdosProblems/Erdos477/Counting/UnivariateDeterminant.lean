/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The one-variable local determinant divisor for the remaining curve estimates.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.Determinant

namespace Erdos477.Counting

open scoped BigOperators Polynomial

lemma choose_card_two_le_sum (S : Finset ℕ) : S.card.choose 2 ≤ ∑ k ∈ S, k := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hmax ih =>
      have ha : a ∉ S := fun h => (hmax a h).false
      have hcard : S.card ≤ a := by
        have hsub : S ⊆ Finset.range a := fun x hx => Finset.mem_range.mpr (hmax x hx)
        simpa using Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem ha, Nat.choose_succ_succ, Nat.choose_one_right,
        Finset.sum_insert ha]
      exact Nat.add_le_add hcard ih

lemma choose_card_two_le_sum_injective {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (hf : Function.Injective f) : (Fintype.card ι).choose 2 ≤ ∑ i, f i := by
  classical
  have h := choose_card_two_le_sum (Finset.univ.image f)
  simpa only [Finset.card_image_of_injective _ hf, Finset.card_univ,
    Finset.sum_image (fun i _ j _ h => hf h)] using h

variable {R : Type*} [CommRing R]

/-- Evaluation on a one-variable residue class yields the exact divisor
`p^(s choose 2)`. The ring and the polynomials are arbitrary. -/
theorem pow_dvd_univariate_eval_det {s : ℕ} (p : R) (F : Fin s → R[X]) (x : Fin s → R) :
    p ^ s.choose 2 ∣ Matrix.det (Matrix.of fun i j => (F i).eval (p * x j)) := by
  classical
  let S : Finset ℕ := Finset.univ.biUnion (fun i => (F i).support)
  have heval (i j : Fin s) :
      (F i).eval (p * x j) = ∑ k : S, ((F i).coeff k * p ^ (k : ℕ)) * x j ^ (k : ℕ) := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum]
    calc
      _ = ∑ k ∈ S, (F i).coeff k * (p * x j) ^ k := by
        apply Finset.sum_subset
        · intro k hk
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hk⟩
        · intro k _ hk
          have hk0 : (F i).coeff k = 0 := Polynomial.notMem_support_iff.mp hk
          rw [hk0, zero_mul]
      _ = ∑ k : S, (F i).coeff k * (p * x j) ^ (k : ℕ) :=
        (Finset.sum_coe_sort S _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_pow]
        ring
  simp_rw [heval]
  apply pow_dvd_det_weighted_sum p (fun k : S => (k : ℕ))
    (fun i k => (F i).coeff k) (fun k j => x j ^ (k : ℕ))
  intro f hf
  simpa only [Fintype.card_fin] using choose_card_two_le_sum_injective
    (fun i => (f i : ℕ)) (Subtype.val_injective.comp hf)

theorem pow_dvd_univariate_eval_det_translate {s : ℕ} (p a : R)
    (F : Fin s → R[X]) (x : Fin s → R) :
    p ^ s.choose 2 ∣ Matrix.det (Matrix.of fun i j => (F i).eval (a + p * x j)) := by
  simpa only [Polynomial.taylor_eval, add_comm a] using
    pow_dvd_univariate_eval_det p (fun i => Polynomial.taylor a (F i)) x

theorem pow_dvd_det_of_univariate_expansion {s : ℕ} (p : R)
    (A : Matrix (Fin s) (Fin s) R) (F : Fin s → R[X]) (x : Fin s → R) (N : ℕ)
    (hN : s.choose 2 ≤ N)
    (happrox : ∀ i j, p ^ N ∣ A i j - (F i).eval (p * x j)) : p ^ s.choose 2 ∣ A.det := by
  exact pow_dvd_det_of_approximation p (s.choose 2) N hN A
    (Matrix.of fun i j => (F i).eval (p * x j)) happrox (pow_dvd_univariate_eval_det p F x)

#print axioms pow_dvd_univariate_eval_det
-- 'Erdos477.Counting.pow_dvd_univariate_eval_det' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
