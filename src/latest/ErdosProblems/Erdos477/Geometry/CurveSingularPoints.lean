/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A uniform bound for singular integer points on an irreducible plane curve.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.CurveCriticalPoints

namespace Erdos477.Geometry

variable {K : Type*} [Field K] [CharZero K]

lemma pderiv_ne_zero_of_degreeOf_pos {σ : Type*} (P : MvPolynomial σ K) (i : σ)
    (hdegree : 0 < P.degreeOf i) : MvPolynomial.pderiv i P ≠ 0 := by
  classical
  rw [MvPolynomial.degreeOf_eq_sup] at hdegree
  obtain ⟨m, hm, hmi⟩ := Finset.lt_sup_iff.mp hdegree
  let l := m - Finsupp.single i 1
  have heq : l + Finsupp.single i 1 = m :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.succ_le_of_lt hmi))
  apply MvPolynomial.ne_zero_iff.mpr
  refine ⟨l, ?_⟩
  rw [MvPolynomial.coeff_pderiv, heq]
  have hcast : (l i : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (l i)
  exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hm) hcast

omit [CharZero K] in
lemma exists_positive_plane_degreeOf (P : MvPolynomial (Fin 2) K) (hP : 0 < P.totalDegree) :
    ∃ i, 0 < P.degreeOf i := by
  by_contra! h
  have hzero : P.totalDegree ≤ 0 := by
    apply Finset.sup_le
    intro m hm
    have h0 := (MvPolynomial.le_degreeOf_of_mem_support 0 hm).trans (h 0)
    have h1 := (MvPolynomial.le_degreeOf_of_mem_support 1 hm).trans (h 1)
    change m.sum (fun _ n => n) ≤ 0
    rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
    omega
  omega

theorem card_integer_plane_intersection_le (P Q : MvPolynomial (Fin 2) K)
    (hP : Irreducible P) (hdiv : ¬ P ∣ Q) (S : Finset (Fin 2 → ℤ))
    (hS : ∀ z ∈ S, MvPolynomial.eval (fun i => (z i : K)) P = 0 ∧
      MvPolynomial.eval (fun i => (z i : K)) Q = 0) :
    S.card ≤ P.totalDegree * Q.totalDegree := by
  classical
  let π : (Fin 2 → ℤ) → K × K := fun z => (z 0, z 1)
  have hinj : Function.Injective π := by
    intro z w h
    have h0 : z 0 = w 0 := Int.cast_injective (congrArg Prod.fst h)
    have h1 : z 1 = w 1 := Int.cast_injective (congrArg Prod.snd h)
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have h := card_common_zeroes_le P Q hP hdiv (S.image π) (by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    have hvec : ![(π z).1, (π z).2] = fun i => (z i : K) := by
      funext i
      fin_cases i <;> rfl
    rw [hvec]
    exact hS z hz)
  rwa [Finset.card_image_of_injective _ hinj] at h

theorem card_integer_curve_singular_points_le (P : MvPolynomial (Fin 2) K)
    (hP : Irreducible P) (hdegree : 0 < P.totalDegree) (S : Finset (Fin 2 → ℤ))
    (hroot : ∀ z ∈ S, MvPolynomial.eval (fun i => (z i : K)) P = 0)
    (hsingular : ∀ z ∈ S, ∀ i, MvPolynomial.eval (fun j => (z j : K))
      (MvPolynomial.pderiv i P) = 0) :
    S.card ≤ P.totalDegree * (P.totalDegree - 1) := by
  obtain ⟨i, hi⟩ := exists_positive_plane_degreeOf P hdegree
  have hQ : MvPolynomial.pderiv i P ≠ 0 := pderiv_ne_zero_of_degreeOf_pos P i hi
  have hdiv : ¬ P ∣ MvPolynomial.pderiv i P := by
    intro h
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain h hQ
    have hlt := totalDegree_pderiv_le P i
    omega
  exact (card_integer_plane_intersection_le P (MvPolynomial.pderiv i P) hP hdiv S
    (fun z hz => ⟨hroot z hz, hsingular z hz i⟩)).trans
      (Nat.mul_le_mul_left _ (totalDegree_pderiv_le P i))

#print axioms card_integer_curve_singular_points_le
-- 'Erdos477.Geometry.card_integer_curve_singular_points_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
