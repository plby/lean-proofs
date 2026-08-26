/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Local determinant divisibility on an affine diagonal sextic surface.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.LocalGraph

namespace Erdos477.Counting

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Solve the diagonal equation for the sixth power of its last coordinate. -/
noncomputable def diagonalGraph (b : Fin 3 → Rˣ) (c : R) : MvPolynomial (Fin 2) R :=
  MvPolynomial.C (((b 2)⁻¹ : Rˣ) : R) *
    (MvPolynomial.C c - MvPolynomial.C (b 0 : R) * MvPolynomial.X 0 ^ 6 -
      MvPolynomial.C (b 1 : R) * MvPolynomial.X 1 ^ 6)

lemma eval_diagonalGraph (b : Fin 3 → Rˣ) (c : R) (z : Fin 3 → R)
    (hz : ∑ i, (b i : R) * z i ^ 6 = c) :
    z 2 ^ 6 = MvPolynomial.eval ![z 0, z 1] (diagonalGraph b c) := by
  simp only [Fin.sum_univ_three] at hz
  have hlast : (b 2 : R) * z 2 ^ 6 =
      c - (b 0 : R) * z 0 ^ 6 - (b 1 : R) * z 1 ^ 6 := by
    linear_combination hz
  simp only [diagonalGraph, map_mul, map_sub, map_pow, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [← hlast, ← mul_assoc, Units.inv_mul, one_mul]

lemma diagonal_has_unit_coordinate [IsLocalRing R] (b : Fin 3 → Rˣ)
    (c : R) (hc : IsUnit c) (z : Fin 3 → R)
    (hz : ∑ i, (b i : R) * z i ^ 6 = c) : ∃ k, IsUnit (z k) := by
  by_contra h
  push Not at h
  have hsum : (∑ i, (b i : R) * z i ^ 6) ∈ IsLocalRing.maximalIdeal R := by
    apply Ideal.sum_mem
    intro i _
    apply Ideal.mul_mem_left
    exact Ideal.pow_mem_of_mem (IsLocalRing.maximalIdeal R) (h i) 6 (by decide)
  rw [hz] at hsum
  exact hsum hc

/-- A residue class with a unit last coordinate admits the two-variable local
determinant bound. -/
theorem pow_dvd_diagonal_eval_det_chart [IsLocalRing R] [BinomialRing R]
    {s : ℕ} (a : R) (ha : 6 * a = 1) (p : R) (hp : ¬ IsUnit p)
    (b : Fin 3 → Rˣ) (c : R) (center : Fin 3 → R) (hc : IsUnit (center 2))
    (z : Fin s → Fin 3 → R) (hres : ∀ j k, p ∣ z j k - center k)
    (hz : ∀ j, ∑ k, (b k : R) * z j k ^ 6 = c)
    (F : Fin s → MvPolynomial (Fin 3) R) (m : ℕ) :
    p ^ localExponent s m ∣
      Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) := by
  classical
  obtain ⟨v, hv⟩ := hc
  choose x hx using fun j => hres j 0
  choose y hy using fun j => hres j 1
  have hx' (j) : center 0 + p * x j = z j 0 := by rw [← hx j]; ring
  have hy' (j) : center 1 + p * y j = z j 1 := by rw [← hy j]; ring
  have hlast (j) : p ∣ z j 2 - (v : R) := by rw [hv]; exact hres j 2
  have hgraph (j) : z j 2 ^ 6 =
      MvPolynomial.eval ![center 0 + p * x j, center 1 + p * y j]
        (diagonalGraph b c) := by
    rw [hx', hy']
    exact eval_diagonalGraph b c (z j) (hz j)
  have hvec (j) : ![center 0 + p * x j, center 1 + p * y j, z j 2] = z j := by
    funext k
    fin_cases k <;> simp [hx', hy']
  have h := pow_dvd_graph_eval_det a ha p hp v (diagonalGraph b c) F
    (center 0) (center 1) x y (fun j => z j 2) hlast hgraph m
  simpa only [hvec] using h

/-- Every residue class on the diagonal surface, at a prime where the
constant and coefficients are units, has the local determinant bound. -/
theorem pow_dvd_diagonal_eval_det [IsLocalRing R] [BinomialRing R]
    {s : ℕ} (a : R) (ha : 6 * a = 1) (p : R) (hp : ¬ IsUnit p)
    (b : Fin 3 → Rˣ) (c : R) (hc : IsUnit c) (center : Fin 3 → R)
    (hcenter : ∑ k, (b k : R) * center k ^ 6 = c)
    (z : Fin s → Fin 3 → R) (hres : ∀ j k, p ∣ z j k - center k)
    (hz : ∀ j, ∑ k, (b k : R) * z j k ^ 6 = c)
    (F : Fin s → MvPolynomial (Fin 3) R) (m : ℕ) :
    p ^ localExponent s m ∣
      Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) := by
  obtain ⟨k, hk⟩ := diagonal_has_unit_coordinate b c hc center hcenter
  let e : Equiv.Perm (Fin 3) := Equiv.swap 2 k
  have he : e 2 = k := Equiv.swap_apply_left 2 k
  let b' := b ∘ e
  let center' := center ∘ e
  let z' : Fin s → Fin 3 → R := fun j => z j ∘ e
  let F' : Fin s → MvPolynomial (Fin 3) R := fun i =>
    MvPolynomial.rename e.symm (F i)
  have hunit : IsUnit (center' 2) := by simpa only [center', Function.comp_apply, he] using hk
  have hres' (j i) : p ∣ z' j i - center' i := hres j (e i)
  have hz' (j) : ∑ i, (b' i : R) * z' j i ^ 6 = c := by
    change (∑ i, (b (e i) : R) * z j (e i) ^ 6) = c
    exact (Equiv.sum_comp e (fun i => (b i : R) * z j i ^ 6)).trans (hz j)
  have h := pow_dvd_diagonal_eval_det_chart a ha p hp b' c center' hunit z'
    hres' hz' F' m
  have heval (i j) : MvPolynomial.eval (z' j) (F' i) =
      MvPolynomial.eval (z j) (F i) := by
    dsimp only [F', z']
    rw [MvPolynomial.eval_rename]
    simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  simpa only [heval] using h

#print axioms pow_dvd_diagonal_eval_det
-- 'Erdos477.Counting.pow_dvd_diagonal_eval_det' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
