/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite determinant arithmetic for the counting inputs of Erdős Problem 477.
Formal author: Codex.

The weighted expansion lemma is the algebraic step in the local determinant
method: repeated basis rows give zero, and distinct rows give the product of
their divisibility factors. No surface counting theorem is assumed here.
-/

import Mathlib

namespace Erdos477.Counting

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
variable {R : Type*} [CommRing R]

/-- Expand each row independently before taking its determinant. -/
lemma det_row_sum (g : ι → κ → ι → R) :
    Matrix.det (Matrix.of fun i j => ∑ k, g i k j) =
      ∑ f : ι → κ, Matrix.det (Matrix.of fun i j => g i (f i) j) := by
  calc
    _ = Matrix.det (Matrix.of fun i => ∑ k, g i k) := by
      congr 1
      ext i j
      simp only [Matrix.of_apply, Finset.sum_apply]
    _ = _ :=
      (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R).toMultilinearMap.map_sum g

/-- A weighted row expansion forces the corresponding power to divide the
determinant. The condition on `L` is purely a finite combinatorial condition. -/
theorem pow_dvd_det_weighted_sum (p : R) (w : κ → ℕ) (C : ι → κ → R)
    (W : κ → ι → R) (L : ℕ)
    (hL : ∀ f : ι → κ, Function.Injective f → L ≤ ∑ i, w (f i)) :
    p ^ L ∣ Matrix.det (Matrix.of fun i j => ∑ k, (C i k * p ^ w k) * W k j) := by
  classical
  rw [det_row_sum]
  apply Finset.dvd_sum
  intro f _
  have hd := Matrix.det_mul_column (fun i => C i (f i) * p ^ w (f i))
    (Matrix.of fun i j => W (f i) j)
  simp only [Matrix.of_apply] at hd
  rw [hd]
  by_cases hf : Function.Injective f
  · have hp : p ^ L ∣ p ^ (∑ i, w (f i)) := pow_dvd_pow p (hL f hf)
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hp _) _
  · obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp hf
    have hzero : Matrix.det (Matrix.of fun i j => W (f i) j) = 0 :=
      Matrix.det_zero_of_row_eq hne (by change W (f i) = W (f j); rw [heq])
    rw [hzero, mul_zero]
    exact dvd_zero _

/-- Monomial evaluations on a two-dimensional residue class supply the
weights `a+b` required by the preceding determinant lemma. -/
theorem pow_dvd_det_bivariate_expansion (p : R) (e : κ → ℕ × ℕ)
    (he : Function.Injective e) (C : ι → κ → R) (x y : ι → R) (L : ℕ)
    (hL : ∀ f : ι → ℕ × ℕ, Function.Injective f →
      L ≤ ∑ i, ((f i).1 + (f i).2)) :
    p ^ L ∣ Matrix.det (Matrix.of fun i j =>
      ∑ k, C i k * ((p * x j) ^ (e k).1 * (p * y j) ^ (e k).2)) := by
  have hentry (i j : ι) :
      (∑ k, C i k * ((p * x j) ^ (e k).1 * (p * y j) ^ (e k).2)) =
      ∑ k, (C i k * p ^ ((e k).1 + (e k).2)) *
        (x j ^ (e k).1 * y j ^ (e k).2) := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [mul_pow, pow_add]
    ring
  simp_rw [hentry]
  apply pow_dvd_det_weighted_sum
  intro f hf
  exact hL (e ∘ f) (he.comp hf)

/-- A sufficiently large positive divisor forces a small integer determinant
to vanish; this is the final arithmetic step of the determinant method. -/
lemma det_eq_zero_of_dvd_of_abs_lt (A : Matrix ι ι ℤ) {q : ℤ}
    (hq : q ∣ A.det) (hsmall : |A.det| < q) : A.det = 0 := by
  exact Int.eq_zero_of_abs_lt_dvd hq hsmall

/-- Entrywise congruences imply the corresponding determinant congruence. -/
lemma dvd_det_sub_det (q : R) (A B : Matrix ι ι R)
    (h : ∀ i j, q ∣ A i j - B i j) : q ∣ A.det - B.det := by
  let I : Ideal R := Ideal.span {q}
  let φ := Ideal.Quotient.mk I
  have heq : A.map φ = B.map φ := by
    ext i j
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr (h i j)
  have hdet : φ A.det = φ B.det :=
    (φ.map_det A).trans ((congrArg Matrix.det heq).trans (φ.map_det B).symm)
  have hz : φ (A.det - B.det) = 0 := by rw [map_sub, hdet, sub_self]
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)

/-- Divisibility survives an entrywise approximation to sufficiently high
order. This permits truncated local expansions in place of exact ones. -/
lemma pow_dvd_det_of_approximation (p : R) (L N : ℕ) (hLN : L ≤ N)
    (A B : Matrix ι ι R) (happrox : ∀ i j, p ^ N ∣ A i j - B i j)
    (hB : p ^ L ∣ B.det) : p ^ L ∣ A.det := by
  have hdiff : p ^ L ∣ A.det - B.det :=
    (pow_dvd_pow p hLN).trans (dvd_det_sub_det (p ^ N) A B happrox)
  simpa only [sub_add_cancel] using dvd_add hdiff hB

#print axioms pow_dvd_det_bivariate_expansion
-- 'Erdos477.Counting.pow_dvd_det_bivariate_expansion' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
