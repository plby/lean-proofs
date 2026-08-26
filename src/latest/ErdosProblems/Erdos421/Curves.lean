import Mathlib

/-!
# Elementary algebra for the split-product curves

The affine-line exclusion needed for the square-root point bound follows
directly by comparing degrees after an affine parametrization. This file does
not assert the CCDN point-count estimate.
-/

namespace Erdos421

open Polynomial

noncomputable def splitProduct {K : Type*} [CommRing K] {r : ℕ} (a : Fin r → K) : K[X] :=
  ∏ i, (X - C (a i))

theorem splitProduct_monic {K : Type*} [CommRing K] {r : ℕ} (a : Fin r → K) :
    (splitProduct a).Monic :=
  monic_prod_of_monic _ _ (fun i _ ↦ monic_X_sub_C (a i))

@[simp] theorem splitProduct_natDegree {K : Type*} [CommRing K] [Nontrivial K]
    {r : ℕ} (a : Fin r → K) : (splitProduct a).natDegree = r := by
  unfold splitProduct
  rw [natDegree_prod_of_monic _ _ (fun i _ ↦ monic_X_sub_C (a i))]
  simp

@[simp] theorem splitProduct_eval {K : Type*} [CommRing K]
    {r : ℕ} (a : Fin r → K) (x : K) :
    (splitProduct a).eval x = ∏ i, (x - a i) := by
  simp [splitProduct, eval_prod]

/-- Unequal positive degrees prevent an identity on any parametrized affine line. -/
theorem unequal_degrees_no_line_identity {K : Type*} [Field K]
    {f g : K[X]} (hdeg : g.natDegree < f.natDegree) (hg : 0 < g.natDegree)
    (a b c d : K) (hdir : a ≠ 0 ∨ c ≠ 0) :
    f.comp (C a * X + C b) - g.comp (C c * X + C d) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro heq
  have hdegrees := congrArg Polynomial.natDegree heq
  by_cases ha : a = 0
  · have hc : c ≠ 0 := hdir.resolve_left (not_not.mpr ha)
    simp only [ha, C_0, zero_mul, zero_add, comp_C, natDegree_C,
      natDegree_comp, natDegree_add_C, natDegree_C_mul_X c hc, mul_one] at hdegrees
    omega
  · have hclin : (C c * X + C d).natDegree ≤ 1 := by
      rw [natDegree_add_C]
      exact (natDegree_C_mul_le c X).trans natDegree_X_le
    rw [natDegree_comp, natDegree_add_C, natDegree_C_mul_X a ha, mul_one,
      natDegree_comp] at hdegrees
    have hle := Nat.mul_le_mul_left g.natDegree hclin
    rw [mul_one, ← hdegrees] at hle
    omega

/-- In particular, none of the raw split-product equations contains an affine
line, even after extending the coefficient field. -/
theorem split_products_no_line_identity {K : Type*} [Field K]
    {r s : ℕ} (hs : 0 < s) (hrs : s < r) (u : Fin r → K) (v : Fin s → K)
    (a b c d : K) (hdir : a ≠ 0 ∨ c ≠ 0) :
    (splitProduct u).comp (C a * X + C b) -
      (splitProduct v).comp (C c * X + C d) ≠ 0 := by
  apply unequal_degrees_no_line_identity _ _ a b c d hdir <;> simpa

end Erdos421
