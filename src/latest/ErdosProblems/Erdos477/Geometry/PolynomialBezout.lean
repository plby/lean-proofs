/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Polynomial Bézout identities and divisibility from products omitting one factor.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Geometry

open Polynomial
open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [Field K] [IsAlgClosed K]

theorem exists_bezout_of_no_common_root (f : ι → K[X])
    (hroot : ∀ x : K, ∃ i, (f i).eval x ≠ 0) :
    ∃ a : ι → K[X], ∑ i, a i * f i = 1 := by
  let I : Ideal K[X] := Ideal.span (Set.range f)
  have hI : I = ⊤ := by
    by_contra hne
    let g := Submodule.IsPrincipal.generator I
    have hnonunit : ¬ IsUnit g := by
      intro hg
      exact hne (I.eq_top_of_isUnit_mem (Submodule.IsPrincipal.generator_mem I) hg)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root g
      (fun hd => hnonunit (Polynomial.isUnit_iff_degree_eq_zero.mpr hd))
    obtain ⟨i, hi⟩ := hroot x
    apply hi
    have hdiv : g ∣ f i := (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp
      (Ideal.subset_span (Set.mem_range_self i))
    exact eval_eq_zero_of_dvd_of_eval_eq_zero hdiv hx
  apply Ideal.mem_span_range_iff_exists_fun.mp
  change (1 : K[X]) ∈ I
  rw [hI]
  trivial

lemma prod_dvd_of_except_dvd {R : Type*} [CommRing R] [DecidableEq ι]
    (f a : ι → R) (ha : ∑ i, a i * f i = 1) (g : R)
    (hdiv : ∀ i, (∏ j ∈ Finset.univ.erase i, f j) ∣ g) : (∏ i, f i) ∣ g := by
  rw [← mul_one g, ← ha, Finset.mul_sum]
  apply Finset.dvd_sum
  intro i _
  obtain ⟨q, hq⟩ := hdiv i
  refine ⟨a i * q, ?_⟩
  rw [hq, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  ring

/-- If the factors have no common root, divisibility by every product omitting
one factor implies divisibility by the full product, including multiplicities. -/
theorem polynomial_prod_dvd_of_except_dvd [DecidableEq ι] (f : ι → K[X])
    (hroot : ∀ x : K, ∃ i, (f i).eval x ≠ 0) (g : K[X])
    (hdiv : ∀ i, (∏ j ∈ Finset.univ.erase i, f j) ∣ g) : (∏ i, f i) ∣ g := by
  obtain ⟨a, ha⟩ := exists_bezout_of_no_common_root f hroot
  exact prod_dvd_of_except_dvd f a ha g hdiv

#print axioms polynomial_prod_dvd_of_except_dvd
-- 'Erdos477.Geometry.polynomial_prod_dvd_of_except_dvd' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
