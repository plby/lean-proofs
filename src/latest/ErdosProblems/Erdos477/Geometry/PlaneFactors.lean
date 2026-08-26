/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Factor covers of a plane equation, with exact control of the total degrees.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.PlaneBezout

namespace Erdos477.Geometry

open scoped BigOperators

variable {σ K : Type*} [Field K]

lemma totalDegree_pos_of_irreducible (P : MvPolynomial σ K) (hP : Irreducible P) :
    0 < P.totalDegree := by
  apply Nat.pos_of_ne_zero
  intro hdegree
  have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree
  have hc : P.coeff 0 ≠ 0 := by
    intro h
    rw [h, MvPolynomial.C_0] at hC
    exact hP.ne_zero hC
  apply hP.not_isUnit
  rw [hC]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

lemma totalDegree_multiset_prod_eq (S : Multiset (MvPolynomial σ K))
    (hS : ∀ P ∈ S, P ≠ 0) : S.prod.totalDegree = (S.map MvPolynomial.totalDegree).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | @cons P S ih =>
      have hP : P ≠ 0 := hS P (Multiset.mem_cons_self _ _)
      have hS' : ∀ Q ∈ S, Q ≠ 0 := fun Q hQ => hS Q (Multiset.mem_cons_of_mem hQ)
      have hprod : S.prod ≠ 0 := Multiset.prod_ne_zero (fun h => hS' 0 h rfl)
      rw [Multiset.prod_cons, MvPolynomial.totalDegree_mul_of_isDomain hP hprod,
        ih hS', Multiset.map_cons, Multiset.sum_cons]

lemma totalDegree_eq_of_associated (P Q : MvPolynomial σ K) (hP : P ≠ 0)
    (h : Associated P Q) : P.totalDegree = Q.totalDegree := by
  have hQ : Q ≠ 0 := h.ne_zero_iff.mp hP
  exact (MvPolynomial.totalDegree_le_of_dvd_of_isDomain h.dvd hQ).antisymm
    (MvPolynomial.totalDegree_le_of_dvd_of_isDomain h.symm.dvd hP)

/-- Each nonzero polynomial has an irreducible factor cover whose degrees
sum exactly to its degree. The cover counts repeated factors with multiplicity. -/
theorem exists_irreducible_factor_cover (P : MvPolynomial σ K) (hP : P ≠ 0) :
    ∃ S : Multiset (MvPolynomial σ K),
      (∀ Q ∈ S, Irreducible Q ∧ Q ∣ P) ∧
      (S.map MvPolynomial.totalDegree).sum = P.totalDegree ∧
      ∀ z : σ → K, MvPolynomial.eval z P = 0 →
        ∃ Q ∈ S, MvPolynomial.eval z Q = 0 := by
  classical
  let S := UniqueFactorizationMonoid.factors P
  have hirr (Q) (hQ : Q ∈ S) : Irreducible Q :=
    UniqueFactorizationMonoid.irreducible_of_factor Q hQ
  have hprod := UniqueFactorizationMonoid.factors_prod hP
  have hS : ∀ Q ∈ S, Q ≠ 0 := fun Q hQ => (hirr Q hQ).ne_zero
  have hS0 : S.prod ≠ 0 := Multiset.prod_ne_zero (fun h => hS 0 h rfl)
  refine ⟨S, fun Q hQ => ⟨hirr Q hQ,
    UniqueFactorizationMonoid.dvd_of_mem_factors hQ⟩, ?_, ?_⟩
  · rw [← totalDegree_multiset_prod_eq S hS]
    exact totalDegree_eq_of_associated S.prod P hS0 hprod
  · intro z hz
    have hzero : MvPolynomial.eval z S.prod = 0 := by
      have h := map_dvd (MvPolynomial.eval z) hprod.symm.dvd
      rw [hz, zero_dvd_iff] at h
      exact h
    rw [map_multiset_prod] at hzero
    have hmem := Multiset.prod_eq_zero_iff.mp hzero
    obtain ⟨Q, hQ, heval⟩ := Multiset.mem_map.mp hmem
    exact ⟨Q, hQ, heval⟩

lemma totalDegree_finset_prod_eq (S : Finset (MvPolynomial σ K))
    (hS : ∀ P ∈ S, P ≠ 0) :
    (∏ P ∈ S, P).totalDegree = ∑ P ∈ S, P.totalDegree := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert P S hPS ih =>
      have hP : P ≠ 0 := hS P (Finset.mem_insert_self _ _)
      have hS' : ∀ Q ∈ S, Q ≠ 0 := fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ)
      have hprod : (∏ Q ∈ S, Q) ≠ 0 := Finset.prod_ne_zero_iff.mpr hS'
      rw [Finset.prod_insert hPS, Finset.sum_insert hPS,
        MvPolynomial.totalDegree_mul_of_isDomain hP hprod, ih hS']

lemma sum_degrees_le_of_pairwise_dvd (S : Finset (MvPolynomial σ K))
    (hS : ∀ Q ∈ S, Q ≠ 0) (hpair : (↑S : Set (MvPolynomial σ K)).Pairwise IsRelPrime)
    (P : MvPolynomial σ K) (hP : P ≠ 0) (hdiv : ∀ Q ∈ S, Q ∣ P) :
    (∑ Q ∈ S, Q.totalDegree) ≤ P.totalDegree := by
  rw [← totalDegree_finset_prod_eq S hS]
  exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain
    (Finset.prod_dvd_of_isRelPrime hpair hdiv) hP

/-- Repeated and associated factors can be removed. The resulting pairwise
relatively prime family still covers all zeroes and has bounded degree sum. -/
theorem exists_distinct_factor_cover (P : MvPolynomial σ K) (hP : P ≠ 0) :
    ∃ S : Finset (MvPolynomial σ K),
      (∀ Q ∈ S, Irreducible Q ∧ Q ∣ P) ∧
      (↑S : Set (MvPolynomial σ K)).Pairwise IsRelPrime ∧
      (∑ Q ∈ S, Q.totalDegree) ≤ P.totalDegree ∧ S.card ≤ P.totalDegree ∧
      ∀ z : σ → K, MvPolynomial.eval z P = 0 →
        ∃ Q ∈ S, MvPolynomial.eval z Q = 0 := by
  classical
  let : NormalizedGCDMonoid (MvPolynomial σ K) := Nonempty.some inferInstance
  let F := UniqueFactorizationMonoid.normalizedFactors P
  let S := F.toFinset
  have hmem (Q) : Q ∈ S ↔ Q ∈ F := Multiset.mem_toFinset
  have hirr (Q) (hQ : Q ∈ S) : Irreducible Q :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor Q ((hmem Q).mp hQ)
  have hdiv (Q) (hQ : Q ∈ S) : Q ∣ P :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors ((hmem Q).mp hQ)
  have hpair : (↑S : Set (MvPolynomial σ K)).Pairwise IsRelPrime := by
    intro Q hQ R hR hne
    apply (hirr Q hQ).isRelPrime_iff_not_dvd.mpr
    intro hQR
    have hassoc := (hirr Q hQ).associated_of_dvd (hirr R hR) hQR
    have hnorm := normalize_eq_normalize_iff.mpr ⟨hassoc.dvd, hassoc.symm.dvd⟩
    rw [UniqueFactorizationMonoid.normalize_normalized_factor Q ((hmem Q).mp hQ),
      UniqueFactorizationMonoid.normalize_normalized_factor R ((hmem R).mp hR)] at hnorm
    exact hne hnorm
  have hsum := sum_degrees_le_of_pairwise_dvd S (fun Q hQ => (hirr Q hQ).ne_zero)
    hpair P hP hdiv
  have hcard : S.card ≤ ∑ Q ∈ S, Q.totalDegree := by
    calc
      _ = ∑ _Q ∈ S, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun Q hQ => totalDegree_pos_of_irreducible Q (hirr Q hQ))
  refine ⟨S, fun Q hQ => ⟨hirr Q hQ, hdiv Q hQ⟩, hpair, hsum, hcard.trans hsum, ?_⟩
  intro z hz
  have hzero : MvPolynomial.eval z F.prod = 0 := by
    have h := map_dvd (MvPolynomial.eval z)
      (UniqueFactorizationMonoid.prod_normalizedFactors hP).symm.dvd
    rw [hz, zero_dvd_iff] at h
    exact h
  rw [map_multiset_prod] at hzero
  obtain ⟨Q, hQ, heval⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hzero)
  exact ⟨Q, (hmem Q).mpr hQ, heval⟩

#print axioms exists_irreducible_factor_cover
-- 'Erdos477.Geometry.exists_irreducible_factor_cover' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
