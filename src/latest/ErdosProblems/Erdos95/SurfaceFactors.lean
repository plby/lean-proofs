/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.NonClustering

/-!
# Irreducible factors of a partition wall

This file packages unique factorization for three-variable real
polynomials in the form needed by the incidence induction.  In particular,
every line contained in a nonzero wall is contained in one of its
irreducible factors, and a wall of degree `d` has at most `d` distinct
irreducible factors.
-/

namespace Erdos95.SurfaceFactors

open Erdos95.Algebraic Erdos95.ES Erdos95.NonClustering
open UniqueFactorizationMonoid

abbrev Poly3 := MvPolynomial (Fin 3) ℝ

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- The finset of normalized irreducible factors of a polynomial. -/
noncomputable def irreducibleFactors (Q : Poly3) : Finset Poly3 :=
  (UniqueFactorizationMonoid.normalizedFactors Q).toFinset

theorem mem_irreducibleFactors_iff {Q R : Poly3} :
    R ∈ irreducibleFactors Q ↔
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q := by
  exact Multiset.mem_toFinset

theorem irreducible_of_mem_irreducibleFactors {Q R : Poly3}
    (hR : R ∈ irreducibleFactors Q) : Irreducible R := by
  exact irreducible_of_normalized_factor R
    (mem_irreducibleFactors_iff.mp hR)

theorem ne_zero_of_mem_irreducibleFactors {Q R : Poly3}
    (hR : R ∈ irreducibleFactors Q) : R ≠ 0 :=
  (irreducible_of_mem_irreducibleFactors hR).ne_zero

theorem dvd_of_mem_irreducibleFactors {Q R : Poly3}
    (hR : R ∈ irreducibleFactors Q) : R ∣ Q :=
  dvd_of_mem_normalizedFactors (mem_irreducibleFactors_iff.mp hR)

theorem normalize_eq_of_mem_irreducibleFactors {Q R : Poly3}
    (hR : R ∈ irreducibleFactors Q) : normalize R = R :=
  normalize_normalized_factor R (mem_irreducibleFactors_iff.mp hR)

theorem not_dvd_of_ne_of_normalized_irreducible
    {Q R : Poly3} (hQirr : Irreducible Q) (hRirr : Irreducible R)
    (hQnorm : normalize Q = Q) (hRnorm : normalize R = R)
    (hne : Q ≠ R) : ¬Q ∣ R := by
  intro hQR
  have hRQ : R ∣ Q := hQirr.dvd_symm hRirr hQR
  apply hne
  simpa only [hQnorm, hRnorm] using normalize_eq_normalize hQR hRQ

theorem totalDegree_le_of_mem_irreducibleFactors {Q R : Poly3}
    (hQ : Q ≠ 0) (hR : R ∈ irreducibleFactors Q) :
    R.totalDegree ≤ Q.totalDegree :=
  MvPolynomial.totalDegree_le_of_dvd_of_isDomain
    (dvd_of_mem_irreducibleFactors hR) hQ

private theorem exists_mem_lineContained_of_lineContained_prod
    (s : Multiset Poly3) (x v : Fin 3 → ℝ)
    (h : LineContained s.prod x v) :
    ∃ R ∈ s, LineContained R x v := by
  induction s using Multiset.induction_on with
  | empty =>
      rw [Multiset.prod_zero, lineContained_iff] at h
      simp at h
  | @cons R s ih =>
      rw [Multiset.prod_cons, lineContained_mul_iff] at h
      rcases h with hR | hs
      · exact ⟨R, by simp, hR⟩
      · obtain ⟨T, hTs, hT⟩ := ih hs
        exact ⟨T, by simp [hTs], hT⟩

/-- A line contained in a nonzero polynomial wall lies in one of its
normalized irreducible factors. -/
theorem exists_factor_lineContained {Q : Poly3} (hQ : Q ≠ 0)
    {x v : Fin 3 → ℝ} (hline : LineContained Q x v) :
    ∃ R ∈ irreducibleFactors Q, LineContained R x v := by
  let s := normalizedFactors Q
  have hassoc : Associated Q s.prod := (prod_normalizedFactors hQ).symm
  obtain ⟨A, hA⟩ := hassoc.dvd
  have hprod : LineContained s.prod x v := by
    rw [hA, lineContained_mul_iff]
    exact Or.inl hline
  obtain ⟨R, hRs, hRline⟩ :=
    exists_mem_lineContained_of_lineContained_prod s x v hprod
  exact ⟨R, mem_irreducibleFactors_iff.mpr hRs, hRline⟩

/-- Every point of a nonzero polynomial wall lies on one of its normalized
irreducible factor walls. -/
theorem exists_factor_eval_eq_zero {Q : Poly3} (hQ : Q ≠ 0)
    {x : Fin 3 → ℝ} (hx : MvPolynomial.eval x Q = 0) :
    ∃ R ∈ irreducibleFactors Q, MvPolynomial.eval x R = 0 := by
  let s := normalizedFactors Q
  have hassoc : Associated Q s.prod := (prod_normalizedFactors hQ).symm
  obtain ⟨A, hA⟩ := hassoc.dvd
  have hprod : MvPolynomial.eval x s.prod = 0 := by
    rw [hA, map_mul, hx, zero_mul]
  let φ : Poly3 →+* ℝ := MvPolynomial.eval₂Hom (RingHom.id ℝ) x
  have hprod' : φ s.prod = 0 := by simpa [φ] using hprod
  rw [map_multiset_prod, Multiset.prod_eq_zero_iff] at hprod'
  obtain ⟨R, hRs, hRzero⟩ := Multiset.mem_map.mp hprod'
  refine ⟨R, mem_irreducibleFactors_iff.mpr ?_, by simpa [φ] using hRzero⟩
  simpa [s] using hRs

private theorem totalDegree_multiset_prod
    (s : Multiset Poly3) (hs : ∀ R ∈ s, R ≠ 0) :
    s.prod.totalDegree = (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons R s ih =>
      have hR : R ≠ 0 := hs R (by simp)
      have hs0 : s.prod ≠ 0 := Multiset.prod_ne_zero (by
        intro hzero
        exact hs 0 (Multiset.mem_cons_of_mem hzero) rfl)
      rw [Multiset.prod_cons,
        MvPolynomial.totalDegree_mul_of_isDomain hR hs0,
        Multiset.map_cons, Multiset.sum_cons]
      rw [ih (fun T hTs ↦ hs T (by simp [hTs]))]

private theorem sum_toFinset_le_multiset_sum
    (s : Multiset Poly3) (f : Poly3 → ℕ) :
    ∑ R ∈ s.toFinset, f R ≤ (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons R s ih =>
      by_cases hR : R ∈ s.toFinset
      · simpa [hR] using
          ih.trans (Nat.le_add_left (s.map f).sum (f R))
      · simpa [hR] using Nat.add_le_add_left ih (f R)

private theorem multiset_card_le_sum_totalDegree
    (s : Multiset Poly3) (hirr : ∀ R ∈ s, Irreducible R) :
    s.card ≤ (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons R s ih =>
      have hRpos : 0 < R.totalDegree :=
        irreducible_totalDegree_pos (hirr R (by simp))
      have his : s.card ≤ (s.map MvPolynomial.totalDegree).sum :=
        ih (fun T hTs ↦ hirr T (by simp [hTs]))
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
      omega

private theorem totalDegree_prod_normalizedFactors {Q : Poly3} (hQ : Q ≠ 0) :
    (normalizedFactors Q).prod.totalDegree = Q.totalDegree := by
  have hprod0 : (normalizedFactors Q).prod ≠ 0 :=
    Multiset.prod_ne_zero (by
      intro hzero
      exact (irreducible_of_normalized_factor 0 hzero).ne_zero rfl)
  have hassoc := prod_normalizedFactors hQ
  apply le_antisymm
  · exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain hassoc.dvd hQ
  · exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain hassoc.symm.dvd hprod0

/-- A degree-`d` nonzero polynomial has at most `d` distinct irreducible
factors. -/
theorem card_irreducibleFactors_le_totalDegree {Q : Poly3} (hQ : Q ≠ 0) :
    (irreducibleFactors Q).card ≤ Q.totalDegree := by
  calc
    (irreducibleFactors Q).card ≤ (normalizedFactors Q).card := by
      exact Multiset.toFinset_card_le _
    _ ≤ ((normalizedFactors Q).map MvPolynomial.totalDegree).sum :=
      multiset_card_le_sum_totalDegree _
        (fun R hR ↦ irreducible_of_normalized_factor R hR)
    _ = (normalizedFactors Q).prod.totalDegree := by
      symm
      exact totalDegree_multiset_prod _ (fun R hR ↦
        (irreducible_of_normalized_factor R hR).ne_zero)
    _ = Q.totalDegree := totalDegree_prod_normalizedFactors hQ

/-- The sum of the degrees of the distinct normalized irreducible factors is
at most the degree of the original nonzero polynomial. -/
theorem sum_totalDegree_irreducibleFactors_le {Q : Poly3} (hQ : Q ≠ 0) :
    ∑ R ∈ irreducibleFactors Q, R.totalDegree ≤ Q.totalDegree := by
  calc
    ∑ R ∈ irreducibleFactors Q, R.totalDegree ≤
        ((normalizedFactors Q).map MvPolynomial.totalDegree).sum := by
      exact sum_toFinset_le_multiset_sum _ _
    _ = (normalizedFactors Q).prod.totalDegree := by
      symm
      exact totalDegree_multiset_prod _ (fun R hR ↦
        (irreducible_of_normalized_factor R hR).ne_zero)
    _ = Q.totalDegree := totalDegree_prod_normalizedFactors hQ

/-- A degree-only version of the constant in the irreducible-surface
non-clustering theorem. -/
def surfaceLineConstant (d : ℕ) : ℕ :=
  d * d * (2 * (d * d) + d + d + 2) + 1 +
    d * (d + 2) * (2 * (d * (d + 2)) + d + (d + 2) + 2)

theorem irreducibleSurfaceLineConstant_eq (Q : Poly3) :
    irreducibleSurfaceLineConstant Q = surfaceLineConstant Q.totalDegree := by
  rfl

theorem surfaceLineConstant_mono : Monotone surfaceLineConstant := by
  intro a b hab
  unfold surfaceLineConstant
  gcongr

/-- Uniform irreducible-wall occupancy for the Elekes--Sharir family. -/
theorem card_lineIndicesOnSurface_le_degree
    (P : Finset PlanePoint) {Q : Poly3} (hQirr : Irreducible Q)
    {d : ℕ} (hdeg : Q.totalDegree ≤ d) :
    (lineIndicesOnSurface P Q).card ≤
      surfaceLineConstant d * (P.card + 1) := by
  calc
    (lineIndicesOnSurface P Q).card ≤
        irreducibleSurfaceLineConstant Q * (P.card + 1) :=
      card_lineIndicesOnSurface_le_irreducible P hQirr
    _ = surfaceLineConstant Q.totalDegree * (P.card + 1) := by
      rw [irreducibleSurfaceLineConstant_eq]
    _ ≤ surfaceLineConstant d * (P.card + 1) := by
      gcongr
      exact surfaceLineConstant_mono hdeg

end Erdos95.SurfaceFactors
