/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovOccupancy
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Erdős Problem 446: labelled words and multinomial occupancy mass

The finite first-crossing comparison is most transparent for labelled maps
`Fin k → Fin v`.  This file proves that their cardinality is exactly the
factorial-scaled reciprocal-factorial occupancy mass.  The proof compares
the function expansion and the multinomial expansion of a multivariate
polynomial, so it does not require a separate permutation enumeration.
-/

namespace Erdos446

open Finset MvPolynomial
open scoped BigOperators

/-- The number of letters of a labelled word which occupy slot `j`. -/
def wordOccupancy {k v : ℕ} (f : Fin k → Fin v) (j : Fin v) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter fun i ↦ f i = j).card

/-- The monomial exponent vector of a labelled word. -/
noncomputable def wordExponent {k v : ℕ} (f : Fin k → Fin v) : Fin v →₀ ℕ :=
  ∑ i, Finsupp.single (f i) 1

theorem wordExponent_apply {k v : ℕ} (f : Fin k → Fin v) (j : Fin v) :
    wordExponent f j = wordOccupancy f j := by
  classical
  rw [wordExponent, wordOccupancy, Finset.card_filter]
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem wordExponent_eq_iff {k v : ℕ} (f : Fin k → Fin v)
    (c : Fin v → ℕ) :
    wordExponent f = (Finsupp.equivFunOnFinite.symm c) ↔
      wordOccupancy f = c := by
  constructor
  · intro h
    funext j
    have hj := congrArg (fun z : Fin v →₀ ℕ ↦ z j) h
    simpa [wordExponent_apply] using hj
  · intro h
    apply Finsupp.ext
    intro j
    rw [wordExponent_apply, congrFun h j]
    simp

theorem prod_X_word_eq_monomial {k v : ℕ} (f : Fin k → Fin v) :
    (∏ i, (X (f i) : MvPolynomial (Fin v) ℕ)) =
      monomial (wordExponent f) 1 := by
  classical
  rw [wordExponent, monomial_sum_one]
  rfl

/-- The coefficient of an occupancy monomial in the function expansion is
the number of labelled words with that occupancy. -/
theorem coeff_sum_prod_X_eq_card_wordExponent_fiber
    {k v : ℕ} (c : Fin v → ℕ) :
    coeff (Finsupp.equivFunOnFinite.symm c)
        (∑ f : Fin k → Fin v,
          ∏ i, (X (f i) : MvPolynomial (Fin v) ℕ)) =
      ((Finset.univ : Finset (Fin k → Fin v)).filter fun f ↦
        wordExponent f = Finsupp.equivFunOnFinite.symm c).card := by
  classical
  change (coeffAddMonoidHom (R := ℕ)
    (Finsupp.equivFunOnFinite.symm c))
      (∑ f : Fin k → Fin v,
        ∏ i, (X (f i) : MvPolynomial (Fin v) ℕ)) = _
  rw [map_sum (coeffAddMonoidHom
    (R := ℕ) (Finsupp.equivFunOnFinite.symm c))]
  calc
    (∑ f : Fin k → Fin v,
        coeff (Finsupp.equivFunOnFinite.symm c)
          (∏ i, (X (f i) : MvPolynomial (Fin v) ℕ))) =
        ∑ f : Fin k → Fin v,
          if wordExponent f = Finsupp.equivFunOnFinite.symm c
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [prod_X_word_eq_monomial, coeff_monomial]
    _ = _ := by rw [Finset.card_filter]

/-- The coefficient of an occupancy monomial in the multinomial expansion
is the corresponding multinomial coefficient. -/
theorem coeff_sum_X_pow_eq_multinomial
    {k v : ℕ} (c : Fin v → ℕ) (hc : ∑ j, c j = k) :
    coeff (Finsupp.equivFunOnFinite.symm c)
        ((∑ j : Fin v, (X j : MvPolynomial (Fin v) ℕ)) ^ k) =
      Nat.multinomial Finset.univ c := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  change (coeffAddMonoidHom (R := ℕ)
    (Finsupp.equivFunOnFinite.symm c))
      (∑ d ∈ Finset.piAntidiag (Finset.univ : Finset (Fin v)) k,
        C (Nat.multinomial Finset.univ d) *
          ∏ i ∈ Finset.univ, X i ^ d i) = _
  rw [map_sum (coeffAddMonoidHom
    (R := ℕ) (Finsupp.equivFunOnFinite.symm c))]
  have hmem : c ∈ Finset.piAntidiag (Finset.univ : Finset (Fin v)) k := by
    simpa [Finset.mem_piAntidiag] using hc
  rw [Finset.sum_eq_single c]
  · change coeff (Finsupp.equivFunOnFinite.symm c)
        (C (Nat.multinomial Finset.univ c) *
          ∏ i, X i ^ c i) = _
    rw [coeff_C_mul]
    rw [prod_X_pow, coeff_monomial]
    have hind : Finsupp.indicator (Finset.univ : Finset (Fin v))
        (fun i _ ↦ c i) = Finsupp.equivFunOnFinite.symm c := by
      ext j
      simp
    simp [hind]
  · intro d hd hdc
    change coeff (Finsupp.equivFunOnFinite.symm c)
        (C (Nat.multinomial Finset.univ d) *
          ∏ i, X i ^ d i) = _
    rw [coeff_C_mul]
    rw [prod_X_pow, coeff_monomial]
    split_ifs with heq
    · exfalso
      apply hdc
      funext j
      have hj := congrArg (fun z : Fin v →₀ ℕ ↦ z j) heq
      simpa using hj
    · simp
  · exact fun hnot ↦ (hnot hmem).elim

/-- A fixed occupancy vector has exactly its multinomial coefficient many
labelled realizations. -/
theorem card_wordOccupancy_fiber
    {k v : ℕ} (c : Fin v → ℕ) (hc : ∑ j, c j = k) :
    ((Finset.univ : Finset (Fin k → Fin v)).filter fun f ↦
        wordOccupancy f = c).card =
      Nat.multinomial Finset.univ c := by
  classical
  rw [← coeff_sum_X_pow_eq_multinomial c hc,
    Fintype.sum_pow, coeff_sum_prod_X_eq_card_wordExponent_fiber]
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (wordExponent_eq_iff f c).symm

/-- Labelled words satisfying the offset Smirnov prefix barriers. -/
def smirnovWords (k u v : ℕ) : Finset (Fin k → Fin v) :=
  Finset.univ.filter fun f ↦
    ∀ h : ℕ, 1 ≤ h → h ≤ v →
      ∑ j ∈ (Finset.univ.filter fun j : Fin v ↦ j.val < h),
        wordOccupancy f j < u + h

theorem mem_smirnovWords {k u v : ℕ} {f : Fin k → Fin v} :
    f ∈ smirnovWords k u v ↔
      ∀ h : ℕ, 1 ≤ h → h ≤ v →
        ∑ j ∈ (Finset.univ.filter fun j : Fin v ↦ j.val < h),
          wordOccupancy f j < u + h := by
  simp [smirnovWords]

theorem wordOccupancy_sum {k v : ℕ} (f : Fin k → Fin v) :
    ∑ j, wordOccupancy f j = k := by
  classical
  simp_rw [wordOccupancy]
  calc
    ∑ j : Fin v,
        ((Finset.univ : Finset (Fin k)).filter fun i ↦ f i = j).card =
        (Finset.univ : Finset (Fin k)).card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise
        (f := f) (s := Finset.univ) (t := Finset.univ) (by simp)
    _ = k := Fintype.card_fin k

theorem wordOccupancy_mem_compositionsOf {k v : ℕ} (f : Fin k → Fin v) :
    wordOccupancy f ∈ compositionsOf v k := by
  rw [mem_compositionsOf, wordOccupancy_sum]

theorem wordOccupancy_mem_smirnovOccupancies_iff
    {k u v : ℕ} (f : Fin k → Fin v) :
    wordOccupancy f ∈ smirnovOccupancies k u v ↔
      f ∈ smirnovWords k u v := by
  rw [mem_smirnovOccupancies, mem_smirnovWords]
  simp only [wordOccupancy_sum, true_and]
  rfl

/-- The cardinality of the good labelled words is exactly `k!` times the
reciprocal-factorial Smirnov occupancy mass. -/
theorem card_smirnovWords_eq_factorial_mul_mass (k u v : ℕ) :
    ((smirnovWords k u v).card : ℝ) =
      (k.factorial : ℝ) * smirnovOccupancyMass k u v := by
  classical
  rw [smirnovOccupancyMass]
  calc
    ((smirnovWords k u v).card : ℝ) =
        ∑ c ∈ smirnovOccupancies k u v,
          (Nat.multinomial Finset.univ c : ℝ) := by
      rw [← Nat.cast_sum]
      congr 1
      rw [Finset.card_eq_sum_card_fiberwise
        (f := wordOccupancy) (s := smirnovWords k u v)
        (t := smirnovOccupancies k u v) (by
          intro f hf
          exact wordOccupancy_mem_smirnovOccupancies_iff f |>.mpr hf)]
      apply Finset.sum_congr rfl
      intro c hc
      rw [← card_wordOccupancy_fiber c
        (mem_smirnovOccupancies.mp hc).1]
      congr 1
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hf
        exact hf.2
      · intro hf
        refine ⟨?_, hf⟩
        exact (wordOccupancy_mem_smirnovOccupancies_iff f).mp
          (by simpa [hf] using hc)
    _ = ∑ c ∈ smirnovOccupancies k u v,
          (k.factorial : ℝ) * (1 / compositionFactorial c) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [inv_compositionFactorial_eq_multinomial_div_of_mem
        (mem_compositionsOf.mpr (mem_smirnovOccupancies.mp hc).1)]
      field_simp
    _ = (k.factorial : ℝ) *
          ∑ c ∈ smirnovOccupancies k u v,
            1 / compositionFactorial c := by
      rw [Finset.mul_sum]

theorem smirnovProbability_eq_card_smirnovWords_div
    {k u v : ℕ} :
    smirnovProbability k u v =
      ((smirnovWords k u v).card : ℝ) / (v : ℝ) ^ k := by
  rw [smirnovProbability, ← card_smirnovWords_eq_factorial_mul_mass]

end Erdos446
