/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.Foundations
import ErdosProblems.Erdos874.FreimanDimension
import ErdosProblems.Erdos874.ProgressionExtraction

/-!
# The modular decomposition step for Erdős Problem 874

This file isolates the exact finite congruence argument used in the
Deshouillers--Freiman structural analysis.  If a restricted layer of an
exceptional set `C` contains a long progression of difference `q`, translating
that progression by two sums supported outside `C` would make two different
positive restricted layers of `A` intersect.  Admissibility therefore forbids
such a pair whenever the two outside sums are congruent modulo `q` and their
quotient displacement is shorter than the progression.

The final section records the equally important identification of the
structural difference.  Once every element of `A` is in one residue class
modulo `q`, and a restricted layer of `C ⊆ A` contains two adjacent terms of
a `q`-progression, `q` satisfies the universal property of the gcd of all
differences of elements of `A`.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Translating a restricted layer on a disjoint support -/

/-- Adding a sum supported in `B` to a restricted sum supported in `C`
produces a restricted sum on `A`, provided `C ⊆ A` and `B ⊆ A \ C`.
The disjointness needed for the cardinality calculation is therefore
automatic. -/
lemma add_sum_mem_restrictedSumset_of_subset_sdiff
    {A C B : Finset ℤ} {t : ℕ} {z : ℤ}
    (hCA : C ⊆ A) (hB : B ⊆ A \ C)
    (hz : z ∈ restrictedSumset t C) :
    z + ∑ x ∈ B, x ∈ restrictedSumset (t + B.card) A := by
  obtain ⟨R, hRC, hRcard, hRsum⟩ := mem_restrictedSumset.mp hz
  have hRA : R ⊆ A := hRC.trans hCA
  have hBA : B ⊆ A := hB.trans Finset.sdiff_subset
  have hRB : Disjoint R B := by
    rw [Finset.disjoint_left]
    intro x hxR hxB
    exact (Finset.mem_sdiff.mp (hB hxB)).2 (hRC hxR)
  apply mem_restrictedSumset.mpr
  refine ⟨R ∪ B, Finset.union_subset hRA hBA, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hRB, hRcard]
  · rw [Finset.sum_union hRB, hRsum]

/-- Witness form of `add_sum_mem_restrictedSumset_of_subset_sdiff`, with the
outside sum already named. -/
lemma add_mem_restrictedSumset_of_subset_sdiff
    {A C B : Finset ℤ} {t : ℕ} {z w : ℤ}
    (hCA : C ⊆ A) (hB : B ⊆ A \ C)
    (hz : z ∈ restrictedSumset t C)
    (hw : ∑ x ∈ B, x = w) :
    z + w ∈ restrictedSumset (t + B.card) A := by
  simpa [← hw] using add_sum_mem_restrictedSumset_of_subset_sdiff hCA hB hz

/-! ## The modular collision obstruction -/

/-- Two translates of a sufficiently long arithmetic progression overlap
when their translation difference is a short multiple of the common
difference.  This is the elementary geometric core of the modular argument.
-/
lemma exists_eq_add_of_sub_eq_mul_of_natAbs_lt
    {u v a q z : ℤ} {L : ℕ}
    (huv : u - v = q * z) (hz : z.natAbs < L) :
    ∃ i j : ℕ, i < L ∧ j < L ∧
      a + q * (i : ℤ) + v = a + q * (j : ℤ) + u := by
  by_cases hnonneg : 0 ≤ z
  · have habs : z.toNat = z.natAbs := by
      have hto : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hnonneg
      have hna : ((z.natAbs : ℕ) : ℤ) = z := Int.natAbs_of_nonneg hnonneg
      exact_mod_cast hto.trans hna.symm
    refine ⟨z.toNat, 0, habs ▸ hz, by omega, ?_⟩
    · rw [Int.toNat_of_nonneg hnonneg]
      simp only [Nat.cast_zero, mul_zero]
      omega
  · have hneg : z < 0 := lt_of_not_ge hnonneg
    refine ⟨0, z.natAbs, by omega, hz, ?_⟩
    simp only [Nat.cast_zero, mul_zero]
    have hzabs : ((z.natAbs : ℕ) : ℤ) = -z := by
      rw [Int.natCast_natAbs, abs_of_neg hneg]
    rw [hzabs]
    linear_combination -huv

/-- **Modular collision obstruction.**

Let a `q`-progression of `L` terms lie in `t^∧ C`.  Two subsets `B,D` of
the regular part cannot have different sizes and sums differing by `q*z`
with `|z| < L`: translating suitable terms of the progression would give the
same integer in the distinct positive layers `t+|B|` and `t+|D|` of `A`.
-/
theorem no_short_congruent_outside_subset_sums
    {A C B D : Finset ℤ} {t q L : ℕ} {z : ℤ}
    (hA : IsAdmissible A) (hCA : C ⊆ A) (ht : 0 < t)
    (hAP : ContainsAP (restrictedSumset t C) (q : ℤ) L)
    (hB : B ⊆ A \ C) (hD : D ⊆ A \ C)
    (hcard : B.card ≠ D.card)
    (hsum : (∑ x ∈ B, x) - ∑ x ∈ D, x = (q : ℤ) * z)
    (hz : z.natAbs < L) : False := by
  obtain ⟨a, ha⟩ := hAP
  obtain ⟨i, j, hi, hj, heq⟩ :=
    exists_eq_add_of_sub_eq_mul_of_natAbs_lt
      (a := a) (u := ∑ x ∈ B, x) (v := ∑ x ∈ D, x) hsum hz
  have hiAP : a + (q : ℤ) * (i : ℤ) ∈ restrictedSumset t C :=
    ha (mem_arithmeticProgression.mpr ⟨i, hi, rfl⟩)
  have hjAP : a + (q : ℤ) * (j : ℤ) ∈ restrictedSumset t C :=
    ha (mem_arithmeticProgression.mpr ⟨j, hj, rfl⟩)
  have hleft :
      a + (q : ℤ) * (i : ℤ) + ∑ x ∈ D, x ∈
        restrictedSumset (t + D.card) A :=
    add_sum_mem_restrictedSumset_of_subset_sdiff hCA hD hiAP
  have hright :
      a + (q : ℤ) * (j : ℤ) + ∑ x ∈ B, x ∈
        restrictedSumset (t + B.card) A :=
    add_sum_mem_restrictedSumset_of_subset_sdiff hCA hB hjAP
  have hne : t + D.card ≠ t + B.card := by
    intro h
    exact hcard (Nat.add_left_cancel h.symm)
  have hdisj := hA (by omega : 0 < t + D.card) (by omega : 0 < t + B.card) hne
  exact (Finset.disjoint_left.mp hdisj) hleft (heq ▸ hright)

/-- Empty-subset specialization: no nonempty subset of the regular part can
have a short nonzero-cardinality sum which is a multiple of the structural
difference. -/
theorem no_short_zero_residue_outside_subset_sum
    {A C B : Finset ℤ} {t q L : ℕ} {z : ℤ}
    (hA : IsAdmissible A) (hCA : C ⊆ A) (ht : 0 < t)
    (hAP : ContainsAP (restrictedSumset t C) (q : ℤ) L)
    (hB : B ⊆ A \ C) (hB0 : B.Nonempty)
    (hsum : ∑ x ∈ B, x = (q : ℤ) * z)
    (hz : z.natAbs < L) : False := by
  apply no_short_congruent_outside_subset_sums hA hCA ht hAP hB
    (Finset.empty_subset _) (Finset.card_ne_zero.mpr hB0)
  · simpa using hsum
  · exact hz

/-! ## Common residue classes and the difference gcd -/

/-- `d` divides every difference of two elements of `A`; equivalently, `A`
is contained in a single residue class modulo `d`. -/
def IsDifferenceDivisor (d : ℕ) (A : Finset ℤ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, (d : ℤ) ∣ x - y

/-- Universal-property formulation saying that `d` is the nonnegative gcd
of all differences of elements of `A`. -/
def IsDifferenceGCD (d : ℕ) (A : Finset ℤ) : Prop :=
  IsDifferenceDivisor d A ∧
    ∀ e : ℕ, IsDifferenceDivisor e A → e ∣ d

/-- A set contained in an arithmetic progression lies in one residue class
modulo its common difference. -/
lemma ContainedInAP.isDifferenceDivisor
    {A : Finset ℤ} {start : ℤ} {step length : ℕ}
    (hA : ContainedInAP A start step length) :
    IsDifferenceDivisor step A := by
  intro x hx y hy
  obtain ⟨i, hi, hxi⟩ := hA.exists_coordinate hx
  obtain ⟨j, hj, hyj⟩ := hA.exists_coordinate hy
  refine ⟨(i : ℤ) - (j : ℤ), ?_⟩
  rw [hxi, hyj]
  ring

/-- Equal-cardinality subset sums are congruent modulo every common
difference divisor. -/
lemma IsDifferenceDivisor.dvd_sub_sum_of_card_eq
    {A R S : Finset ℤ} {d : ℕ}
    (hd : IsDifferenceDivisor d A)
    (hRA : R ⊆ A) (hSA : S ⊆ A)
    (hR : R.Nonempty) (hcard : R.card = S.card) :
    (d : ℤ) ∣ (∑ x ∈ R, x) - ∑ x ∈ S, x := by
  obtain ⟨b, hbR⟩ := hR
  have hbA : b ∈ A := hRA hbR
  have hRdiv : (d : ℤ) ∣ ∑ x ∈ R, (x - b) := by
    exact Finset.dvd_sum fun x hx ↦ hd x (hRA hx) b hbA
  have hSdiv : (d : ℤ) ∣ ∑ x ∈ S, (x - b) := by
    exact Finset.dvd_sum fun x hx ↦ hd x (hSA hx) b hbA
  have hsub := dvd_sub hRdiv hSdiv
  have hRsum : ∑ x ∈ R, (x - b) = (∑ x ∈ R, x) - (R.card : ℤ) * b := by
    simp [Finset.sum_sub_distrib]
  have hSsum : ∑ x ∈ S, (x - b) = (∑ x ∈ S, x) - (S.card : ℤ) * b := by
    simp [Finset.sum_sub_distrib]
  rw [hRsum, hSsum] at hsub
  rw [hcard] at hsub
  have heq :
      ((∑ x ∈ R, x) - (S.card : ℤ) * b) -
          ((∑ x ∈ S, x) - (S.card : ℤ) * b) =
        (∑ x ∈ R, x) - ∑ x ∈ S, x := by
    ring
  rw [heq] at hsub
  exact hsub

/-- **Identification of the structural step.**  If `q` divides every
difference in `A`, while a positive restricted layer of `C ⊆ A` contains two
adjacent terms of a `q`-progression, then `q` is the gcd of all differences in
`A`.  Thus the common difference obtained from the modular decomposition is
intrinsic, rather than an artefact of the chosen progression. -/
theorem isDifferenceGCD_of_long_progression
    {A C : Finset ℤ} {t q L : ℕ}
    (hCA : C ⊆ A) (ht : 0 < t) (_hq : 0 < q) (hL : 2 ≤ L)
    (hqA : IsDifferenceDivisor q A)
    (hAP : ContainsAP (restrictedSumset t C) (q : ℤ) L) :
    IsDifferenceGCD q A := by
  refine ⟨hqA, ?_⟩
  intro d hd
  obtain ⟨a, ha⟩ := hAP
  have ha0 : a ∈ restrictedSumset t C := by
    apply ha
    exact mem_arithmeticProgression.mpr ⟨0, by omega, by simp⟩
  have ha1 : a + (q : ℤ) ∈ restrictedSumset t C := by
    apply ha
    exact mem_arithmeticProgression.mpr ⟨1, by omega, by simp⟩
  obtain ⟨R, hRC, hRcard, hRsum⟩ := mem_restrictedSumset.mp ha0
  obtain ⟨S, hSC, hScard, hSsum⟩ := mem_restrictedSumset.mp ha1
  have hRnonempty : R.Nonempty := Finset.card_pos.mp (hRcard.symm ▸ ht)
  have hdqZ : (d : ℤ) ∣ (q : ℤ) := by
    have hdiv := hd.dvd_sub_sum_of_card_eq
      (hRC.trans hCA) (hSC.trans hCA) hRnonempty (hRcard.trans hScard.symm)
    rw [hRsum, hSsum] at hdiv
    simpa using (dvd_neg.mpr hdiv)
  exact_mod_cast hdqZ

/-- Convenient corollary when the common-residue conclusion is supplied by
an explicit containing arithmetic progression. -/
theorem isDifferenceGCD_of_containedInAP_of_long_progression
    {A C : Finset ℤ} {start : ℤ} {t q L shortLength : ℕ}
    (hCA : C ⊆ A) (ht : 0 < t) (hq : 0 < q) (hL : 2 ≤ L)
    (hA : ContainedInAP A start q shortLength)
    (hAP : ContainsAP (restrictedSumset t C) (q : ℤ) L) :
    IsDifferenceGCD q A :=
  isDifferenceGCD_of_long_progression hCA ht hq hL
    hA.isDifferenceDivisor hAP

end

end Erdos874
