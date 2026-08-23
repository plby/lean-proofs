import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Erdős Problem 248: logical core

This file contains the part of the argument which is independent of the
analytic construction of the sieve measure.  In particular, it records the
exact target predicate, the countable family of bad events, extraction of a
point outside a bad union of measure strictly less than one, and the passage
from arbitrarily large witnesses to an infinite set.
-/

open MeasureTheory
open scoped ArithmeticFunction.omega ENNReal

namespace Erdos248

/-- The simultaneous bound required in Erdős Problem 248. -/
def IsGood (C : ℝ) (n : ℕ) : Prop :=
  ∀ k ≥ 1, ω (n + k) ≤ C * k

/-- Failure of the required estimate at one positive shift. -/
def IsBadAt (C : ℝ) (k n : ℕ) : Prop :=
  1 ≤ k ∧ C * k < ω (n + k)

theorem not_isGood_iff_exists_isBadAt {C : ℝ} {n : ℕ} :
    ¬ IsGood C n ↔ ∃ k, IsBadAt C k n := by
  simp only [IsGood, IsBadAt, not_forall, not_le, exists_prop]

theorem mem_iUnion_isBadAt_iff {C : ℝ} {n : ℕ} :
    n ∈ ⋃ k : ℕ, {m : ℕ | IsBadAt C k m} ↔ ¬ IsGood C n := by
  rw [not_isGood_iff_exists_isBadAt]
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]

/-- A probability measure whose union of bad-shift events has mass below one
contains a point satisfying every shift estimate. -/
theorem exists_isGood_of_measure_iUnion_isBadAt_lt_one
    (C : ℝ) (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hbad : μ (⋃ k : ℕ, {n : ℕ | IsBadAt C k n}) < 1) :
    ∃ n, IsGood C n := by
  have hne : (⋃ k : ℕ, {n : ℕ | IsBadAt C k n}) ≠ Set.univ := by
    intro h
    rw [h, measure_univ] at hbad
    exact (lt_irrefl 1) hbad
  by_contra hgood
  push Not at hgood
  apply hne
  ext n
  simp only [Set.mem_univ, iff_true]
  exact mem_iUnion_isBadAt_iff.mpr (hgood n)

/-- A finite measure package sufficient for one arbitrarily large witness.

The analytic part of the proof constructs such a package from its product
Selberg weight.  Keeping the normalization and the support condition explicit
means that no probabilistic assumption is hidden in the reduction. -/
structure SieveCertificate (C : ℝ) (B : ℕ) where
  measure : Measure ℕ
  measure_univ : measure Set.univ = 1
  low_mass : measure {n : ℕ | n ≤ B} = 0
  bad_mass : measure (⋃ k : ℕ, {n : ℕ | IsBadAt C k n}) < 1

/-- A sieve certificate contains a witness above its prescribed lower
endpoint satisfying every shift estimate. -/
theorem SieveCertificate.exists_gt_isGood {C : ℝ} {B : ℕ}
    (cert : SieveCertificate C B) :
    ∃ n : ℕ, B < n ∧ IsGood C n := by
  let bad : Set ℕ := ⋃ k : ℕ, {n : ℕ | IsBadAt C k n}
  let low : Set ℕ := {n : ℕ | n ≤ B}
  have h_union : cert.measure (bad ∪ low) < 1 := by
    apply lt_of_le_of_lt (measure_union_le bad low)
    simpa only [low, cert.low_mass, add_zero] using cert.bad_mass
  have hne : bad ∪ low ≠ Set.univ := by
    intro h
    rw [h, cert.measure_univ] at h_union
    exact (lt_irrefl 1) h_union
  have hex : ∃ n : ℕ, n ∉ bad ∪ low := by
    by_contra hno
    apply hne
    apply Set.eq_univ_of_forall
    intro n
    by_contra hn
    exact hno ⟨n, hn⟩
  obtain ⟨n, hn⟩ := hex
  refine ⟨n, ?_, ?_⟩
  · have hnlow : n ∉ low := fun hmem ↦ hn (Set.mem_union_right bad hmem)
    simpa only [low, Set.mem_ofPred_eq, not_le] using hnlow
  · have hnbad : n ∉ bad := fun hmem ↦ hn (Set.mem_union_left low hmem)
    by_contra hgood
    exact hnbad (mem_iUnion_isBadAt_iff.mpr hgood)

/-- Arbitrarily large simultaneous witnesses form an infinite set. -/
theorem infinite_isGood_of_forall_exists_gt (C : ℝ)
    (h : ∀ B : ℕ, ∃ n : ℕ, B < n ∧ IsGood C n) :
    {n : ℕ | IsGood C n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨n, hBn, hn⟩ := h B
  exact ⟨n, hn, hBn⟩

/-- The final target follows as soon as the analytic argument supplies one
positive constant and arbitrarily large simultaneous witnesses. -/
theorem erdos248_of_arbitrarily_large
    (h : ∃ C > (0 : ℝ), ∀ B : ℕ, ∃ n : ℕ, B < n ∧ IsGood C n) :
    ∃ C > (0 : ℝ), {n : ℕ | ∀ k ≥ 1, ω (n + k) ≤ C * k}.Infinite := by
  obtain ⟨C, hC, hlarge⟩ := h
  refine ⟨C, hC, ?_⟩
  simpa only [IsGood] using infinite_isGood_of_forall_exists_gt C hlarge

/-- Certificate-level form of the final reduction.  This is the exact
interface consumed by the analytic construction. -/
theorem erdos248_of_sieve_certificates
    (h : ∃ C > (0 : ℝ), ∀ B : ℕ, Nonempty (SieveCertificate C B)) :
    ∃ C > (0 : ℝ), {n : ℕ | ∀ k ≥ 1, ω (n + k) ≤ C * k}.Infinite := by
  apply erdos248_of_arbitrarily_large
  obtain ⟨C, hC, hcert⟩ := h
  exact ⟨C, hC, fun B ↦ (hcert B).some.exists_gt_isGood⟩

end Erdos248
