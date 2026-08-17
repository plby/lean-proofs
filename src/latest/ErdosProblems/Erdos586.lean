/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos586.Completion

/-!
# Erdős Problem 586

Balister, Bollobás, Morris, Sahasrabudhe, and Tiba proved that every finite
covering system has two distinct occurrences whose moduli are related by
divisibility.  The public statement below deliberately uses only a raw list of
residue/modulus pairs.  In particular, distinct indices are retained even when
two list entries are equal.

The mathematical proof and its correspondence with this formalization are
described in `tex/586.tex`.
-/

namespace Erdos586

/-! ## Raw public interface -/

/-- Every modulus in the raw list is nontrivial. -/
def RawNontrivial (A : List (ℤ × ℕ)) : Prop :=
  ∀ i : Fin A.length, 1 < (A.get i).2

/-- Every integer belongs to one of the raw list's congruence classes. -/
def RawIsCovering (A : List (ℤ × ℕ)) : Prop :=
  ∀ z : ℤ, ∃ i : Fin A.length,
    z ≡ (A.get i).1 [ZMOD (A.get i).2]

/-- The conclusion of Problem 586 for a raw list: two distinct occurrences
have moduli related by divisibility. -/
def RawHasDividingPair (A : List (ℤ × ℕ)) : Prop :=
  ∃ i j : Fin A.length,
    i ≠ j ∧ (A.get i).2 ∣ (A.get j).2

/-! ## Conversion to the structured internal family -/

/-- Attach the proof of nontriviality to each occurrence.  `List.ofFn`
preserves positions, so this conversion neither deduplicates nor reorders the
input family. -/
def internalFamily (A : List (ℤ × ℕ))
    (hA : RawNontrivial A) : CoveringFamily :=
  List.ofFn fun i : Fin A.length =>
    { residue := (A.get i).1
      modulus := (A.get i).2
      one_lt_modulus := hA i }

@[simp] lemma internalFamily_length (A : List (ℤ × ℕ))
    (hA : RawNontrivial A) :
    (internalFamily A hA).length = A.length := by
  simp [internalFamily]

/-- The raw occurrence corresponding to an occurrence in `internalFamily`. -/
def toRawIndex (A : List (ℤ × ℕ)) (hA : RawNontrivial A)
    (i : Fin (internalFamily A hA).length) : Fin A.length :=
  Fin.cast (internalFamily_length A hA) i

@[simp] lemma toRawIndex_val (A : List (ℤ × ℕ))
    (hA : RawNontrivial A)
    (i : Fin (internalFamily A hA).length) :
    (toRawIndex A hA i).val = i.val := rfl

@[simp] lemma internalFamily_get_residue (A : List (ℤ × ℕ))
    (hA : RawNontrivial A)
    (i : Fin (internalFamily A hA).length) :
    ((internalFamily A hA).get i).residue =
      (A.get (toRawIndex A hA i)).1 := by
  cases i
  simp [internalFamily, toRawIndex]
  rfl

@[simp] lemma internalFamily_get_modulus (A : List (ℤ × ℕ))
    (hA : RawNontrivial A)
    (i : Fin (internalFamily A hA).length) :
    ((internalFamily A hA).get i).modulus =
      (A.get (toRawIndex A hA i)).2 := by
  cases i
  simp [internalFamily, toRawIndex]
  rfl

lemma internalFamily_isCovering {A : List (ℤ × ℕ)}
    (hnontrivial : RawNontrivial A) (hcover : RawIsCovering A) :
    IsCovering (internalFamily A hnontrivial) := by
  intro z
  obtain ⟨i, hi⟩ := hcover z
  let j : Fin (internalFamily A hnontrivial).length :=
    Fin.cast (internalFamily_length A hnontrivial).symm i
  refine ⟨j, ?_⟩
  have hj : toRawIndex A hnontrivial j = i := by
    apply Fin.ext
    rfl
  rw [internalFamily_get_residue, internalFamily_get_modulus, hj]
  exact hi

lemma rawHasDividingPair_of_internal
    {A : List (ℤ × ℕ)} (hnontrivial : RawNontrivial A)
    (hpair : HasDividingPair (internalFamily A hnontrivial)) :
    RawHasDividingPair A := by
  obtain ⟨i, j, hij, hdvd⟩ := hpair
  refine ⟨toRawIndex A hnontrivial i, toRawIndex A hnontrivial j, ?_, ?_⟩
  · intro heq
    apply hij
    apply Fin.ext
    simpa using congrArg Fin.val heq
  · rw [internalFamily_get_modulus, internalFamily_get_modulus] at hdvd
    exact hdvd

lemma internalFamily_isDivisibilityAntichain_of_no_raw_pair
    {A : List (ℤ × ℕ)} (hnontrivial : RawNontrivial A)
    (hnoPair : ¬ RawHasDividingPair A) :
    IsDivisibilityAntichain (internalFamily A hnontrivial) := by
  by_contra hnotAnti
  have hpair : HasDividingPair (internalFamily A hnontrivial) :=
    (not_isDivisibilityAntichain_iff_hasDividingPair _).mp hnotAnti
  exact hnoPair (rawHasDividingPair_of_internal hnontrivial hpair)

/-- The elementary reduction used at the start of the BBMST argument.  A
hypothetical raw counterexample supplies a minimal occurrence-indexed cover
whose moduli are a divisibility antichain and none of whose moduli is a prime
power. -/
lemma minimal_no_prime_power_subcover_of_raw_counterexample
    {A : List (ℤ × ℕ)}
    (hnontrivial : RawNontrivial A) (hcover : RawIsCovering A)
    (hnoPair : ¬ RawHasDividingPair A) :
    ∃ s : Finset (Fin (internalFamily A hnontrivial).length),
      IsMinimalCover (internalFamily A hnontrivial) s ∧
        ∀ i ∈ s,
          ¬ IsPrimePow ((internalFamily A hnontrivial).get i).modulus := by
  apply exists_minimal_subcover_no_prime_power
  · exact internalFamily_isCovering hnontrivial hcover
  · exact internalFamily_isDivisibilityAntichain_of_no_raw_pair
      hnontrivial hnoPair

/-- The complete elementary counterexample package passed to the analytic
sieve: minimality, the inherited directed antichain property, and exclusion
of prime powers. -/
lemma minimal_counterexample_data
    {A : List (ℤ × ℕ)}
    (hnontrivial : RawNontrivial A) (hcover : RawIsCovering A)
    (hnoPair : ¬ RawHasDividingPair A) :
    ∃ s : Finset (Fin (internalFamily A hnontrivial).length),
      IsMinimalCover (internalFamily A hnontrivial) s ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        ¬ ((internalFamily A hnontrivial).get i).modulus ∣
          ((internalFamily A hnontrivial).get j).modulus) ∧
      (∀ i ∈ s,
        ¬ IsPrimePow ((internalFamily A hnontrivial).get i).modulus) := by
  let B := internalFamily A hnontrivial
  have hanti : IsDivisibilityAntichain B :=
    internalFamily_isDivisibilityAntichain_of_no_raw_pair
      hnontrivial hnoPair
  obtain ⟨s, hminimal, hnopp⟩ :=
    minimal_no_prime_power_subcover_of_raw_counterexample
      hnontrivial hcover hnoPair
  refine ⟨s, hminimal, ?_, hnopp⟩
  intro i hi j hj hij
  exact hanti i j hij

/-- Erdős Problem 586: every finite covering system with moduli greater than
one contains two distinct occurrences whose moduli are related by
divisibility. -/
theorem erdos_586 (A : List (ℤ × ℕ))
    (hnontrivial : ∀ i : Fin A.length, 1 < (A.get i).2)
    (hcover : ∀ z : ℤ, ∃ i : Fin A.length,
      z ≡ (A.get i).1 [ZMOD (A.get i).2]) :
    ∃ i j : Fin A.length,
      i ≠ j ∧ (A.get i).2 ∣ (A.get j).2 := by
  change RawNontrivial A at hnontrivial
  change RawIsCovering A at hcover
  change RawHasDividingPair A
  by_contra hnoPair
  obtain ⟨s, hminimal, hanti, _⟩ :=
    minimal_counterexample_data hnontrivial hcover hnoPair
  exact no_minimal_antichain_cover
    (internalFamily A hnontrivial) s hminimal hanti

end Erdos586

#print axioms Erdos586.erdos_586
