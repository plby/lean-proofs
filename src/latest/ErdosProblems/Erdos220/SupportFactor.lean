import ErdosProblems.Erdos220.SmallMoment

/-!
# Factoring the six-support sum

In the sixth-moment expansion used for Erdős problem 220, each prime chooses
the subset of the six denominator variables in which it occurs.  Orthogonality
kills a choice in which a prime occurs exactly once.  This file proves, purely
by finite combinatorics, that the remaining weighted sum factors into the
expected product of local factors.
-/

open scoped BigOperators

namespace Erdos220

/-! ## One-prime positivity -/

lemma sixthSupportWeight_nonneg {p : ℝ} (hp : 1 ≤ p) (I : Finset (Fin 6)) :
    0 ≤ sixthSupportWeight p I := by
  rw [sixthSupportWeight]
  split_ifs
  · exact div_nonneg (pow_nonneg (by positivity) _)
      (pow_nonneg (sub_nonneg.mpr hp) _)
  · exact zero_le_one

/-! ## Six tuples of subsets -/

/-- A six-tuple of subsets of `P`, represented prime-by-prime: `T p` is the
set of indices `i : Fin 6` for which `p` belongs to the `i`-th subset.  This
representation makes the Euler-product factorization literal. -/
abbrev SixSubsetTuple (P : Finset ℕ) := (p : P) → Finset (Fin 6)

/-- The multiplicity with which `p` occurs among the six subsets. -/
def sixMultiplicity {P : Finset ℕ} (T : SixSubsetTuple P) (p : P) : ℕ :=
  (T p).card

/-- Every prime used by the tuple occurs at least twice (equivalently, no
prime has multiplicity exactly one). -/
def IsAdmissibleSixTuple {P : Finset ℕ} (T : SixSubsetTuple P) : Prop :=
  ∀ p : P, sixMultiplicity T p ≠ 1

instance instDecidableIsAdmissibleSixTuple {P : Finset ℕ}
    (T : SixSubsetTuple P) : Decidable (IsAdmissibleSixTuple T) := by
  unfold IsAdmissibleSixTuple
  infer_instance

/-- The `i`-th one of the six subsets is nonempty. -/
def SixthSubsetNonempty {P : Finset ℕ} (T : SixSubsetTuple P) (i : Fin 6) : Prop :=
  ∃ p : P, i ∈ T p

/-- All six individual subsets are nonempty. -/
def AllSixSubsetsNonempty {P : Finset ℕ} (T : SixSubsetTuple P) : Prop :=
  ∀ i : Fin 6, SixthSubsetNonempty T i

instance instDecidableAllSixSubsetsNonempty {P : Finset ℕ}
    (T : SixSubsetTuple P) : Decidable (AllSixSubsetsNonempty T) := by
  unfold AllSixSubsetsNonempty SixthSubsetNonempty
  infer_instance

/-- Product of the prime-support weights attached to a six-tuple. -/
noncomputable def sixSubsetWeight (P : Finset ℕ) (T : SixSubsetTuple P) : ℝ :=
  ∏ p : P, sixthSupportWeight (p : ℝ) (T p)

/-- A version of `sixSubsetWeight` which is zero unless every prime support
survives orthogonality. -/
noncomputable def survivingSixSubsetWeight
    (P : Finset ℕ) (T : SixSubsetTuple P) : ℝ :=
  ∏ p : P, if (T p).card ≠ 1 then
    sixthSupportWeight (p : ℝ) (T p) else 0

lemma sixSubsetWeight_nonneg (P : Finset ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p) (T : SixSubsetTuple P) :
    0 ≤ sixSubsetWeight P T := by
  apply Finset.prod_nonneg
  intro p _
  exact sixthSupportWeight_nonneg
    (by exact_mod_cast (hP p p.property).trans' (by omega)) (T p)

/-- Pointwise, the zero-extended weight is the ordinary product weight on an
admissible tuple and zero on a nonadmissible tuple. -/
lemma survivingSixSubsetWeight_eq_ite (P : Finset ℕ) (T : SixSubsetTuple P) :
    survivingSixSubsetWeight P T =
      if IsAdmissibleSixTuple T then sixSubsetWeight P T else 0 := by
  classical
  by_cases hT : IsAdmissibleSixTuple T
  · rw [if_pos hT]
    simp only [survivingSixSubsetWeight, sixSubsetWeight]
    apply Finset.prod_congr rfl
    intro p _
    rw [if_pos (by simpa [sixMultiplicity] using hT p)]
  · rw [if_neg hT]
    rw [survivingSixSubsetWeight]
    have hex : ∃ p : P, ¬ sixMultiplicity T p ≠ 1 := by
      simpa only [IsAdmissibleSixTuple, not_forall] using hT
    obtain ⟨p, hp⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    rw [if_neg (by simpa [sixMultiplicity] using hp)]

/-- The unrestricted sum of zero-extended survivor weights factors exactly
as an Euler product. -/
theorem sum_survivingSixSubsetWeight_eq_prod (P : Finset ℕ) :
    ∑ T : SixSubsetTuple P, survivingSixSubsetWeight P T =
      ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
  classical
  unfold survivingSixSubsetWeight
  calc
    (∑ T : SixSubsetTuple P,
        ∏ p : P, if (T p).card ≠ 1 then
          sixthSupportWeight (p : ℝ) (T p) else 0) =
        ∏ p : P, ∑ I : Finset (Fin 6), if I.card ≠ 1 then
          sixthSupportWeight (p : ℝ) I else 0 := by
      exact (Fintype.prod_sum (fun (p : P) (I : Finset (Fin 6)) ↦
        if I.card ≠ 1 then sixthSupportWeight (p : ℝ) I else 0)).symm
    _ = ∏ p : P, sixthLocalFactor (p : ℝ) := by
      apply Finset.prod_congr rfl
      intro p _
      rw [← Finset.sum_filter]
      simpa [admissibleSixthSupports] using
          sum_sixthSupportWeight_eq (p : ℝ)
    _ = ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
      simpa using (Finset.prod_coe_sort P (fun p : ℕ ↦ sixthLocalFactor (p : ℝ)))

/-- Exact factorization of the sum over the surviving tuples. -/
theorem sum_admissible_sixSubsetWeight_eq_prod (P : Finset ℕ) :
    ∑ T ∈ (Finset.univ : Finset (SixSubsetTuple P)).filter IsAdmissibleSixTuple,
        sixSubsetWeight P T =
      ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
  classical
  rw [← sum_survivingSixSubsetWeight_eq_prod P]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  rw [survivingSixSubsetWeight_eq_ite]

/-- Any extra restriction on the six individual subsets can only decrease
the survivor sum.  This is the upper-bound form normally used after imposing
nonemptiness of denominator supports. -/
theorem sum_six_subset_weights_le_sixthLocalFactor_prod
    (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p)
    (required : SixSubsetTuple P → Prop) [DecidablePred required] :
    ∑ T ∈ (Finset.univ : Finset (SixSubsetTuple P)).filter
        (fun T ↦ IsAdmissibleSixTuple T ∧ required T),
        sixSubsetWeight P T ≤
      ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
  classical
  rw [← sum_admissible_sixSubsetWeight_eq_prod P]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
    exact hT.1
  · intro T hT _
    exact sixSubsetWeight_nonneg P hP T

/-- In particular, requiring every one of the six subsets to be nonempty
still leaves an upper bound by the same local Euler product. -/
theorem sum_nonempty_six_subset_weights_le_sixthLocalFactor_prod
    (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) :
    ∑ T ∈ (Finset.univ : Finset (SixSubsetTuple P)).filter
        (fun T ↦ IsAdmissibleSixTuple T ∧ AllSixSubsetsNonempty T),
        sixSubsetWeight P T ≤
      ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
  classical
  exact sum_six_subset_weights_le_sixthLocalFactor_prod P hP
    AllSixSubsetsNonempty

end Erdos220
