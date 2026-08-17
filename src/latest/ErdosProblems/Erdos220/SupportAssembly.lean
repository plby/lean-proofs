import ErdosProblems.Erdos220.SupportFactor

/-!
# Summing estimates indexed by six nonempty prime subsets

This file is the finite bookkeeping bridge between a termwise sixth-moment
estimate and `SupportFactor`.  It deliberately knows nothing about the
Fourier definition of a term: an injective transposition into prime-by-prime
support tuples, a termwise estimate on admissible supports, and vanishing on
nonadmissible supports are enough.
-/

open scoped BigOperators

namespace Erdos220

/-- Six labelled, nonempty subsets of an ambient finite set `P`. -/
def nonemptySixSubsetFamilies (P : Finset ℕ) :
    Finset (Fin 6 → Finset ℕ) :=
  Fintype.piFinset fun _ : Fin 6 ↦ P.powerset.erase ∅

lemma mem_nonemptySixSubsetFamilies {P : Finset ℕ}
    {U : Fin 6 → Finset ℕ} :
    U ∈ nonemptySixSubsetFamilies P ↔
      (∀ i, U i ⊆ P) ∧ (∀ i, (U i).Nonempty) := by
  classical
  rw [nonemptySixSubsetFamilies, Fintype.mem_piFinset]
  constructor
  · intro hU
    constructor
    · intro i
      exact Finset.mem_powerset.mp (Finset.mem_of_mem_erase (hU i))
    · intro i
      exact Finset.nonempty_iff_ne_empty.mpr
        (Finset.ne_of_mem_erase (hU i))
  · rintro ⟨hsub, hne⟩ i
    exact Finset.mem_erase.mpr
      ⟨Finset.nonempty_iff_ne_empty.mp (hne i),
        Finset.mem_powerset.mpr (hsub i)⟩

/-- An injective encoding of a finite family of admissible, nonempty support
tuples has total weight bounded by the complete local Euler product. -/
theorem sum_encoded_admissible_weights_le_localFactorProduct
    {A : Type*} [DecidableEq A] (P : Finset ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p) (S : Finset A)
    (encode : A → SixSubsetTuple P)
    (hinj : Set.InjOn encode S)
    (hnonempty : ∀ a ∈ S, AllSixSubsetsNonempty (encode a)) :
    ∑ a ∈ S.filter (fun a ↦ IsAdmissibleSixTuple (encode a)),
        sixSubsetWeight P (encode a) ≤
      ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
  classical
  let G := S.filter fun a ↦ IsAdmissibleSixTuple (encode a)
  have hinjG : Set.InjOn encode G :=
    hinj.mono (Finset.filter_subset _ _)
  have himage : G.image encode ⊆
      (Finset.univ : Finset (SixSubsetTuple P)).filter
        (fun T ↦ IsAdmissibleSixTuple T ∧ AllSixSubsetsNonempty T) := by
    intro T hT
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hT
    have ha' := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ha'.2, hnonempty a ha'.1⟩
  calc
    ∑ a ∈ S.filter (fun a ↦ IsAdmissibleSixTuple (encode a)),
        sixSubsetWeight P (encode a) =
        ∑ T ∈ G.image encode, sixSubsetWeight P T := by
          dsimp [G]
          symm
          exact Finset.sum_image hinjG
    _ ≤ ∑ T ∈ (Finset.univ : Finset (SixSubsetTuple P)).filter
          (fun T ↦ IsAdmissibleSixTuple T ∧ AllSixSubsetsNonempty T),
          sixSubsetWeight P T := by
        apply Finset.sum_le_sum_of_subset_of_nonneg himage
        intro T hT _
        exact sixSubsetWeight_nonneg P hP T
    _ ≤ ∏ p ∈ P, sixthLocalFactor (p : ℝ) :=
      sum_nonempty_six_subset_weights_le_sixthLocalFactor_prod P hP

/-- Finite support assembly in the form used by the sixth-moment proof.

`term U` is allowed to have either sign.  On an admissible support it is
bounded by `scale` times the transposed support weight; on a support having a
prime of multiplicity one it vanishes exactly.  Hence its total over the six
nonempty families is at most `scale` times the local Euler product. -/
theorem sum_six_family_contributions_le_localFactorProduct
    (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p)
    (encode : (Fin 6 → Finset ℕ) → SixSubsetTuple P)
    (hinj : Set.InjOn encode (nonemptySixSubsetFamilies P))
    (hnonempty : ∀ U ∈ nonemptySixSubsetFamilies P,
      AllSixSubsetsNonempty (encode U))
    (scale : ℝ) (hscale : 0 ≤ scale)
    (term : (Fin 6 → Finset ℕ) → ℝ)
    (hterm : ∀ U ∈ nonemptySixSubsetFamilies P,
      IsAdmissibleSixTuple (encode U) →
        term U ≤ scale * sixSubsetWeight P (encode U))
    (hzero : ∀ U ∈ nonemptySixSubsetFamilies P,
      ¬ IsAdmissibleSixTuple (encode U) → term U = 0) :
    ∑ U ∈ nonemptySixSubsetFamilies P, term U ≤
      scale * ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
  classical
  let S := nonemptySixSubsetFamilies P
  let G := S.filter fun U ↦ IsAdmissibleSixTuple (encode U)
  have hsum_filter :
      (∑ U ∈ S, term U) = ∑ U ∈ G, term U := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro U hU
    by_cases hgood : IsAdmissibleSixTuple (encode U)
    · simp [hgood]
    · simp [hgood, hzero U hU hgood]
  rw [hsum_filter]
  calc
    ∑ U ∈ G, term U ≤
        ∑ U ∈ G, scale * sixSubsetWeight P (encode U) := by
      apply Finset.sum_le_sum
      intro U hU
      have hUG := Finset.mem_filter.mp hU
      exact hterm U hUG.1 hUG.2
    _ = scale * ∑ U ∈ G, sixSubsetWeight P (encode U) := by
      rw [Finset.mul_sum]
    _ ≤ scale * ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      dsimp [G, S]
      exact sum_encoded_admissible_weights_le_localFactorProduct
        P hP (nonemptySixSubsetFamilies P) encode hinj hnonempty

/-- The requested normalization, with the scale written as `s * h^3`. -/
theorem sum_six_family_contributions_le_localFactorProduct_natScale
    (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p)
    (encode : (Fin 6 → Finset ℕ) → SixSubsetTuple P)
    (hinj : Set.InjOn encode (nonemptySixSubsetFamilies P))
    (hnonempty : ∀ U ∈ nonemptySixSubsetFamilies P,
      AllSixSubsetsNonempty (encode U))
    (s h : ℕ) (term : (Fin 6 → Finset ℕ) → ℝ)
    (hterm : ∀ U ∈ nonemptySixSubsetFamilies P,
      IsAdmissibleSixTuple (encode U) →
        term U ≤ (s : ℝ) * (h : ℝ) ^ 3 *
          sixSubsetWeight P (encode U))
    (hzero : ∀ U ∈ nonemptySixSubsetFamilies P,
      ¬ IsAdmissibleSixTuple (encode U) → term U = 0) :
    ∑ U ∈ nonemptySixSubsetFamilies P, term U ≤
      (s : ℝ) * (h : ℝ) ^ 3 *
        ∏ p ∈ P, sixthLocalFactor (p : ℝ) := by
  exact sum_six_family_contributions_le_localFactorProduct
    P hP encode hinj hnonempty ((s : ℝ) * (h : ℝ) ^ 3)
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
      term hterm hzero

end Erdos220
