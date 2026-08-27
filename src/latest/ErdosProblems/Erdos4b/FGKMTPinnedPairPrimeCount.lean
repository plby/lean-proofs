/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedPrimeExpansion
import ErdosProblems.Erdos4b.FGKMTPinnedPrimeCrt
import BoundedGaps.Maynard.ImprovedGPY.S2Pair

/-!
# Literal prime counts in the reduced pinned CRT class

Compatible divisor pairs give one reduced class; incompatible pairs
give zero. The existing prime-progression API uses `[A+1,B+1)`,
which is exactly the literal interval `(A,B]` used here.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

theorem commonPinnedDivisorCondition_pair_iff {m M R Q : ℕ}
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M)
    (hQ : Q.Prime) (hRQ : R < Q) (h : Fin (m + 1) → ℕ)
    (hinj : Function.Injective h) (hshift : ∀ i, h i < 2 * (m + 1) ^ 2)
    (j : Fin (m + 1)) (d e : commonPrimeUniverse M R → Option (Fin m)) (P : ℕ) :
    (commonPinnedDivisorCondition m Q (fun q => q.val) h j d P ∧
      commonPinnedDivisorCondition m Q (fun q => q.val) h j e P) ↔
      AssignmentCompatible d e ∧
        commonPinnedDivisorCondition m Q (fun q => q.val) h j (mergeAssignment d e) P := by
  apply commonPinnedDivisorPair_iff_merged commonPrimeUniverse_prime Subtype.val_injective
  · intro q hdiv
    rcases (Nat.dvd_prime hQ).mp hdiv with heq | heq
    · exact (commonPrimeUniverse_prime q).ne_one heq
    · have := (mem_commonPrimeUniverse.mp q.property).2.1
      omega
  · exact hinj
  · intro q i
    exact (hshift i).trans (commonPrimeUniverse_large hsmall q)

theorem commonPinnedPairPrimeCount_zero_of_incompatible {m W M R Q A B v : ℕ}
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M)
    (hQ : Q.Prime) (hRQ : R < Q) (h : Fin (m + 1) → ℕ)
    (hinj : Function.Injective h) (hshift : ∀ i, h i < 2 * (m + 1) ^ 2)
    (j : Fin (m + 1)) (d e : commonPrimeUniverse M R → Option (Fin m))
    (hde : ¬AssignmentCompatible d e) :
    commonPinnedPairPrimeCount m W Q A B v (fun q => q.val) h j d e = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro P _hP hcond
  exact hde ((commonPinnedDivisorCondition_pair_iff hsmall hQ hRQ h hinj hshift j d e P).mp
    hcond.2).1

theorem commonPinnedPairPrimeCount_eq_progression {m W M R Q A B v D c : ℕ}
    (h : Fin (m + 1) → ℕ) (j : Fin (m + 1))
    (d e : commonPrimeUniverse M R → Option (Fin m))
    (hclass : ∀ P : ℕ, (P ≡ v [MOD W] ∧
      commonPinnedDivisorCondition m Q (fun q => q.val) h j d P ∧
        commonPinnedDivisorCondition m Q (fun q => q.val) h j e P) ↔ P ≡ c [MOD D]) :
    commonPinnedPairPrimeCount m W Q A B v (fun q => q.val) h j d e =
      primeVariableProgressionCount (A + 1) (B + 1) D c := by
  classical
  unfold commonPinnedPairPrimeCount commonPinnedPrimeSet primeVariableProgressionCount
  apply congrArg Finset.card
  ext P
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hinterval, hprime⟩, hcond⟩
    exact ⟨⟨by omega, by omega⟩, hprime, (hclass P).mp hcond⟩
  · rintro ⟨hinterval, hprime, hcond⟩
    exact ⟨⟨⟨by omega, by omega⟩, hprime⟩, (hclass P).mpr hcond⟩

theorem exists_commonPinnedPairPrimeCount_eq_reduced {m W M R Q A B v : ℕ}
    (hW : 0 < W) (hv : v.Coprime W) (hWM : W ∣ M)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M)
    (hQ : Q.Prime) (hRQ : R < Q) (h : Fin (m + 1) → ℕ)
    (hinj : Function.Injective h) (hshift : ∀ i, h i < 2 * (m + 1) ^ 2)
    (j : Fin (m + 1)) (d e : commonPrimeUniverse M R → Option (Fin m))
    (hde : AssignmentCompatible d e) :
    ∃ c : ℕ, c < W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e) ∧
      c.Coprime (W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e)) ∧
      commonPinnedPairPrimeCount m W Q A B v (fun q => q.val) h j d e =
        primeVariableProgressionCount (A + 1) (B + 1)
          (W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e)) c := by
  obtain ⟨c, hc, hcop, hclass⟩ := exists_commonPinnedAssignment_reduced_class hW hv hWM
    hsmall hQ hRQ h hinj hshift j (mergeAssignment d e)
  refine ⟨c, hc, hcop, commonPinnedPairPrimeCount_eq_progression h j d e ?_⟩
  intro P
  rw [commonPinnedDivisorCondition_pair_iff hsmall hQ hRQ h hinj hshift j d e P,
    and_iff_right hde]
  exact hclass P

theorem cast_commonPinnedPrimeSet_card {A B : ℕ} (hAB : A ≤ B) :
    ((commonPinnedPrimeSet A B).card : ℝ) = (primeCountTotal B : ℝ) - primeCountTotal A := by
  have hint : Finset.Ioc A B = Finset.Ico (A + 1) (B + 1) := by
    ext P
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  unfold commonPinnedPrimeSet primeCountTotal Nat.primeCounting Nat.primeCounting'
  rw [hint, Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range,
    Finset.natCast_card_filter, Finset.natCast_card_filter, Finset.natCast_card_filter]
  exact Finset.sum_Ico_eq_sub _ (by omega)

theorem commonPinnedPairPrimeCount_error {m W M R Q A B v : ℕ}
    (hW : 0 < W) (hv : v.Coprime W) (hWM : W ∣ M) (hAB : A ≤ B)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M)
    (hQ : Q.Prime) (hRQ : R < Q) (h : Fin (m + 1) → ℕ)
    (hinj : Function.Injective h) (hshift : ∀ i, h i < 2 * (m + 1) ^ 2)
    (j : Fin (m + 1)) (d e : commonPrimeUniverse M R → Option (Fin m)) :
    |(commonPinnedPairPrimeCount m W Q A B v (fun q => q.val) h j d e : ℝ) -
        ((commonPinnedPrimeSet A B).card : ℝ) / W.totient *
          assignmentCrtKernel (fun q : commonPrimeUniverse M R => (q.val : ℝ) - 1) d e| ≤
      maxProgressionDiscrepancy B
        (W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e)) +
      maxProgressionDiscrepancy A
        (W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e)) := by
  classical
  rw [pinnedAssignmentCrtKernel_eq_totient commonPrimeUniverse_prime Subtype.val_injective]
  by_cases hde : AssignmentCompatible d e
  · rw [if_pos hde]
    obtain ⟨c, hc, hcop, hcount⟩ := exists_commonPinnedPairPrimeCount_eq_reduced hW hv hWM
      hsmall hQ hRQ h hinj hshift j d e hde
    have hprodCop := assignmentPrimeProduct_coprime commonPrimeUniverse_prime
      (fun q hdiv => commonPrimeUniverse_not_dvd q (hdiv.trans hWM)) (mergeAssignment d e)
    have hphi : W.totient * (assignmentPrimeProduct (fun q => q.val)
        (mergeAssignment d e)).totient =
        (W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e)).totient :=
      (Nat.totient_mul hprodCop.symm).symm
    rw [div_mul_div_comm, mul_one, ← Nat.cast_mul, hphi, hcount, cast_commonPinnedPrimeSet_card hAB]
    have hmod : 0 < W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e) :=
      Nat.mul_pos hW (assignmentPrimeProduct_pos (fun q => (commonPrimeUniverse_prime q).pos) _)
    have hcres : c ∈ coprimeResidues
        (W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc, hcop⟩
    have herror := primeVariableProgressionCount_intervalDiscrepancy_le_global_sum
      (q := W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e))
      (r := c) (show 0 < A + 1 by omega) (show A + 1 ≤ B + 1 by omega)
    simp only [Nat.add_sub_cancel] at herror
    exact herror.trans (add_le_add (progressionDiscrepancy_le_max hmod hcres)
      (progressionDiscrepancy_le_max hmod hcres))
  · rw [if_neg hde, mul_zero, commonPinnedPairPrimeCount_zero_of_incompatible
      hsmall hQ hRQ h hinj hshift j d e hde, Nat.cast_zero, sub_zero, abs_zero]
    exact add_nonneg (maxProgressionDiscrepancy_nonneg _ _) (maxProgressionDiscrepancy_nonneg _ _)

open scoped Classical in
theorem commonPinnedPairPrimeCount_compatible_error {m W M R Q A B v : ℕ}
    (hW : 0 < W) (hv : v.Coprime W) (hWM : W ∣ M) (hAB : A ≤ B)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M)
    (hQ : Q.Prime) (hRQ : R < Q) (h : Fin (m + 1) → ℕ)
    (hinj : Function.Injective h) (hshift : ∀ i, h i < 2 * (m + 1) ^ 2)
    (j : Fin (m + 1)) (d e : commonPrimeUniverse M R → Option (Fin m)) :
    |(commonPinnedPairPrimeCount m W Q A B v (fun q => q.val) h j d e : ℝ) -
        ((commonPinnedPrimeSet A B).card : ℝ) / W.totient *
          assignmentCrtKernel (fun q : commonPrimeUniverse M R => (q.val : ℝ) - 1) d e| ≤
      if AssignmentCompatible d e then
        maxProgressionDiscrepancy B
          (W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e)) +
        maxProgressionDiscrepancy A
          (W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e))
      else 0 := by
  classical
  by_cases hde : AssignmentCompatible d e
  · rw [if_pos hde]
    exact commonPinnedPairPrimeCount_error hW hv hWM hAB hsmall hQ hRQ h hinj hshift j d e
  · rw [if_neg hde, commonPinnedPairPrimeCount_zero_of_incompatible
      hsmall hQ hRQ h hinj hshift j d e hde,
      pinnedAssignmentCrtKernel_eq_totient commonPrimeUniverse_prime Subtype.val_injective,
      if_neg hde]
    simp

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonPinnedPairPrimeCount_eq_reduced
#print axioms Erdos4b.FGKMT.commonPinnedPairPrimeCount_error
#print axioms Erdos4b.FGKMT.commonPinnedPairPrimeCount_compatible_error
