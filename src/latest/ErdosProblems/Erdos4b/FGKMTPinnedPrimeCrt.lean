/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedPrimeRoots
import ErdosProblems.Erdos4b.FGKMTAssignmentReducedCrt
import ErdosProblems.Erdos4b.FGKMTInverseArithmetic
import ErdosProblems.Erdos4b.FGKMTCommonPinnedSupport

/-!
# The actual pinned divisor conditions form a reduced prime progression

The modulus is the presieve modulus times the selected prime product.
The associated finite CRT kernel is exactly its totient reciprocal.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem commonPinnedAssignment_divisor_iff_roots {α : Type*} [Fintype α]
    {m Q : ℕ} {p : α → ℕ} (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (h : Fin (m + 1) → ℕ) (hhinj : Function.Injective h)
    (hsmall : ∀ q i, h i < p q) (j : Fin (m + 1))
    (r : α → Option (Fin m)) (P : ℕ) :
    (∀ i, (assignmentPrimeTuple p r i : ℤ) ∣
      (Q : ℤ) - (h j : ℤ) * P + (h (j.succAbove i) : ℤ) * P) ↔
      ∀ q i, r q = some i → (P : ZMod (p q)) = commonPinnedRoot h j Q (p q) i := by
  rw [assignmentDivisorCondition_iff_local hp hinj]
  apply forall_congr'
  intro q
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro _hr
  simpa only [Int.cast_natCast] using
    (commonPinnedRoot_iff_int_dvd (hp q) h hhinj (hsmall q) j i (P : ℤ)).symm

theorem commonPinnedDivisorPair_iff_merged {α : Type*} [Fintype α]
    {m Q : ℕ} {p : α → ℕ} (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (hQ : ∀ q, ¬p q ∣ Q) (h : Fin (m + 1) → ℕ) (hhinj : Function.Injective h)
    (hsmall : ∀ q i, h i < p q) (j : Fin (m + 1))
    (d e : α → Option (Fin m)) (P : ℕ) :
    ((∀ i, (assignmentPrimeTuple p d i : ℤ) ∣
        (Q : ℤ) - (h j : ℤ) * P + (h (j.succAbove i) : ℤ) * P) ∧
      (∀ i, (assignmentPrimeTuple p e i : ℤ) ∣
        (Q : ℤ) - (h j : ℤ) * P + (h (j.succAbove i) : ℤ) * P)) ↔
      AssignmentCompatible d e ∧
        ∀ i, (assignmentPrimeTuple p (mergeAssignment d e) i : ℤ) ∣
          (Q : ℤ) - (h j : ℤ) * P + (h (j.succAbove i) : ℤ) * P := by
  simp only [commonPinnedAssignment_divisor_iff_roots hp hinj h hhinj hsmall j]
  exact assignmentRootPair_iff_merged (fun q => commonPinnedRoot h j Q (p q))
    (fun q => commonPinnedRoot_injective (hp q) (hQ q) h hhinj (hsmall q) j) d e P

theorem exists_commonPinnedAssignment_reduced_class {m W M R Q v : ℕ}
    (hW : 0 < W) (hv : v.Coprime W) (hWM : W ∣ M)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M)
    (hQ : Q.Prime) (hRQ : R < Q) (h : Fin (m + 1) → ℕ)
    (hinj : Function.Injective h) (hshift : ∀ i, h i < 2 * (m + 1) ^ 2)
    (j : Fin (m + 1)) (r : commonPrimeUniverse M R → Option (Fin m)) :
    ∃ c : ℕ, c < W * assignmentPrimeProduct (fun q => q.val) r ∧
      c.Coprime (W * assignmentPrimeProduct (fun q => q.val) r) ∧ ∀ P : ℕ,
      (P ≡ v [MOD W] ∧ ∀ i,
        (assignmentPrimeTuple (fun q => q.val) r i : ℤ) ∣
          (Q : ℤ) - (h j : ℤ) * P + (h (j.succAbove i) : ℤ) * P) ↔
        P ≡ c [MOD W * assignmentPrimeProduct (fun q => q.val) r] := by
  have hp (q : commonPrimeUniverse M R) := commonPrimeUniverse_prime q
  have hcop (q : commonPrimeUniverse M R) : q.val.Coprime W :=
    ((hp q).coprime_iff_not_dvd).mpr (fun hd => commonPrimeUniverse_not_dvd q (hd.trans hWM))
  have hnot (q : commonPrimeUniverse M R) : ¬q.val ∣ Q := by
    intro hd
    rcases (Nat.dvd_prime hQ).mp hd with he | he
    · exact (hp q).ne_one he
    · have hqR := (mem_commonPrimeUniverse.mp q.property).2.1
      omega
  have hbound (q : commonPrimeUniverse M R) (i : Fin (m + 1)) : h i < q.val :=
    (hshift i).trans (commonPrimeUniverse_large hsmall q)
  obtain ⟨c, hc, hcunit, hclass⟩ := exists_assignment_reduced_class hW hv hp
    Subtype.val_injective hcop (fun q => commonPinnedRoot h j Q q.val)
    (fun q i => commonPinnedRoot_ne_zero (hp q) (hnot q) h hinj (hbound q) j i) r
  refine ⟨c, hc, hcunit, ?_⟩
  intro P
  have hlocal : (∀ i, (assignmentPrimeTuple (fun q => q.val) r i : ℤ) ∣
        (Q : ℤ) - (h j : ℤ) * P + (h (j.succAbove i) : ℤ) * P) ↔
      ∀ q i, r q = some i → (P : ZMod q.val) = commonPinnedRoot h j Q q.val i := by
    exact commonPinnedAssignment_divisor_iff_roots hp Subtype.val_injective h hinj hbound j r P
  rw [hlocal]
  exact hclass P

open scoped Classical in
theorem pinnedAssignmentCrtKernel_eq_totient {α ι : Type*} [Fintype α] [DecidableEq ι]
    {p : α → ℕ} (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (d e : α → Option ι) :
    assignmentCrtKernel (fun q => (p q : ℝ) - 1) d e =
      if AssignmentCompatible d e then
        1 / ((assignmentPrimeProduct p (mergeAssignment d e)).totient : ℝ) else 0 := by
  classical
  by_cases hc : AssignmentCompatible d e
  · rw [if_pos hc, assignmentPrimeProduct_totient hp hinj,
      one_div, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro q _hq
    cases hd : d q with
    | none => cases he : e q <;> simp [localCrtDensity, mergeAssignment, hd, he]
    | some i =>
        cases he : e q with
        | none => simp [localCrtDensity, mergeAssignment, hd]
        | some l => simp [localCrtDensity, mergeAssignment, hd, hc q i l hd he]
  · rw [if_neg hc]
    unfold AssignmentCompatible at hc
    push Not at hc
    obtain ⟨q, i, l, hd, he, hil⟩ := hc
    exact Finset.prod_eq_zero (Finset.mem_univ q)
      (by simp only [hd, he, localCrtDensity, if_neg hil])

theorem assignmentPrimeProduct_merge_le {α ι : Type*} [Fintype α]
    (p : α → ℕ) (d e : α → Option ι) :
    assignmentPrimeProduct p (mergeAssignment d e) ≤
      assignmentPrimeProduct p d * assignmentPrimeProduct p e := by
  classical
  unfold assignmentPrimeProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro q _hq
  cases hd : d q with
  | none => cases he : e q <;> simp [mergeAssignment, hd, he]
  | some i =>
      cases he : e q with
      | none => simp [mergeAssignment, hd]
      | some l => simpa [mergeAssignment, hd, he] using Nat.le_mul_self (p q)

theorem commonPinnedPair_period_le {α : Type*} [DecidableEq α] [Fintype α]
    {m R W : ℕ} {p : α → ℕ} (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (hR : 1 < R) (j : Fin (m + 1)) (d e : α → Option (Fin m))
    (hd : commonPinnedCoefficient m R p j d ≠ 0)
    (he : commonPinnedCoefficient m R p j e ≠ 0) :
    W * assignmentPrimeProduct p (mergeAssignment d e) ≤ W * R ^ 2 := by
  have hdR : assignmentPrimeProduct p d < R := by
    by_contra hh
    exact hd (commonPinnedCoefficient_zero_of_product_ge hp hinj hR j d (by omega))
  have heR : assignmentPrimeProduct p e < R := by
    by_contra hh
    exact he (commonPinnedCoefficient_zero_of_product_ge hp hinj hR j e (by omega))
  apply Nat.mul_le_mul_left
  exact (assignmentPrimeProduct_merge_le p d e).trans (by nlinarith)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonPinnedAssignment_reduced_class
#print axioms Erdos4b.FGKMT.pinnedAssignmentCrtKernel_eq_totient
#print axioms Erdos4b.FGKMT.commonPinnedDivisorPair_iff_merged
#print axioms Erdos4b.FGKMT.commonPinnedPair_period_le
