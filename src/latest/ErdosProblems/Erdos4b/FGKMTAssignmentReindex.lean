/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeUniverse
import ErdosProblems.Erdos4b.FGKMTRoughSupport

/-!
# Exact reindexing of the arithmetic diagonal

The full natural box and the prime-assignment space are in bijection on
nonzero summands. Rough weights enforce squarefreeness and coprimality;
the profile support enforces the product radius. No endpoint is dropped.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def weightedTupleTerm (k M : ℕ) (g : ℕ → ℝ) (F : (Fin k → ℕ) → ℝ)
    (r : Fin k → ℕ) : ℝ := F r * roughSieveWeight M g (∏ i, r i)

theorem weightedTupleTerm_support {k M R : ℕ} {g : ℕ → ℝ} {F : (Fin k → ℕ) → ℝ}
    (hF : ∀ r, (∀ i, 0 < r i) → R ≤ (∏ i, r i) → F r = 0)
    {r : Fin k → ℕ} (hr : weightedTupleTerm k M g F r ≠ 0) :
    Squarefree (∏ i, r i) ∧ M.Coprime (∏ i, r i) ∧ (∏ i, r i) < R := by
  have hnon := mul_ne_zero_iff.mp hr
  have hsup := roughSieveWeight_support hnon.2
  refine ⟨hsup.1, hsup.2, ?_⟩
  by_contra hR
  apply hnon.1
  apply hF r _ (by omega)
  intro i
  exact Nat.pos_of_ne_zero (hsup.1.squarefree_of_dvd
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))).ne_zero

theorem recover_weightedTupleTerm {k M R : ℕ} {g : ℕ → ℝ} {F : (Fin k → ℕ) → ℝ}
    (hF : ∀ r, (∀ i, 0 < r i) → R ≤ (∏ i, r i) → F r = 0)
    {r : Fin k → ℕ} (hr : weightedTupleTerm k M g F r ≠ 0) :
    assignmentPrimeTuple (fun q : commonPrimeUniverse M R => q.val)
      (assignmentOfTuple (fun q : commonPrimeUniverse M R => q.val) r) = r := by
  have hs := weightedTupleTerm_support hF hr
  have hc := commonPrimeUniverse_covers_tuple hs.1 hs.2.1.symm hs.2.2.le
  exact assignmentPrimeTuple_assignmentOfTuple commonPrimeUniverse_prime Subtype.val_injective
    hc.1 hc.2

theorem sum_assignments_eq_sum_box (k M R : ℕ) (g : ℕ → ℝ) (F : (Fin k → ℕ) → ℝ)
    (hF : ∀ r, (∀ i, 0 < r i) → R ≤ (∏ i, r i) → F r = 0) :
    (∑ r : commonPrimeUniverse M R → Option (Fin k),
      F (assignmentPrimeTuple (fun q => q.val) r) *
        roughSieveWeight M g (assignmentPrimeProduct (fun q => q.val) r)) =
      ∑ e : Fin k → Fin (R + 1), F (fun i => (e i).val) *
        roughSieveWeight M g (∏ i, (e i).val) := by
  classical
  let p := fun q : commonPrimeUniverse M R => q.val
  let f := fun e : Fin k → Fin (R + 1) => weightedTupleTerm k M g F (fun i => (e i).val)
  let G := fun r : commonPrimeUniverse M R → Option (Fin k) =>
    F (assignmentPrimeTuple p r) * roughSieveWeight M g (assignmentPrimeProduct p r)
  have hG (r : commonPrimeUniverse M R → Option (Fin k)) :
      G r = weightedTupleTerm k M g F (assignmentPrimeTuple p r) := by
    dsimp only [G, weightedTupleTerm]
    rw [prod_assignmentPrimeTuple]
  have heq (e : Fin k → Fin (R + 1)) (he : f e ≠ 0) :
      assignmentPrimeTuple p (assignmentOfTuple p (fun i => (e i).val)) =
        (fun i => (e i).val) := recover_weightedTupleTerm hF he
  have hval (e : Fin k → Fin (R + 1)) (he : f e ≠ 0) :
      f e = G (assignmentOfTuple p (fun i => (e i).val)) := by
    rw [hG, heq e he]
  suffices hsum : (∑ e, f e) = ∑ r, G r by exact hsum.symm
  apply Finset.sum_bij_ne_zero
    (fun e _he _hzero => assignmentOfTuple p (fun i => (e i).val))
  · intro e _he _hzero
    exact Finset.mem_univ _
  · intro e₁ _he₁ hn₁ e₂ _he₂ hn₂ hmap
    have htuple : (fun i => (e₁ i).val) = (fun i => (e₂ i).val) := by
      rw [← heq e₁ hn₁, hmap, heq e₂ hn₂]
    funext i
    exact Fin.ext (congrFun htuple i)
  · intro r _hr hGr
    have hrnon : weightedTupleTerm k M g F (assignmentPrimeTuple p r) ≠ 0 := by
      rwa [← hG]
    have hs := weightedTupleTerm_support hF hrnon
    have hcoord (i : Fin k) : assignmentPrimeTuple p r i < R + 1 := by
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hs.1.ne_zero)
        (Finset.dvd_prod_of_mem (assignmentPrimeTuple p r) (Finset.mem_univ i))
      exact lt_of_le_of_lt hle (lt_trans hs.2.2 (Nat.lt_succ_self R))
    let e : Fin k → Fin (R + 1) := fun i => ⟨assignmentPrimeTuple p r i, hcoord i⟩
    have he : f e = G r := (hG r).symm
    have henon : f e ≠ 0 := he.symm ▸ hGr
    refine ⟨e, Finset.mem_univ e, henon, ?_⟩
    apply assignmentPrimeTuple_injective commonPrimeUniverse_prime Subtype.val_injective
    exact heq e henon
  · intro e _he hn
    exact hval e hn

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.recover_weightedTupleTerm
#print axioms Erdos4b.FGKMT.sum_assignments_eq_sum_box
