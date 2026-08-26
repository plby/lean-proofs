/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedCoefficientExtension
import ErdosProblems.Erdos4b.GeneralFourierQuadruple

/-!
# Removing a pinned coordinate from the finite divisor box

Extension by one is a bijection onto the full tuples whose pinned
coordinate is one. The sum identity only discards zero summands.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem extendPinnedDivisorTuple_restrict {K : ℕ} (h : Fin K)
    (d : Fin K → ℕ) (hd : d h = 1) :
    extendPinnedDivisorTuple h (fun i : PinnedShiftIndex h ↦ d i.val) = d := by
  funext i
  by_cases hi : i = h
  · subst i
    simp [hd]
  · simp [extendPinnedDivisorTuple, hi]

theorem extendPinnedDivisorTuple_mem_cutoff {K : ℕ} (h : Fin K)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (d : PinnedShiftIndex h → ℕ)
    (hd : d ∈ cutoffDivisorTupleSupport (PinnedShiftIndex h) P) :
    extendPinnedDivisorTuple h d ∈ cutoffDivisorTupleSupport (Fin K) P := by
  rw [mem_cutoffDivisorTupleSupport P hP] at hd ⊢
  intro i
  by_cases hi : i = h
  · subst i
    simp
  · simpa only [extendPinnedDivisorTuple, dif_neg hi] using hd ⟨i, hi⟩

theorem restrictPinnedDivisorTuple_mem_cutoff {K : ℕ} (h : Fin K)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (d : Fin K → ℕ)
    (hd : d ∈ cutoffDivisorTupleSupport (Fin K) P) :
    (fun i : PinnedShiftIndex h ↦ d i.val) ∈
      cutoffDivisorTupleSupport (PinnedShiftIndex h) P := by
  rw [mem_cutoffDivisorTupleSupport P hP] at hd ⊢
  exact fun i ↦ hd i.val

theorem sum_cutoffDivisorPairs_eq_pinned
    {K : ℕ} {M : Type*} [AddCommMonoid M] (h : Fin K)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : (Fin K → ℕ) → (Fin K → ℕ) → M)
    (hpin : ∀ d ∈ cutoffDivisorTupleSupport (Fin K) P,
      ∀ e ∈ cutoffDivisorTupleSupport (Fin K) P, f d e ≠ 0 → d h = 1 ∧ e h = 1) :
    (∑ d ∈ cutoffDivisorTupleSupport (Fin K) P,
      ∑ e ∈ cutoffDivisorTupleSupport (Fin K) P, f d e) =
      ∑ d ∈ cutoffDivisorTupleSupport (PinnedShiftIndex h) P,
      ∑ e ∈ cutoffDivisorTupleSupport (PinnedShiftIndex h) P,
        f (extendPinnedDivisorTuple h d) (extendPinnedDivisorTuple h e) := by
  classical
  rw [← Finset.sum_product (f := fun de ↦ f de.1 de.2),
    ← Finset.sum_product (f := fun de ↦
      f (extendPinnedDivisorTuple h de.1) (extendPinnedDivisorTuple h de.2))]
  apply Finset.sum_bij_ne_zero (fun de _ _ ↦
    (fun i : PinnedShiftIndex h ↦ de.1 i.val, fun i : PinnedShiftIndex h ↦ de.2 i.val))
  · intro de hde hne
    exact Finset.mem_product.mpr
      ⟨restrictPinnedDivisorTuple_mem_cutoff h P hP de.1 (Finset.mem_product.mp hde).1,
        restrictPinnedDivisorTuple_mem_cutoff h P hP de.2 (Finset.mem_product.mp hde).2⟩
  · intro de hde hne de' hde' hne' heq
    have hp := hpin de.1 (Finset.mem_product.mp hde).1 de.2
      (Finset.mem_product.mp hde).2 hne
    have hp' := hpin de'.1 (Finset.mem_product.mp hde').1 de'.2
      (Finset.mem_product.mp hde').2 hne'
    apply Prod.ext
    · have he := congrArg (fun x ↦ extendPinnedDivisorTuple h x.1) heq
      simpa only [extendPinnedDivisorTuple_restrict h _ hp.1,
        extendPinnedDivisorTuple_restrict h _ hp'.1] using he
    · have he := congrArg (fun x ↦ extendPinnedDivisorTuple h x.2) heq
      simpa only [extendPinnedDivisorTuple_restrict h _ hp.2,
        extendPinnedDivisorTuple_restrict h _ hp'.2] using he
  · intro de hde hne
    refine ⟨(extendPinnedDivisorTuple h de.1, extendPinnedDivisorTuple h de.2),
      Finset.mem_product.mpr
        ⟨extendPinnedDivisorTuple_mem_cutoff h P hP de.1 (Finset.mem_product.mp hde).1,
          extendPinnedDivisorTuple_mem_cutoff h P hP de.2 (Finset.mem_product.mp hde).2⟩,
      hne, ?_⟩
    simp only [extendPinnedDivisorTuple_at_other]
  · intro de hde hne
    have hp := hpin de.1 (Finset.mem_product.mp hde).1 de.2
      (Finset.mem_product.mp hde).2 hne
    rw [extendPinnedDivisorTuple_restrict h _ hp.1,
      extendPinnedDivisorTuple_restrict h _ hp.2]

end

end Erdos4b
