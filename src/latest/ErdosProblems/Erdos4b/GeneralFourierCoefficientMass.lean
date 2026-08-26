/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierEndpointMass
import BoundedGaps.Maynard.MaynardArithmeticBounds

/-!
# A cutoff-independent bound on the coefficient mass

Only divisor tuples with a nonzero coefficient are counted. The
positive product-tuple bound gives a logarithmic loss for each fixed
dimension, rather than a coordinate-box power of the sieve radius.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem mem_positiveProductTuples_of_pos_of_prod_le
    {ι : Type*} [Fintype ι] {R : ℕ} (d : ι → ℕ)
    (hd : ∀ i, 0 < d i) (hprod : ∏ i, d i ≤ R) :
    d ∈ BoundedGaps.Maynard.positiveProductTuples ι R := by
  rw [BoundedGaps.Maynard.mem_positiveProductTuples_iff]
  refine ⟨fun i ↦ Finset.mem_Icc.mpr ⟨hd i, ?_⟩, hprod⟩
  exact (Nat.le_of_dvd (Finset.prod_pos (fun i hi ↦ hd i))
    (Finset.dvd_prod_of_mem d (Finset.mem_univ i))).trans hprod

theorem doubledSelbergCoefficientMass_le_product_radii
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) (RD RE : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (hD : ∀ d ∈ D, ∀ i, 0 < d i) (hE : ∀ e ∈ E, ∀ i, 0 < e i)
    (hbound : ∀ d ∈ D, ∀ e ∈ E, |lambda d e| ≤ C)
    (hsupport : ∀ d ∈ D, ∀ e ∈ E, lambda d e ≠ 0 →
      (∏ i, d i) ≤ RD ∧ (∏ i, e i) ≤ RE) :
    doubledSelbergCoefficientMass H D E lambda ≤
      C * ((RD : ℝ) * (1 + Real.log RD) ^ Fintype.card H) *
        ((RE : ℝ) * (1 + Real.log RE) ^ Fintype.card H) := by
  classical
  let S := (D ×ˢ E).filter (fun de ↦ lambda de.1 de.2 ≠ 0)
  have hmass : doubledSelbergCoefficientMass H D E lambda =
      ∑ de ∈ S, |lambda de.1 de.2| := by
    rw [doubledSelbergCoefficientMass, ← Finset.sum_product D E
      (fun de : (H → ℕ) × (H → ℕ) ↦ |lambda de.1 de.2|)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro de hde hnot
    have hz : lambda de.1 de.2 = 0 := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨hde, hn⟩)
    simp only [hz, abs_zero]
  have hsub : S ⊆ (BoundedGaps.Maynard.positiveProductTuples H RD) ×ˢ
      (BoundedGaps.Maynard.positiveProductTuples H RE) := by
    intro de hde
    obtain ⟨hde, hne⟩ := Finset.mem_filter.mp hde
    obtain ⟨hd, he⟩ := Finset.mem_product.mp hde
    have hprod := hsupport de.1 hd de.2 he hne
    exact Finset.mem_product.mpr
      ⟨mem_positiveProductTuples_of_pos_of_prod_le de.1 (hD de.1 hd) hprod.1,
        mem_positiveProductTuples_of_pos_of_prod_le de.2 (hE de.2 he) hprod.2⟩
  have hcard : (S.card : ℝ) ≤
      ((BoundedGaps.Maynard.positiveProductTuples H RD).card : ℝ) *
        (BoundedGaps.Maynard.positiveProductTuples H RE).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product _ _)
  calc
    _ ≤ (S.card : ℝ) * C := by
      rw [hmass]
      calc
        _ ≤ ∑ _de ∈ S, C := by
          apply Finset.sum_le_sum
          intro de hde
          have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hde).1
          exact hbound de.1 hmem.1 de.2 hmem.2
        _ = _ := by simp
    _ ≤ (((BoundedGaps.Maynard.positiveProductTuples H RD).card : ℝ) *
        (BoundedGaps.Maynard.positiveProductTuples H RE).card) * C :=
      mul_le_mul_of_nonneg_right hcard hC
    _ ≤ ((RD : ℝ) * (1 + Real.log RD) ^ Fintype.card H) *
        ((RE : ℝ) * (1 + Real.log RE) ^ Fintype.card H) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      apply mul_le_mul
        (BoundedGaps.Maynard.card_positiveProductTuples_le_one_add_log H RD)
        (BoundedGaps.Maynard.card_positiveProductTuples_le_one_add_log H RE)
        (Nat.cast_nonneg _)
      exact (Nat.cast_nonneg _).trans
        (BoundedGaps.Maynard.card_positiveProductTuples_le_one_add_log H RD)
    _ = _ := by ring

end

end Erdos4b
