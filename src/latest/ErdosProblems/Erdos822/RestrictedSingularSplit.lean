/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.RestrictedSingularThreshold
import ErdosProblems.Erdos822.PrimeMassArithmetic

/-! # Separating controlled prime factors from the determinant charge -/

namespace Erdos822

open scoped BigOperators Classical

theorem primeSingularProduct_filter_mul_compl (P : Finset ℕ) (Q : ℕ → Prop) :
    primeSingularProduct P = primeSingularProduct (P.filter Q) *
      primeSingularProduct (P.filter (fun p ↦ ¬ Q p)) := by
  unfold primeSingularProduct
  simp only [Finset.prod_filter]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases hQ : Q p <;> simp [hQ]

theorem singularFactor_eq_primeSingularProduct (H z y : ℕ) :
    Erdos851.singularFactor H z y =
      primeSingularProduct ((Erdos851.sievePrimes z y).filter (fun p ↦ p ∣ H)) := by
  simp only [Erdos851.singularFactor, primeSingularProduct, Finset.prod_filter]

theorem sum_inv_primeFilter_dvd_le_full {P : Finset ℕ} {a : ℕ}
    (ha : a ≠ 0) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P.filter (fun p ↦ p ∣ a), (1 : ℝ) / p) ≤ primeDivisorReciprocalMass a := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp, hpa⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hP p hp, hpa, ha⟩
  · intro p hp hnot
    positivity

theorem sum_inv_primeFilter_dvd_le_tail {P : Finset ℕ} {a z : ℕ}
    (ha : a ≠ 0) (hP : ∀ p ∈ P, p.Prime ∧ z < p) :
    (∑ p ∈ P.filter (fun p ↦ p ∣ a), (1 : ℝ) / p) ≤
      ∑ p ∈ primeFactorsAbove a z, (1 : ℝ) / p := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp, hpa⟩ := Finset.mem_filter.mp hp
    exact mem_primeFactorsAbove_iff.mpr ⟨Nat.mem_primeFactors.mpr ⟨(hP p hp).1, hpa, ha⟩, (hP p hp).2⟩
  · intro p hp hnot
    positivity

theorem sum_inv_primeFilter_bad_le {P : Finset ℕ} {a b z : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hP : ∀ p ∈ P, p.Prime ∧ z < p) :
    (∑ p ∈ P.filter (fun p ↦ p ∣ a ∨ p ∣ b), (1 : ℝ) / p) ≤
      (∑ p ∈ primeFactorsAbove a z, (1 : ℝ) / p) + primeDivisorReciprocalMass b := by
  have hsplit : (∑ p ∈ P.filter (fun p ↦ p ∣ a ∨ p ∣ b), (1 : ℝ) / p) ≤
      (∑ p ∈ P.filter (fun p ↦ p ∣ a), (1 : ℝ) / p) +
      ∑ p ∈ P.filter (fun p ↦ p ∣ b), (1 : ℝ) / p := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    by_cases hpa : p ∣ a <;> by_cases hpb : p ∣ b <;> simp [hpa, hpb]
  exact hsplit.trans (add_le_add (sum_inv_primeFilter_dvd_le_tail ha hP)
    (sum_inv_primeFilter_dvd_le_full hb (fun p hp ↦ (hP p hp).1)))

theorem primeSingularProduct_le_controlled_mul_good {P : Finset ℕ} {a b z : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hz : 2 ≤ z)
    (hP : ∀ p ∈ P, p.Prime ∧ z < p) :
    primeSingularProduct P ≤
      Real.exp (2 * ((∑ p ∈ primeFactorsAbove a z, (1 : ℝ) / p) + primeDivisorReciprocalMass b)) *
        primeSingularProduct (P.filter (fun p ↦ ¬ p ∣ a ∧ ¬ p ∣ b)) := by
  have hbad := primeSingularProduct_le_exp
    (P := P.filter (fun p ↦ p ∣ a ∨ p ∣ b)) (fun p hp ↦ by
      have hp' := hP p (Finset.mem_filter.mp hp).1
      exact ⟨hp'.1, by omega⟩)
  have hmass := sum_inv_primeFilter_bad_le ha hb hP
  have hbad' := hbad.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmass (by norm_num)))
  rw [primeSingularProduct_filter_mul_compl P (fun p ↦ p ∣ a ∨ p ∣ b)]
  simp only [not_or]
  have hgood0 : 0 ≤ primeSingularProduct (P.filter (fun p ↦ ¬ p ∣ a ∧ ¬ p ∣ b)) :=
    primeSingularProduct_nonneg (fun p hp ↦ (hP p (Finset.mem_filter.mp hp).1).1)
  convert mul_le_mul_of_nonneg_right hbad' hgood0 using 1 <;> congr 1
  apply congrArg primeSingularProduct
  ext p
  simp

#print axioms primeSingularProduct_le_controlled_mul_good

end Erdos822
