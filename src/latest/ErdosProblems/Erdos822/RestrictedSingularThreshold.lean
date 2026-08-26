/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.KernelSplit

/-! # A first-moment majorant for a restricted singular product -/

namespace Erdos822

open scoped BigOperators Classical

noncomputable def primeSingularProduct (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (p : ℝ) / ((p : ℝ) - 1)

theorem primeSingularProduct_nonneg {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    0 ≤ primeSingularProduct P := by
  apply Finset.prod_nonneg
  intro p hp
  have hpR : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
  exact div_nonneg (by positivity) (by linarith)

theorem primeSingularProduct_le_exp {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    primeSingularProduct P ≤ Real.exp (2 * ∑ p ∈ P, (1 : ℝ) / p) := by
  calc
    _ ≤ ∏ p ∈ P, Real.exp ((2 : ℝ) / p) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpR : (1 : ℝ) < p := by exact_mod_cast (hP p hp).1.one_lt
        exact div_nonneg (by positivity) (by linarith)
      · intro p hp
        calc
          _ ≤ 1 + (2 : ℝ) / p := singularLocal_le_one_add_two_div (hP p hp).1 (hP p hp).2
          _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp ((2 : ℝ) / p)
    _ = Real.exp (∑ p ∈ P, (2 : ℝ) / p) := (Real.exp_sum ..).symm
    _ = _ := by congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring

theorem primeSingularProduct_le_inverseEuler {P : Finset ℕ} {z y : ℕ}
    (hP : P ⊆ Erdos851.sievePrimes z y) :
    primeSingularProduct P ≤
      Erdos851.inverseLocalEulerProduct Erdos851.oneShiftDensity z y := by
  have hlocal (p : ℕ) (hp : p ∈ Erdos851.sievePrimes z y) :
      (p : ℝ) / ((p : ℝ) - 1) = (1 - Erdos851.oneShiftDensity p)⁻¹ := by
    have hpR : (1 : ℝ) < p := by exact_mod_cast (Erdos851.mem_sievePrimes.mp hp).2.2.one_lt
    unfold Erdos851.oneShiftDensity
    field_simp
  have hone (p : ℕ) (hp : p ∈ Erdos851.sievePrimes z y) :
      (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    have hpR : (1 : ℝ) < p := by exact_mod_cast (Erdos851.mem_sievePrimes.mp hp).2.2.one_lt
    exact (le_div_iff₀ (by linarith)).mpr (by linarith)
  calc
    _ ≤ ∏ p ∈ Erdos851.sievePrimes z y, (p : ℝ) / ((p : ℝ) - 1) := by
      apply Finset.prod_le_prod_of_subset_of_one_le hP
      · intro p hp
        exact (by norm_num : (0 : ℝ) ≤ 1).trans (hone p (hP hp))
      · intro p hp hnot
        exact hone p hp
    _ = _ := Finset.prod_congr rfl hlocal

theorem exists_restrictedSingularProduct_firstMoment_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ (P : Finset ℕ) (z y : ℕ), 2 ≤ z → z ≤ y →
      P ⊆ Erdos851.sievePrimes z y →
      primeSingularProduct P ≤ Real.exp 2 +
        (D * (Real.log (y : ℝ) / Real.log (z : ℝ))) * (∑ p ∈ P, (1 : ℝ) / p) := by
  obtain ⟨D, hD, hbound⟩ := Erdos851.exists_oneShift_dimension_bound
  refine ⟨D, hD, ?_⟩
  intro P z y hz hzy hP
  let f := ∑ p ∈ P, (1 : ℝ) / p
  have hf : 0 ≤ f := Finset.sum_nonneg fun p hp ↦ by positivity
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hM : 0 ≤ D * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by positivity
  by_cases hf1 : f ≤ 1
  · have h := primeSingularProduct_le_exp (P := P) (fun p hp ↦
      ⟨(Erdos851.mem_sievePrimes.mp (hP hp)).2.2, by have := (Erdos851.mem_sievePrimes.mp (hP hp)).1; omega⟩)
    calc
      _ ≤ Real.exp (2 * f) := h
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith only [hf1])
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hM hf)
  · have h := (primeSingularProduct_le_inverseEuler hP).trans (hbound z y hz hzy)
    calc
      _ ≤ D * (Real.log (y : ℝ) / Real.log (z : ℝ)) := h
      _ ≤ (D * (Real.log (y : ℝ) / Real.log (z : ℝ))) * f :=
        le_mul_of_one_le_right hM (le_of_lt (lt_of_not_ge hf1))
      _ ≤ _ := le_add_of_nonneg_left (Real.exp_pos 2).le

#print axioms exists_restrictedSingularProduct_firstMoment_bound

end Erdos822
