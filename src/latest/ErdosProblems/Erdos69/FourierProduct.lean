import ErdosProblems.Erdos69.FourierDeficit

/-! # Decay of the independent prime characteristic function -/

open scoped BigOperators

namespace Erdos69.Elementary

theorem fourierPhase_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    fourierPhase (∑ i ∈ s, f i) = ∏ i ∈ s, fourierPhase (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fourierPhase_zero]
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, fourierPhase_add, ih]

namespace FiniteLaw

variable {ρ ι Ω : Type*} [Fintype ρ] [Fintype ι] [Fintype Ω] [DecidableEq ρ]

theorem independentProduct_fourier_sum (μ : ρ → FiniteLaw Ω) (X : ρ → Ω → ℝ) :
    (independentProduct μ).complexMean (fun x ↦ fourierPhase (∑ j, X j (x j))) =
      ∏ j, (μ j).complexMean (fun x ↦ fourierPhase (X j x)) := by
  simp_rw [fourierPhase_sum]
  exact independentProduct_complexMean_prod μ (fun j x ↦ fourierPhase (X j x))

theorem categorical_product_fourier_le (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (hc : ∀ j, Fintype.card ι ≤ p j) (s : Finset ρ)
    (hs : ∀ j ∈ s, 2 * Fintype.card ι ≤ p j)
    (c : ι → ℝ) (i : ι) (hi : |c i| ≤ 1 / 2) :
    ‖(independentProduct (fun j ↦ categorical ι (p j) (hp j) (hc j))).complexMean
      (fun x ↦ fourierPhase (∑ j, optionalValue c (x j)))‖ ≤
        Real.exp (-4 * c i ^ 2 * ∑ j ∈ s, (1 : ℝ) / p j) := by
  classical
  rw [independentProduct_fourier_sum (fun j ↦ categorical ι (p j) (hp j) (hc j))
    (fun _ ↦ optionalValue c), norm_prod]
  have hlocal (j : ρ) :
      ‖(categorical ι (p j) (hp j) (hc j)).complexMean
          (fun x ↦ fourierPhase (optionalValue c x))‖ ≤
        if j ∈ s then Real.exp (-4 * c i ^ 2 / p j) else 1 := by
    split_ifs with hj
    · exact categorical_fourier_norm_le (p j) (hp j) (hs j hj) c i hi
    · exact norm_mean_fourierPhase_le_one _ _
  calc
    _ ≤ ∏ j, if j ∈ s then Real.exp (-4 * c i ^ 2 / p j) else 1 :=
      Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun j _ ↦ hlocal j)
    _ = ∏ j ∈ s, Real.exp (-4 * c i ^ 2 / p j) := Finset.prod_ite_mem_eq _ _
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

end FiniteLaw

end Erdos69.Elementary
