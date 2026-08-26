import ErdosProblems.Erdos69.FiniteMoments

/-! # Repeated coordinates in categorical moment comparisons -/

open scoped BigOperators

namespace Erdos69.Elementary.FiniteLaw

variable {Ω ρ ι : Type*} [Fintype Ω] [Fintype ρ] [Fintype ι]
  [DecidableEq ρ] [DecidableEq ι]

theorem mean_point_indicator [DecidableEq Ω] (μ : FiniteLaw Ω) (a : Ω) :
    μ.mean (fun x ↦ if x = a then (1 : ℝ) else 0) = μ.mass a := by
  classical
  simp [mean]

theorem categorical_mass_of_ne_none (p : ℕ) (hp : 0 < p)
    (hc : Fintype.card ι ≤ p) (a : Option ι) (ha : a ≠ none) :
    (categorical ι p hp hc).mass a = (1 : ℝ) / p := by
  cases a with
  | none => exact (ha rfl).elim
  | some i => rfl

theorem independentProduct_mean_partial_assignment (μ : ρ → FiniteLaw (Option ι))
    (s : Finset ρ) (a : ρ → Option ι) :
    (independentProduct μ).mean (fun x ↦
      if ∀ p ∈ s, x p = a p then (1 : ℝ) else 0) = ∏ p ∈ s, (μ p).mass (a p) := by
  have heq (x : ρ → Option ι) :
      (if ∀ p ∈ s, x p = a p then (1 : ℝ) else 0) =
        ∏ p, (if p ∈ s then (if x p = a p then (1 : ℝ) else 0) else 1) := by
    rw [Finset.prod_ite_mem_eq, Finset.prod_boole]
    split_ifs <;> rfl
  simp_rw [heq]
  rw [independentProduct_mean_prod μ
    (fun p x ↦ if p ∈ s then (if x = a p then (1 : ℝ) else 0) else 1)]
  have hmean (p : ρ) :
      (μ p).mean (fun x ↦ if p ∈ s then (if x = a p then (1 : ℝ) else 0) else 1) =
        if p ∈ s then (μ p).mass (a p) else 1 := by
    split_ifs <;> simp [mean_point_indicator]
  simp_rw [hmean]
  exact Finset.prod_ite_mem_eq _ _

theorem categorical_mean_partial_assignment (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (hc : ∀ j, Fintype.card ι ≤ p j) (s : Finset ρ) (a : ρ → Option ι)
    (ha : ∀ j ∈ s, a j ≠ none) :
    (independentProduct (fun j ↦ categorical ι (p j) (hp j) (hc j))).mean
      (fun x ↦ if ∀ j ∈ s, x j = a j then (1 : ℝ) else 0) =
        ∏ j ∈ s, (1 : ℝ) / p j := by
  rw [independentProduct_mean_partial_assignment]
  exact Finset.prod_congr rfl (fun j hj ↦ categorical_mass_of_ne_none _ _ _ _ (ha j hj))

theorem categorical_tuple_comparison (μ : FiniteLaw Ω) (A : Ω → ρ → Option ι)
    (p : ρ → ℕ) (hp : ∀ j, 0 < p j) (hc : ∀ j, Fintype.card ι ≤ p j)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hjoint : ∀ (s : Finset ρ) (a : ρ → Option ι), (∀ j ∈ s, a j ≠ none) →
      |μ.mean (fun x ↦ if ∀ j ∈ s, A x j = a j then (1 : ℝ) else 0) -
        ∏ j ∈ s, (1 : ℝ) / p j| ≤ δ)
    (m : ℕ) (f : Fin m → ρ × ι) :
    |μ.mean (fun x ↦ ∏ k, (if A x (f k).1 = some (f k).2 then (1 : ℝ) else 0)) -
      (independentProduct (fun j ↦ categorical ι (p j) (hp j) (hc j))).mean
        (fun x ↦ ∏ k, (if x (f k).1 = some (f k).2 then (1 : ℝ) else 0))| ≤ δ := by
  classical
  simp_rw [Fintype.prod_boole]
  by_cases hex : ∃ a : ρ → Option ι, ∀ k, a (f k).1 = some (f k).2
  · obtain ⟨a, ha⟩ := hex
    let s : Finset ρ := Finset.univ.image (fun k ↦ (f k).1)
    have heq (x : ρ → Option ι) :
        (∀ k, x (f k).1 = some (f k).2) ↔ ∀ j ∈ s, x j = a j := by
      constructor
      · intro hx j hj
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
        exact (hx k).trans (ha k).symm
      · intro hx k
        exact (hx _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)).trans (ha k)
    have hn (j : ρ) (hj : j ∈ s) : a j ≠ none := by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      rw [ha k]
      simp
    simp_rw [heq]
    rw [categorical_mean_partial_assignment p hp hc s a hn]
    exact hjoint s a hn
  · have hn (x : ρ → Option ι) : ¬∀ k, x (f k).1 = some (f k).2 := by
      intro hx
      exact hex ⟨x, hx⟩
    simp only [if_neg (hn _), mean_const, sub_self, abs_zero]
    exact hδ

end Erdos69.Elementary.FiniteLaw
