import ErdosProblems.Erdos587.HooleyCubeFiber

/-! # A cube-fiber representative with at most dimension-many fractional coefficients -/

open scoped BigOperators

namespace Erdos587.CFP

theorem delta_fractional_coefficients_linearIndependent {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℝ) (α β : ι → ℝ)
    (hβ : β ∈ (Set.Icc (0 : ι → ℝ) 1 ∩
      {x | Fintype.linearCombination ℝ v x = Fintype.linearCombination ℝ v α}).extremePoints ℝ) :
    LinearIndependent ℝ (fun i : (Finset.univ.filter (fun i => 0 < β i ∧ β i < 1)) => v i) := by
  classical
  let S := Finset.univ.filter (fun i => 0 < β i ∧ β i < 1)
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  let γ : ι → ℝ := fun j => if h : j ∈ S then c ⟨j, h⟩ else 0
  have hsum : (∑ j : ι, γ j • v j) = ∑ j : S, c j • v j := by
    rw [show (∑ j : S, c j • v j) = ∑ j ∈ S.attach, c j • v j from rfl,
      Finset.sum_attach_eq_sum_dite]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [γ]
    split_ifs <;> simp
  have hγ : Fintype.linearCombination ℝ v γ = 0 := by
    rw [Fintype.linearCombination_apply, hsum]
    exact hc
  have hsupp : ∀ j, γ j ≠ 0 → 0 < β j ∧ β j < 1 := by
    intro j hj
    by_cases hjS : j ∈ S
    · exact (Finset.mem_filter.mp hjS).2
    · simp only [γ, dif_neg hjS] at hj
      exact (hj rfl).elim
  have hγzero := delta_extreme_cube_fiber_kernel_eq_zero (Fintype.linearCombination ℝ v)
    (Fintype.linearCombination ℝ v α) β hβ γ hγ hsupp
  have hi := congrFun hγzero (i : ι)
  have hiS : (i : ι) ∈ S := by simpa only [S] using i.property
  simpa only [γ, dif_pos hiS, Pi.zero_apply] using hi

theorem delta_exists_few_fractional_coefficients {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℝ) (α : ι → ℝ) (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ β : ι → ℝ, (∀ i, β i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∑ i, β i • v i) = (∑ i, α i • v i) ∧
      (Finset.univ.filter (fun i => 0 < β i ∧ β i < 1)).card ≤ d := by
  classical
  have hαcube : α ∈ Set.Icc (0 : ι → ℝ) 1 := ⟨fun i => (hα i).1, fun i => (hα i).2⟩
  obtain ⟨β, hβ⟩ := delta_exists_extreme_cube_fiber (Fintype.linearCombination ℝ v) α hαcube
  have hind := delta_fractional_coefficients_linearIndependent v α β hβ
  refine ⟨β, fun i => ⟨hβ.1.1.1 i, hβ.1.1.2 i⟩, ?_, ?_⟩
  · exact hβ.1.2
  · simpa only [Fintype.card_coe, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hind.fintype_card_le_finrank

end Erdos587.CFP
