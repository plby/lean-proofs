import ErdosProblems.Erdos587.HooleyZonotope
import ErdosProblems.Erdos587.HooleySubsetRounding

/-! # An integral center for zonotope-to-subset-sum rounding -/

open scoped BigOperators

namespace Erdos587.CFP

theorem delta_centered_zonotope_subset_rounding {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (L R : Fin d → ℝ) (hL : ∀ j, 0 ≤ L j)
    (hv : ∀ i j, |(v i j : ℝ)| ≤ L j) (θ : ι → ℝ)
    (hθ : ∀ i, θ i ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) (z : Fin d → ℤ)
    (hz : ∀ j, |(z j : ℝ) - (round ((∑ i, (v i j : ℝ)) / 2) : ℤ) -
      ∑ i, θ i * (v i j : ℝ)| ≤ R j) :
    ∃ S : Finset ι, ∀ j,
      |(z j : ℝ) - ∑ i ∈ S, (v i j : ℝ)| ≤ R j + (d : ℝ) * L j + 1 / 2 := by
  let α : ι → ℝ := fun i => θ i + 1 / 2
  have hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    obtain ⟨hi0, hi1⟩ := hθ i
    constructor <;> dsimp only [α] <;> linarith
  obtain ⟨S, hS⟩ := delta_exists_subset_sum_coordinate_rounding
    (fun i j => (v i j : ℝ)) L hL hv α hα
  refine ⟨S, ?_⟩
  intro j
  let c : ℝ := (∑ i, (v i j : ℝ)) / 2
  have hcenter : |(round c : ℝ) - c| ≤ (1 / 2 : ℝ) := by
    simpa only [abs_sub_comm] using abs_sub_round c
  have hsum : (∑ i, α i * (v i j : ℝ)) = (∑ i, θ i * (v i j : ℝ)) + c := by
    dsimp only [α, c]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hid : (z j : ℝ) - ∑ i ∈ S, (v i j : ℝ) =
      ((z j : ℝ) - (round c : ℝ) - ∑ i, θ i * (v i j : ℝ)) +
      ((round c : ℝ) - c) + ((∑ i, α i * (v i j : ℝ)) - ∑ i ∈ S, (v i j : ℝ)) := by
    rw [hsum]
    ring
  rw [hid]
  calc
    _ ≤ |(z j : ℝ) - (round c : ℝ) - ∑ i, θ i * (v i j : ℝ)| +
        |(round c : ℝ) - c| + |(∑ i, α i * (v i j : ℝ)) - ∑ i ∈ S, (v i j : ℝ)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ R j + 1 / 2 + (d : ℝ) * L j := add_le_add (add_le_add (hz j) hcenter) (hS j)
    _ = _ := by ring

end Erdos587.CFP
