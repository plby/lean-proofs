import ErdosProblems.Erdos587.HooleyZonotopeRounding

/-! # An integral zonotope center with no upward error in the evaluation map -/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

lemma delta_eval_coordinate_sum {d : ℕ} (f : (Fin d → ℤ) →+ ℤ) (z : Fin d → ℤ) :
    f z = ∑ j, z j * f (Pi.single j 1) := by
  have hz := pi_eq_sum_univ' z
  conv_lhs => rw [hz]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact map_zsmul f (z j) (Pi.single j 1)

theorem delta_exists_lower_half_center {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (f : (Fin d → ℤ) →+ ℤ) :
    ∃ c : Fin d → ℤ,
      (∀ j, |(c j : ℝ) - (∑ i, (v i j : ℝ)) / 2| ≤ (1 / 2 : ℝ)) ∧
      (f c : ℝ) ≤ (∑ i, (f (v i) : ℝ)) / 2 := by
  classical
  let s : Fin d → ℤ := ∑ i, v i
  let a : Fin d → ℤ := fun j => f (Pi.single j 1)
  let c : Fin d → ℤ := fun j => if 0 ≤ a j then s j / 2 else -((-s j) / 2)
  have hfloor (z : ℤ) : 0 ≤ z - 2 * (z / 2) ∧ z - 2 * (z / 2) ≤ 1 := by omega
  have hcoord (j : Fin d) : |2 * c j - s j| ≤ 1 ∧ 2 * c j * a j ≤ s j * a j := by
    dsimp only [c]
    by_cases ha : 0 ≤ a j
    · rw [if_pos ha]
      obtain ⟨hlo, hhi⟩ := hfloor (s j)
      refine ⟨abs_le.mpr ⟨by omega, by omega⟩, ?_⟩
      exact mul_le_mul_of_nonneg_right (by omega) ha
    · rw [if_neg ha]
      obtain ⟨hlo, hhi⟩ := hfloor (-s j)
      refine ⟨abs_le.mpr ⟨by omega, by omega⟩, ?_⟩
      exact mul_le_mul_of_nonpos_right (by omega) (le_of_not_ge ha)
  refine ⟨c, ?_, ?_⟩
  · intro j
    have hh : |2 * (c j : ℝ) - (s j : ℝ)| ≤ 1 := by exact_mod_cast (hcoord j).1
    have hs : (s j : ℝ) = ∑ i, (v i j : ℝ) := by simp only [s, Finset.sum_apply, Int.cast_sum]
    rw [abs_le] at hh ⊢
    rw [← hs]
    constructor <;> linarith [hh.1, hh.2]
  · have hsum : 2 * f c ≤ f s := by
      rw [delta_eval_coordinate_sum f c, delta_eval_coordinate_sum f s, Finset.mul_sum]
      exact Finset.sum_le_sum (fun j _ => by simpa only [mul_assoc] using (hcoord j).2)
    have hs : (f s : ℝ) = ∑ i, (f (v i) : ℝ) := by simp only [s, map_sum, Int.cast_sum]
    have hh : 2 * (f c : ℝ) ≤ (f s : ℝ) := by exact_mod_cast hsum
    rw [hs] at hh
    linarith

end Erdos587.GeneralizedAP

namespace Erdos587.CFP

theorem delta_zonotope_subset_rounding_of_center {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (L R : Fin d → ℝ) (hL : ∀ j, 0 ≤ L j)
    (hv : ∀ i j, |(v i j : ℝ)| ≤ L j) (θ : ι → ℝ)
    (hθ : ∀ i, θ i ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) (c z : Fin d → ℤ)
    (hc : ∀ j, |(c j : ℝ) - (∑ i, (v i j : ℝ)) / 2| ≤ (1 / 2 : ℝ))
    (hz : ∀ j, |(z j : ℝ) - (c j : ℝ) - ∑ i, θ i * (v i j : ℝ)| ≤ R j) :
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
  let t : ℝ := (∑ i, (v i j : ℝ)) / 2
  have hsum : (∑ i, α i * (v i j : ℝ)) = (∑ i, θ i * (v i j : ℝ)) + t := by
    dsimp only [α, t]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hid : (z j : ℝ) - ∑ i ∈ S, (v i j : ℝ) =
      ((z j : ℝ) - (c j : ℝ) - ∑ i, θ i * (v i j : ℝ)) +
      ((c j : ℝ) - t) + ((∑ i, α i * (v i j : ℝ)) - ∑ i ∈ S, (v i j : ℝ)) := by
    rw [hsum]
    ring
  rw [hid]
  calc
    _ ≤ |(z j : ℝ) - (c j : ℝ) - ∑ i, θ i * (v i j : ℝ)| +
        |(c j : ℝ) - t| + |(∑ i, α i * (v i j : ℝ)) - ∑ i ∈ S, (v i j : ℝ)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ R j + 1 / 2 + (d : ℝ) * L j := add_le_add (add_le_add (hz j) (hc j)) (hS j)
    _ = _ := by ring

end Erdos587.CFP
