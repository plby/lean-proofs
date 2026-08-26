/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The discarded bins adjacent to the logarithmic endpoint region are negligible almost surely.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.RightTrimGeometry
import ErdosProblems.Erdos521.RelativeIntervalMoments
import ErdosProblems.Erdos521.ClampedDyadicGrid
import ErdosProblems.Erdos521.FourthMomentNegligible

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem eventually_right_trim_fourth_moment :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ j : ℕ in atTop,
      (∫ ε, (intervalRootCount ε (2 ^ j) (dyadicPoint (j - Nat.sqrt j))
        (endpointCenter (localMomentBulkConstant 4) (2 ^ j)) : ℝ) ^ 4 ∂sequenceLaw) ≤ B * (j : ℝ) ^ 2 := by
  obtain ⟨B, hB, hmom⟩ := eventually_relative_interval_moments 4 (by norm_num)
  have hdegree : Tendsto (fun j : ℕ ↦ (2 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  let C := localMomentBulkConstant 4
  refine ⟨B, hB, ?_⟩
  filter_upwards [hdegree.eventually hmom, eventually_central_end_le_endpoint C,
    eventually_endpoint_le_dyadic_last (localMomentBulkConstant_pos 4), eventually_central_end_lower,
    eventually_ge_atTop 9] with j hj hstart hend hlower hj₉
  let b := endpointCenter C (2 ^ j)
  let g := fun i : ℕ ↦ min (dyadicPoint (j - Nat.sqrt j + i)) b
  have hb₁ : b < 1 := hend.trans_lt (dyadicPoint_lt_one j)
  have hg : Monotone g := by
    intro i k hik
    exact min_le_min (dyadicPoint_mono (Nat.add_le_add_left hik _)) le_rfl
  have hg₀ : g 0 = dyadicPoint (j - Nat.sqrt j) := by
    simpa only [g, Nat.add_zero] using min_eq_left hstart
  have hgN : g (Nat.sqrt j) = b := by
    dsimp only [g]
    rw [Nat.sub_add_cancel (Nat.sqrt_le_self j), min_eq_right hend]
  have hcell (i : ℕ) (_hi : i ∈ Finset.range (Nat.sqrt j)) :
      (∫ ε, (intervalRootCount ε (2 ^ j) (g i) (g (i + 1)) : ℝ) ^ 4 ∂sequenceLaw) ≤ B := by
    apply hj _ _
    · apply hlower.trans
      exact le_min (dyadicPoint_mono (Nat.le_add_right _ _)) hstart
    · exact min_le_right _ _
    · simpa only [g, Nat.add_assoc] using clamped_dyadic_width (j - Nat.sqrt j + i) hb₁.le
  have hr : 1 ≤ Nat.sqrt j := Nat.le_sqrt.mpr (by omega)
  have h := integral_intervalRootCount_partition_pow_le (2 ^ j) (Nat.sqrt j) 4 hr (by norm_num) g hg hcell
  rw [hg₀, hgN] at h
  apply h.trans
  have hroot : (Nat.sqrt j : ℝ) ^ 2 ≤ j := by exact_mod_cast Nat.sqrt_le' j
  have hpow : (Nat.sqrt j : ℝ) ^ 4 ≤ (j : ℝ) ^ 2 := by
    calc
      _ = ((Nat.sqrt j : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hroot 2
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hpow hB.le

theorem ae_right_trim_div_index_tendsto_zero :
    ∀ᵐ ε ∂sequenceLaw, Tendsto (fun j : ℕ ↦
      (intervalRootCount ε (2 ^ j) (dyadicPoint (j - Nat.sqrt j))
        (endpointCenter (localMomentBulkConstant 4) (2 ^ j)) : ℝ) / j) atTop (𝓝 0) := by
  obtain ⟨B, _, hB⟩ := eventually_right_trim_fourth_moment
  exact ae_nat_div_tendsto_zero_of_fourth_moment sequenceLaw
    (fun j ε ↦ intervalRootCount ε (2 ^ j) (dyadicPoint (j - Nat.sqrt j))
      (endpointCenter (localMomentBulkConstant 4) (2 ^ j)))
    (fun j ↦ intervalRootCount_pow_integrable (2 ^ j) 4 _ _) ⟨B, hB⟩

end Erdos521
