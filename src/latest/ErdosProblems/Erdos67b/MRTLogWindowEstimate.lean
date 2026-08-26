import ErdosProblems.Erdos67b.MRTLogWindowGeometry

/-! # Paying all lower-scale blocks in the actual Elliott logarithmic window -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

theorem mrtWeighted_logWindow_le_of_dyadic {X W w Y₀ K : ℕ} {R δ : ℝ}
    (hW : 0 < W) (hWX : W ≤ X) (hw : 0 < w) (hR : 1 ≤ R) (hδ : 0 ≤ δ)
    (hlog : 1 ≤ Real.log W) (hK : max Y₀ (4 * w) ≤ 2 ^ K)
    (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) (hg1 : ∀ n, 0 < n → g n ≤ 1)
    (hlocal : ∀ Y : ℕ, Y₀ ≤ Y → Y ≤ X →
      Real.log X ≤ R * Real.log ((Y / w : ℕ) : ℝ) →
      (∑ n ∈ Finset.Ioc Y (2 * Y), g n) ≤ δ * Y) :
    (∑ n ∈ elliottLogWindow X W, g n / n) ≤
      K + 1 + (2 / R + 4 * δ) * Real.log W := by
  let N := X / W
  let J := mrtLogWindowBlockCount W
  let B := mrtLogGoodBlockIndex K W R
  have hN : 0 < N := (mrtLogWindow_lower_bounds hW hWX).1
  have hX : 0 < X := hW.trans_le hWX
  have hupper : X ≤ 2 * W * N := (mrtLogWindow_lower_bounds hW hWX).2
  have htrivial : ∀ j ∈ Finset.range J, mrtWeightedDyadicBlock N X j g ≤ 1 :=
    fun j _ ↦ mrtWeightedDyadicBlock_le_one hN X j g hg hg1
  have hgood : ∀ j ∈ Finset.range J, B ≤ j → mrtWeightedDyadicBlock N X j g ≤ δ := by
    intro j hj hBj
    by_cases hYX : X ≤ 2 ^ j * N
    · rw [mrtWeightedDyadicBlock_eq_zero hYX]
      exact hδ
    · have hscale := mrtGood_dyadic_scale hX hW hN hw hR hupper hK hBj
      rw [mrtWeightedDyadicBlock_eq_Ioc]
      apply mrtWeighted_Ioc_truncated_le (Nat.mul_pos (pow_pos (by norm_num) _) hN) X g hg
      exact hlocal _ hscale.1 (by omega) hscale.2
  rw [mrtElliott_weighted_eq_blocks hW hWX]
  calc
    _ ≤ B + δ * J := mrtSum_blocks_le_early_add hδ _ htrivial hgood
    _ ≤ (K + 1 + 2 * Real.log W / R) + δ * (4 * Real.log W) :=
      add_le_add (mrtLogGoodBlockIndex_le K hW hR)
        (mul_le_mul_of_nonneg_left (mrtLogWindowBlockCount_le hlog) hδ)
    _ = _ := by ring

theorem mrtNormalizedShortSum_le_one {H : ℕ} (hH : 0 < H) (f : ℕ → ℂ) (α : ℝ)
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (n : ℕ) :
    ‖modulatedShortSum f n H α‖ / H ≤ 1 := by
  apply (div_le_one (by exact_mod_cast hH : (0 : ℝ) < H)).2
  apply norm_modulatedShortSum_le
  intro j hj
  apply hf
  have h := (Finset.mem_Icc.1 hj).1
  omega

theorem mrtLogAverage_eq_normalized (f : ℕ → ℂ) (X W H : ℕ) (α : ℝ) :
    logAverageModulatedShortSum f X W H α =
      ∑ n ∈ elliottLogWindow X W, (‖modulatedShortSum f n H α‖ / H) / n := by
  unfold logAverageModulatedShortSum
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem mrtLogAverage_le_of_local_firstMoment {X W H w Y₀ K : ℕ} {R δ : ℝ}
    (hW : 0 < W) (hWX : W ≤ X) (hH : 0 < H) (hw : 0 < w) (hR : 1 ≤ R) (hδ : 0 ≤ δ)
    (hlog : 1 ≤ Real.log W) (hK : max Y₀ (4 * w) ≤ 2 ^ K)
    (f : ℕ → ℂ) (α : ℝ) (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (hlocal : ∀ Y : ℕ, Y₀ ≤ Y → Y ≤ X →
      Real.log X ≤ R * Real.log ((Y / w : ℕ) : ℝ) →
      (∑ n ∈ Finset.Ioc Y (2 * Y), ‖modulatedShortSum f n H α‖) ≤ δ * H * Y) :
    logAverageModulatedShortSum f X W H α ≤
      K + 1 + (2 / R + 4 * δ) * Real.log W := by
  rw [mrtLogAverage_eq_normalized]
  apply mrtWeighted_logWindow_le_of_dyadic hW hWX hw hR hδ hlog hK
    (fun n ↦ ‖modulatedShortSum f n H α‖ / H) (fun n ↦ by positivity)
    (fun n _ ↦ mrtNormalizedShortSum_le_one hH f α hf n)
  intro Y hY hYX hscale
  rw [← Finset.sum_div]
  apply (div_le_iff₀ (by exact_mod_cast hH : (0 : ℝ) < H)).2
  exact (hlocal Y hY hYX hscale).trans_eq (by ring)

end

end Erdos67b
