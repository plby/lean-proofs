import ErdosProblems.Erdos1148.CompactSubsetLifts
import ErdosProblems.Erdos1148.BoundedFrameInjectivity

/-! # A uniform injective right-neighborhood radius over a compact quotient set -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_compact_modular_injective_radius {K : Set ModularOrbitSpace} (hK : IsCompact K) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 / 192 ∧ ∀ η : ℝ, 0 ≤ η → η ≤ η₀ →
      ∀ g : SL(2, ℝ), modularMk g ∈ K → ∀ u v : SL(2, ℝ),
        EntryCloseOne η u → EntryCloseOne η v →
        modularMk (g * u) = modularMk (g * v) → u = v := by
  obtain ⟨A, hA, hbounded⟩ := exists_compact_integral_bounded_lifts hK
  let η₀ := min (1 / 192 : ℝ) (1 / (32 * A ^ 2))
  have hη₀ : 0 < η₀ := lt_min (by norm_num) (by positivity)
  refine ⟨η₀, hη₀, min_le_left _ _, ?_⟩
  intro η hη hηle g hg u v hu hv heq
  have hsmall : η ≤ 1 := (hηle.trans (min_le_left _ _)).trans (by norm_num)
  have hmul : η * (32 * A ^ 2) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (hηle.trans (min_le_right _ _))
  have hscale : 16 * A ^ 2 * η < 1 := by nlinarith only [hmul]
  obtain ⟨γ, hγ⟩ := hbounded g hg
  apply modularMk_injective_on_small_right_neighborhood hA.le hη hsmall hscale
    ((γ : SL(2, ℝ)) * g) hγ hu hv
  simpa only [mul_assoc, modularMk_integral_mul] using heq

end Erdos1148.DukeArithmetic
