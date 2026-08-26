import ErdosProblems.Erdos1148.ModularHaarBowenBall
import ErdosProblems.Erdos1148.CompactSubsetLifts

/-! # Uniform Bowen-ball volume over a compact part of the modular quotient -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups ENNReal

theorem exists_compact_modularForwardHaarBall_mass_lower {K : Set ModularOrbitSpace}
    (hK : IsCompact K) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 / 8 ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∃ c : ℝ, 0 < c ∧ ∀ g : SL(2, ℝ), modularMk g ∈ K →
        ∀ S : ℝ, 0 ≤ S → ENNReal.ofReal (c * Real.exp (-S)) ≤
          normalizedModularHaarMeasure (modularForwardHaarBall η S g) := by
  obtain ⟨A, hA, hbounded⟩ := exists_compact_integral_bounded_lifts hK
  let η₀ := min (1 / 8 : ℝ) (1 / (32 * A ^ 2))
  have hη₀ : 0 < η₀ := lt_min (by norm_num) (by positivity)
  refine ⟨η₀, hη₀, min_le_left _ _, ?_⟩
  intro η hη hηle
  have hsmall : η ≤ 1 / 8 := hηle.trans (min_le_left _ _)
  have hmul : η * (32 * A ^ 2) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (hηle.trans (min_le_right _ _))
  have hscale : 16 * A ^ 2 * η < 1 := by nlinarith
  obtain ⟨c, hc, hmass⟩ := modularForwardHaarBall_mass_lower_of_bounded hA.le hη hsmall hscale
  refine ⟨c, hc, ?_⟩
  intro g hg S hS
  obtain ⟨γ, hγ⟩ := hbounded g hg
  have h := hmass ((γ : SL(2, ℝ)) * g) hγ S hS
  rwa [modularForwardHaarBall_integral_mul] at h

end Erdos1148.DukeArithmetic
