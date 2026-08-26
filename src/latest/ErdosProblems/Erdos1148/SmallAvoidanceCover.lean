import ErdosProblems.Erdos1148.ModularAvoidanceCover
import ErdosProblems.Erdos1148.ModularOpenThickening

/-! # Arbitrarily small exponential prefactors for compact-start avoidance covers -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter
open scoped MatrixGroups Topology

theorem exists_small_compact_avoidance_cover {K U : Set ModularOrbitSpace}
    (hK : IsCompact K) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 192 ∧ ∀ q : ℝ, 0 < q → ∀ᶠ n : ℕ in atTop,
      ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
        (N : ℝ) ≤ q * Real.exp n ∧
        K ∩ finiteOrbitAvoidance modularTimeOne U n ⊆ ⋃ i, modularMk '' B i ∧
        (∀ i, IsCompact (B i)) ∧ ∀ i, LiftForwardClose r n (B i) := by
  obtain ⟨η₀, hη₀, _, hcover⟩ := exists_compact_avoidance_cover_bound hK
  obtain ⟨V, δ, hVopen, hVne, hδ, hthick⟩ := exists_open_modular_right_thickening hU hne
  let η := min η₀ (min δ (1 / 3072 : ℝ))
  have hη : 0 < η := lt_min hη₀ (lt_min hδ (by norm_num))
  have hη₀le : η ≤ η₀ := min_le_left _ _
  have hηδ : η ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hηsmall : η ≤ 1 / 3072 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨c, hc, hcovers⟩ := hcover η hη hη₀le
  have hthick' : ∀ x ∈ V, ∀ u ∈ forwardHaarTube η 0, modularRightTranslate u x ∈ U := by
    intro x hx u hu
    exact hthick x hx u (forwardHaarTube_mono hηδ hu)
  have hlim := modularHaar_open_avoidance_tendsto_zero hVopen hVne
  have hreal : Tendsto (fun n : ℕ => normalizedModularHaarMeasure.real
      (finiteOrbitAvoidance modularTimeOne V n)) atTop (𝓝 0) := by
    simpa only [Measure.real, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  have hdiv : Tendsto (fun n : ℕ => normalizedModularHaarMeasure.real
      (finiteOrbitAvoidance modularTimeOne V n) / c) atTop (𝓝 0) := by
    simpa only [zero_div] using hreal.div_const c
  refine ⟨16 * η, by positivity, by linarith, ?_⟩
  intro q hq
  have hevent := (tendsto_order.mp hdiv).2 q hq
  filter_upwards [hevent] with n hn
  obtain ⟨N, B, hN, hcov, hB, hclose⟩ := hcovers U V hthick' n
  exact ⟨N, B, hN.trans (mul_le_mul_of_nonneg_right hn.le (Real.exp_pos _).le),
    hcov, hB, hclose⟩

end Erdos1148.DukeArithmetic
