import Arxiv.Arxiv2411_18291.NibbleComparisonSequences

/-! # Concrete frozen-edge comparison increments at successive process times -/

namespace Arxiv2411_18291.NibbleComparisonParameters

variable {k : ℕ} {a g D p₀ L : ℝ} (P : NibbleComparisonParameters k a g D p₀ L)

include P

theorem degree_upper_steps (i : ℕ) (hi : p₀ ≤ removalDensity k g (i + 1)) :
    let p := removalDensity k g i
    let δ := nibbleDegreeUpperComparison k a g D (i + 1) - nibbleDegreeUpperComparison k a g D i
    |δ| ≤ 2 * nibbleEdgeSlope k g D p ∧ δ ≤ 0 ∧
      -(((k - 1 : ℕ) : ℝ) * nibbleDegreeMain k D p ^ 2 / nibbleCliqueMain k g D p) +
        (6 * ((k - 1 : ℕ) : ℝ) + 4) * nibbleEdgeScale a D p * nibbleDegreeMain k D p /
          nibbleCliqueMain k g D p ≤ δ := by
  have hstep := removalDensity_difference k g i
  obtain ⟨hs0, hsp, hhalf, hp⟩ := P.consecutive_bounds hi hstep
  have hp0 := P.floor_pos.trans_le hp
  have hk : 0 < k := by have h := P.rank; omega
  obtain ⟨habs, hneg, htrend⟩ := nibbleDegreeUpper_step_control P.rank P.error_pos.le
    P.graph_pos P.degree_pos hs0 hsp (removalDensity_le_one k P.graph_pos i) hhalf hstep
    (P.power_bound hp) P.small P.many_edges
  dsimp only
  refine ⟨habs, hneg, ?_⟩
  rw [nibbleEdgeSlope_eq_main_ratio (by have h := P.rank; omega)
    P.graph_pos.ne' P.degree_pos.ne' hp0.ne',
    nibbleEdgeStepScale_eq hk P.graph_pos.ne' P.degree_pos.ne' hp0.ne'] at htrend
  calc
    _ = -(((k - 1 : ℕ) : ℝ) * nibbleDegreeMain k D (removalDensity k g i) ^ 2 /
        nibbleCliqueMain k g D (removalDensity k g i)) +
        (6 * ((k - 1 : ℕ) : ℝ) + 4) *
          (nibbleEdgeScale a D (removalDensity k g i) *
            nibbleDegreeMain k D (removalDensity k g i) /
            nibbleCliqueMain k g D (removalDensity k g i)) := by ring
    _ ≤ _ := htrend

theorem degree_lower_steps (i : ℕ) (hi : p₀ ≤ removalDensity k g (i + 1)) :
    let p := removalDensity k g i
    let δ := nibbleDegreeLowerComparison k a g D (i + 1) - nibbleDegreeLowerComparison k a g D i
    |δ| ≤ 2 * nibbleEdgeSlope k g D p ∧
      δ ≤ -(((k - 1 : ℕ) : ℝ) * nibbleDegreeMain k D p ^ 2 / nibbleCliqueMain k g D p) -
        6 * ((k - 1 : ℕ) : ℝ) * nibbleEdgeScale a D p * nibbleDegreeMain k D p /
          nibbleCliqueMain k g D p -
        4 * nibbleDegreeMain k D p * (2 * nibbleEdgeSlope k g D p) / nibbleCliqueMain k g D p := by
  have hstep := removalDensity_difference k g i
  obtain ⟨hs0, hsp, hhalf, hp⟩ := P.consecutive_bounds hi hstep
  have hp0 := P.floor_pos.trans_le hp
  have hk : 0 < k := by have h := P.rank; omega
  obtain ⟨habs, htrend⟩ := nibbleDegreeLower_step_control P.rank P.error_pos.le
    P.graph_pos P.degree_pos hs0 hsp (removalDensity_le_one k P.graph_pos i) hhalf hstep
    (P.power_bound hp) P.small P.many_edges
  dsimp only
  refine ⟨habs, ?_⟩
  calc
    _ ≤ _ := htrend
    _ = _ := by
      rw [nibbleEdgeSlope_eq_main_ratio (by have h := P.rank; omega)
        P.graph_pos.ne' P.degree_pos.ne' hp0.ne',
        nibbleEdgeStepScale_eq hk P.graph_pos.ne' P.degree_pos.ne' hp0.ne']
      ring

end Arxiv2411_18291.NibbleComparisonParameters
