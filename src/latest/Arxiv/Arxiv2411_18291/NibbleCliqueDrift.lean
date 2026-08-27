import Arxiv.Arxiv2411_18291.NibbleCountConditions
import Arxiv.Arxiv2411_18291.NibbleCliqueStepControl
import Arxiv.Arxiv2411_18291.CliqueCountCriticalDrift

/-! # Clique-count drift for the concrete reciprocal comparisons -/

namespace Arxiv2411_18291.NibbleCountConditions

variable {k : ℕ} {a g D p₀ L : ℝ}
variable (P : NibbleComparisonParameters k a g D p₀ L) (Q : NibbleCountConditions k a g D p₀ L)

include P Q

theorem comparison_steps {s p : ℝ} (hs : p₀ ≤ s) (hp1 : p ≤ 1)
    (hstep : p - s = (k : ℝ) / g) :
    let δu := nibbleCliqueUpper k a g D s - nibbleCliqueUpper k a g D p
    let δl := nibbleCliqueLower k a g D s - nibbleCliqueLower k a g D p;
    -nibbleCliqueSlope k D p ≤ δu ∧ δl ≤ -nibbleCliqueSlope k D p ∧
      |δu| ≤ 130 * (k : ℝ) ^ 3 * D ∧ |δl| ≤ 130 * (k : ℝ) ^ 3 * D := by
  obtain ⟨hs0, hsp, hhalf, hp⟩ := P.consecutive_bounds hs hstep
  exact nibbleClique_comparison_step_control P.rank P.error_pos.le P.graph_pos P.degree_pos.le
    hs0 hsp hp1 hhalf hstep (P.error_le_floor.trans hp) Q.step_bound

theorem upper_drift {s p H : ℝ} (hs : p₀ ≤ s) (hp1 : p ≤ 1)
    (hstep : p - s = (k : ℝ) / g)
    (hH : nibbleCliqueUpper k a g D p - a ^ 3 * D * g ≤ H) :
    -((k : ℝ) ^ 2 * H / (p * g)) + (k : ℝ) ^ 2 * L -
      (nibbleCliqueUpper k a g D s - nibbleCliqueUpper k a g D p) ≤ 0 := by
  obtain ⟨_, _, _, hp⟩ := P.consecutive_bounds hs hstep
  have hp0 := P.floor_pos.trans_le hp
  have hk : 0 < k := by have h := P.rank; omega
  have hδ := (Q.comparison_steps P hs hp1 hstep).1
  rw [nibbleCliqueSlope_eq_main_ratio hk P.graph_pos.ne' hp0.ne'] at hδ
  exact clique_count_upper_drift_nonpos (mul_pos hp0 P.graph_pos)
    (Q.overlap_margin P hp hp1) hH hδ

theorem lower_drift {s p H : ℝ} (hs : p₀ ≤ s) (hp1 : p ≤ 1)
    (hstep : p - s = (k : ℝ) / g)
    (hhalf : nibbleCliqueMain k g D p / 2 ≤ H)
    (hH : H ≤ nibbleCliqueLower k a g D p + a ^ 3 * D * g) :
    0 ≤ -((k : ℝ) ^ 2 * H / (p * g)) -
      (p * g) * nibbleDegreeError k a D p ^ 2 / H -
      (nibbleCliqueLower k a g D s - nibbleCliqueLower k a g D p) := by
  obtain ⟨_, _, _, hp⟩ := P.consecutive_bounds hs hstep
  have hp0 := P.floor_pos.trans_le hp
  have hk : 0 < k := by have h := P.rank; omega
  have hδ := (Q.comparison_steps P hs hp1 hstep).2.1
  rw [nibbleCliqueSlope_eq_main_ratio hk P.graph_pos.ne' hp0.ne'] at hδ
  exact clique_count_lower_drift_nonneg (mul_pos hp0 P.graph_pos)
    (nibbleCliqueMain_pos hk P.graph_pos P.degree_pos hp0) hhalf hH
    (Q.variance_margin P hp hp1) hδ

end Arxiv2411_18291.NibbleCountConditions
