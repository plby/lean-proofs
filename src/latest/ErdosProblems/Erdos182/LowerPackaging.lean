import ErdosProblems.Erdos182.Asymptotics
import ErdosProblems.Erdos182.Foundations

namespace Erdos182

open Filter Asymptotics
open scoped Classical

/-- Package eventual dense regular-subgraph-free witnesses into the lower bound
for the regular extremal number, expressed using `logLog2`. -/
theorem prs_extremal_lower_of_allDegreeWitness
    (h : ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      (1 / 60 : ℝ) * (n : ℝ) * logLog n ≤ (G.edgeFinset.card : ℝ) ∧
        ∀ q : ℕ, 3 ≤ q → IsRegularSubgraphFree G q) :
    ∃ c > 0, ∀ k : ℕ, 3 ≤ k →
      ∀ᶠ n : ℕ in atTop,
        c * ((n : ℝ) * logLog2 n) ≤ (regularExtremalNumber n k : ℝ) := by
  obtain ⟨C, hC, hO⟩ := logLog2_isTheta_logLog.1.exists_pos
  refine ⟨(1 / 60 : ℝ) / C, div_pos (by norm_num) hC, ?_⟩
  intro k hk
  filter_upwards [h, hO.bound, eventually_logLog_pos, eventually_logLog2_pos] with
    n hn hbound hlogLog hlogLog2
  obtain ⟨G, hcard, hfree⟩ := hn
  have hlogs : logLog2 n ≤ C * logLog n := by
    simpa [abs_of_pos hlogLog2, abs_of_pos hlogLog] using hbound
  have hscale : 0 ≤ (1 / 60 : ℝ) / C :=
    le_of_lt (div_pos (by norm_num) hC)
  have hedge : (G.edgeFinset.card : ℝ) ≤ (regularExtremalNumber n k : ℝ) := by
    exact_mod_cast card_edgeFinset_le_regularExtremalNumber G (hfree k hk)
  calc
    ((1 / 60 : ℝ) / C) * ((n : ℝ) * logLog2 n)
        ≤ ((1 / 60 : ℝ) / C) * ((n : ℝ) * (C * logLog n)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlogs (Nat.cast_nonneg n)) hscale
    _ = (1 / 60 : ℝ) * (n : ℝ) * logLog n := by
      field_simp [ne_of_gt hC]
    _ ≤ (G.edgeFinset.card : ℝ) := hcard
    _ ≤ (regularExtremalNumber n k : ℝ) := hedge

end Erdos182
