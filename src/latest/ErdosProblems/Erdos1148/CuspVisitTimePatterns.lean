import ErdosProblems.Erdos1148.CuspPatternExponentialRate
import ErdosProblems.Erdos1148.CuspRunGeometry

/-! # Small exponential pattern counts in natural-number time coordinates -/

namespace Erdos1148.DukeArithmetic

theorem exists_cusp_visit_time_patterns_small_rate {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ C : ℝ, 0 < H₀ ∧ 0 < C ∧ ∀ H : ℝ, H₀ ≤ H → ∀ n : ℕ,
      ∃ P : Finset (Finset ℕ), (P.card : ℝ) ≤ C * Real.exp (ε * n) ∧
        ∀ x : ModularOrbitSpace, modularCuspVisitTimes H n x ∈ P := by
  classical
  obtain ⟨H₀, C, hH₀, hC, hpatterns⟩ := exists_cusp_visit_pattern_small_rate hε
  refine ⟨H₀, C, hH₀, hC, ?_⟩
  intro H hH n
  obtain ⟨Q, hQ, hcover⟩ := hpatterns H hH n
  let P := Q.image (fun V => V.image Fin.val)
  refine ⟨P, ?_, ?_⟩
  · have hcard : (P.card : ℝ) ≤ (Q.card : ℝ) := by
      exact_mod_cast Finset.card_image_le (s := Q) (f := fun V => V.image Fin.val)
    exact hcard.trans hQ
  · intro x
    exact Finset.mem_image.mpr ⟨modularCuspVisitPattern H n x, hcover x, rfl⟩

end Erdos1148.DukeArithmetic
