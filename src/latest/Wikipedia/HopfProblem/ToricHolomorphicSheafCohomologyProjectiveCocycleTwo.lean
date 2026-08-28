import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyProjectiveCocycleSplitting
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarOnePartialLaurent

/-!
# Actual holomorphic splitting on the projective triple overlap

First split in the second coordinate with its punctured first-coordinate
parameter. The reciprocal part then has an ordinary entire parametric
Laurent splitting in the first coordinate. The three resulting actual
functions extend to exactly the three projective double overlaps.
-/

noncomputable section

open Complex Set
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ProjectiveCocycle

/-- Literal surjectivity of the three-chart degree-one differential,
with its actual projective coordinate transformations and signs. -/
theorem exists_triple_overlap_splitting {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.1 ≠ 0 ∧ q.2 ≠ 0}) :
    ∃ g₀₁ g₀₂ g₁₂ : ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ g₀₁ {q | q.1 ≠ 0} ∧
      AnalyticOnNhd ℂ g₀₂ {q | q.2 ≠ 0} ∧
      AnalyticOnNhd ℂ g₁₂ {q | q.2 ≠ 0} ∧
      ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
        f (x, y) = g₀₁ (x, y) - g₀₂ (x, y) + g₁₂ (x⁻¹, y / x) := by
  obtain ⟨p, m, hp, hm, _, hpm⟩ := DoublePuncturedDbarOne.exists_partial_second_splitting hf
  obtain ⟨A, B, hA, hB, _, hAB⟩ := exists_first_coordinate_splitting hm
  refine ⟨p, fun q => -A (q.1, q.2⁻¹), fun q => B (q.1, q.1 / q.2), hp, ?_, ?_, ?_⟩
  · intro q hq
    exact (AnalyticAt.comp (f := fun p : ℂ × ℂ => (p.1, p.2⁻¹))
      (hA (q.1, q.2⁻¹) (mem_univ _))
      (analyticAt_fst.prod (analyticAt_snd.inv hq))).neg
  · intro q hq
    exact AnalyticAt.comp (f := fun p : ℂ × ℂ => (p.1, p.1 / p.2))
      (hB (q.1, q.1 / q.2) (mem_univ _))
      (analyticAt_fst.prod (analyticAt_fst.div analyticAt_snd hq))
  · intro x y hx hy
    have he : x⁻¹ / (y / x) = y⁻¹ := by field_simp
    rw [hpm x y hx hy, hAB x y⁻¹ hx]
    simp only [sub_neg_eq_add, he, add_assoc]

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ProjectiveCocycle
