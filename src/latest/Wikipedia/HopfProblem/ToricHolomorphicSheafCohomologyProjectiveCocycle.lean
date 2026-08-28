import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyProjectiveCocycleLiouville
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowdownDescent

/-!
# An actual entire cochain for every projective three-chart cocycle

Three parametric Cauchy-integral decompositions, their proved analytic
uniqueness, Liouville's theorem, and holomorphic descent through the
actual incidence blowup construct the cochain. This is a statement
about genuine holomorphic functions in the specified chart coordinates;
it does not define or assume any sheaf cohomology vanishing.
-/

noncomputable section

open Complex Set
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ProjectiveCocycle

/-- Every literal additive cocycle in the three standard projective
coordinate charts is the difference of actual entire chart functions. -/
theorem ChartCocycle.exists_entire_cochain (h : ChartCocycle) :
    ∃ g₀ g₁ g₂ : ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ g₀ univ ∧ AnalyticOnNhd ℂ g₁ univ ∧
      AnalyticOnNhd ℂ g₂ univ ∧
      (∀ x y : ℂ, x ≠ 0 → h.zeroOne (x, y) = g₀ (x, y) - g₁ (x⁻¹, y / x)) ∧
      (∀ x y : ℂ, y ≠ 0 → h.zeroTwo (x, y) = g₀ (x, y) - g₂ (x / y, y⁻¹)) ∧
      (∀ u v : ℂ, v ≠ 0 → h.oneTwo (u, v) = g₁ (u, v) - g₂ (v⁻¹, u / v)) := by
  obtain ⟨L⟩ := exists_laurentData h
  obtain ⟨G, hG, hGF, hGD⟩ := BlowdownDescent.exists_chart_descent
    L.F_analytic L.D_analytic L.blowup_identity
  refine ⟨fun q => L.A q + L.C (0, 0), L.C, fun q => -G q,
    L.A_analytic.add analyticOnNhd_const, L.C_analytic, hG.neg,
    L.zeroOne_corrected, ?_, ?_⟩
  · intro x y hy
    rw [L.zeroTwo_corrected x y hy]
    simp only [sub_neg_eq_add, div_eq_mul_inv, hGF]
  · intro u v hv
    rw [L.oneTwo_eq u v hv]
    simp only [sub_neg_eq_add, div_eq_mul_inv, hGD]

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ProjectiveCocycle
