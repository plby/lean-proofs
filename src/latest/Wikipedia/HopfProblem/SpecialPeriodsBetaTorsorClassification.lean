import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorGlobal
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorCusp
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorBounded

/-!
# Existence and the complete constant family of beta solutions

A solution is holomorphic, satisfies the two original generator equations,
and has beta plus tau bounded on a distinguished high cusp horodisc.  The
actual local construction supplies such a solution and its holomorphic
extension in the genuine cusp coordinate.  Any two solutions differ by one
constant: their difference is genuinely descended to an entire function,
whose boundedness follows from the actual cusp geometry and the original
boundedness condition.  No analytic extension of a competing solution is
assumed for classification.
-/

noncomputable section

open Set Metric Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor.Data

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

variable (D : Data)

/-- The actual beta equations and the bounded distinguished-cusp condition. -/
structure IsSolution (β : ℍ → ℂ) : Prop where
  holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β
  generators : D.GeneratorLaws β
  cusp_bounded : ∃ Y M : ℝ, ∀ z : ℍ, Y < z.im → ‖β z + (D.tau z : ℂ)‖ ≤ M

theorem IsSolution.add_const {β : ℍ → ℂ} (hβ : D.IsSolution β) (c : ℂ) :
    D.IsSolution (fun z => β z + c) := by
  obtain ⟨Y, M, hM⟩ := hβ.cusp_bounded
  refine ⟨hβ.holomorphic.add contMDiff_const, hβ.generators.add_const D c,
    Y, M + ‖c‖, ?_⟩
  intro z hz
  calc
    ‖(β z + c) + (D.tau z : ℂ)‖ = ‖(β z + (D.tau z : ℂ)) + c‖ := by
      congr 1
      ring
    _ ≤ ‖β z + (D.tau z : ℂ)‖ + ‖c‖ := norm_add_le _ _
    _ ≤ M + ‖c‖ := add_le_add (hM z hz) le_rfl

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ

/-- A constructed beta satisfies the actual bounded cusp condition and has
a normalized analytic representative in the genuine exponential cusp chart. -/
theorem exists_solution_with_cusp_extension :
    ∃ (β : ℍ → ℂ) (C : ℂ → ℂ), D.IsSolution β ∧
      AnalyticAt ℂ C 0 ∧ C 0 = 0 ∧
      ∃ Y : ℝ, ∀ z : ℍ, Y < z.im →
        β z + (D.tau z : ℂ) = C (Triangle.cuspQ z) := by
  obtain ⟨R, hR, β, B, hβ, hgen, hB, hB0, hformula⟩ := D.exists_global_beta π hπ
  have hBzero : AnalyticAt ℂ B 0 := hB 0 (mem_ball_self (inv_pos.mpr hR))
  obtain ⟨Y, M, hbound⟩ := bounded_of_analytic_cusp_formula π hπ hBzero hformula
  obtain ⟨C, hC, hC0, Y', hCformula⟩ :=
    analytic_cusp_formula_to_q_extension π hπ hBzero hformula
  exact ⟨β, C, ⟨hβ, hgen, Y, M, hbound⟩, hC, hC0.trans hB0, Y', hCformula⟩

theorem exists_solution : ∃ β : ℍ → ℂ, D.IsSolution β := by
  obtain ⟨β, _, hβ, _⟩ := D.exists_solution_with_cusp_extension π hπ
  exact ⟨β, hβ⟩

/-- **Classification under bounded cusp growth.** No descended difference
or analytic extension of either competing solution is an input. -/
theorem IsSolution.eq_add_const {β γ : ℍ → ℂ}
    (hβ : D.IsSolution β) (hγ : D.IsSolution γ) :
    ∃ c : ℂ, β = fun z => γ z + c := by
  obtain ⟨c, hc⟩ := exists_const_beta_difference_of_bounded π hπ
    β γ (fun z => (D.tau z : ℂ)) hβ.holomorphic hγ.holomorphic
    (hβ.generators.sub_invariant D hγ.generators) hβ.cusp_bounded hγ.cusp_bounded
  exact ⟨c, funext hc⟩

/-- Relative to any one actual solution, all solutions are exactly its
constant translates; each translate satisfies the bounded cusp condition. -/
theorem solution_iff_eq_add_const {βpart : ℍ → ℂ} (hpart : D.IsSolution βpart)
    (β : ℍ → ℂ) :
    D.IsSolution β ↔ ∃ c : ℂ, β = fun z => βpart z + c := by
  constructor
  · intro hβ
    exact hβ.eq_add_const D π hπ hpart
  · rintro ⟨c, rfl⟩
    exact hpart.add_const D c

/-- **The actual affine family of global beta functions.** A particular
solution is constructed, rather than supplied, and the complete family is
proved to be `βpart + c`. -/
theorem exists_beta_affine_family :
    ∃ βpart : ℍ → ℂ, D.IsSolution βpart ∧
      ∀ β : ℍ → ℂ, D.IsSolution β ↔ ∃ c : ℂ, β = fun z => βpart z + c := by
  obtain ⟨βpart, hpart⟩ := D.exists_solution π hπ
  exact ⟨βpart, hpart, D.solution_iff_eq_add_const π hπ hpart⟩

/-- The particular function can simultaneously have zero cusp constant,
an actual analytic cusp expansion, and the complete affine-family property. -/
theorem exists_normalized_beta_affine_family :
    ∃ (βpart : ℍ → ℂ) (C : ℂ → ℂ), D.IsSolution βpart ∧
      AnalyticAt ℂ C 0 ∧ C 0 = 0 ∧
      (∃ Y : ℝ, ∀ z : ℍ, Y < z.im →
        βpart z + (D.tau z : ℂ) = C (Triangle.cuspQ z)) ∧
      ∀ β : ℍ → ℂ, D.IsSolution β ↔ ∃ c : ℂ, β = fun z => βpart z + c := by
  obtain ⟨βpart, C, hpart, hC, hC0, hformula⟩ := D.exists_solution_with_cusp_extension π hπ
  exact ⟨βpart, C, hpart, hC, hC0, hformula, D.solution_iff_eq_add_const π hπ hpart⟩

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor.Data
