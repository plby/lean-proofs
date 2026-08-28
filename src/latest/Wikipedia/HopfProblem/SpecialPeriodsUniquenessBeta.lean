import Wikipedia.HopfProblem.SpecialPeriodsUniquenessTau
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorClassification

/-!
# The complete family of special beta functions

The constructed special tau and mu determine the actual beta torsor.
Its constructed admissible beta is a solution, and all holomorphic beta
functions satisfying the two original affine equations and boundedness
of beta plus tau at imaginary infinity are precisely its constant
translates. No tau, mu, or sphere uniformization is an existence input.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods

open Triangle

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

/-- The beta torsor defined by the actual constructed special tau and mu. -/
def specialBetaTorsorData : BetaTorsor.Data where
  tau := specialTauHalfPlane
  mu := specialMu
  tau_holomorphic := specialTauHalfPlane_holomorphic
  mu_holomorphic := specialMu_holomorphic
  tau_covariant := specialTauHalfPlane_covariant
  mu_one z := by
    simpa only [specialTauHalfPlane_coe] using (specialPeriods_generator₁ z).2.1
  mu_two z := by
    simpa only [specialTauHalfPlane_coe] using (specialPeriods_generator₂ z).2.1

/-- The torsor equations retain exactly the source's affine terms. -/
theorem specialBetaTorsorData_generatorLaws_iff (β : ℍ → ℂ) :
    specialBetaTorsorData.GeneratorLaws β ↔
      (∀ z : ℍ, β (generatorOneSL • z) =
        β z + 2 - 6 * (1 - specialMu z) ^ 2 / specialTau z) ∧
      (∀ z : ℍ, β (generatorTwoSL • z) =
        β z - 3 - 6 * specialMu z ^ 2 / specialTau z) := by
  simp only [BetaTorsor.Data.GeneratorLaws, specialBetaTorsorData,
    BetaTorsor.phiOne, BetaTorsor.phiTwo, specialTauHalfPlane_coe,
    sub_eq_add_neg, add_assoc]

private theorem boundedAtImInfty_iff_exists_strict_height {f : ℍ → ℂ} :
    IsBoundedAtImInfty f ↔ ∃ Y M : ℝ, ∀ z : ℍ, Y < z.im → ‖f z‖ ≤ M := by
  constructor
  · intro hf
    obtain ⟨M, Y, hM⟩ := isBoundedAtImInfty_iff.mp hf
    exact ⟨Y, M, fun z hz => hM z hz.le⟩
  · rintro ⟨Y, M, hM⟩
    apply isBoundedAtImInfty_iff.mpr
    exact ⟨M, Y + 1, fun z hz => hM z (by linarith)⟩

/-- The actual torsor solution predicate is exactly holomorphicity, the
literal two affine equations, and the original bounded-cusp condition. -/
theorem specialBetaTorsorData_isSolution_iff (β : ℍ → ℂ) :
    specialBetaTorsorData.IsSolution β ↔
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β ∧
      (∀ z : ℍ, β (generatorOneSL • z) =
        β z + 2 - 6 * (1 - specialMu z) ^ 2 / specialTau z) ∧
      (∀ z : ℍ, β (generatorTwoSL • z) =
        β z - 3 - 6 * specialMu z ^ 2 / specialTau z) ∧
      IsBoundedAtImInfty (fun z => β z + specialTau z) := by
  constructor
  · intro hβ
    have hg := (specialBetaTorsorData_generatorLaws_iff β).mp hβ.generators
    refine ⟨hβ.holomorphic, hg.1, hg.2, ?_⟩
    apply boundedAtImInfty_iff_exists_strict_height.mpr
    simpa only [specialBetaTorsorData, specialTauHalfPlane_coe] using hβ.cusp_bounded
  · rintro ⟨hβ, hβ₁, hβ₂, hb⟩
    refine ⟨hβ, (specialBetaTorsorData_generatorLaws_iff β).mpr ⟨hβ₁, hβ₂⟩, ?_⟩
    simpa only [specialBetaTorsorData, specialTauHalfPlane_coe] using
      boundedAtImInfty_iff_exists_strict_height.mp hb

/-- The actual globally admissible beta constructed earlier is a solution
of its actual torsor, with bounded beta plus tau at the cusp. -/
theorem specialBeta_isSolution : specialBetaTorsorData.IsSolution specialBeta := by
  apply (specialBetaTorsorData_isSolution_iff specialBeta).mpr
  exact ⟨specialBeta_holomorphic, fun z => (specialPeriods_generator₁ z).2.2,
    fun z => (specialPeriods_generator₂ z).2.2, specialBeta_add_tau_cusp.bounded⟩

/-- **Unconditional beta classification.** For the constructed special
tau and mu, every bounded-cusp holomorphic beta satisfying the two original
affine equations is a constant translate of the constructed special beta,
and every such translate satisfies all these conditions. -/
theorem specialBeta_solution_iff_eq_add_const (β : ℍ → ℂ) :
    (ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β ∧
      (∀ z : ℍ, β (generatorOneSL • z) =
        β z + 2 - 6 * (1 - specialMu z) ^ 2 / specialTau z) ∧
      (∀ z : ℍ, β (generatorTwoSL • z) =
        β z - 3 - 6 * specialMu z ^ 2 / specialTau z) ∧
      IsBoundedAtImInfty (fun z => β z + specialTau z)) ↔
      ∃ c : ℂ, β = fun z => specialBeta z + c := by
  rw [← specialBetaTorsorData_isSolution_iff]
  exact specialBetaTorsorData.solution_iff_eq_add_const triangleSphereUniformization
    triangleSphereUniformization_cusp specialBeta_isSolution β

/-- Distinct constants give distinct beta functions. -/
theorem specialBeta_add_const_injective :
    Function.Injective (fun c : ℂ => fun z : ℍ => specialBeta z + c) := by
  intro c d h
  exact add_left_cancel (congrFun h UpperHalfPlane.I)

/-- The additive constant in the complete beta family is unique. -/
theorem specialBeta_existsUnique_add_const {β : ℍ → ℂ}
    (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β)
    (hβ₁ : ∀ z : ℍ, β (generatorOneSL • z) =
      β z + 2 - 6 * (1 - specialMu z) ^ 2 / specialTau z)
    (hβ₂ : ∀ z : ℍ, β (generatorTwoSL • z) =
      β z - 3 - 6 * specialMu z ^ 2 / specialTau z)
    (hb : IsBoundedAtImInfty (fun z => β z + specialTau z)) :
    ∃! c : ℂ, β = fun z => specialBeta z + c := by
  obtain ⟨c, hc⟩ := (specialBeta_solution_iff_eq_add_const β).mp ⟨hβ, hβ₁, hβ₂, hb⟩
  exact ⟨c, hc, fun d hd => specialBeta_add_const_injective (hd.symm.trans hc)⟩

end Wikipedia.HopfProblem.SpecialPeriods
