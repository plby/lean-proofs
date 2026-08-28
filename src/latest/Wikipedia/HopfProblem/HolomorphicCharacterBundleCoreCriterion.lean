import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreSections
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreTrivialization

/-!
# Analytic triviality as a proved cocycle criterion

For the general cocycle bundle, compatible nowhere-zero holomorphic local
coefficients exist exactly when the actual bundle admits a global analytic
linear trivialization. Equivalently, the transition functions are a
holomorphic coboundary. The coboundary condition is a conclusion/criterion
here, never an assumption in the construction of the bundle.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle.TransitionData

variable {M ι : Type*} [TopologicalSpace M] (A : TransitionData M ι)
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] (I : ModelWithCorners ℂ E H) [A.IsHolomorphic I]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

theorem exists_compatible_nonzero_localCoefficients_iff_analyticTrivialization :
    (∃ f : ι → M → ℂ, A.IsCompatible f ∧
      (∀ i, ContMDiffOn I I₁ ω (f i) (A.baseSet i)) ∧
      ∀ i x, x ∈ A.baseSet i → f i x ≠ 0) ↔
        Nonempty (A.AnalyticTrivialization I) := by
  rw [← A.exists_holomorphic_nonzero_section_iff_analyticTrivialization I]
  constructor
  · rintro ⟨f, hf, hhol, hne⟩
    exact ⟨A.sectionFromLocal f, A.sectionFromLocal_holomorphic I f hf hhol,
      A.sectionFromLocal_ne_zero f hne⟩
  · rintro ⟨s, hs, hne⟩
    exact ⟨A.localCoefficient s, A.localCoefficient_compatible s,
      A.localCoefficient_holomorphic I s hs,
      fun i x _ => A.localCoefficient_ne_zero s hne i x⟩

theorem exists_holomorphic_coboundary_iff_analyticTrivialization :
    (∃ f : ι → M → ℂ,
      (∀ i, ContMDiffOn I I₁ ω (f i) (A.baseSet i)) ∧
      (∀ i x, x ∈ A.baseSet i → f i x ≠ 0) ∧
      ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
        (A.transition i j x : ℂ) = f j x / f i x) ↔
          Nonempty (A.AnalyticTrivialization I) := by
  rw [← A.exists_compatible_nonzero_localCoefficients_iff_analyticTrivialization I]
  constructor
  · rintro ⟨f, hhol, hne, htrans⟩
    refine ⟨f, ?_, hhol, hne⟩
    intro i j x hx
    rw [htrans i j x hx]
    exact div_mul_cancel₀ _ (hne i x hx.1)
  · rintro ⟨f, hf, hhol, hne⟩
    refine ⟨f, hhol, hne, ?_⟩
    intro i j x hx
    exact (eq_div_iff (hne i x hx.1)).mpr (hf i j x hx)

end Wikipedia.HopfProblem.HolomorphicCharacterBundle.TransitionData
