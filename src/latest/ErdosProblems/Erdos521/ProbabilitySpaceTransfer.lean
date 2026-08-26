/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The conclusions hold on every probability space carrying independent fair signs.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Oscillation

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem ae_of_independent_signs {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ n, HasLaw (X n) signLaw μ)
    (hind : iIndepFun X μ) {P : (ℕ → ℝ) → Prop} (hP : ∀ᵐ ε ∂sequenceLaw, P ε) :
    ∀ᵐ ω ∂μ, P (fun n ↦ X n ω) := by
  have hmeas : AEMeasurable (fun ω n ↦ X n ω) μ :=
    aemeasurable_pi_iff.mpr (fun n ↦ (hX n).aemeasurable)
  have hjoint : HasLaw (fun ω n ↦ X n ω) sequenceLaw μ := hind.hasLaw_infinitePi hX hmeas
  apply ae_of_ae_map hjoint.aemeasurable
  rwa [hjoint.map_eq]

theorem ae_rootCount_oscillation_of_independent_signs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, HasLaw (X n) signLaw μ) (hind : iIndepFun X μ) :
    ∀ᵐ ω ∂μ,
      liminf (fun n ↦ (normalizedRootCount (fun k ↦ X k ω) n : EReal)) atTop = (1 / Real.pi : ℝ) ∧
      (2 / Real.pi : ℝ) ≤ limsup (fun n ↦ (normalizedRootCount (fun k ↦ X k ω) n : EReal)) atTop :=
  ae_of_independent_signs μ X hX hind ae_rootCount_oscillation

theorem ae_not_tendsto_rootCount_of_independent_signs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, HasLaw (X n) signLaw μ) (hind : iIndepFun X μ) :
    ∀ᵐ ω ∂μ, ∀ L : ℝ, ¬ Tendsto (normalizedRootCount (fun k ↦ X k ω)) atTop (𝓝 L) :=
  ae_of_independent_signs μ X hX hind ae_not_tendsto_normalizedRootCount

end Erdos521
