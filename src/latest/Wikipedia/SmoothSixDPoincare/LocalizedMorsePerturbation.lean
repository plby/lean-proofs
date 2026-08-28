import Wikipedia.SmoothSixDPoincare.MorseCompactStability
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Localized perturbations preserving previously nondegenerate critical points

A smooth cutoff localizes the linear perturbation. On its unit plateau the
perturbation is Morse by the regular-value argument; on a previously treated
compact set it remains Morse by openness in the perturbation parameter.
-/

noncomputable section

open Set Metric MeasureTheory MeasureTheory.Measure
open scoped Topology ContDiff

namespace Wikipedia.SmoothSixDPoincare.MorsePerturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def cutoffPerturbation (f φ : E → ℝ) (a x : E) : ℝ :=
  f x - φ x * dualEquiv a x

theorem contDiff_cutoffPerturbation {f φ : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (Function.uncurry (cutoffPerturbation f φ)) :=
  (hf.comp contDiff_snd).sub ((hφ.comp contDiff_snd).mul
    ((dualEquiv.contDiff.comp contDiff_fst).clm_apply contDiff_snd))

@[simp] theorem cutoffPerturbation_zero (f φ : E → ℝ) : cutoffPerturbation f φ 0 = f := by
  funext x
  simp [cutoffPerturbation]

theorem cutoffPerturbation_eq_of_zero (f φ : E → ℝ) (a x : E) (hx : φ x = 0) :
    cutoffPerturbation f φ a x = f x := by
  simp [cutoffPerturbation, hx]

theorem cutoffPerturbation_eventuallyEq {f φ : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hφ : EqOn φ (fun _ => 1) U) (a : E) {x : E} (hx : x ∈ U) :
    cutoffPerturbation f φ a =ᶠ[𝓝 x] linearPerturbation f a := by
  filter_upwards [hU.mem_nhds hx] with y hy
  simp [cutoffPerturbation, linearPerturbation, hφ hy]

theorem isMorseOn_cutoffPerturbation {f φ : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {U : Set E} (hU : IsOpen U) (hφ : EqOn φ (fun _ => 1) U) {a : E}
    (ha : a ∈ RegularValues.regularValues (coordinateGradient f)) :
    IsMorseOn (cutoffPerturbation f φ a) U := by
  intro x hx hcrit
  have heq := cutoffPerturbation_eventuallyEq (f := f) hU hφ a hx
  have hfirst := heq.fderiv_eq (𝕜 := ℝ)
  have hsecond := (heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  rw [hsecond]
  exact isMorse_of_regularValue hf ha x (hfirst.symm.trans hcrit)

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]

include μ in
/-- A localized perturbation can add a new Morse region while preserving a compact old one. -/
theorem exists_localized_morse_perturbation {f φ : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ)
    {U K : Set E} (hU : IsOpen U) (hφU : EqOn φ (fun _ => 1) U)
    (hK : IsCompact K) (hfK : IsMorseOn f K) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : E, ‖a‖ < ε ∧ IsMorseOn (cutoffPerturbation f φ a) (U ∪ K) ∧
      ∀ x, φ x = 0 → cutoffPerturbation f φ a x = f x := by
  let V : Set E := {a | IsMorseOn (cutoffPerturbation f φ a) K}
  have hV : IsOpen V := isOpen_isMorseOn (contDiff_cutoffPerturbation hf hφ) hK
  have hV₀ : (0 : E) ∈ V := by simpa [V] using hfK
  have hd := RegularValues.dense_regularValues μ
    ((contDiff_coordinateGradient hf).differentiable (by simp))
  obtain ⟨a, ha, haV, haε⟩ := hd.exists_mem_open (hV.inter isOpen_ball)
    ⟨0, hV₀, mem_ball_self hε⟩
  refine ⟨a, mem_ball_zero_iff.mp haε, ?_, fun x hx => cutoffPerturbation_eq_of_zero f φ a x hx⟩
  intro x hx hcrit
  rcases hx with hx | hx
  · exact isMorseOn_cutoffPerturbation hf hU hφU ha x hx hcrit
  · exact haV x hx hcrit

end Wikipedia.SmoothSixDPoincare.MorsePerturbation
