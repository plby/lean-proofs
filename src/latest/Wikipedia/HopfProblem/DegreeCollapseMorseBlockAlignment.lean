import Wikipedia.HopfProblem.DegreeCollapseNativeFieldChartChange
import Wikipedia.SmoothSixDPoincare.MorseModelFlow
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Aligning a Morse ray without changing the native field

A genuine orthogonal reflection carries a positive multiple of any
nonzero reference vector to any other nonzero vector in the same block.
Independent linear changes within the two Morse blocks commute with the
descent field and its complete flow. Their native coordinate changes
therefore retain the original field exactly.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Any two independent changes inside the rate blocks commute with descent. -/
theorem morse_block_change_descent (A : N ≃L[ℝ] N) (B : P ≃L[ℝ] P) (z : N × P) :
    (A.prodCongr B) (MorseHandle.descent z) = MorseHandle.descent ((A.prodCongr B) z) := by
  apply Prod.ext
  · rfl
  · change B (-z.2) = -B z.2
    exact B.map_neg _

/-- The complete model flow has the same time parameter after the block change. -/
theorem morse_block_change_flow (A : N ≃L[ℝ] N) (B : P ≃L[ℝ] P) (t : ℝ) (z : N × P) :
    (A.prodCongr B) (MorseHandle.descentFlow t z) =
      MorseHandle.descentFlow t ((A.prodCongr B) z) := by
  apply Prod.ext
  · change A (Real.exp t • z.1) = Real.exp t • A z.1
    exact A.map_smul _ _
  · change B (Real.exp (-t) • z.2) = Real.exp (-t) • B z.2
    exact B.map_smul _ _

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Absorbing these block changes into the actual native coordinates changes no field value. -/
theorem native_morse_field_block_change
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, N × P) M (N × P) ∞)
    (A : N ≃L[ℝ] N) (B : P ≃L[ℝ] P) {x : M} (hx : x ∈ e.source) :
    FlowConstruction.partialChartField
        (e.trans (A.prodCongr B).toDiffeomorph.toPartialDiffeomorph) MorseHandle.descent x =
      FlowConstruction.partialChartField e MorseHandle.descent x :=
  partialChartField_linear_change e (A.prodCongr B) MorseHandle.descent
    (morse_block_change_descent A B) hx

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]

/-- A constructed reflection aligns any two nonzero rays, with positive scale. -/
theorem exists_positive_ray_alignment {u v : D} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ (r : ℝ) (A : D ≃ₗᵢ[ℝ] D), 0 < r ∧ A (r • u) = v ∧
      ∀ s : ℝ, A ((s * r) • u) = s • v := by
  let r := ‖v‖ / ‖u‖
  have hr : 0 < r := div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hu)
  have hnorm : ‖r • u‖ = ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact div_mul_cancel₀ ‖v‖ (norm_ne_zero_iff.mpr hu)
  let A : D ≃ₗᵢ[ℝ] D := (ℝ ∙ (r • u - v))ᗮ.reflection
  have hA : A (r • u) = v := Submodule.reflection_sub hnorm
  refine ⟨r, A, hr, hA, ?_⟩
  intro s
  rw [← smul_smul, A.map_smul, hA]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
