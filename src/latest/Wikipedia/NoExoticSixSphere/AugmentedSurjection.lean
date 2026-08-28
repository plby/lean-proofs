import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Adding one transverse equation to a surjective tangent differential

If a scalar equation vanishes on a parametrized tangent space, another
differential is surjective there, and the scalar differential is nonzero
on some transverse vector, their product is surjective.
-/

namespace NoExoticSixSphere

variable {E F K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

theorem surjective_augmented_differential
    (L : E →L[ℝ] ℝ) (D : E →L[ℝ] F) (T : K →L[ℝ] E)
    (hLT : ∀ v, L (T v) = 0) (hDT : Function.Surjective (D.comp T))
    (u : E) (hu : L u ≠ 0) : Function.Surjective (L.prod D) := by
  rintro ⟨t, w⟩
  obtain ⟨v, hv⟩ := hDT (w - (t / L u) • D u)
  refine ⟨(t / L u) • u + T v, Prod.ext ?_ ?_⟩
  · change L ((t / L u) • u + T v) = t
    rw [map_add, map_smul, hLT, add_zero]
    exact div_mul_cancel₀ t hu
  · change D ((t / L u) • u + T v) = w
    change D (T v) = w - (t / L u) • D u at hv
    rw [map_add, map_smul, hv, ← add_sub_assoc, add_sub_cancel_left]

end NoExoticSixSphere
