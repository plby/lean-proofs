import Wikipedia.NoExoticSixSphere.AugmentedSurjection

/-!
# Adding several transverse equations to a surjective tangent differential

The transverse equation need not be scalar. Its surjectivity, vanishing
on the parametrized tangent space, and surjectivity of the remaining
differential along that tangent space imply surjectivity of the full pair.
No vanishing of the second differential on transverse vectors is required.
-/

namespace NoExoticSixSphere

variable {E F G K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

theorem surjective_vector_augmented_differential
    (L : E →L[ℝ] G) (D : E →L[ℝ] F) (T : K →L[ℝ] E)
    (hL : Function.Surjective L) (hLT : ∀ v, L (T v) = 0)
    (hDT : Function.Surjective (D.comp T)) : Function.Surjective (L.prod D) := by
  rintro ⟨t, w⟩
  obtain ⟨u, hu⟩ := hL t
  obtain ⟨v, hv⟩ := hDT (w - D u)
  refine ⟨u + T v, Prod.ext ?_ ?_⟩
  · change L (u + T v) = t
    rw [map_add, hu, hLT, add_zero]
  · change D (u + T v) = w
    change D (T v) = w - D u at hv
    rw [map_add, hv, ← add_sub_assoc, add_sub_cancel_left]

end NoExoticSixSphere
