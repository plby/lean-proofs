import Wikipedia.HopfProblem.SmoothMorseLemmaSignedCoordinates
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Smooth signed coordinates for a nondegenerate Hessian

The signed linear coordinates are a genuine global diffeomorphism of the
normed model spaces, fixing the origin and preserving the half-Hessian formula.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The signed Hessian coordinates, viewed as an actual smooth diffeomorphism. -/
theorem exists_signed_diffeomorph (H : Bilinear E)
    (hH : ∀ x y, H x y = H y x) (hHbij : Function.Bijective H) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
      ∃ C : E ≃ₘ[ℝ] (Fin (Module.finrank ℝ E) → ℝ),
        C 0 = 0 ∧ ∀ x, (1 / 2 : ℝ) * H x x = ∑ i, w i * (C x i) ^ 2 := by
  obtain ⟨w, hw, C, hC⟩ := exists_signed_coordinates H hH hHbij
  exact ⟨w, hw, C.toDiffeomorph, C.map_zero, hC⟩

end Wikipedia.HopfProblem.SmoothMorseLemma
