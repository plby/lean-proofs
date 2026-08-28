import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! # Smooth Euclidean partial derivatives in a manifold-parameter family -/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {B H M V E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ContMDiffAt.fderiv_parameter {F : M → V → E} {g : M → V} {p : M}
    (hF : ContMDiffAt (I.prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ (Function.uncurry F) (p, g p))
    (hg : ContMDiffAt I 𝓘(ℝ, V) ∞ g p) :
    ContMDiffAt I 𝓘(ℝ, V →L[ℝ] E) ∞ (fun x ↦ fderiv ℝ (F x) (g x)) p := by
  have hd := hF.mfderiv F g hg (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  let D : M → V →L[ℝ] E := fun x ↦ mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (F x) (g x)
  have he : inTangentCoordinates 𝓘(ℝ, V) 𝓘(ℝ, E) g (fun x ↦ F x (g x)) D p = D :=
    inTangentCoordinates_model_space (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, E)) g
      (fun x ↦ F x (g x)) D p
  change ContMDiffAt I 𝓘(ℝ, V →L[ℝ] E) ∞
    (inTangentCoordinates 𝓘(ℝ, V) 𝓘(ℝ, E) g (fun x ↦ F x (g x)) D p) p at hd
  rw [he] at hd
  have hD : D = (fun x ↦ fderiv ℝ (F x) (g x)) := funext (fun _ ↦ mfderiv_eq_fderiv)
  rw [hD] at hd
  exact hd

end NoExoticSixSphere
