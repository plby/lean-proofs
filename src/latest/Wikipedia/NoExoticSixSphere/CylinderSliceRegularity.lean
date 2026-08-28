import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# A regular time slice makes the cylinder map regular there

The derivative of the slice is the cylinder derivative composed with the
time-slice inclusion. Surjectivity of the slice derivative therefore implies
surjectivity of the cylinder derivative, without a hypothesis on its time
derivative or a regularity assumption elsewhere in the cylinder.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]

theorem mfderiv_cylinder_surjective_of_slice (F : ℝ × M → N) (f : M → N)
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod I) J ∞ F) (t : ℝ)
    (hslice : ∀ y, F (t, y) = f y) (x : M)
    (hreg : Function.Surjective (mfderiv I J f x)) :
    Function.Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod I) J F (t, x)) := by
  let j : M → ℝ × M := fun y ↦ (t, y)
  have hj : ContMDiff I ((𝓘(ℝ, ℝ)).prod I) ∞ j :=
    contMDiff_const.prodMk contMDiff_id
  have hc := mfderiv_comp x (hF.mdifferentiable (by simp) (t, x))
    (hj.mdifferentiable (by simp) x)
  have heq : F ∘ j = f := funext hslice
  rw [heq] at hc
  intro v
  obtain ⟨w, hw⟩ := hreg v
  refine ⟨(mfderiv I ((𝓘(ℝ, ℝ)).prod I) j x) w, ?_⟩
  exact (congrArg (fun L : B →L[ℝ] C ↦ L w) hc).symm.trans hw

end NoExoticSixSphere
