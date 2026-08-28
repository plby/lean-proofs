import Wikipedia.NoExoticSixSphere.RegularFiberManifold

/-!
# Tangent kernels for manifold-valued regular fibers

For the constructed atlas on the original fiber, the image of the inclusion
differential is the kernel of the original map's differential. This statement
does not replace the original map by an unrestricted chart-coordinate function.
-/

open scoped Manifold ContDiff
open Module

namespace NoExoticSixSphere

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  (f : ContinuousMap M N) (hf : ContMDiff I J ∞ f) (b : N)
  (hreg : ∀ x, f x = b → Function.Surjective (mfderiv I J f x))
  (k : ℕ) (hd : finrank ℝ B = finrank ℝ C + k)

theorem regularFiber_differential_comp_inclusion (x : {x : M // f x = b}) :
    letI := regularFiberAtlas f hf b hreg k hd;
    (mfderiv I J f x.val).comp
      (mfderiv (𝓡 k) I (Subtype.val : {x : M // f x = b} → M) x) = 0 := by
  let := regularFiberAtlas f hf b hreg k hd
  have h := mfderiv_comp x (hf.mdifferentiable (by simp) x.val)
    ((regularFiber_contMDiff_subtype_val f hf b hreg k hd).mdifferentiable (by simp) x)
  have heq : f ∘ (Subtype.val : {x : M // f x = b} → M) = fun _ ↦ b :=
    funext (fun z ↦ z.property)
  rw [heq, mfderiv_const] at h
  exact h.symm

theorem regularFiber_range_inclusion_le_kernel (x : {x : M // f x = b}) :
    letI := regularFiberAtlas f hf b hreg k hd;
    (mfderiv (𝓡 k) I (Subtype.val : {x : M // f x = b} → M) x).range ≤
      (mfderiv I J f x.val).ker := by
  let := regularFiberAtlas f hf b hreg k hd
  rintro v ⟨w, rfl⟩
  change (mfderiv I J f x.val)
    ((mfderiv (𝓡 k) I (Subtype.val : {x : M // f x = b} → M) x) w) = 0
  exact congrArg (fun L : EuclideanSpace ℝ (Fin k) →L[ℝ] C ↦ L w)
    (regularFiber_differential_comp_inclusion f hf b hreg k hd x)

theorem regularFiber_range_inclusion_eq_kernel (x : {x : M // f x = b}) :
    letI := regularFiberAtlas f hf b hreg k hd;
    (mfderiv (𝓡 k) I (Subtype.val : {x : M // f x = b} → M) x).range =
      (mfderiv I J f x.val).ker := by
  let := regularFiberAtlas f hf b hreg k hd
  let : FiniteDimensional ℝ (TangentSpace I x.val) := inferInstanceAs (FiniteDimensional ℝ B)
  let : FiniteDimensional ℝ (TangentSpace (𝓡 k) x) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin k)))
  apply Submodule.eq_of_le_of_finrank_eq
    (regularFiber_range_inclusion_le_kernel f hf b hreg k hd x)
  rw [LinearMap.finrank_range_of_inj
    (regularFiber_injective_mfderiv_subtype_val f hf b hreg k hd x)]
  let D : B →L[ℝ] C := mfderiv I J f x.val
  change finrank ℝ (EuclideanSpace ℝ (Fin k)) = finrank ℝ D.ker
  rw [finrank_euclideanSpace_fin]
  exact (finrank_kernel_of_surjective D (hreg x.val x.property) k hd).symm

end NoExoticSixSphere
