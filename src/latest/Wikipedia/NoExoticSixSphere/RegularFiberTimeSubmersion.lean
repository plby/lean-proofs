import Wikipedia.NoExoticSixSphere.RegularFiberDifferential

/-!
# Time submersions on the native regular fiber

A tangent lift in the kernel of the original ambient map is a genuine
tangent vector of its constructed regular fiber. The actual chain rule
then transports a prescribed time derivative. This criterion retains
the original map and native atlas throughout.
-/

noncomputable section

open Function Module
open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  (f : C(M, N)) (hf : ContMDiff I J ∞ f) (b : N)
  (hreg : ∀ x, f x = b → Surjective (mfderiv I J f x))
  (k : ℕ) (hd : finrank ℝ B = finrank ℝ C + k)

theorem regularFiber_surjective_mfderiv_time (t : M → ℝ)
    (ht : ContMDiff I 𝓘(ℝ, ℝ) ∞ t) (x : {x : M // f x = b})
    (hlift : ∀ z : ℝ, ∃ v : B, mfderiv I J f x.val v = 0 ∧
      mfderiv I 𝓘(ℝ, ℝ) t x.val v = z) :
    letI := regularFiberAtlas f hf b hreg k hd;
    Surjective (mfderiv (𝓡 k) 𝓘(ℝ, ℝ) (t ∘ Subtype.val : {x : M // f x = b} → ℝ) x) := by
  let := regularFiberAtlas f hf b hreg k hd
  let A : EuclideanSpace ℝ (Fin k) →L[ℝ] B :=
    mfderiv (𝓡 k) I (Subtype.val : {x : M // f x = b} → M) x
  let D : B →L[ℝ] C := mfderiv I J f x.val
  let L : B →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) t x.val
  let R : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ :=
    mfderiv (𝓡 k) 𝓘(ℝ, ℝ) (t ∘ Subtype.val : {x : M // f x = b} → ℝ) x
  have hA : A.range = D.ker := regularFiber_range_inclusion_eq_kernel f hf b hreg k hd x
  have hR : R = L.comp A := mfderiv_comp x (ht.mdifferentiableAt (by simp))
    ((regularFiber_contMDiff_subtype_val f hf b hreg k hd).mdifferentiableAt (by simp))
  change Surjective R
  intro z
  obtain ⟨v, hv, htv⟩ := hlift z
  have hmem : v ∈ A.range := by
    rw [hA]
    exact hv
  obtain ⟨u, hu⟩ := hmem
  change A u = v at hu
  refine ⟨u, ?_⟩
  rw [hR, ContinuousLinearMap.comp_apply, hu]
  exact htv

end NoExoticSixSphere
