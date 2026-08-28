import Wikipedia.NoExoticSixSphere.RegularFiberDifferential
import Wikipedia.NoExoticSixSphere.Definitions

/-!
# Regular sphere-valued fibers and compact homotopy slabs

A regular fiber of a map from the ambient sphere to the normal sphere has
dimension six. With an extra real time variable it has dimension seven.
Closed bounded time slabs are compact. No regular homotopy, boundary atlas,
or collar is assumed to follow merely from these assertions.
-/

open scoped Manifold ContDiff
open Set Module

namespace NoExoticSixSphere

theorem exists_sixDimensionalSphereFiber (N : ℕ) (hN : 6 ≤ N)
    (f : C(Sphere N, Sphere (N - 6)))
    (hf : ContMDiff (𝓡 N) (𝓡 (N - 6)) ∞ f) (b : Sphere (N - 6))
    (hreg : ∀ x, f x = b → Function.Surjective (mfderiv (𝓡 N) (𝓡 (N - 6)) f x)) :
    ∃ c : ChartedSpace (EuclideanSpace ℝ (Fin 6)) {x : Sphere N // f x = b},
      letI := c;
      IsManifold (𝓡 6) ∞ {x : Sphere N // f x = b} ∧
      ContMDiff (𝓡 6) (𝓡 N) ∞ (Subtype.val : {x : Sphere N // f x = b} → Sphere N) := by
  apply exists_regularFiberManifold f hf b hreg 6
  simp only [finrank_euclideanSpace_fin]
  omega

theorem exists_sevenDimensionalSphereCylinderFiber (N : ℕ) (hN : 6 ≤ N)
    (f : C(ℝ × Sphere N, Sphere (N - 6)))
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 (N - 6)) ∞ f)
    (b : Sphere (N - 6))
    (hreg : ∀ x, f x = b → Function.Surjective
      (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 (N - 6)) f x)) :
    ∃ c : ChartedSpace (EuclideanSpace ℝ (Fin 7)) {x : ℝ × Sphere N // f x = b},
      letI := c;
      IsManifold (𝓡 7) ∞ {x : ℝ × Sphere N // f x = b} ∧
      ContMDiff (𝓡 7) ((𝓘(ℝ, ℝ)).prod (𝓡 N)) ∞
        (Subtype.val : {x : ℝ × Sphere N // f x = b} → ℝ × Sphere N) := by
  apply exists_regularFiberManifold f hf b hreg 7
  simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
  omega

theorem isCompact_sphereCylinderFiber_slab (N : ℕ)
    (f : C(ℝ × Sphere N, Sphere (N - 6))) (b : Sphere (N - 6)) (s t : ℝ) :
    IsCompact {x : {x : ℝ × Sphere N // f x = b} | x.val.1 ∈ Icc s t} := by
  have hclosed : IsClosed {x | f x = b} := isClosed_eq f.continuous continuous_const
  have he := Topology.IsClosedEmbedding.subtypeVal hclosed
  have hc := (isCompact_Icc : IsCompact (Icc s t)).prod
    (isCompact_univ : IsCompact (univ : Set (Sphere N)))
  convert he.isCompact_preimage hc using 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage, mem_prod, mem_univ, and_true]

end NoExoticSixSphere
