import Wikipedia.NoExoticSixSphere.RegularLevelDifferential
import Wikipedia.NoExoticSixSphere.Definitions

/-!
# Seven-dimensional regular levels in the homotopy cylinder

For the dimensions used by a six-sphere collapse, a regular level in real
time times the ambient sphere has dimension seven. A closed bounded time
slab of a continuous level is compact. The boundary and collar structures,
and existence of a regular homotopy, are separate requirements.
-/

open scoped Manifold ContDiff
open Set Module

namespace NoExoticSixSphere

theorem exists_sevenDimensionalCylinderLevel (N : ℕ) (hN : 6 ≤ N)
    (f : ℝ × Sphere N → EuclideanSpace ℝ (Fin (N - 6)))
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 (N - 6)) ∞ f)
    (hreg : ∀ x, f x = 0 → Function.Surjective
      (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 (N - 6)) f x)) :
    ∃ c : ChartedSpace (EuclideanSpace ℝ (Fin 7)) {x : ℝ × Sphere N // f x = 0},
      letI := c;
      IsManifold (𝓡 7) ∞ {x : ℝ × Sphere N // f x = 0} ∧
      ContMDiff (𝓡 7) ((𝓘(ℝ, ℝ)).prod (𝓡 N)) ∞
        ((↑) : {x : ℝ × Sphere N // f x = 0} → ℝ × Sphere N) := by
  apply exists_regularLevelManifold isOpen_univ hf.contMDiffOn (subset_univ _) hreg 7
  simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
  omega

theorem isCompact_cylinderLevel_slab (N : ℕ)
    (f : ℝ × Sphere N → EuclideanSpace ℝ (Fin (N - 6))) (hf : Continuous f) (s t : ℝ) :
    IsCompact {x : {x : ℝ × Sphere N // f x = 0} | x.val.1 ∈ Icc s t} := by
  have hclosed : IsClosed {x | f x = 0} := isClosed_eq hf continuous_const
  have he := Topology.IsClosedEmbedding.subtypeVal hclosed
  have hc := (isCompact_Icc : IsCompact (Icc s t)).prod
    (isCompact_univ : IsCompact (univ : Set (Sphere N)))
  convert he.isCompact_preimage hc using 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage, mem_prod, mem_univ, and_true]

end NoExoticSixSphere
