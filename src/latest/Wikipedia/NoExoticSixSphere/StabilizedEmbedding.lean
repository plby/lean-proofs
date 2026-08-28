import Wikipedia.NoExoticSixSphere.NormalNullhomotopy

/-!
# Stabilizing an actual Euclidean embedding

Adding zero coordinates preserves smoothness, injectivity and the injective
differential. For compact manifolds it remains a closed embedding. The normal
rank grows by the number of added coordinates, giving the needed access to
arbitrarily high codimension without assuming a stable normal frame.
-/

open scoped Manifold ContDiff
open Function

namespace NoExoticSixSphere

/-- Include Euclidean space into a larger Euclidean space by adding zero coordinates. -/
noncomputable def appendZeroMap (N k : ℕ) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin (N + k)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := k)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin k)))

/-- Adding zero coordinates is injective. -/
theorem appendZeroMap_injective (N k : ℕ) : Injective (appendZeroMap N k) := by
  have hinl : Injective (ContinuousLinearMap.inl ℝ
      (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin k))) :=
    fun _ _ h ↦ congrArg Prod.fst h
  exact (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := k)).symm.injective.comp hinl

namespace EuclideanEmbedding

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (e : EuclideanEmbedding n M)

/-- The given embedding, with `k` extra zero coordinates. -/
noncomputable def stabilizedMap (k : ℕ) : M → EuclideanSpace ℝ (Fin (e.ambientDimension + k)) :=
  appendZeroMap e.ambientDimension k ∘ e.toFun

/-- The stabilized map is smooth in the original smooth atlas. -/
theorem contMDiff_stabilizedMap (k : ℕ) :
    ContMDiff (𝓡 n) (𝓡 (e.ambientDimension + k)) ∞ (e.stabilizedMap k) :=
  (appendZeroMap e.ambientDimension k).contDiff.comp_contMDiff e.smooth

/-- Stabilization does not destroy the injectivity of the differential. -/
theorem injective_mfderiv_stabilizedMap (k : ℕ) (x : M) :
    Injective (mfderiv (𝓡 n) (𝓡 (e.ambientDimension + k)) (e.stabilizedMap k) x) := by
  let A := appendZeroMap e.ambientDimension k
  have hA : MDifferentiableAt (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension + k)) A (e.toFun x) :=
    A.differentiableAt.mdifferentiableAt
  change Injective (mfderiv (𝓡 n) (𝓡 (e.ambientDimension + k)) (A ∘ e.toFun) x)
  rw [mfderiv_comp x hA (e.smooth.mdifferentiable (by simp) x), mfderiv_eq_fderiv, A.fderiv]
  exact (appendZeroMap_injective e.ambientDimension k).comp (e.injective_mfderiv x)

/-- The stabilized map is still a genuine closed smooth embedding of a compact manifold. -/
noncomputable def stabilize [CompactSpace M] (k : ℕ) : EuclideanEmbedding n M where
  ambientDimension := e.ambientDimension + k
  toFun := e.stabilizedMap k
  smooth := e.contMDiff_stabilizedMap k
  closedEmbedding := (e.contMDiff_stabilizedMap k).continuous.isClosedEmbedding
    ((appendZeroMap_injective e.ambientDimension k).comp e.closedEmbedding.injective)
  injective_mfderiv := e.injective_mfderiv_stabilizedMap k

/-- The normal rank increases by exactly the number of added coordinates. -/
theorem finrank_stabilizedNormalSpace [CompactSpace M] (k : ℕ) (x : M) :
    Module.finrank ℝ ((e.stabilize k).NormalSpace x) = (e.ambientDimension - n) + k := by
  rw [(e.stabilize k).finrank_normalSpace]
  change e.ambientDimension + k - n = e.ambientDimension - n + k
  have h := e.dimension_le_ambient x
  omega

/-- Any desired lower bound on the actual normal rank is attained by stabilization. -/
theorem le_finrank_stabilizedNormalSpace [CompactSpace M] (k : ℕ) (x : M) :
    k ≤ Module.finrank ℝ ((e.stabilize k).NormalSpace x) := by
  rw [e.finrank_stabilizedNormalSpace]
  exact Nat.le_add_left _ _

end EuclideanEmbedding

/-- Every smooth topological sphere has actual closed smooth embeddings of arbitrarily large
normal rank. This does not assert that their normal bundles are trivial. -/
theorem exists_highCodimensionEmbedding {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (h : M ≃ₜ Sphere n) (r : ℕ) :
    ∃ e : EuclideanEmbedding n M, r ≤ e.ambientDimension - n := by
  let : CompactSpace M := compactSpace_of_homeomorph h
  obtain ⟨e⟩ := nonempty_euclideanEmbedding_of_homeomorph h
  let v : Sphere n := Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one)
  have hn := e.dimension_le_ambient (h.symm v)
  refine ⟨e.stabilize r, ?_⟩
  change r ≤ e.ambientDimension + r - n
  omega

end NoExoticSixSphere
