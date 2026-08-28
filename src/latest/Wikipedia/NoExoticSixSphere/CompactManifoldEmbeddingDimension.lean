import Wikipedia.NoExoticSixSphere.GenericLinearEmbedding

/-!
# A proved ambient-dimension bound for compact smooth embeddings

Project the actual partition-of-unity embedding by a generic linear map.
Every target dimension strictly greater than twice the manifold dimension
is available, with the original smooth atlas and injective differential.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def EuclideanEmbedding.compress [CompactSpace M]
    (e : EuclideanEmbedding n M) (q : ℕ) (hq : 2 * n < q) : EuclideanEmbedding n M :=
  LinearProjection.embedding e
    (Classical.choose (LinearProjection.exists_good_near e hq 0 zero_lt_one))
    (Classical.choose_spec (LinearProjection.exists_good_near e hq 0 zero_lt_one)).1

theorem EuclideanEmbedding.compress_dimension [CompactSpace M]
    (e : EuclideanEmbedding n M) (q : ℕ) (hq : 2 * n < q) :
    (e.compress q hq).ambientDimension = q := rfl

theorem EuclideanEmbedding.exists_linear_compression [CompactSpace M]
    (e : EuclideanEmbedding n M) (q : ℕ) (hq : 2 * n < q) :
    ∃ L : EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] EuclideanSpace ℝ (Fin q),
      ContMDiff (𝓡 n) (𝓡 q) ∞ (L ∘ e.toFun) ∧
      Topology.IsClosedEmbedding (L ∘ e.toFun) ∧
      ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 q) (L ∘ e.toFun) x) := by
  obtain ⟨L, hL, _⟩ := LinearProjection.exists_good_near e hq 0 zero_lt_one
  let e' := LinearProjection.embedding e L hL
  exact ⟨L, e'.smooth, e'.closedEmbedding, e'.injective_mfderiv⟩

theorem exists_euclideanEmbedding_dimension [CompactSpace M] [T2Space M]
    (q : ℕ) (hq : 2 * n < q) :
    ∃ e : EuclideanEmbedding n M, e.ambientDimension = q := by
  obtain ⟨N, f, hs, he, hi⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  let e₀ : EuclideanEmbedding n M := ⟨N, f, hs, he, hi⟩
  obtain ⟨L, hL, _⟩ := LinearProjection.exists_good_near e₀ hq 0 zero_lt_one
  exact ⟨LinearProjection.embedding e₀ L hL, rfl⟩

theorem exists_euclideanEmbedding_twice_add_one [CompactSpace M] [T2Space M] :
    ∃ e : EuclideanEmbedding n M, e.ambientDimension = 2 * n + 1 :=
  exists_euclideanEmbedding_dimension (2 * n + 1) (Nat.lt_succ_self _)

end NoExoticSixSphere
