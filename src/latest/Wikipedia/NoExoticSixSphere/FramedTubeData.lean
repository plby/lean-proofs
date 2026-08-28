import Wikipedia.NoExoticSixSphere.SmoothFramedTube

/-!
# A chosen framed tube with its actual radius and formula retained

The certificate includes the smooth partial diffeomorphism, its full source,
and its exact round-fiber formula. Choosing this certificate does not forget
which tube is used by the subsequent collapse construction.
-/

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (e : EuclideanEmbedding n M)
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)

structure FramedTubeData where
  radius : ℝ
  radius_pos : 0 < radius
  tube : PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension)
    (M × e.NormalModel) (EuclideanSpace ℝ (Fin e.ambientDimension)) ∞
  source_univ : tube.source = univ
  formula : ∀ p, tube p = e.toFun p.1 +
    a.ambient p.1 (OpenPartialHomeomorph.univBall (0 : e.NormalModel) radius p.2)

namespace FramedTubeData

variable {e a} (d : e.FramedTubeData a)

theorem isOpenEmbedding : IsOpenEmbedding d.tube :=
  d.tube.toOpenPartialHomeomorph.isOpenEmbedding d.source_univ

theorem tube_zero (m : M) : d.tube (m, 0) = e.toFun m := by
  rw [d.formula, OpenPartialHomeomorph.univBall_apply_zero, map_zero, add_zero]

theorem range_subset_target : range e.toFun ⊆ d.tube.target := by
  rintro _ ⟨m, rfl⟩
  rw [← d.tube_zero m]
  exact d.tube.map_source' (by rw [d.source_univ]; trivial)

end FramedTubeData

variable [IsManifold (𝓡 n) ∞ M] [Nonempty M] [CompactSpace M]

theorem nonempty_framedTubeData : Nonempty (e.FramedTubeData a) := by
  obtain ⟨r, hr, Φ, hs, hf, _, _⟩ := e.exists_smoothFramedTube a
  exact ⟨⟨r, hr, Φ, hs, hf⟩⟩

def framedTubeData : e.FramedTubeData a := Classical.choice (e.nonempty_framedTubeData a)

end NoExoticSixSphere.EuclideanEmbedding
