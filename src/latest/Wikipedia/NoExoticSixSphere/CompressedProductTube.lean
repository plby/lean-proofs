import Wikipedia.NoExoticSixSphere.UniformProductTube
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Opening a product tube with an unrestricted normal coordinate

The standard homeomorphism from a normed space to a ball compresses the
normal coordinate. A product disk contained in a partial homeomorphism's
source therefore gives an open embedding of the entire product.
-/

open Set Topology

namespace NoExoticSixSphere.CompressedProductTube

variable {M K Y : Type*} [TopologicalSpace M]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [TopologicalSpace Y]
  (Φ : OpenPartialHomeomorph (M × K) Y) (r : ℝ)

noncomputable def map (p : M × K) : Y :=
  Φ (p.1, OpenPartialHomeomorph.univBall (0 : K) r p.2)

theorem map_zero (x : M) : map Φ r (x, 0) = Φ (x, 0) := by
  simp only [map, OpenPartialHomeomorph.univBall_apply_zero]

theorem isOpenEmbedding_map (hr : 0 < r)
    (hsource : ∀ x v, ‖v‖ ≤ r → (x, v) ∈ Φ.source) :
    IsOpenEmbedding (map Φ r) := by
  let c := (OpenPartialHomeomorph.refl M).prod
    (OpenPartialHomeomorph.univBall (0 : K) r)
  let Ψ := c.trans Φ
  have hs : Ψ.source = univ := by
    apply eq_univ_of_forall
    intro p
    change p ∈ c.source ∧ c p ∈ Φ.source
    refine ⟨?_, ?_⟩
    · change p.1 ∈ (univ : Set M) ∧
        p.2 ∈ (OpenPartialHomeomorph.univBall (0 : K) r).source
      simp only [OpenPartialHomeomorph.univBall_source, mem_univ, and_self]
    · have hmem : OpenPartialHomeomorph.univBall (0 : K) r p.2 ∈
          (OpenPartialHomeomorph.univBall (0 : K) r).target :=
        (OpenPartialHomeomorph.univBall (0 : K) r).map_source (by simp)
      rw [OpenPartialHomeomorph.univBall_target _ hr, Metric.mem_ball, dist_zero_right] at hmem
      exact hsource p.1 _ hmem.le
  exact Ψ.isOpenEmbedding hs

end NoExoticSixSphere.CompressedProductTube
