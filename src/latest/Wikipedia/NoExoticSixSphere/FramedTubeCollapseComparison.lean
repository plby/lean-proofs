import Wikipedia.NoExoticSixSphere.SmoothFramedCollapse
import Wikipedia.NoExoticSixSphere.CollapseFiberEquiv
import Wikipedia.NoExoticSixSphere.RadialCompressionIsometry
import Wikipedia.NoExoticSixSphere.RoundTubeRadiusHomotopy

/-!
# Comparing a certified smooth collapse with a round reindexed tube

The target coordinate change is the one-point extension of the inverse
fiber isometry. Radius invariance then compares the certified chosen tube
with any open round tube having the same core and reindexed ordered frame.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedTubeData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedTubeData a)
  {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  (u : K ≃ₗᵢ[ℝ] e.NormalModel)

def reindexedTube (p : M × K) : EuclideanSpace ℝ (Fin e.ambientDimension) :=
  d.tube (p.1, u p.2)

theorem isOpenEmbedding_reindexedTube : IsOpenEmbedding (d.reindexedTube u) :=
  d.isOpenEmbedding.comp ((Homeomorph.refl M).prodCongr u.toHomeomorph).isOpenEmbedding

theorem reindexedTube_formula (p : M × K) :
    d.reindexedTube u p = e.toFun p.1 + a.ambient p.1
      (u (OpenPartialHomeomorph.univBall (0 : K) d.radius p.2)) := by
  rw [reindexedTube, d.formula]
  exact congrArg (fun v : e.NormalModel ↦ e.toFun p.1 + a.ambient p.1 v)
    (map_univBall_linearIsometry u.toLinearIsometry d.radius d.radius_pos p.2).symm

variable [IsManifold (𝓡 n) ∞ M] [CompactSpace M]

def reindexedCollapse :
    C(OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension)), OnePoint K) :=
  (⟨u.symm.toHomeomorph.onePointCongr, u.symm.toHomeomorph.onePointCongr.continuous⟩ :
    C(OnePoint e.NormalModel, OnePoint K)).comp d.collapseData.map

theorem reindexedCollapse_apply (z : OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension))) :
    d.reindexedCollapse u z = OpenFiberCollapse.collapseOnePoint (d.reindexedTube u) z :=
  (OpenFiberCollapse.collapseOnePoint_fiberEquiv d.tube u.toEquiv
    d.isOpenEmbedding.injective z).symm

theorem reindexedCollapse_infty : d.reindexedCollapse u OnePoint.infty = OnePoint.infty := by
  rw [d.reindexedCollapse_apply, OpenFiberCollapse.collapseOnePoint_infty]

theorem exists_based_homotopy_to_roundTube (r : ℝ) (hr : 0 < r)
    (τ : M × K → EuclideanSpace ℝ (Fin e.ambientDimension)) (hE : IsOpenEmbedding τ)
    (hf : ∀ p, τ p = e.toFun p.1 + a.ambient p.1
      (u (OpenPartialHomeomorph.univBall (0 : K) r p.2))) :
    ∃ H : (d.reindexedCollapse u).Homotopy
      ⟨OpenFiberCollapse.collapseOnePoint τ, OpenFiberCollapse.continuous_collapseOnePoint τ hE⟩,
        ∀ t : I, H (t, OnePoint.infty) = OnePoint.infty := by
  let B : M → K →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
    fun m ↦ (a.ambient m).comp u.toContinuousLinearEquiv.toContinuousLinearMap
  have hd : d.reindexedTube u = RoundTubeRadiusHomotopy.tube e.toFun B d.radius :=
    funext (fun p ↦ d.reindexedTube_formula u p)
  have ht : τ = RoundTubeRadiusHomotopy.tube e.toFun B r := funext hf
  have hEd : IsOpenEmbedding (RoundTubeRadiusHomotopy.tube e.toFun B d.radius) :=
    hd ▸ d.isOpenEmbedding_reindexedTube u
  have hEt : IsOpenEmbedding (RoundTubeRadiusHomotopy.tube e.toFun B r) := ht ▸ hE
  obtain ⟨H, hH⟩ := RoundTubeRadiusHomotopy.exists_based_homotopy e.toFun B
    d.radius r d.radius_pos hr hEd hEt
  let H' : (d.reindexedCollapse u).Homotopy
      ⟨OpenFiberCollapse.collapseOnePoint τ,
        OpenFiberCollapse.continuous_collapseOnePoint τ hE⟩ := {
    toContinuousMap := H.toContinuousMap
    map_zero_left := fun z ↦ (H.map_zero_left z).trans (by
      change OpenFiberCollapse.collapseOnePoint
        (RoundTubeRadiusHomotopy.tube e.toFun B d.radius) z = d.reindexedCollapse u z
      rw [← hd]
      exact (d.reindexedCollapse_apply u z).symm)
    map_one_left := fun z ↦ (H.map_one_left z).trans (by
      change OpenFiberCollapse.collapseOnePoint (RoundTubeRadiusHomotopy.tube e.toFun B r) z =
        OpenFiberCollapse.collapseOnePoint τ z
      rw [← ht]) }
  exact ⟨H', hH⟩

end NoExoticSixSphere.EuclideanEmbedding.FramedTubeData
