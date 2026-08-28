import Wikipedia.SmoothSixDPoincare.DiskNormalProjection
import Wikipedia.SmoothSixDPoincare.OpenDiskProjectionFrame

/-!
# Constructed normal frames near a disk in the original manifold

The Gram formula, native tangent projection, and radial projection transport
construct a smooth frame of the actual normal space inside the manifold.
Its model has precisely the intrinsic codimension. The frame and its range
equations hold on an open neighborhood including the disk boundary.

This does not assert compatibility with a prescribed Whitney boundary framing.
-/

noncomputable section

open Function Module Set
open scoped Manifold ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding

variable {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M)

/-- Every native immersed closed disk has a constructed smooth intrinsic normal frame nearby. -/
theorem exists_smooth_normalFrame_near_closedBall {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hi : ∀ x ∈ Metric.closedBall (0 : D) 1,
      Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : finrank ℝ D + n = finrank ℝ E) :
    ∃ V : Set D, IsOpen V ∧ Metric.closedBall (0 : D) 1 ⊆ V ∧
      ∃ A : D → EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin e.ambientDimension),
        ContDiffOn ℝ ∞ A V ∧
          ∀ x ∈ V, Injective (A x) ∧ (A x).range = e.diskNormalSpace f x := by
  obtain ⟨U, hU, hKU, hsP, hP⟩ := e.exists_open_diskNormalProjection hf hi
  have hidem : ∀ x ∈ U, IsIdempotentElem (e.diskNormalProjection f x) := by
    intro x hx
    rw [hP x hx]
    exact (e.diskNormalSpace f x).isIdempotentElem_starProjection
  obtain ⟨V, hV, hKV, hVU, A, hA, hAi⟩ :=
    DiskFraming.exists_smooth_frame_on_neighborhood_closedBall
      hU hKU (e.diskNormalProjection f) hidem hsP
  have hz : (0 : D) ∈ Metric.closedBall (0 : D) 1 := Metric.mem_closedBall_self zero_le_one
  have hr : (e.diskNormalProjection f 0).range = e.diskNormalSpace f 0 := by
    rw [hP 0 (hKU hz), Submodule.range_starProjection]
  have hdim : finrank ℝ (e.diskNormalSpace f 0) = n := by
    have h := e.finrank_diskTangent_add_normal hf (hi 0 hz)
    omega
  have hcenter : finrank ℝ (e.diskNormalProjection f 0).range = n :=
    (congrArg (fun S : Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) =>
      finrank ℝ S) hr).trans hdim
  let φ : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      (e.diskNormalProjection f 0).range :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hcenter.symm)
  refine ⟨V, hV, hKV, fun x => (A x).comp φ.toContinuousLinearMap,
    hA.clm_comp contDiffOn_const, ?_⟩
  intro x hx
  refine ⟨((hAi x hx).1).comp φ.injective, ?_⟩
  calc
    ((A x).comp φ.toContinuousLinearMap).range = (A x).range :=
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr φ.surjective)
    _ = (e.diskNormalProjection f x).range := (hAi x hx).2
    _ = e.diskNormalSpace f x := by rw [hP x (hVU hx), Submodule.range_starProjection]

end Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding
