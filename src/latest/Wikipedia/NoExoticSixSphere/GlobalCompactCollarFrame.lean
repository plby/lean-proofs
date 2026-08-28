import Wikipedia.NoExoticSixSphere.PrescribedCompactCollarFrame
import Wikipedia.NoExoticSixSphere.SmoothLocalExtension

/-!+# Smooth extension of the original frame over a compact-tube collar

The genuine tube domain contains a uniform transverse disk. Away from the
radial origin its original manifold frame is smooth, so it extends globally
while retaining every value on a closed annular product strictly inside that
tube. No normalization or normality is asserted outside the protected product.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {n d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M)
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (C : Sphere 3 → Vector d →L[ℝ] Vector e.ambientDimension)
  (R : e.RetractionNear (range f)) (b : Sphere 3)

theorem exists_global_compactCollarNormalFrame (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f)
    (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector d →L[ℝ] Vector e.ambientDimension) ∞ C)
    (q r δ : ℝ) (hq : 0 < q) (hδr : δ < r)
    (hdom : ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector d) r,
      (s, v) ∈ e.compactSphereTubeDomain f C R) :
    ∃ F : C(Vector 4 × Vector d,
        Vector ((e.ambientDimension - n) + 5) →L[ℝ] Vector (e.ambientDimension + 6)),
      ContDiff ℝ ∞ F ∧ EqOn F (e.compactCollarNormalFrame a f C R b)
        ((closedBall (0 : Vector 4) 1 ∩ {x | q ≤ ‖x‖}) ×ˢ closedBall (0 : Vector d) δ) := by
  let U := {x : Vector 4 | x ≠ 0} ×ˢ ball (0 : Vector d) r
  have hU : IsOpen U := isOpen_ne.prod isOpen_ball
  let K := (closedBall (0 : Vector 4) 1 ∩ {x | q ≤ ‖x‖}) ×ˢ closedBall (0 : Vector d) δ
  have hK : IsClosed K :=
    (isClosed_closedBall.inter (isClosed_le continuous_const continuous_norm)).prod
      isClosed_closedBall
  have hKU : K ⊆ U := by
    intro p hp
    exact ⟨norm_pos_iff.mp (hq.trans_le hp.1.2), (closedBall_subset_ball hδr) hp.2⟩
  have hs : ContDiffOn ℝ ∞ (e.compactCollarNormalFrame a f C R b) U := by
    intro p hp
    exact (e.contDiffAt_compactCollarNormalFrame a f C R b hf hC hp.1 p.2
      (hdom (SphereRadialRetraction.retract b p.1) p.2
        (ball_subset_closedBall hp.2))).contDiffWithinAt
  obtain ⟨G, hGs, hGK⟩ := exists_contDiff_eqOn_closed (e.compactCollarNormalFrame a f C R b)
    hK hU hKU hs
  exact ⟨⟨G, hGs.continuous⟩, hGs, hGK⟩

end NoExoticSixSphere.EuclideanEmbedding
