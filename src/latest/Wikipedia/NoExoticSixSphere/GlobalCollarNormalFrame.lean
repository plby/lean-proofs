import Wikipedia.NoExoticSixSphere.PrescribedCollarNormalFrame
import Wikipedia.NoExoticSixSphere.SmoothLocalExtension

/-!
# A globally smooth ambient family retaining the prescribed collar frame

The prescribed frame is smooth on the nonzero radial domain and the actual
uniform tube. A smooth extension retains its exact values on a closed annular
product strictly inside that tube. Its values outside the protected product
are not asserted orthonormal or normal.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (C : Sphere 3 → Vector 3 →L[ℝ] Vector e.ambientDimension)
  (R : TubularRetraction e) (b : Sphere 3)

theorem exists_global_collarNormalFrame (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 →L[ℝ] Vector e.ambientDimension) ∞ C)
    (q r δ : ℝ) (hq : 0 < q) (hδr : δ < r)
    (hdom : ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 3) r,
      (s, v) ∈ e.sphereTubeDomain f C R) :
    ∃ F : C(Vector 4 × Vector 3,
        Vector ((e.ambientDimension - 6) + 5) →L[ℝ] Vector (e.ambientDimension + 6)),
      ContDiff ℝ ∞ F ∧ EqOn F (e.collarNormalFrame a f C R b)
        ((closedBall (0 : Vector 4) 1 ∩ {x | q ≤ ‖x‖}) ×ˢ closedBall (0 : Vector 3) δ) := by
  let U := {x : Vector 4 | x ≠ 0} ×ˢ ball (0 : Vector 3) r
  have hU : IsOpen U := isOpen_ne.prod isOpen_ball
  let K := (closedBall (0 : Vector 4) 1 ∩ {x | q ≤ ‖x‖}) ×ˢ closedBall (0 : Vector 3) δ
  have hK : IsClosed K :=
    (isClosed_closedBall.inter (isClosed_le continuous_const continuous_norm)).prod
      isClosed_closedBall
  have hKU : K ⊆ U := by
    intro p hp
    exact ⟨norm_pos_iff.mp (hq.trans_le hp.1.2), (closedBall_subset_ball hδr) hp.2⟩
  have hs : ContDiffOn ℝ ∞ (e.collarNormalFrame a f C R b) U := by
    intro p hp
    exact (e.contDiffAt_collarNormalFrame a f C R b hf hC hp.1 p.2
      (hdom (SphereRadialRetraction.retract b p.1) p.2
        (ball_subset_closedBall hp.2))).contDiffWithinAt
  obtain ⟨G, hGs, hGK⟩ := exists_contDiff_eqOn_closed (e.collarNormalFrame a f C R b)
    hK hU hKU hs
  exact ⟨⟨G, hGs.continuous⟩, hGs, hGK⟩

end NoExoticSixSphere.EuclideanEmbedding
