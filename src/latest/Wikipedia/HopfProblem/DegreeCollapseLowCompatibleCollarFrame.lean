import Wikipedia.HopfProblem.DegreeCollapseLowCollarNormalComparison
import Wikipedia.HopfProblem.DegreeCollapseLowProductNormalCollar
import Wikipedia.NoExoticSixSphere.SmoothLocalExtension

/-!

# The full original normal frame on the whole corrected low-surgery collar

A smooth global extension retains the prescribed native columns on a protected
annular product. Relative interpolation and normalization install those exact
columns in the actual corrected normal spaces. The product map is unchanged;
the inner core frame away from the protected collar need not be retained.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : NoExoticSixSphere.Sphere d → M)
  (C : NoExoticSixSphere.Sphere d → Vector (7 - d) →L[ℝ] Vector e.ambientDimension)
  (R : EuclideanEmbedding.TubularRetraction e) (b : NoExoticSixSphere.Sphere d)

theorem exists_global_collarNormalFrame (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
    (hC : ContMDiff (𝓡 d) 𝓘(ℝ, Vector (7 - d) →L[ℝ] Vector e.ambientDimension) ∞ C)
    (q r δ : ℝ) (hq : 0 < q) (hδr : δ < r)
    (hdom : ∀ s : NoExoticSixSphere.Sphere d, ∀ v ∈ closedBall (0 : Vector (7 - d)) r,
      (s, v) ∈ sphereTubeDomain e f C R) :
    ∃ F : C(Vector (d + 1) × Vector (7 - d),
        Vector ((e.ambientDimension - 7) + (1 + (d + 1))) →L[ℝ]
          Vector (e.ambientDimension + (1 + (1 + (d + 1))))),
      ContDiff ℝ ∞ F ∧ EqOn F (collarNormalFrame e a f C R b)
        ((closedBall (0 : Vector (d + 1)) 1 ∩ {x | q ≤ ‖x‖}) ×ˢ
          closedBall (0 : Vector (7 - d)) δ) := by
  let U := {x : Vector (d + 1) | x ≠ 0} ×ˢ ball (0 : Vector (7 - d)) r
  have hU : IsOpen U := isOpen_ne.prod isOpen_ball
  let K := (closedBall (0 : Vector (d + 1)) 1 ∩ {x | q ≤ ‖x‖}) ×ˢ closedBall (0 : Vector (7 - d)) δ
  have hK : IsClosed K :=
    (isClosed_closedBall.inter (isClosed_le continuous_const continuous_norm)).prod
      isClosed_closedBall
  have hKU : K ⊆ U := by
    intro p hp
    exact ⟨norm_pos_iff.mp (hq.trans_le hp.1.2), (closedBall_subset_ball hδr) hp.2⟩
  have hs : ContDiffOn ℝ ∞ (collarNormalFrame e a f C R b) U := by
    intro p hp
    exact (contDiffAt_collarNormalFrame e a f C R b hf hC hp.1 p.2
      (hdom (SphereRadialRetraction.retract b p.1) p.2
        (ball_subset_closedBall hp.2))).contDiffWithinAt
  obtain ⟨G, hGs, hGK⟩ := exists_contDiff_eqOn_closed (collarNormalFrame e a f C R b)
    hK hU hKU hs
  exact ⟨⟨G, hGs.continuous⟩, hGs, hGK⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : NoExoticSixSphere.Sphere d → M) (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
  {b : NoExoticSixSphere.Sphere d}
  (D : FramedDisk b (e.toFun ∘ f) (fun s => a.orthonormal (f s)))
  (A : LowFramedProduct.FramedProduct (q := 7 - d) D.map D.frame)
  (R : EuclideanEmbedding.TubularRetraction e) (χ : ContDiffBump (0 : Vector (d + 1)))
  (B : LowDiskThickening.FramedCoreProduct (curvedDiskProduct e f D A R χ) D.frame)
  (hχ : (1 / 2 : ℝ) < χ.rOut) (hχ1 : χ.rOut < 1)
  (hc : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, χ.rOut ≤ ‖x‖ →
    D.map x = collar b (e.toFun ∘ f) x ∧
    D.frame x = boundaryFrameOperator d
      (a.orthonormal (f (SphereRadialRetraction.retract b x))).val ∧
    A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val)
  (hdom : ∀ s : NoExoticSixSphere.Sphere d, ∀ v ∈ closedBall (0 : Vector (7 - d)) B.radius,
    (s, v) ∈ sphereTubeDomain e f A.boundaryTransverse R)

include hc in
theorem collarNormalFrame_eq_product_core {x : Vector (d + 1)}
    (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) (hxr : χ.rOut ≤ ‖x‖) :
    collarNormalFrame e a f A.boundaryTransverse R b (x, 0) = B.normalFrame (x, 0) :=
  (collarNormalFrame_core e a f A.boundaryTransverse R b x).trans
    ((hc x hx hxr).2.1.symm.trans (B.normalFrame_core x hx).symm)

include hf hd hχ hc hdom in
theorem exists_compatible_frame_extension (q δ : ℝ) (hqχ : χ.rOut < q)
    (hδ : 0 < δ) (hδB : δ < B.radius) :
    ∃ F : C(Vector (d + 1) × Vector (7 - d),
        Vector ((e.ambientDimension - 7) + (1 + (d + 1))) →L[ℝ]
          Vector (e.ambientDimension + (1 + (1 + (d + 1))))),
      ContDiff ℝ ∞ F ∧
      EqOn F (collarNormalFrame e a f A.boundaryTransverse R b)
        ((closedBall (0 : Vector (d + 1)) 1 ∩ {x | q ≤ ‖x‖}) ×ˢ closedBall (0 : Vector (7 - d)) δ) ∧
      (∀ x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ {x | q ≤ ‖x‖},
        F (x, 0) = B.normalFrame (x, 0)) ∧
      (∀ p ∈ (closedBall (0 : Vector (d + 1)) 1 ∩ {x | q ≤ ‖x‖}) ×ˢ
          closedBall (0 : Vector (7 - d)) δ,
        ∀ w, ‖F p w‖ = ‖w‖) ∧
      ∀ p ∈ (closedBall (0 : Vector (d + 1)) 1 ∩ {x | q ≤ ‖x‖}) ×ˢ
          closedBall (0 : Vector (7 - d)) δ,
        (F p).range ≤ (fderiv ℝ (curvedDiskProduct e f D A R χ) p).rangeᗮ := by
  have hq0 : 0 < q := by linarith
  obtain ⟨F, hFs, hFc⟩ := exists_global_collarNormalFrame e a f A.boundaryTransverse R b hf
    A.contMDiff_boundaryTransverse q B.radius δ hq0 hδB hdom
  refine ⟨F, hFs, hFc, ?_, ?_, ?_⟩
  · intro x hx
    have hF0 : F (x, 0) = collarNormalFrame e a f A.boundaryTransverse R b (x, 0) :=
      hFc (x := (x, (0 : Vector (7 - d)))) ⟨hx, mem_closedBall_self hδ.le⟩
    exact hF0.trans
      (collarNormalFrame_eq_product_core e a f D A R χ B hc hx.1 (hqχ.le.trans hx.2))
  · intro p hp w
    rw [hFc (x := p) hp]
    exact norm_collarNormalFrame e a f A.boundaryTransverse R b p w
  · intro p hp
    rw [hFc (x := p) hp]
    exact collarNormalFrame_normal_curvedDiskProduct e a f hf hd D A R χ hχ
      (fun x hx hxr ↦ ⟨(hc x hx hxr).1, (hc x hx hxr).2.2⟩)
      hp.1.1 (hqχ.trans_le hp.1.2) p.2
      (hdom (SphereRadialRetraction.retract b p.1) p.2
        ((closedBall_subset_closedBall hδB.le) hp.2))

include hf hd hχ hχ1 hc hdom in
theorem exists_compatible_curvedCollarFrame :
    ∃ q : ℝ, χ.rOut < q ∧ q < 1 ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ B.radius ∧
      ∃ G : Vector (d + 1) × Vector (7 - d) →
          Vector ((e.ambientDimension - 7) + (1 + (d + 1))) →L[ℝ]
          Vector (e.ambientDimension + (1 + (1 + (d + 1)))),
        (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ v ∈ closedBall (0 : Vector (7 - d)) ε,
          ContDiffAt ℝ ∞ G (x, v) ∧ (∀ w, ‖G (x, v) w‖ = ‖w‖) ∧
            (G (x, v)).range = (fderiv ℝ (curvedDiskProduct e f D A R χ) (x, v)).rangeᗮ) ∧
        ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, q ≤ ‖x‖ → ∀ v ∈ closedBall (0 : Vector (7 - d)) ε,
          G (x, v) = collarNormalFrame e a f A.boundaryTransverse R b (x, v) := by
  let q := (χ.rOut + 1) / 2
  have hqχ : χ.rOut < q := by dsimp only [q]; linarith
  have hq1 : q < 1 := by dsimp only [q]; linarith
  let δ := B.radius / 2
  have hδ : 0 < δ := by dsimp only [δ]; exact half_pos B.radius_pos
  have hδB : δ < B.radius := by dsimp only [δ]; linarith [B.radius_pos]
  let S := closedBall (0 : Vector (d + 1)) 1 ∩ {x | q ≤ ‖x‖}
  have hS : IsCompact S := (isCompact_closedBall (0 : Vector (d + 1)) 1).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hSK : S ⊆ closedBall (0 : Vector (d + 1)) 1 := inter_subset_left
  obtain ⟨F, hFs, hFc, hFA, hFn, hFr⟩ :=
    exists_compatible_frame_extension e a f hf hd D A R χ B hχ hc hdom q δ hqχ hδ hδB
  obtain ⟨ε, hε, hεδ, G, hG, hGF⟩ :=
    B.exists_normalFrame_collar hS hSK δ hδ hδB.le F hFs hFA hFn hFr
  refine ⟨q, hqχ, hq1, ε, hε, hεδ.trans hδB.le, G, hG, ?_⟩
  intro x hx hxq v hv
  exact (hGF (x := (x, v)) ⟨⟨hx, hxq⟩, hv⟩).trans
    (hFc (x := (x, v)) ⟨⟨hx, hxq⟩, (closedBall_subset_closedBall hεδ) hv⟩)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
