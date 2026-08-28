import Wikipedia.NoExoticSixSphere.CompactCurvedCollarDerivative
import Wikipedia.NoExoticSixSphere.GlobalCompactCollarFrame
import Wikipedia.NoExoticSixSphere.ProductNormalFrameReplacement

/-!
# Installing the original normal frame on the compact-tube product's whole collar

The original manifold frame agrees with the product frame on an annular zero
section. A smooth extension and relative normal-frame replacement give a full
orthonormal frame with exact agreement on a thinner whole collar. The actual
corrected product map remains unchanged. The old frame on the inner disk core
is not claimed to be retained.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {n d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M)
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f)
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - n) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : DiskThickening.FramedProduct D.toFun T d) (R : e.RetractionNear (range f))
  (χ : ContDiffBump (0 : Vector 4))
  (B : DiskThickening.FramedCoreProduct (e.compactCurvedDiskProduct f D A R χ) T)
  (hCb : ∀ s v, appendZeroMap e.ambientDimension 6
    (boundaryComplementOperator A.transverse s v) = A.transverse s.val v)
  (hχ : (1 / 2 : ℝ) < χ.rOut) (hχ1 : χ.rOut < 1)
  (hc : ∀ x ∈ closedBall (0 : Vector 4) 1, χ.rOut ≤ ‖x‖ →
    D.toFun x = collar b (e.toFun ∘ f) x ∧
    T x = boundaryFrameOperator (a.orthonormal (f (SphereRadialRetraction.retract b x))).val ∧
    A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val)
  (hdom : ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector d) B.radius,
    (s, v) ∈ e.compactSphereTubeDomain f (boundaryComplementOperator A.transverse) R)

include hc in
theorem compactCollarNormalFrame_eq_product_core {x : Vector 4}
    (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : χ.rOut ≤ ‖x‖) :
    e.compactCollarNormalFrame a f (boundaryComplementOperator A.transverse) R b (x, 0) =
      B.normalFrame (x, 0) :=
  (e.compactCollarNormalFrame_core a f (boundaryComplementOperator A.transverse) R b x).trans
    ((hc x hx hxr).2.1.symm.trans (B.normalFrame_core x hx).symm)

include hf hCb hχ hc hdom in
theorem exists_compatible_compactFrame_extension (q δ : ℝ) (hqχ : χ.rOut < q)
    (hδ : 0 < δ) (hδB : δ < B.radius) :
    ∃ F : C(Vector 4 × Vector d,
        Vector ((e.ambientDimension - n) + 5) →L[ℝ] Vector (e.ambientDimension + 6)),
      ContDiff ℝ ∞ F ∧
      EqOn F (e.compactCollarNormalFrame a f (boundaryComplementOperator A.transverse) R b)
        ((closedBall (0 : Vector 4) 1 ∩ {x | q ≤ ‖x‖}) ×ˢ closedBall (0 : Vector d) δ) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1 ∩ {x | q ≤ ‖x‖},
        F (x, 0) = B.normalFrame (x, 0)) ∧
      (∀ p ∈ (closedBall (0 : Vector 4) 1 ∩ {x | q ≤ ‖x‖}) ×ˢ closedBall (0 : Vector d) δ,
        ∀ w, ‖F p w‖ = ‖w‖) ∧
      ∀ p ∈ (closedBall (0 : Vector 4) 1 ∩ {x | q ≤ ‖x‖}) ×ˢ closedBall (0 : Vector d) δ,
        (F p).range ≤ (fderiv ℝ (e.compactCurvedDiskProduct f D A R χ) p).rangeᗮ := by
  have hq0 : 0 < q := by linarith
  obtain ⟨F, hFs, hFc⟩ := e.exists_global_compactCollarNormalFrame a f
    (boundaryComplementOperator A.transverse) R b hf
    (contMDiff_boundaryComplementOperator A.transverse A.smooth_transverse)
    q B.radius δ hq0 hδB hdom
  refine ⟨F, hFs, hFc, ?_, ?_, ?_⟩
  · intro x hx
    have hF0 : F (x, 0) = e.compactCollarNormalFrame a f
        (boundaryComplementOperator A.transverse) R b (x, 0) :=
      hFc (x := (x, (0 : Vector d))) ⟨hx, mem_closedBall_self hδ.le⟩
    exact hF0.trans (e.compactCollarNormalFrame_eq_product_core a f D A R χ B hc
      hx.1 (hqχ.le.trans hx.2))
  · intro p hp w
    rw [hFc (x := p) hp]
    exact e.norm_compactCollarNormalFrame a f (boundaryComplementOperator A.transverse) R b p w
  · intro p hp
    rw [hFc (x := p) hp]
    exact e.compactCollarNormalFrame_normal_product a f hf D A R χ hCb hχ
      (fun x hx hxr ↦ ⟨(hc x hx hxr).1, (hc x hx hxr).2.2⟩)
      hp.1.1 (hqχ.trans_le hp.1.2) p.2
      (hdom (SphereRadialRetraction.retract b p.1) p.2
        ((closedBall_subset_closedBall hδB.le) hp.2))

include hf hCb hχ hχ1 hc hdom in
theorem exists_compatible_compactCurvedCollarFrame :
    ∃ q : ℝ, χ.rOut < q ∧ q < 1 ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ B.radius ∧
      ∃ G : Vector 4 × Vector d → Vector ((e.ambientDimension - n) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector d) ε,
          ContDiffAt ℝ ∞ G (x, v) ∧ (∀ w, ‖G (x, v) w‖ = ‖w‖) ∧
            (G (x, v)).range =
              (fderiv ℝ (e.compactCurvedDiskProduct f D A R χ) (x, v)).rangeᗮ) ∧
        ∀ x ∈ closedBall (0 : Vector 4) 1, q ≤ ‖x‖ → ∀ v ∈ closedBall (0 : Vector d) ε,
          G (x, v) = e.compactCollarNormalFrame a f
            (boundaryComplementOperator A.transverse) R b (x, v) := by
  let q := (χ.rOut + 1) / 2
  have hqχ : χ.rOut < q := by dsimp only [q]; linarith
  have hq1 : q < 1 := by dsimp only [q]; linarith
  let δ := B.radius / 2
  have hδ : 0 < δ := by dsimp only [δ]; exact half_pos B.radius_pos
  have hδB : δ < B.radius := by dsimp only [δ]; linarith [B.radius_pos]
  let S := closedBall (0 : Vector 4) 1 ∩ {x | q ≤ ‖x‖}
  have hS : IsCompact S := (isCompact_closedBall (0 : Vector 4) 1).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hSK : S ⊆ closedBall (0 : Vector 4) 1 := inter_subset_left
  obtain ⟨F, hFs, hFc, hFA, hFn, hFr⟩ :=
    e.exists_compatible_compactFrame_extension a f hf D A R χ B hCb hχ hc hdom
      q δ hqχ hδ hδB
  obtain ⟨ε, hε, hεδ, G, hG, hGF⟩ :=
    B.exists_normalFrame_collar hS hSK δ hδ hδB.le F hFs hFA hFn hFr
  refine ⟨q, hqχ, hq1, ε, hε, hεδ.trans hδB.le, G, hG, ?_⟩
  intro x hx hxq v hv
  exact (hGF (x := (x, v)) ⟨⟨hx, hxq⟩, hv⟩).trans
    (hFc (x := (x, v)) ⟨⟨hx, hxq⟩, (closedBall_subset_closedBall hεδ) hv⟩)

end NoExoticSixSphere.EuclideanEmbedding
