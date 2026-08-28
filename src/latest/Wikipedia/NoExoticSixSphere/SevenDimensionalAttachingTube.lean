import Wikipedia.NoExoticSixSphere.SevenDimensionalFramedProduct
import Wikipedia.NoExoticSixSphere.EmbeddedCompactSphereTube
import Wikipedia.NoExoticSixSphere.SpanningDiskRadialProductFrame
import Wikipedia.NoExoticSixSphere.SpanningDiskProductAvoidance

/-!
# The actual seven-manifold tube for the constructed eight-dimensional product

The boundary four-frame of the actual framed D4 x D4 product determines an
embedded sphere tube in the original seven-manifold. The retraction used to
construct it is obtained near the compact sphere image, so the manifold need
not be compact. The tube fixes the original sphere, and its embedded core
derivative is exactly the original sphere derivative and the same boundary
four-frame used by the disk product. The disk, prescribed partial normal
frame, and transverse frame all have exact radial values on a whole collar;
radializing the transverse frame preserves its original boundary columns.
One common positive radius stays within the framed product, embeds the
manifold tube, and makes the whole affine product interior avoid the old
ambient space.

This does not yet bend the whole product collar to match the tube, attach
the product, or round an eight-dimensional surgery trace.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

universe u

theorem exists_product_and_tube_of_dimension_seven {M : Type u}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
    [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (b : Sphere 3) (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
    (hi : Injective f) (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) :
    ∃ D : DiskData b (e.toFun ∘ f), ∃ r : ℝ, (1 / 2 : ℝ) < r ∧ r < 1 ∧
      ∃ T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        ∃ A : DiskThickening.FramedProduct D.toFun T 4,
          (∀ s : Sphere 3, T s.val = boundaryFrameOperator (a.orthonormal (f s)).val) ∧
          (∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
            D.toFun x = collar b (e.toFun ∘ f) x ∧
            T x = boundaryFrameOperator
              (a.orthonormal (f (SphereRadialRetraction.retract b x))).val ∧
            A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val) ∧
          ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector e.ambientDimension) ∞
            (boundaryComplementOperator A.transverse) ∧
          (∀ s v, ‖boundaryComplementOperator A.transverse s v‖ = ‖v‖) ∧
          (∀ s, (boundaryComplementOperator A.transverse s).range = e.sphereNormalSpace f s) ∧
          (∀ s v, appendZeroMap e.ambientDimension 6
            (boundaryComplementOperator A.transverse s v) = A.transverse s.val v) ∧
          ∃ R : e.RetractionNear (range f), ∃ ε : ℝ, 0 < ε ∧
            ε ≤ A.radius ∧
            (∀ x ∈ ball (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector 4) ε,
              DiskThickening.map D.toFun A.transverse (x, v) ∉
                range (appendZeroMap e.ambientDimension 6)) ∧
            IsClosedEmbedding (fun p : Sphere 3 × closedBall (0 : Vector 4) ε ↦
              e.compactSphereTube f (boundaryComplementOperator A.transverse) R (p.1, p.2.val)) ∧
            (∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) ε,
              (s, v) ∈ e.compactSphereTubeDomain f (boundaryComplementOperator A.transverse) R ∧
                IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 4)) (𝓡 7) ∞
                  (e.compactSphereTube f (boundaryComplementOperator A.transverse) R) (s, v)) ∧
            (∀ s : Sphere 3,
              e.compactSphereTube f (boundaryComplementOperator A.transverse) R (s, 0) = f s) ∧
            ∀ s : Sphere 3, mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension)
              (e.toFun ∘ e.compactSphereTube f (boundaryComplementOperator A.transverse) R) (s, 0) =
                (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).coprod
                  (boundaryComplementOperator A.transverse s) := by
  obtain ⟨D, r, _, hr1, T, A₀, hTb, hTc, hBs, hBn, hBr, hBa⟩ :=
    e.exists_framedProduct_of_dimension_seven a b f hf hi hd
  have han (s : Sphere 3) : (a.orthonormal (f s)).val.range ≤
      (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ := by
    rw [a.orthonormal_range, e.range_normalProjection]
    exact Submodule.orthogonal_le (e.range_mfderiv_embeddedSphere_le f hf s)
  have hN : ((e.ambientDimension - 7) + 5) + 4 + 4 = e.ambientDimension + 6 := by
    have h := e.dimension_le_ambient (f b)
    omega
  obtain ⟨ρ, hρhalf, hρ1, _, A, hAb, hAc⟩ := D.exists_framedProduct_radialCollar
    (e.smooth.comp hf) (e.injective_mfderiv_embeddedSphere f hf hd)
    (fun s ↦ a.orthonormal (f s)) han A₀ hTb r hr1
    (fun x hx hxr ↦ (hTc x hx hxr).2) hN
  have hCeq : boundaryComplementOperator A.transverse =
      boundaryComplementOperator A₀.transverse := by
    funext s
    unfold boundaryComplementOperator
    rw [hAb s]
  let C := boundaryComplementOperator A.transverse
  have hCs : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector e.ambientDimension) ∞ C := by
    change ContMDiff _ _ _ (boundaryComplementOperator A.transverse)
    rw [hCeq]
    exact hBs
  have hCn (s : Sphere 3) (v : Vector 4) : ‖C s v‖ = ‖v‖ := by
    change ‖boundaryComplementOperator A.transverse s v‖ = ‖v‖
    rw [hCeq]
    exact hBn s v
  have hiC (s : Sphere 3) : Injective (C s) := Stiefel.injective ⟨C s, hCn s⟩
  have hCr (s : Sphere 3) : (C s).range = e.sphereNormalSpace f s := by
    change (boundaryComplementOperator A.transverse s).range = _
    rw [hCeq]
    exact hBr s
  have hCa (s : Sphere 3) (v : Vector 4) :
      appendZeroMap e.ambientDimension 6 (C s v) = A.transverse s.val v := by
    change appendZeroMap e.ambientDimension 6
      (boundaryComplementOperator A.transverse s v) = _
    rw [hCeq, hAb s]
    exact hBa s v
  obtain ⟨R, ε, hε, he, hl⟩ := e.exists_compactSphereTube f C hf hi hCs hd hiC hCr
  obtain ⟨δ, hδ, hδA, hδavoid⟩ := D.exists_affine_interior_avoids A hCa ρ hρhalf hρ1
    (fun x hx hρx ↦ ⟨(hAc x hx hρx).1, (hAc x hx hρx).2.2⟩)
  let η := min ε δ
  have hηε : η ≤ ε := min_le_left _ _
  have hηδ : η ≤ δ := min_le_right _ _
  let j : Sphere 3 × closedBall (0 : Vector 4) η →
      Sphere 3 × closedBall (0 : Vector 4) ε :=
    fun p ↦ (p.1, ⟨p.2.val, (closedBall_subset_closedBall hηε) p.2.property⟩)
  have hj : Continuous j := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hji : Injective j := by
    intro p z hpz
    exact Prod.ext (congrArg (fun w : Sphere 3 × closedBall (0 : Vector 4) ε ↦ w.1) hpz)
      (Subtype.ext (congrArg (fun w : Sphere 3 × closedBall (0 : Vector 4) ε ↦ w.2.val) hpz))
  refine ⟨D, ρ, hρhalf, hρ1, T, A, hTb, hAc, hCs, hCn, hCr, hCa, R, η,
    lt_min hε hδ, hηδ.trans hδA,
    (fun x hx v hv ↦ hδavoid x hx v ((closedBall_subset_closedBall hηδ) hv)),
    he.comp (hj.isClosedEmbedding hji),
    (fun s v hv ↦ hl s v ((closedBall_subset_closedBall hηε) hv)),
    e.compactSphereTube_core f C R, ?_⟩
  intro s
  exact (e.mfderiv_embedded_compactSphereTube_core f C R hf hCs hd hiC hCr s).trans
    (e.mfderiv_ambientSphereTube_core f C hf hCs s)

end NoExoticSixSphere.EuclideanEmbedding
