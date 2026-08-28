import Wikipedia.NoExoticSixSphere.FramedCollaredDiskParity

/-!
# The inward collar sign gives the same zero-parity conclusion

A fixed reflection of the height line fixes every prescribed boundary
normal column and the boundary map itself. It turns negative radial
height into positive height. The actual disk derivatives and normal
operators are reflected together, preserving their injectivity and
disjoint ranges. No change of the original boundary atlas or frame occurs.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredDiskFrame

open GLOrthonormalization

def heightReflection (N : ℕ) : (Vector N × ℝ) ≃L[ℝ] (Vector N × ℝ) :=
  (ContinuousLinearEquiv.refl ℝ (Vector N)).prodCongr
    ((LinearEquiv.smulOfNeZero ℝ ℝ (-1) (by norm_num)).toContinuousLinearEquiv)

theorem heightReflection_apply (N : ℕ) (p : Vector N × ℝ) :
    heightReflection N p = (p.1, -p.2) := by
  change (p.1, (-1 : ℝ) * p.2) = _
  rw [neg_one_mul]

theorem heightReflection_normal {N k : ℕ} (A : Vector k →L[ℝ] Vector N) :
    (heightReflection N).toContinuousLinearMap.comp
        ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp A) =
      (ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp A := by
  apply ContinuousLinearMap.ext
  intro v
  change heightReflection N (A v, 0) = (A v, 0)
  rw [heightReflection_apply, neg_zero]

theorem heightReflection_disjoint {N k : ℕ}
    (A : Vector k →L[ℝ] (Vector N × ℝ)) (D : Vector 4 →L[ℝ] (Vector N × ℝ))
    (hr : Disjoint A.range D.range) :
    Disjoint ((heightReflection N).toContinuousLinearMap.comp A).range
      ((heightReflection N).toContinuousLinearMap.comp D).range := by
  change Disjoint ((heightReflection N).toLinearMap.comp A.toLinearMap).range
    ((heightReflection N).toLinearMap.comp D.toLinearMap).range
  rw [LinearMap.range_comp, LinearMap.range_comp]
  exact Submodule.disjoint_map (heightReflection N).injective hr

end NoExoticSixSphere.CollaredDiskFrame

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization CollaredDiskFrame
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem sphereParity_zero_of_framed_collared_disk_negative
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hDF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, Injective (fderiv ℝ F x))
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (A : C(Disk (E := Vector 4), e.NormalModel →L[ℝ] (Vector e.ambientDimension × ℝ)))
    (hA : ∀ x, Injective (A x))
    (hAD : ∀ x, Disjoint (A x).range (fderiv ℝ F x.val).range)
    (hAb : ∀ s, A (boundaryToDisk s) =
      (ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp (a.ambient (f s)))
    (hheight : ∀ s : Sphere 3, (fderiv ℝ F s.val s.val).2 < 0) :
    e.sphereParity a f hf hi hd = 0 := by
  let L := heightReflection e.ambientDimension
  let F' := L ∘ F
  let A' : C(Disk (E := Vector 4),
      e.NormalModel →L[ℝ] (Vector e.ambientDimension × ℝ)) :=
    ⟨fun x ↦ L.toContinuousLinearMap.comp (A x), continuous_const.clm_comp A.continuous⟩
  have hF' (x : Vector 4) (hx : x ∈ Metric.closedBall 0 1) : ContDiffAt ℝ ∞ F' x :=
    L.contDiff.contDiffAt.comp x (hF x hx)
  have hdF' (x : Vector 4) (hx : x ∈ Metric.closedBall 0 1) :
      fderiv ℝ F' x = L.toContinuousLinearMap.comp (fderiv ℝ F x) := by
    change fderiv ℝ (L ∘ F) x = _
    rw [fderiv_comp x L.differentiableAt ((hF x hx).differentiableAt (by simp)),
      L.fderiv]
  apply e.sphereParity_zero_of_framed_collared_disk a f hf hi hd F' hF' ?_ ?_ A' ?_ ?_ ?_ ?_
  · intro x hx
    rw [hdF' x hx]
    exact L.injective.comp (hDF x hx)
  · intro s
    change heightReflection e.ambientDimension (F s.val) = _
    rw [hb, heightReflection_apply, neg_zero]
  · intro x
    exact L.injective.comp (hA x)
  · intro x
    change Disjoint (L.toContinuousLinearMap.comp (A x)).range (fderiv ℝ F' x.val).range
    rw [hdF' x.val x.property]
    exact heightReflection_disjoint (A x) (fderiv ℝ F x.val) (hAD x)
  · intro s
    change L.toContinuousLinearMap.comp (A (boundaryToDisk s)) = _
    rw [hAb]
    exact heightReflection_normal (a.ambient (f s))
  · intro s
    rw [hdF' s.val (Metric.sphere_subset_closedBall s.property)]
    change 0 < (heightReflection e.ambientDimension (fderiv ℝ F s.val s.val)).2
    rw [heightReflection_apply]
    exact neg_pos.mpr (hheight s)

end NoExoticSixSphere.EuclideanEmbedding
