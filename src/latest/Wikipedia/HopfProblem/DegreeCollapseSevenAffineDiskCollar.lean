import Wikipedia.HopfProblem.DegreeCollapseSevenBoundaryTransverse
import Wikipedia.HopfProblem.DegreeCollapseSevenInternalSphereTube
import Wikipedia.NoExoticSixSphere.SmoothSphereRadialCollar

/-!
# SevenAffineDiskCollar

The full affine attaching face retains the original ambient coordinates. When the transverse frame is radial on a collar, its height proves avoidance of the old ambient plane for every transverse vector.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : EightDimensionalFramedProduct.FramedProduct D.toFun T)
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (SevenSurgery.normalFrameOnSphere e a f s).val)

include hf hd hTb in
theorem thickening_boundary_affine (s : Sphere 3) (v : Vector 4) :
    GeneralDiskThickening.map D.toFun A.transverse (s.val, v) =
      appendZeroMap e.ambientDimension 6 (SevenSurgery.ambientSphereTube e f A.boundaryTransverse (s, v)) := by
  change D.toFun s.val + A.transverse s.val v =
    appendZeroMap e.ambientDimension 6 (e.toFun (f s) + A.boundaryTransverse s v)
  rw [map_add, SevenSurgery.append_boundaryTransverse e a f hf hd D A hTb s v]
  exact congrArg (fun w ↦ w + A.transverse s.val v) (D.boundary s)

include hf hd hTb in
theorem mfderiv_retracted_boundaryTube_core (r : EuclideanEmbedding.TubularRetraction e) (s : Sphere 3) :
    mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension)
      (e.toFun ∘ SevenSurgery.internalSphereTube e f A.boundaryTransverse r) (s, 0) =
    mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension)
      (SevenSurgery.ambientSphereTube e f A.boundaryTransverse) (s, 0) :=
  SevenSurgery.mfderiv_embedded_internalSphereTube_core e f A.boundaryTransverse r hf
    A.contMDiff_boundaryTransverse hd
    (fun s ↦ Stiefel.injective
      ⟨A.boundaryTransverse s, SevenSurgery.norm_boundaryTransverse e a f hf hd D A hTb s⟩)
    (SevenSurgery.range_boundaryTransverse e a f hf hd D A hTb) s

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : EightDimensionalFramedProduct.FramedProduct D.toFun T)
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (SevenSurgery.normalFrameOnSphere e a f s).val)

include hf hd hTb in
theorem thickening_radial_collar {x : Vector 4} (hx : (1 / 2 : ℝ) < ‖x‖)
    (hDx : D.toFun x = collar b (e.toFun ∘ f) x)
    (hCx : A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val)
    (v : Vector 4) :
    GeneralDiskThickening.map D.toFun A.transverse (x, v) = coordinates e.ambientDimension 4
      ((SevenSurgery.ambientSphereTube e f A.boundaryTransverse (SphereRadialRetraction.retract b x, v),
        definingFunction x), 0) := by
  let s := SphereRadialRetraction.retract b x
  have hD' : D.toFun x = coordinates e.ambientDimension 4
      ((e.toFun (f s), definingFunction x), 0) := by
    rw [hDx]
    change coordinates e.ambientDimension 4
      ((SmoothSphereAmbient.extension b (e.toFun ∘ f) x, definingFunction x), 0) = _
    rw [SmoothSphereAmbient.extension_eq_radial_of_half_le b (e.toFun ∘ f) hx.le]
    rfl
  have hC' : A.transverse x v = coordinates e.ambientDimension 4
      ((A.boundaryTransverse s v, 0), 0) := by
    rw [hCx]
    exact (SevenSurgery.append_boundaryTransverse e a f hf hd D A hTb s v).symm.trans
      (coordinates_old e.ambientDimension 4 _).symm
  change D.toFun x + A.transverse x v = _
  rw [hD', hC', ← map_add]
  simp only [Prod.mk_add_mk, add_zero]
  rfl

include a hf hd hTb in
theorem thickening_radial_collar_avoids {x : Vector 4} (hx : x ∈ ball (0 : Vector 4) 1)
    (hhalf : (1 / 2 : ℝ) < ‖x‖) (hDx : D.toFun x = collar b (e.toFun ∘ f) x)
    (hCx : A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val)
    (v : Vector 4) :
    GeneralDiskThickening.map D.toFun A.transverse (x, v) ∉
      range (appendZeroMap e.ambientDimension 6) := by
  rintro ⟨y, hy⟩
  have hH := SevenSurgery.thickening_radial_collar e a f hf hd D A hTb hhalf hDx hCx v
  have he : ((SevenSurgery.ambientSphereTube e f A.boundaryTransverse
        (SphereRadialRetraction.retract b x, v), definingFunction x), (0 : ℝ × Vector 4)) =
      ((y, 0), 0) := (coordinates e.ambientDimension 4).injective (by
    rw [← hH, coordinates_old]
    exact hy.symm)
  have hρ : definingFunction x = 0 :=
    congrArg (fun p : (Vector e.ambientDimension × ℝ) × (ℝ × Vector 4) ↦ p.1.2) he
  have hn : ‖x‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using (definingFunction_eq_zero_iff x).mp hρ
  have hlt : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
  exact (ne_of_lt hlt) hn

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
