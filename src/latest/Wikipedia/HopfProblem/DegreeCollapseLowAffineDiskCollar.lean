import Wikipedia.HopfProblem.DegreeCollapseLowRadialTransverseProduct
import Wikipedia.HopfProblem.DegreeCollapseLowEmbeddedSphereTube

/-!

# The whole low-surgery affine collar and original ambient tube

The entire affine attaching face retains the actual original ambient tube.
On the radial collar its exact height is the original defining function,
so every interior collar point avoids the whole old ambient space for
every transverse vector. The retracted native tube has the same core
derivative after composition with the original embedding.
-/

noncomputable section

open Function
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

include hf hd in
theorem thickening_boundary_affine (s : NoExoticSixSphere.Sphere d) (v : Vector (7 - d)) :
    LowDiskThickening.map D.map A.transverse (s.val, v) =
      appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))
        (ambientSphereTube e f A.boundaryTransverse (s, v)) := by
  change D.map s.val + A.transverse s.val v =
    appendZeroMap e.ambientDimension (1 + (1 + (d + 1))) (e.toFun (f s) + A.boundaryTransverse s v)
  rw [map_add, append_boundaryTransverse e a f hf hd D A s v]
  exact congrArg (fun w ↦ w + A.transverse s.val v) (D.boundary s)

include hf hd in
theorem mfderiv_retracted_boundaryTube_core (r : EuclideanEmbedding.TubularRetraction e)
    (s : NoExoticSixSphere.Sphere d) :
    mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension)
      (e.toFun ∘ internalSphereTube e f A.boundaryTransverse r) (s, 0) =
    mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension)
      (ambientSphereTube e f A.boundaryTransverse) (s, 0) :=
  mfderiv_embedded_internalSphereTube_core e f A.boundaryTransverse r hf
    A.contMDiff_boundaryTransverse hd
    (fun s ↦ Stiefel.injective
      ⟨A.boundaryTransverse s, norm_boundaryTransverse e a f hf hd D A s⟩)
    (range_boundaryTransverse e a f hf hd D A) s

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

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

include hf hd in
theorem thickening_radial_collar {x : Vector (d + 1)} (hx : (1 / 2 : ℝ) < ‖x‖)
    (hDx : D.map x = collar b (e.toFun ∘ f) x)
    (hCx : A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val)
    (v : Vector (7 - d)) :
    LowDiskThickening.map D.map A.transverse (x, v) = coordinates e.ambientDimension (d + 1)
      ((ambientSphereTube e f A.boundaryTransverse (SphereRadialRetraction.retract b x, v),
        definingFunction x), 0) := by
  let s := SphereRadialRetraction.retract b x
  have hD' : D.map x = coordinates e.ambientDimension (d + 1)
      ((e.toFun (f s), definingFunction x), 0) := by
    rw [hDx]
    change coordinates e.ambientDimension (d + 1)
      ((SmoothSphereAmbient.extension b (e.toFun ∘ f) x, definingFunction x), 0) = _
    rw [SmoothSphereAmbient.extension_eq_radial_of_half_le b (e.toFun ∘ f) hx.le]
    rfl
  have hC' : A.transverse x v = coordinates e.ambientDimension (d + 1)
      ((A.boundaryTransverse s v, 0), 0) := by
    rw [hCx]
    exact (append_boundaryTransverse e a f hf hd D A s v).symm.trans
      (coordinates_old e.ambientDimension (d + 1) _).symm
  change D.map x + A.transverse x v = _
  rw [hD', hC', ← map_add]
  simp only [Prod.mk_add_mk, add_zero]
  rfl

include a hf hd in
theorem thickening_radial_collar_avoids {x : Vector (d + 1)} (hx : x ∈ ball (0 : Vector (d + 1)) 1)
    (hhalf : (1 / 2 : ℝ) < ‖x‖) (hDx : D.map x = collar b (e.toFun ∘ f) x)
    (hCx : A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val)
    (v : Vector (7 - d)) :
    LowDiskThickening.map D.map A.transverse (x, v) ∉
      range (appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))) := by
  rintro ⟨y, hy⟩
  have hH := thickening_radial_collar e a f hf hd D A hhalf hDx hCx v
  have he : ((ambientSphereTube e f A.boundaryTransverse
        (SphereRadialRetraction.retract b x, v), definingFunction x), (0 : ℝ × Vector (d + 1))) =
      ((y, 0), 0) := (coordinates e.ambientDimension (d + 1)).injective (by
    rw [← hH, coordinates_old]
    exact hy.symm)
  have hρ : definingFunction x = 0 :=
    congrArg (fun p : (Vector e.ambientDimension × ℝ) × (ℝ × Vector (d + 1)) ↦ p.1.2) he
  have hn : ‖x‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using (definingFunction_eq_zero_iff x).mp hρ
  have hlt : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
  exact (ne_of_lt hlt) hn

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
