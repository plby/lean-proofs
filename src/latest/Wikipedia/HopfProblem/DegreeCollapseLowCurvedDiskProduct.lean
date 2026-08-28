import Wikipedia.HopfProblem.DegreeCollapseLowSphereTubeDifference
import Wikipedia.HopfProblem.DegreeCollapseLowRadialCorrection
import Wikipedia.HopfProblem.DegreeCollapseLowAffineDiskCollar

/-!

# Actual curved low-surgery products with their whole native attaching face

The supported correction keeps the original disk core and its full derivative.
Its whole boundary and radial collar match the original native manifold tube.
Embedding, full normal framing and uniform interior avoidance are separate
obligations, not consequences assumed from these exact core identities.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  (f : NoExoticSixSphere.Sphere d → M) {b : NoExoticSixSphere.Sphere d}
  (D : FramedDisk b (e.toFun ∘ f) (fun s => a.orthonormal (f s)))
  (A : LowFramedProduct.FramedProduct (q := 7 - d) D.map D.frame)
  (R : EuclideanEmbedding.TubularRetraction e) (χ : ContDiffBump (0 : Vector (d + 1)))

def curvedDiskProduct (p : Vector (d + 1) × Vector (7 - d)) :
    Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  LowDiskThickening.map D.map A.transverse p + appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))
    (LowRadialCorrection.correction χ b (sphereTubeDifference e f A.boundaryTransverse R) p)

theorem curvedDiskProduct_core (x : Vector (d + 1)) :
    curvedDiskProduct e f D A R χ (x, 0) = D.map x := by
  rw [curvedDiskProduct, LowRadialCorrection.correction_core χ b _
    (sphereTubeDifference_core e f A.boundaryTransverse R), map_zero, add_zero,
    LowDiskThickening.map_core]

theorem curvedDiskProduct_eq_affine {x : Vector (d + 1)}
    (hx : x ∈ closedBall (0 : Vector (d + 1)) χ.rIn) (v : Vector (7 - d)) :
    curvedDiskProduct e f D A R χ (x, v) = LowDiskThickening.map D.map A.transverse (x, v) := by
  rw [curvedDiskProduct, LowRadialCorrection.correction_eq_zero χ b _ hx,
    map_zero, add_zero]

theorem curvedDiskProduct_avoids {p : Vector (d + 1) × Vector (7 - d)}
    (hp : LowDiskThickening.map D.map A.transverse p ∉
      range (appendZeroMap e.ambientDimension (1 + (1 + (d + 1))))) :
    curvedDiskProduct e f D A R χ p ∉
      range (appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))) := by
  rintro ⟨y, hy⟩
  let w := LowRadialCorrection.correction χ b
    (sphereTubeDifference e f A.boundaryTransverse R) p
  apply hp
  refine ⟨y - w, ?_⟩
  rw [map_sub, hy]
  change (LowDiskThickening.map D.map A.transverse p +
    appendZeroMap e.ambientDimension (1 + (1 + (d + 1))) w) -
      appendZeroMap e.ambientDimension (1 + (1 + (d + 1))) w = _
  exact add_sub_cancel_right _ _

variable (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)

include hf in
theorem contDiffAt_curvedDiskProduct {x : Vector (d + 1)}
    (hx : x ∈ closedBall (0 : Vector (d + 1)) 1)
    (v : Vector (7 - d))
    (hp : (SphereRadialRetraction.retract b x, v) ∈ sphereTubeDomain e f A.boundaryTransverse R) :
    ContDiffAt ℝ ∞ (curvedDiskProduct e f D A R χ) (x, v) := by
  have hH := LowDiskThickening.contDiffAt_map D.map A.transverse x v
    D.smooth.contDiffAt (A.smooth_transverse x hx)
  have hc := LowRadialCorrection.contDiffAt_correction χ b
    (sphereTubeDifference e f A.boundaryTransverse R) x v
      (contMDiffAt_sphereTubeDifference e f A.boundaryTransverse R hf
        A.contMDiff_boundaryTransverse hp)
  exact hH.add
    ((appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))).contDiff.contDiffAt.comp (x, v) hc)

variable (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))

include hf hd in
theorem fderiv_curvedDiskProduct_core {x : Vector (d + 1)}
    (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
    fderiv ℝ (curvedDiskProduct e f D A R χ) (x, 0) =
      fderiv ℝ (LowDiskThickening.map D.map A.transverse) (x, 0) := by
  let g := sphereTubeDifference e f A.boundaryTransverse R
  have hgs (s : NoExoticSixSphere.Sphere d) :
      ContMDiffAt ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension) ∞
      g (s, 0) := contMDiffAt_sphereTubeDifference e f A.boundaryTransverse R hf
    A.contMDiff_boundaryTransverse (core_mem_sphereTubeDomain e f A.boundaryTransverse R s)
  have hgj (s : NoExoticSixSphere.Sphere d) :
      mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension) g (s, 0) = 0 :=
    mfderiv_sphereTubeDifference_core e f A.boundaryTransverse R hf A.contMDiff_boundaryTransverse
      hd (fun s ↦ Stiefel.injective
        ⟨A.boundaryTransverse s, norm_boundaryTransverse e a f hf hd D A s⟩)
      (range_boundaryTransverse e a f hf hd D A) s
  have hc := (LowRadialCorrection.contDiffAt_correction χ b g x 0
    (hgs (SphereRadialRetraction.retract b x))).differentiableAt (by simp)
  have hj := LowRadialCorrection.fderiv_correction_core χ b g hgs
    (sphereTubeDifference_core e f A.boundaryTransverse R) hgj x
  have hc' := hc.hasFDerivAt
  rw [hj] at hc'
  have hH := (LowDiskThickening.contDiffAt_map D.map A.transverse x 0
    D.smooth.contDiffAt (A.smooth_transverse x hx)).differentiableAt (by simp)
  have he := (hH.hasFDerivAt.add
    ((appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))).hasFDerivAt.comp (x, 0) hc')).fderiv
  change fderiv ℝ (curvedDiskProduct e f D A R χ) (x, 0) = _ at he
  simpa only [ContinuousLinearMap.comp_zero, add_zero] using he

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

noncomputable section

open Function
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
  (R : EuclideanEmbedding.TubularRetraction e) (χ : ContDiffBump (0 : Vector (d + 1)))

include hf hd in
theorem curvedDiskProduct_collar {x : Vector (d + 1)} (hx : (1 / 2 : ℝ) < ‖x‖)
    (hχ : χ.rOut ≤ ‖x‖) (hDx : D.map x = collar b (e.toFun ∘ f) x)
    (hCx : A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val)
    (v : Vector (7 - d)) :
    curvedDiskProduct e f D A R χ (x, v) = coordinates e.ambientDimension (d + 1)
      ((e.toFun (internalSphereTube e f A.boundaryTransverse R
        (SphereRadialRetraction.retract b x, v)), definingFunction x), 0) := by
  rw [curvedDiskProduct, thickening_radial_collar e a f hf hd D A hx hDx hCx,
    LowRadialCorrection.correction_eq_radial χ b _ hχ,
    ← coordinates_old e.ambientDimension (d + 1), ← map_add]
  simp only [Prod.mk_add_mk, add_zero]
  rw [ambientSphereTube_add_difference e]

include hf hd in
theorem curvedDiskProduct_boundary (hχ : χ.rOut ≤ 1)
    (s : NoExoticSixSphere.Sphere d) (v : Vector (7 - d)) :
    curvedDiskProduct e f D A R χ (s.val, v) = appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))
      (e.toFun (internalSphereTube e f A.boundaryTransverse R (s, v))) := by
  have hχs : χ.rOut ≤ ‖s.val‖ := by rw [ClosedHemisphere.unit_norm]; exact hχ
  rw [curvedDiskProduct, thickening_boundary_affine e a f hf hd D A,
    LowRadialCorrection.correction_eq_radial χ b _ hχs,
    SphereRadialRetraction.retract_coe, ← map_add, ambientSphereTube_add_difference e]

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
