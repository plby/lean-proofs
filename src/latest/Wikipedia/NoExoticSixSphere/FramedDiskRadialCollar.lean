import Wikipedia.NoExoticSixSphere.FramedDiskAttachingComparison
import Wikipedia.NoExoticSixSphere.SmoothSphereRadialCollar

/-!
# The exact affine product collar and its interior avoidance

When the disk and transverse frame have their retained radial values, the
entire thickened collar is the original ambient sphere tube with the disk's
normal height and zero graph coordinates. Every interior collar point misses
the old ambient space, regardless of the transverse vector.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : DiskThickening.FramedProduct D.toFun T)
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (e.normalFrameOnSphere a f s).val)

include hf hd hTb in
theorem thickening_radial_collar {x : Vector 4} (hx : (1 / 2 : ℝ) < ‖x‖)
    (hDx : D.toFun x = collar b (e.toFun ∘ f) x)
    (hCx : A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val)
    (v : Vector 3) :
    DiskThickening.map D.toFun A.transverse (x, v) = coordinates e.ambientDimension 4
      ((e.ambientSphereTube f A.boundaryTransverse (SphereRadialRetraction.retract b x, v),
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
    exact (e.append_boundaryTransverse a f hf hd D A hTb s v).symm.trans
      (coordinates_old e.ambientDimension 4 _).symm
  change D.toFun x + A.transverse x v = _
  rw [hD', hC', ← map_add]
  simp only [Prod.mk_add_mk, add_zero]
  rfl

include a hf hd hTb in
theorem thickening_radial_collar_avoids {x : Vector 4} (hx : x ∈ ball (0 : Vector 4) 1)
    (hhalf : (1 / 2 : ℝ) < ‖x‖) (hDx : D.toFun x = collar b (e.toFun ∘ f) x)
    (hCx : A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val)
    (v : Vector 3) :
    DiskThickening.map D.toFun A.transverse (x, v) ∉
      range (appendZeroMap e.ambientDimension 6) := by
  rintro ⟨y, hy⟩
  have hH := e.thickening_radial_collar a f hf hd D A hTb hhalf hDx hCx v
  have he : ((e.ambientSphereTube f A.boundaryTransverse
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

end NoExoticSixSphere.EuclideanEmbedding
