import Wikipedia.NoExoticSixSphere.SpanningDiskBoundaryComplementFrame
import Wikipedia.NoExoticSixSphere.FramedDiskThickening
import Wikipedia.NoExoticSixSphere.SmoothSphereRadialCollar

/-!
# Exact affine collar coordinates and avoidance for a radial disk product

The unchanged boundary columns have only old ambient coordinates. Radiality
therefore expresses the entire product collar by the original sphere, its
transverse boundary frame, the actual disk height, and zero graph coordinates.
The nonzero height proves interior collar avoidance for every transverse vector.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization

variable {N k q : ℕ} {b : Sphere 3} {f : Sphere 3 → Vector N} (D : DiskData b f)
  {T : Vector 4 → Vector k →L[ℝ] Vector (N + 6)}
  (A : DiskThickening.FramedProduct D.toFun T q)
  (hCb : ∀ s v, appendZeroMap N 6 (boundaryComplementOperator A.transverse s v) =
    A.transverse s.val v)

include hCb in
theorem affine_radial_collar {x : Vector 4} (hx : (1 / 2 : ℝ) < ‖x‖)
    (hDx : D.toFun x = collar b f x)
    (hCx : A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val)
    (v : Vector q) :
    DiskThickening.map D.toFun A.transverse (x, v) = coordinates N 4
      ((f (SphereRadialRetraction.retract b x) +
        boundaryComplementOperator A.transverse (SphereRadialRetraction.retract b x) v,
        definingFunction x), 0) := by
  let s := SphereRadialRetraction.retract b x
  have hD' : D.toFun x = coordinates N 4 ((f s, definingFunction x), 0) := by
    rw [hDx]
    change coordinates N 4 ((SmoothSphereAmbient.extension b f x, definingFunction x), 0) = _
    rw [SmoothSphereAmbient.extension_eq_radial_of_half_le b f hx.le]
  have hC' : A.transverse x v = coordinates N 4
      ((boundaryComplementOperator A.transverse s v, 0), 0) := by
    rw [hCx]
    exact (hCb s v).symm.trans (coordinates_old N 4 _).symm
  change D.toFun x + A.transverse x v = _
  rw [hD', hC', ← map_add]
  simp only [Prod.mk_add_mk, add_zero]
  rfl

include hCb in
theorem affine_radial_collar_avoids {x : Vector 4} (hx : x ∈ ball (0 : Vector 4) 1)
    (hhalf : (1 / 2 : ℝ) < ‖x‖) (hDx : D.toFun x = collar b f x)
    (hCx : A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val)
    (v : Vector q) :
    DiskThickening.map D.toFun A.transverse (x, v) ∉ range (appendZeroMap N 6) := by
  rintro ⟨y, hy⟩
  have hH := D.affine_radial_collar A hCb hhalf hDx hCx v
  have he : ((f (SphereRadialRetraction.retract b x) +
        boundaryComplementOperator A.transverse (SphereRadialRetraction.retract b x) v,
        definingFunction x), (0 : ℝ × Vector 4)) = ((y, 0), 0) :=
    (coordinates N 4).injective (by rw [← hH, coordinates_old]; exact hy.symm)
  have hρ : definingFunction x = 0 :=
    congrArg (fun p : (Vector N × ℝ) × (ℝ × Vector 4) ↦ p.1.2) he
  have hn : ‖x‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using (definingFunction_eq_zero_iff x).mp hρ
  have hlt : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
  exact (ne_of_lt hlt) hn

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
