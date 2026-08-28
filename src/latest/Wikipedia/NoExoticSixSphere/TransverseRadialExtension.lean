import Wikipedia.NoExoticSixSphere.BoundaryTransverseOperator
import Wikipedia.NoExoticSixSphere.SmoothSphereRadialCollar

/-!
# The actual boundary transverse frame's smooth radial extension

The ambient cutoff extension agrees with the entire stabilized transverse
operator on the sphere and is exactly radial and orthonormal outside its
cutoff support. It is not asserted normal to the disk without a collar
comparison, which is proved separately.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.DiskThickening.FramedProduct

open GLOrthonormalization

variable {N k q : ℕ} {D : Vector 4 → Vector (N + 6)}
  {T : Vector 4 → Vector k →L[ℝ] Vector (N + 6)} (A : FramedProduct D T q) (b : Sphere 3)

def transverseExtension : C(Vector 4, Vector q →L[ℝ] Vector (N + 6)) :=
  ⟨SmoothSphereAmbient.extension b (fun s ↦ A.transverse s.val),
    (SmoothSphereAmbient.contDiff_extension b _ A.contMDiff_transverse_boundary).continuous⟩

theorem contDiff_transverseExtension : ContDiff ℝ ∞ (A.transverseExtension b) :=
  SmoothSphereAmbient.contDiff_extension b _ A.contMDiff_transverse_boundary

theorem transverseExtension_coe (s : Sphere 3) :
    A.transverseExtension b s.val = A.transverse s.val :=
  SmoothSphereAmbient.extension_coe b (fun s ↦ A.transverse s.val) s

theorem transverseExtension_eq_radial {x : Vector 4} (hx : (1 / 2 : ℝ) < ‖x‖) :
    A.transverseExtension b x = A.transverse (SphereRadialRetraction.retract b x).val :=
  SmoothSphereAmbient.extension_eq_radial_of_half_le b (fun s ↦ A.transverse s.val) hx.le

theorem norm_transverseExtension {x : Vector 4} (hx : (1 / 2 : ℝ) < ‖x‖)
    (w : Vector q) : ‖A.transverseExtension b x w‖ = ‖w‖ := by
  rw [A.transverseExtension_eq_radial b hx]
  exact A.norm_transverse _ (Metric.sphere_subset_closedBall
    (SphereRadialRetraction.retract b x).property) w

end NoExoticSixSphere.DiskThickening.FramedProduct
