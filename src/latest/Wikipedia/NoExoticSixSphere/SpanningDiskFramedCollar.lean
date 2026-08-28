import Wikipedia.NoExoticSixSphere.StabilizedDiskCombinedOperator
import Wikipedia.NoExoticSixSphere.SmoothSphereRadialDerivative
import Wikipedia.NoExoticSixSphere.SphereThreeRadialFrame
import Wikipedia.NoExoticSixSphere.SphereThreeFramedDerivative
import Wikipedia.NoExoticSixSphere.SpanningDiskFallback

/-!
# The actual spanning-disk collar in the fixed tangent and radial coordinates

The derivative along the quaternionic tangent frame is the original framed
sphere derivative. Its radial derivative is the new height direction with
coefficient two. These are exact formulas for the retained disk collar.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk

open GLOrthonormalization SphereThreeTangentFrame
open Wikipedia.SmoothSixDPoincare.SphereBoundary

variable {N : ℕ} (b : Sphere 3) (f : Sphere 3 → Vector N)
  (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f)

include hf

theorem fderiv_collar_tangent (s : Sphere 3) (v : Vector 3) :
    fderiv ℝ (collar b f) s.val (operator s.val v) =
      coordinates N 4 ((framedDerivative f s v, 0), 0) := by
  have he : fderiv ℝ (SmoothSphereAmbient.extension b f) s.val (operator s.val v) =
      framedDerivative f s v := by
    rw [SmoothSphereAmbient.extension_independent_fallback b (Stiefel.pole 3)]
    rfl
  have hh : fderiv ℝ (definingFunction (E := Vector 4)) s.val (operator s.val v) = 0 :=
    (fderiv_definingFunction_eq_zero_iff _ _).mpr (inner_operator s v)
  rw [fderiv_collar_apply b f hf, he, hh]

theorem fderiv_collar_radial (s : Sphere 3) :
    fderiv ℝ (collar b f) s.val s.val = coordinates N 4 ((0, 2), 0) := by
  have hh : fderiv ℝ (definingFunction (E := Vector 4)) s.val s.val = 2 := by
    rw [fderiv_definingFunction]
    rw [two_smul, add_apply]
    change inner ℝ s.val s.val + inner ℝ s.val s.val = 2
    rw [real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm]
    norm_num
  rw [fderiv_collar_apply b f hf, SmoothSphereAmbient.fderiv_extension_radial_zero b f hf, hh]

theorem fderiv_collar_radialCoordinates (s : Sphere 3) (v : Vector 4) :
    fderiv ℝ (collar b f) s.val (radialCoordinates s v) = coordinates N 4
      ((framedDerivative f s (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).1,
        2 * EuclideanTailCoordinates.scalar.symm
          (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).2), 0) := by
  rw [radialCoordinates_apply, map_add, map_smul,
    fderiv_collar_tangent b f hf, fderiv_collar_radial b f hf, ← map_smul, ← map_add]
  congr 1
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, zero_add, smul_eq_mul, mul_comm]

namespace DiskData

variable {b f} (D : DiskData b f)

theorem fderiv_radialCoordinates (s : Sphere 3) (v : Vector 4) :
    fderiv ℝ D.toFun s.val (radialCoordinates s v) = coordinates N 4
      ((framedDerivative f s (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).1,
        2 * EuclideanTailCoordinates.scalar.symm
          (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).2), 0) := by
  rw [D.fderiv_eq_collar]
  exact fderiv_collar_radialCoordinates b f hf s v

end DiskData
end NoExoticSixSphere.StabilizedSpanningDisk
