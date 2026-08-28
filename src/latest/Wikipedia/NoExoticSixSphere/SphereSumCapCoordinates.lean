import Wikipedia.NoExoticSixSphere.SphereHemisphereRadialCoordinates
import Wikipedia.SmoothSixDPoincare.ReferenceSphereComplementChart

/-!
# Smooth sphere caps with the prescribed radial neck formula

The complementary reference sphere chart absorbs reciprocal radial size.
The resulting map is smooth at the actual north pole and is a native local
diffeomorphism throughout the open hemisphere. On the cylinder it agrees
exactly with the original reference chart at the linear radial coordinate.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization Wikipedia.SmoothSixDPoincare.SphereCoordinates

abbrev sourceChart := referenceChart (Vector 3) 3 (by simp)

abbrev sourceComplementChart := referenceComplementChart (Vector 3) 3 (by simp)

theorem sourceChart_source : sourceChart.source = univ := referenceChart_source _ _ _

theorem sourceComplementChart_source : sourceComplementChart.source = univ :=
  referenceComplementChart_source _ _ _

theorem sourceComplementChart_inverse_ray {r : ℝ} (hr : 0 < r) (s : Sphere 2) :
    sourceComplementChart (r⁻¹ • s.val) = sourceChart (r • s.val) := by
  have hne : r⁻¹ • s.val ≠ 0 :=
    smul_ne_zero (inv_ne_zero hr.ne') (ne_zero_of_mem_unit_sphere s)
  rw [referenceComplementChart_inversion _ _ _ hne]
  congr 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
    ClosedHemisphere.unit_norm, mul_one, inv_pow, inv_inv, smul_smul]
  congr 1
  field_simp

def sphereCap (ε : ℝ) (x : Sphere 3) : Sphere 3 :=
  sourceComplementChart (ε⁻¹ • gnomonic x)

def capScaling (ε : ℝ) (hε : ε ≠ 0) : Vector 3 ≃L[ℝ] Vector 3 :=
  (LinearEquiv.smulOfNeZero ℝ (Vector 3) ε⁻¹ (inv_ne_zero hε)).toContinuousLinearEquiv

def sphereCapCoordinates (ε : ℝ) (hε : ε ≠ 0) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (Sphere 3) (Sphere 3) ∞ :=
  (gnomonicChart.trans (capScaling ε hε).toDiffeomorph.toPartialDiffeomorph).trans
    sourceComplementChart

theorem sphereCapCoordinates_apply (ε : ℝ) (hε : ε ≠ 0) (x : Sphere 3) :
    sphereCapCoordinates ε hε x = sphereCap ε x := rfl

theorem sphereCapCoordinates_source (ε : ℝ) (hε : ε ≠ 0) :
    (sphereCapCoordinates ε hε).source = {x | 0 < x.val 0} := by
  ext x
  change ((0 < x.val 0 ∧ gnomonic x ∈ (univ : Set (Vector 3))) ∧
    capScaling ε hε (gnomonic x) ∈ sourceComplementChart.source) ↔ 0 < x.val 0
  rw [sourceComplementChart_source]
  simp only [mem_univ, and_true]

theorem isLocalDiffeomorphAt_sphereCap {ε : ℝ} (hε : ε ≠ 0) {x : Sphere 3}
    (hx : 0 < x.val 0) : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (sphereCap ε) x := by
  refine ⟨sphereCapCoordinates ε hε, ?_, fun _ _ ↦ rfl⟩
  rwa [sphereCapCoordinates_source]

theorem contMDiffAt_sphereCap {ε : ℝ} (hε : ε ≠ 0) {x : Sphere 3} (hx : 0 < x.val 0) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (sphereCap ε) x :=
  (isLocalDiffeomorphAt_sphereCap hε hx).contMDiffAt

theorem bijective_mfderiv_sphereCap {ε : ℝ} (hε : ε ≠ 0) {x : Sphere 3}
    (hx : 0 < x.val 0) : Bijective (mfderiv (𝓡 3) (𝓡 3) (sphereCap ε) x) :=
  ((isLocalDiffeomorphAt_sphereCap hε hx).mfderivToContinuousLinearEquiv (by simp)).bijective

theorem sphereCap_injOn {ε : ℝ} (hε : ε ≠ 0) :
    InjOn (sphereCap ε) {x | 0 < x.val 0} := by
  intro x hx y hy he
  apply (sphereCapCoordinates ε hε).injOn
    (by rwa [sphereCapCoordinates_source]) (by rwa [sphereCapCoordinates_source])
  exact he

theorem sphereCap_cylinder {ε : ℝ} (hε : 0 < ε) (t : ℝ) (s : Sphere 2) (ht : 0 < t) :
    sphereCap ε (SphereCylinder.point 2 (t, s)) = sourceChart ((ε * t) • s.val) := by
  rw [sphereCap, gnomonic_cylinder, smul_smul, ← mul_inv]
  exact sourceComplementChart_inverse_ray (mul_pos hε ht) s

theorem sphereCap_pole (ε : ℝ) :
    sphereCap ε (SphereCylinder.endPole 2 true) =
      -referencePole 3 := by
  have hz : gnomonic (SphereCylinder.endPole 2 true) = 0 := by
    rw [gnomonic, SphereCylinder.tail_endPole, smul_zero]
  rw [sphereCap, hz, smul_zero]
  exact referenceComplementChart_zero _ _ _

end NoExoticSixSphere.SphereSumNeck
