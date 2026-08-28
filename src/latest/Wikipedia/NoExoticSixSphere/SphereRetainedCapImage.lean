import Wikipedia.NoExoticSixSphere.SphereRetainedCapCoordinates

/-!
# The folded retained caps use only the removed source disks

The inverse scale-five cap coordinates have exact height thresholds.
The old exterior caps lie strictly beyond those thresholds. Since the
constructed cap homeomorphisms agree with the old cap parametrizations
there, their complementary closed caps map into the removed source disks.
The region between the retained caps lies strictly inside the neck region.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization SphereHemisphereRetraction

theorem northRetainedCap_inverse_head_nonpos (x : Sphere 3) :
    (northRetainedCap.symm x).val 0 ≤ 0 ↔ x.val 0 ≤ (12 / 13 : ℝ) := by
  change (axisDilation (5 : ℝ)⁻¹ x).val 0 ≤ 0 ↔ _
  rw [axisDilation_head (by norm_num), div_le_iff₀ (axisDenominator_pos (by norm_num) x)]
  dsimp [axisNumerator, axisDenominator]
  constructor <;> intro h <;> linarith

theorem southRetainedCap_inverse_head_nonpos (x : Sphere 3) :
    (southRetainedCap.symm x).val 0 ≤ 0 ↔ -(12 / 13 : ℝ) ≤ x.val 0 := by
  change (northRetainedCap.symm (reflectHead x)).val 0 ≤ 0 ↔ _
  rw [northRetainedCap_inverse_head_nonpos, reflectHead_head]
  constructor <;> intro h <;> linarith

theorem northExterior_head_gt {x : Sphere 3} (hx : x ∈ northExterior) :
    (12 / 13 : ℝ) < x.val 0 := by
  have hl : 4 * ‖SphereCylinder.tail 2 x.val‖ ≤ x.val 0 := by
    have hn : ¬ |x.val 0| < 4 * ‖SphereCylinder.tail 2 x.val‖ := hx.2
    have h := le_of_not_gt hn
    rwa [abs_of_pos hx.1] at h
  have hl2 := mul_self_le_mul_self (by positivity : 0 ≤ 4 * ‖SphereCylinder.tail 2 x.val‖) hl
  by_contra hh
  have hh2 := mul_self_le_mul_self hx.1.le (le_of_not_gt hh)
  nlinarith [source_head_tail_sq x]

theorem northCapHomeomorph_mem_removed (ε : ℝ) (hε : 0 < ε) (x : Sphere 3)
    (hx : (northRetainedCap.symm x).val 0 ≤ 0) :
    northCapHomeomorph ε hε x ∈ removedSourceDisk ε := by
  by_contra hout
  obtain ⟨y, hy⟩ := (northExteriorCap_bijective ε hε).surjective
    ⟨northCapHomeomorph ε hε x, hout⟩
  have hc : sphereCap ε y.val = northCapHomeomorph ε hε x := congrArg Subtype.val hy
  have he : y.val = x := (northCapHomeomorph ε hε).injective
    ((northCapHomeomorph_exterior ε hε y.property).trans hc)
  have hh := northExterior_head_gt y.property
  rw [he] at hh
  exact (not_lt_of_ge ((northRetainedCap_inverse_head_nonpos x).mp hx)) hh

theorem southCapHomeomorph_mem_removed (ε : ℝ) (hε : 0 < ε) (x : Sphere 3)
    (hx : (southRetainedCap.symm x).val 0 ≤ 0) :
    southCapHomeomorph ε hε x ∈ removedSourceDisk ε :=
  northCapHomeomorph_mem_removed ε hε (reflectHead x) hx

theorem foldedNorthSource_mem_removed (ε : ℝ) (hε : 0 < ε) (x : North) :
    northCapHomeomorph ε hε (northRetainedCap (reflectHead x.val)) ∈ removedSourceDisk ε := by
  apply northCapHomeomorph_mem_removed
  rw [northRetainedCap.symm_apply_apply, reflectHead_head]
  exact neg_nonpos.mpr ((mem_north_iff x.val).mp x.property)

theorem foldedSouthSource_mem_removed (ε : ℝ) (hε : 0 < ε) (x : North) :
    southCapHomeomorph ε hε (southRetainedCap (reflectHead x.val)) ∈ removedSourceDisk ε := by
  apply southCapHomeomorph_mem_removed
  rw [southRetainedCap.symm_apply_apply, reflectHead_head]
  exact neg_nonpos.mpr ((mem_north_iff x.val).mp x.property)

theorem between_retained_caps_mem_neckRegion (x : Sphere 3)
    (hN : (northRetainedCap.symm x).val 0 ≤ 0)
    (hS : (southRetainedCap.symm x).val 0 ≤ 0) : x ∈ neckRegion := by
  have hh : |x.val 0| ≤ (12 / 13 : ℝ) := abs_le.mpr
    ⟨(southRetainedCap_inverse_head_nonpos x).mp hS,
      (northRetainedCap_inverse_head_nonpos x).mp hN⟩
  have hh2 := mul_self_le_mul_self (abs_nonneg (x.val 0)) hh
  have hs := source_head_tail_sq x
  have ht : (5 / 13 : ℝ) ≤ ‖SphereCylinder.tail 2 x.val‖ := by
    rw [← sq, sq_abs] at hh2
    nlinarith [norm_nonneg (SphereCylinder.tail 2 x.val)]
  change |x.val 0| < 4 * ‖SphereCylinder.tail 2 x.val‖
  linarith

end NoExoticSixSphere.SphereSumNeck
