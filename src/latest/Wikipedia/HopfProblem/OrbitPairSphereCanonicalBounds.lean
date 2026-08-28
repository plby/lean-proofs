import Wikipedia.HopfProblem.OrbitPairSphereCanonicalSegment

/-!
# Chord-distance control of the canonical short sphere segment

At any unit-interval time the canonical nonantipodal segment is no farther
from its initial vertex than its final vertex is. This gives the metric
control needed to compare polygon replacement with a continuous path.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.OrbitPair.SphereCanonicalGeodesic

open NoExoticSixSphere GLOrthonormalization SphereAngle SphereTangentExponential
  SpherePairedGeodesic

variable {n : ℕ}

theorem inner_base_segment (a b : Sphere n) (hab : (a, b) ∈ nonantipodal n) (t : ℝ) :
    inner ℝ a.val (segment a b t).val =
      Real.cos (Real.arccos (inner ℝ a.val b.val) * t) := by
  by_cases he : a = b
  · subst b
    rw [segment_self]
    simp [real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm]
  let V := tangentLog a.val b.val (ClosedHemisphere.unit_norm a)
  have hV : V ≠ 0 := by
    intro hz
    have hlog : logVector a.val b.val = 0 := congrArg Subtype.val hz
    exact he (Subtype.ext ((logVector_eq_zero_iff (x := a.val) (y := b.val)
      (ClosedHemisphere.unit_norm a) (ClosedHemisphere.unit_norm b) hab).mp hlog))
  have hn : ‖V‖ = Real.arccos (inner ℝ a.val b.val) := by
    change ‖logVector a.val b.val‖ = _
    exact norm_logVector (x := a.val) (y := b.val)
      (ClosedHemisphere.unit_norm a) (ClosedHemisphere.unit_norm b) hab
  have horth : inner ℝ a.val (V : Vector (n + 1)) = 0 := inner_tangent a.val V
  change inner ℝ a.val (curve a.val V t) = _
  rw [curve_formula_of_ne_zero (ClosedHemisphere.unit_norm a) V hV]
  simp only [inner_add_right, real_inner_smul_right, horth,
    real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm, one_pow,
    mul_one, mul_zero, add_zero, hn]

theorem dist_segment_start_le (a b : Sphere n) (hab : (a, b) ∈ nonantipodal n)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : dist (segment a b t).val a.val ≤ dist b.val a.val := by
  let angle := Real.arccos (inner ℝ a.val b.val)
  have hangle : 0 ≤ angle := Real.arccos_nonneg _
  have hcos : inner ℝ a.val b.val ≤ Real.cos (angle * t) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg hangle ht.1)
      (Real.arccos_le_pi (inner ℝ a.val b.val))
      (mul_le_of_le_one_right hangle ht.2)
    simpa only [angle, Real.cos_arccos hab.le
      (real_inner_le_one_of_norm_eq_one (ClosedHemisphere.unit_norm a)
        (ClosedHemisphere.unit_norm b))] using h
  have hs : dist (segment a b t).val a.val ^ 2 = 2 - 2 * Real.cos (angle * t) := by
    have hcomm : inner ℝ (segment a b t).val a.val = inner ℝ a.val (segment a b t).val :=
      real_inner_comm _ _
    rw [dist_eq_norm, norm_sub_sq_real, ClosedHemisphere.unit_norm,
      ClosedHemisphere.unit_norm, hcomm, inner_base_segment a b hab]
    dsimp [angle]
    ring
  have he : dist b.val a.val ^ 2 = 2 - 2 * inner ℝ a.val b.val := by
    have hcomm : inner ℝ b.val a.val = inner ℝ a.val b.val := real_inner_comm _ _
    rw [dist_eq_norm, norm_sub_sq_real, ClosedHemisphere.unit_norm,
      ClosedHemisphere.unit_norm, hcomm]
    ring
  nlinarith [show 0 ≤ dist (segment a b t).val a.val from dist_nonneg,
    show 0 ≤ dist b.val a.val from dist_nonneg]

theorem nonantipodal_of_dist_lt_one (a b : Sphere n) (h : dist b.val a.val < 1) :
    (a, b) ∈ nonantipodal n := by
  have he : dist b.val a.val ^ 2 = 2 - 2 * inner ℝ a.val b.val := by
    have hcomm : inner ℝ b.val a.val = inner ℝ a.val b.val := real_inner_comm _ _
    rw [dist_eq_norm, norm_sub_sq_real, ClosedHemisphere.unit_norm,
      ClosedHemisphere.unit_norm, hcomm]
    ring
  change -1 < inner ℝ a.val b.val
  nlinarith [show 0 ≤ dist b.val a.val from dist_nonneg]

end Wikipedia.HopfProblem.OrbitPair.SphereCanonicalGeodesic
