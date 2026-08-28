import Wikipedia.HopfProblem.OrbitPairSphereGreatCircleRotation

/-!
# Exact subdivision of the canonical sphere geodesic

Every subsegment of a nonantipodal geodesic is again nonantipodal. Its canonical
geodesic is the original geodesic with the literal affine time substitution.
The proof uses the actual tangent logarithm and rotated orthonormal plane,
including the constant-geodesic case.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.OrbitPair.SphereCanonicalGeodesic

open NoExoticSixSphere GLOrthonormalization SphereAngle SphereTangentExponential
  SpherePairedGeodesic

variable {n : ℕ}

theorem nonantipodal_of_plane (a b : Sphere n) (y : Vector (n + 1))
    (hxy : inner ℝ a.val y = 0) {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi)
    (hb : b.val = SphereGreatCircle.curve a.val y 1 θ) : (a, b) ∈ nonantipodal n := by
  have hc : inner ℝ a.val b.val = Real.cos θ := by
    rw [hb, SphereGreatCircle.inner_base_curve (ClosedHemisphere.unit_norm a) hxy, one_mul]
  change -1 < inner ℝ a.val b.val
  rw [hc]
  simpa only [Real.cos_pi] using
    Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2

theorem segment_of_plane (a b : Sphere n) (y : Vector (n + 1))
    (hy : ‖y‖ = 1) (hxy : inner ℝ a.val y = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi)
    (hb : b.val = SphereGreatCircle.curve a.val y 1 θ) (u : ℝ) :
    (segment a b u).val = SphereGreatCircle.curve a.val y θ u := by
  have hlog : logVector a.val b.val = θ • y := by
    rw [hb]
    exact SphereGreatCircle.logVector_curve (ClosedHemisphere.unit_norm a) hxy hθ
  let V := tangentLog a.val b.val (ClosedHemisphere.unit_norm a)
  have hn : ‖V‖ = θ := by
    change ‖logVector a.val b.val‖ = θ
    rw [hlog, norm_smul, Real.norm_eq_abs, abs_of_pos hθ.1, hy, mul_one]
  have hV : V ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact ne_of_gt hθ.1)
  have hdir : θ⁻¹ • (V : Vector (n + 1)) = y := by
    change θ⁻¹ • logVector a.val b.val = y
    rw [hlog, smul_smul, inv_mul_cancel₀ (ne_of_gt hθ.1), one_smul]
  change curve a.val V u = _
  rw [curve_formula_of_ne_zero (ClosedHemisphere.unit_norm a) V hV, hn, hdir]
  rfl

theorem exists_plane_of_ne (a b : Sphere n) (hab : (a, b) ∈ nonantipodal n) (hne : a ≠ b) :
    ∃ y : Vector (n + 1), ‖y‖ = 1 ∧ inner ℝ a.val y = 0 ∧
      ∀ u : ℝ, (segment a b u).val =
        SphereGreatCircle.curve a.val y (Real.arccos (inner ℝ a.val b.val)) u := by
  let V := tangentLog a.val b.val (ClosedHemisphere.unit_norm a)
  have hV : V ≠ 0 := by
    intro hz
    exact hne (Subtype.ext ((logVector_eq_zero_iff (x := a.val) (y := b.val)
      (ClosedHemisphere.unit_norm a) (ClosedHemisphere.unit_norm b) hab).mp
        (congrArg Subtype.val hz)))
  have hn : 0 < ‖V‖ := norm_pos_iff.mpr hV
  have hnorm : ‖V‖ = Real.arccos (inner ℝ a.val b.val) := by
    change ‖logVector a.val b.val‖ = _
    exact norm_logVector (x := a.val) (y := b.val)
      (ClosedHemisphere.unit_norm a) (ClosedHemisphere.unit_norm b) hab
  refine ⟨‖V‖⁻¹ • (V : Vector (n + 1)), ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    change ‖V‖⁻¹ * ‖V‖ = 1
    exact inv_mul_cancel₀ (ne_of_gt hn)
  · rw [real_inner_smul_right, inner_tangent, mul_zero]
  · intro u
    change curve a.val V u = _
    have h := curve_formula_of_ne_zero (ClosedHemisphere.unit_norm a) V hV u
    change curve a.val V u = SphereGreatCircle.curve a.val
      (‖V‖⁻¹ • (V : Vector (n + 1))) ‖V‖ u at h
    simpa only [hnorm] using h

theorem subsegment_spec (a b : Sphere n) (hab : (a, b) ∈ nonantipodal n)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s < t) :
    (segment a b s, segment a b t) ∈ nonantipodal n ∧
      ∀ u : ℝ, segment (segment a b s) (segment a b t) u =
        segment a b (s + (t - s) * u) := by
  by_cases he : a = b
  · subst b
    constructor
    · simpa only [segment_self] using diagonal_mem_nonantipodal a
    · intro u
      simp only [segment_self]
  obtain ⟨y, hy, hxy, hplane⟩ := exists_plane_of_ne a b hab he
  let θ := Real.arccos (inner ℝ a.val b.val)
  have hθpos : 0 < θ := Real.arccos_pos.mpr
    ((inner_lt_one_iff_real_of_norm_eq_one (ClosedHemisphere.unit_norm a)
      (ClosedHemisphere.unit_norm b)).mpr (fun h => he (Subtype.ext h)))
  have hθpi : θ < Real.pi := Real.arccos_lt_pi.mpr hab
  have hdiff : t - s ≤ 1 := by linarith [hs.1, ht.2]
  have hα : θ * (t - s) ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨mul_pos hθpos (sub_pos.mpr hst),
      (mul_le_of_le_one_right hθpos.le hdiff).trans_lt hθpi⟩
  let z := SphereGreatCircle.normalDirection a.val y θ s
  have hz : ‖z‖ = 1 := SphereGreatCircle.norm_normalDirection
    (ClosedHemisphere.unit_norm a) hy hxy θ s
  have hxz : inner ℝ (segment a b s).val z = 0 := by
    rw [hplane s]
    exact SphereGreatCircle.inner_curve_normalDirection (ClosedHemisphere.unit_norm a) hy hxy θ s
  have hend : (segment a b t).val =
      SphereGreatCircle.curve (segment a b s).val z 1 (θ * (t - s)) := by
    calc
      (segment a b t).val = SphereGreatCircle.curve a.val y θ t := hplane t
      _ = SphereGreatCircle.curve a.val y θ (s + (t - s)) := by congr 1 <;> ring
      _ = SphereGreatCircle.curve (SphereGreatCircle.curve a.val y θ s) z θ (t - s) :=
        (SphereGreatCircle.curve_shift a.val y θ s (t - s)).symm
      _ = SphereGreatCircle.curve (segment a b s).val z 1 (θ * (t - s)) := by
        rw [hplane s]
        simp only [SphereGreatCircle.curve, one_mul, θ]
  refine ⟨nonantipodal_of_plane _ _ z hxz hα hend, ?_⟩
  intro u
  apply Subtype.ext
  rw [segment_of_plane _ _ z hz hxz hα hend, SphereGreatCircle.curve_speed_mul, hplane s]
  change SphereGreatCircle.curve (SphereGreatCircle.curve a.val y θ s)
    (SphereGreatCircle.normalDirection a.val y θ s) θ ((t - s) * u) = _
  rw [SphereGreatCircle.curve_shift]
  exact (hplane (s + (t - s) * u)).symm

end Wikipedia.HopfProblem.OrbitPair.SphereCanonicalGeodesic
