import Wikipedia.NoExoticSixSphere.SphereCylinderCoordinates
import Wikipedia.NoExoticSixSphere.SphereMapSuspension

/-!
# Suspension in the original smooth cylinder charts

On the sphere minus its poles, suspension is exactly the product map
`(s,x) ↦ (s,f(x))` in the proved cylinder coordinates. The comparison is an
equality of actual maps, not an assigned differential or a homotopy statement.
-/

noncomputable section

namespace NoExoticSixSphere.SphereMapSuspension

open Wikipedia.HopfProblem.SphereHomology

theorem tail_latitude (n : ℕ) (t : unitInterval) (x : Sphere n) :
    SphereCylinder.tail n (Latitude.point n t x).val = Latitude.radius t • x.val := by
  ext i
  rfl

theorem norm_tail_latitude (n : ℕ) (t : unitInterval) (x : Sphere n) :
    ‖SphereCylinder.tail n (Latitude.point n t x).val‖ = Latitude.radius t := by
  rw [tail_latitude, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Latitude.radius_nonneg t), ClosedHemisphere.unit_norm, mul_one]

theorem latitude_mem_band_iff (n : ℕ) (t : unitInterval) (x : Sphere n) :
    Latitude.point n t x ∈ SphereCylinder.band n ↔ t ≠ 0 ∧ t ≠ 1 := by
  constructor
  · intro h
    constructor
    · intro ht
      subst t
      apply h
      rw [tail_latitude, Latitude.radius_zero, zero_smul]
    · intro ht
      subst t
      apply h
      rw [tail_latitude, Latitude.radius_one, zero_smul]
  · rintro ⟨h0, h1⟩
    change SphereCylinder.tail n (Latitude.point n t x).val ≠ 0
    apply norm_ne_zero_iff.mp
    rw [norm_tail_latitude]
    exact ne_of_gt (Latitude.radius_pos_of_interior t h0 h1)

theorem inverse_latitude (n : ℕ) (t : unitInterval) (x : Sphere n)
    (h0 : t ≠ 0) (h1 : t ≠ 1) :
    SphereCylinder.inverse n (Latitude.point n t x) =
      (Latitude.height t / Latitude.radius t, x) := by
  apply Prod.ext
  · change Latitude.height t / ‖SphereCylinder.tail n (Latitude.point n t x).val‖ = _
    rw [norm_tail_latitude]
  · apply Subtype.ext
    have hy := (latitude_mem_band_iff n t x).mpr ⟨h0, h1⟩
    change (SphereRadialRetraction.retract _
      (SphereCylinder.tail n (Latitude.point n t x).val)).val = x.val
    rw [SphereRadialRetraction.retract, dif_neg hy]
    change NormedSpace.normalize (SphereCylinder.tail n (Latitude.point n t x).val) = x.val
    rw [tail_latitude, NormedSpace.normalize_smul_of_pos
      (Latitude.radius_pos_of_interior t h0 h1)]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm x)

variable {m n : ℕ}

theorem map_mem_band_iff (f : C(Sphere m, Sphere n)) (y : Sphere (m + 1)) :
    map f y ∈ SphereCylinder.band n ↔ y ∈ SphereCylinder.band m := by
  obtain ⟨⟨t, x⟩, rfl⟩ := Latitude.point_surjective m y
  rw [map_point, latitude_mem_band_iff, latitude_mem_band_iff]

theorem inverse_map (f : C(Sphere m, Sphere n)) {y : Sphere (m + 1)}
    (hy : y ∈ SphereCylinder.band m) :
    SphereCylinder.inverse n (map f y) =
      ((SphereCylinder.inverse m y).1, f (SphereCylinder.inverse m y).2) := by
  obtain ⟨⟨t, x⟩, rfl⟩ := Latitude.point_surjective m y
  obtain ⟨h0, h1⟩ := (latitude_mem_band_iff m t x).mp hy
  rw [map_point, inverse_latitude n t (f x) h0 h1, inverse_latitude m t x h0 h1]

theorem map_cylinder_point (f : C(Sphere m, Sphere n)) (p : ℝ × Sphere m) :
    map f (SphereCylinder.point m p) = SphereCylinder.point n (p.1, f p.2) := by
  have hy : map f (SphereCylinder.point m p) ∈ SphereCylinder.band n :=
    (map_mem_band_iff f _).mpr (SphereCylinder.tail_point_ne_zero m p)
  calc
    _ = SphereCylinder.point n (SphereCylinder.inverse n (map f (SphereCylinder.point m p))) :=
      (SphereCylinder.point_inverse n _ hy).symm
    _ = _ := by
      rw [inverse_map f (SphereCylinder.tail_point_ne_zero m p), SphereCylinder.inverse_point]

/-- The literal local formula in the existing smooth sphere atlases. -/
theorem map_eq_cylinder (f : C(Sphere m, Sphere n)) {y : Sphere (m + 1)}
    (hy : y ∈ SphereCylinder.band m) :
    map f y = SphereCylinder.point n
      ((SphereCylinder.inverse m y).1, f (SphereCylinder.inverse m y).2) :=
  (congrArg (map f) (SphereCylinder.point_inverse m y hy)).symm.trans
    (map_cylinder_point f (SphereCylinder.inverse m y))

end NoExoticSixSphere.SphereMapSuspension
