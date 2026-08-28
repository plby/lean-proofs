import Wikipedia.NoExoticSixSphere.PartialFrameEquatorialFactor
import Wikipedia.NoExoticSixSphere.PartialFrameOverlapCylinder

/-!
# The actual zero-latitude sphere is the coordinate-pole equator

The homeomorphism uses exactly the zero section of the previously constructed
cylinder chart. This is the base parametrization in the reduced actual
Mayer–Vietoris map, not a separately chosen equatorial parametrization.
-/

noncomputable section

namespace NoExoticSixSphere.SphereCylinder

open GLOrthonormalization

theorem pole_inner (n : ℕ) (y : Vector (n + 2)) :
    inner ℝ (spherePole (n + 1)).val y = y 0 := by
  simp [spherePole, EuclideanSpace.inner_single_left]

theorem south_equator_head_zero (n : ℕ) (y : Equator (antipode (spherePole (n + 1)))) :
    y.val.val 0 = 0 := by
  have h := y.property
  change inner ℝ (-(spherePole (n + 1)).val) y.val.val = 0 at h
  rw [inner_neg_left, pole_inner] at h
  exact neg_eq_zero.mp h

def zeroEquatorPoint (n : ℕ) (x : Sphere n) : Equator (antipode (spherePole (n + 1))) :=
  ⟨point n (0, x), by
    change inner ℝ (-(spherePole (n + 1)).val) (point n (0, x)).val = 0
    rw [inner_neg_left, pole_inner, point_head]
    simp⟩

theorem south_equator_mem_band (n : ℕ) (y : Equator (antipode (spherePole (n + 1)))) :
    y.val ∈ band n := by
  rw [band_eq_base_intersection]
  have h := Stiefel.ColumnBundle.equator_mem_baseSets (antipode (spherePole (n + 1))) y
  have he : antipode (antipode (spherePole (n + 1))) = spherePole (n + 1) :=
    Subtype.ext (neg_neg _)
  rw [he] at h
  exact ⟨h.2, h.1⟩

theorem inverse_south_equator_fst (n : ℕ) (y : Equator (antipode (spherePole (n + 1)))) :
    (inverse n y.val).1 = 0 := by
  change y.val.val 0 / ‖tail n y.val.val‖ = 0
  rw [south_equator_head_zero, zero_div]

def zeroEquatorHomeomorph (n : ℕ) : Sphere n ≃ₜ Equator (antipode (spherePole (n + 1))) where
  toFun := zeroEquatorPoint n
  invFun y := (inverse n y.val).2
  left_inv x := congrArg Prod.snd (inverse_point n (0, x))
  right_inv y := by
    apply Subtype.ext
    have h : inverse n y.val = (0, (inverse n y.val).2) :=
      Prod.ext (inverse_south_equator_fst n y) rfl
    change point n (0, (inverse n y.val).2) = y.val
    rw [← h]
    exact point_inverse n y.val (south_equator_mem_band n y)
  continuous_toFun := by
    have h : Continuous (fun x : Sphere n ↦ point n (0, x)) :=
      (point n).continuous.comp (continuous_const.prodMk continuous_id)
    exact h.subtype_mk _
  continuous_invFun := by
    let f : Equator (antipode (spherePole (n + 1))) → band n :=
      fun y ↦ ⟨y.val, south_equator_mem_band n y⟩
    have hf : Continuous f := continuous_subtype_val.subtype_mk _
    exact ((bandHomeomorph n).continuous.comp hf).snd

theorem zeroEquatorHomeomorph_val (n : ℕ) (x : Sphere n) :
    (zeroEquatorHomeomorph n x).val = point n (0, x) := rfl

end NoExoticSixSphere.SphereCylinder
