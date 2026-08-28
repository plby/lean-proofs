import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
import Wikipedia.HomotopyGroupsOfSpheres.Basic

/-! # Quaternionic unit columns are the standard Euclidean spheres -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open QuaternionicRankOne

local notation "ℍ" => Quaternion ℝ

variable {N : Type*} [Fintype N]

theorem pairing_self_eq_norm_sq (v : N → ℍ) :
    pairing v v = ((‖(WithLp.toLp 2 v : PiLp 2 (fun _ : N => ℍ))‖ ^ 2 : ℝ) : ℍ) := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [pairing, Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, pow_two]
  change (∑ i, algebraMap ℝ ℍ (‖v i‖ * ‖v i‖)) =
    algebraMap ℝ ℍ (∑ i, ‖v i‖ * ‖v i‖)
  rw [map_sum]

theorem pairing_self_eq_one_iff_norm (v : N → ℍ) :
    pairing v v = 1 ↔ ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : N => ℍ))‖ = 1 := by
  rw [pairing_self_eq_norm_sq]
  constructor
  · intro h
    have hr : ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : N => ℍ))‖ ^ 2 = 1 :=
      congrArg (fun q : ℍ => q.re) h
    nlinarith [norm_nonneg (WithLp.toLp 2 v : PiLp 2 (fun _ : N => ℍ))]
  · intro h
    rw [h, one_pow, Quaternion.coe_one]

abbrev QuaternionSpace (n : ℕ) := PiLp 2 (fun _ : Fin (n + 1) => ℍ)

theorem quaternionSpace_finrank (n : ℕ) : Module.finrank ℝ (QuaternionSpace n) = 4 * n + 4 := by
  rw [(WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℍ)).finrank_eq,
    Module.finrank_pi_fintype]
  simp [Quaternion.finrank_eq_four, Nat.add_mul, Nat.mul_comm]

/-- Real orthonormal coordinates on the quaternionic vector space. -/
def quaternionCoordinates (n : ℕ) :
    QuaternionSpace n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (4 * n + 4)) :=
  ((stdOrthonormalBasis ℝ (QuaternionSpace n)).reindex (finCongr (quaternionSpace_finrank n))).repr

/-- The column sphere in quaternionic rank `n+1` is the literal `(4n+3)`-sphere. -/
def columnSphereHomeomorph (n : ℕ) : UnitColumn (Fin (n + 1)) ≃ₜ Sphere (4 * n + 3) where
  toFun v := ⟨quaternionCoordinates n (WithLp.toLp 2 v.val), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [(quaternionCoordinates n).norm_map]
    exact (pairing_self_eq_one_iff_norm v.val).mp v.property⟩
  invFun v := ⟨WithLp.ofLp ((quaternionCoordinates n).symm v.val), by
    apply (pairing_self_eq_one_iff_norm _).mpr
    change ‖(quaternionCoordinates n).symm v.val‖ = 1
    rw [(quaternionCoordinates n).symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp v.property⟩
  left_inv v := by
    apply Subtype.ext
    exact congrArg WithLp.ofLp ((quaternionCoordinates n).symm_apply_apply (WithLp.toLp 2 v.val))
  right_inv v := by
    apply Subtype.ext
    exact (quaternionCoordinates n).apply_symm_apply v.val
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (quaternionCoordinates n).continuous.comp
      ((PiLp.homeomorph 2 (fun _ : Fin (n + 1) => ℍ)).symm.continuous.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (PiLp.homeomorph 2 (fun _ : Fin (n + 1) => ℍ)).continuous.comp
      ((quaternionCoordinates n).symm.continuous.comp continuous_subtype_val)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
