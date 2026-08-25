import StackExchange.Puzzling139335.N6.TripleSectors.Maps
import StackExchange.Puzzling139335.PlaneIsometries
import StackExchange.Puzzling139335.ThreeCorners.Rays

/-!
# Rigidity of placements of the thirty-degree sector

Two independent unit boundary directions and their common origin determine
an affine isometry.  The unordered pair permits precisely the two possible
orientation parities, and both are retained in the conclusion.
-/

open Set

namespace Puzzling139335.N6.TripleSectors

noncomputable section

def directionZero : Plane := point 1 0
def directionThirty : Plane := point (Real.sqrt 3 / 2) (1 / 2)
def directionSixty : Plane := point (1 / 2) (Real.sqrt 3 / 2)
def directionNinety : Plane := point 0 1

theorem ray_zero_eq_direction : ThreeCorners.ray 0 = directionZero := by
  apply point_ext <;> simp [directionZero, point]

theorem ray_pi_six_eq_direction : ThreeCorners.ray (Real.pi / 6) = directionThirty := by
  apply point_ext <;> simp [directionThirty, point, Real.cos_pi_div_six, Real.sin_pi_div_six]

theorem ray_pi_three_eq_direction : ThreeCorners.ray (Real.pi / 3) = directionSixty := by
  apply point_ext <;> simp [directionSixty, point, Real.cos_pi_div_three, Real.sin_pi_div_three]

theorem ray_pi_two_eq_direction : ThreeCorners.ray (Real.pi / 2) = directionNinety := by
  apply point_ext <;> simp [directionNinety, point]

theorem point_eq_boundary_combination (p : Plane) :
    p = (p 0 - Real.sqrt 3 * p 1) • directionZero + (2 * p 1) • directionThirty := by
  apply point_ext
  · change p 0 = (p 0 - Real.sqrt 3 * p 1) * 1 + (2 * p 1) * (Real.sqrt 3 / 2)
    ring
  · change p 1 = (p 0 - Real.sqrt 3 * p 1) * 0 + (2 * p 1) * (1 / 2)
    ring

/-- The origin and two independent thirty-degree boundary directions
determine the entire affine isometry. -/
theorem affine_eq_of_boundary_directions
    (e f : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0) (hf0 : f 0 = 0)
    (ha : e directionZero = f directionZero)
    (hb : e directionThirty = f directionThirty) : e = f := by
  have he (p : Plane) : e p = e.linearIsometryEquiv p := by
    rw [PlaneIsometries.affine_apply_eq_linear_add, he0, add_zero]
  have hf (p : Plane) : f p = f.linearIsometryEquiv p := by
    rw [PlaneIsometries.affine_apply_eq_linear_add, hf0, add_zero]
  have hla : e.linearIsometryEquiv directionZero = f.linearIsometryEquiv directionZero := by
    simpa only [he, hf] using ha
  have hlb : e.linearIsometryEquiv directionThirty = f.linearIsometryEquiv directionThirty := by
    simpa only [he, hf] using hb
  apply AffineIsometryEquiv.ext
  intro p
  rw [he, hf, point_eq_boundary_combination p]
  simp only [map_add, map_smul, hla, hlb]

theorem rotateThirty_origin : rotateThirty (0 : Plane) = 0 := by
  apply point_ext <;> simp

theorem rotateSixty_origin : rotateSixty (0 : Plane) = 0 := by
  apply point_ext <;> simp

theorem reflectThirty_origin : reflectThirty (0 : Plane) = 0 := by
  apply point_ext <;> simp

theorem diagonal_origin : ReflectionSeparation.diagonal (0 : Plane) = 0 := by
  apply point_ext <;> simp

theorem rotateThirty_directionZero : rotateThirty directionZero = directionThirty := by
  apply point_ext <;> simp [directionZero, directionThirty]

theorem rotateThirty_directionThirty : rotateThirty directionThirty = directionSixty := by
  apply point_ext
  · simp only [rotateThirty_zero, directionThirty, directionSixty, point_zero, point_one]
    nlinarith only [sqrt_three_sq]
  · simp only [rotateThirty_one, directionThirty, directionSixty, point_zero, point_one]
    ring

theorem reflectThirty_directionZero : reflectThirty directionZero = directionSixty := by
  apply point_ext <;> simp [directionZero, directionSixty]

theorem reflectThirty_directionThirty : reflectThirty directionThirty = directionThirty := by
  apply reflectThirty_fixed
  change Real.sqrt 3 * (1 / 2) = Real.sqrt 3 / 2
  ring

theorem rotateSixty_directionZero : rotateSixty directionZero = directionSixty := by
  apply point_ext <;> simp [directionZero, directionSixty]

theorem rotateSixty_directionThirty : rotateSixty directionThirty = directionNinety := by
  apply point_ext
  · simp only [rotateSixty_zero, directionThirty, directionNinety, point_zero, point_one]
    ring
  · simp only [rotateSixty_one, directionThirty, directionNinety, point_zero, point_one]
    nlinarith only [sqrt_three_sq]

theorem diagonal_directionZero :
    ReflectionSeparation.diagonal directionZero = directionNinety := by
  apply point_ext <;> simp [directionZero, directionNinety]

theorem diagonal_directionThirty :
    ReflectionSeparation.diagonal directionThirty = directionSixty := by
  apply point_ext <;> simp [directionThirty, directionSixty]

/-- Both possible actual middle placements, from the unordered boundary
direction pair and the fixed vertex. -/
theorem middle_placement_of_boundary_pair
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (hpair : e '' ({directionZero, directionThirty} : Set Plane) =
      {directionThirty, directionSixty}) :
    e = rotateThirty ∨ e = reflectThirty := by
  rw [image_pair, pair_eq_pair_iff] at hpair
  rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    apply affine_eq_of_boundary_directions e rotateThirty he0 rotateThirty_origin
    · exact ha.trans rotateThirty_directionZero.symm
    · exact hb.trans rotateThirty_directionThirty.symm
  · right
    apply affine_eq_of_boundary_directions e reflectThirty he0 reflectThirty_origin
    · exact ha.trans reflectThirty_directionZero.symm
    · exact hb.trans reflectThirty_directionThirty.symm

/-- Both possible actual last placements, again retaining both parities. -/
theorem last_placement_of_boundary_pair
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (hpair : e '' ({directionZero, directionThirty} : Set Plane) =
      {directionSixty, directionNinety}) :
    e = rotateSixty ∨ e = ReflectionSeparation.diagonal := by
  rw [image_pair, pair_eq_pair_iff] at hpair
  rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    apply affine_eq_of_boundary_directions e rotateSixty he0 rotateSixty_origin
    · exact ha.trans rotateSixty_directionZero.symm
    · exact hb.trans rotateSixty_directionThirty.symm
  · right
    apply affine_eq_of_boundary_directions e ReflectionSeparation.diagonal he0 diagonal_origin
    · exact ha.trans diagonal_directionZero.symm
    · exact hb.trans diagonal_directionThirty.symm

end

end Puzzling139335.N6.TripleSectors
