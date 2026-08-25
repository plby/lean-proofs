import StackExchange.Puzzling139335.Definitions
import StackExchange.Puzzling139335.SquareGeometry.Scalar
import Mathlib.LinearAlgebra.AffineSpace.Midpoint

/-!
# The diameter and center of the unit square

A diameter pair in the square has the square's center as its midpoint.
Consequently every congruence taking a piece containing such a pair into
the square fixes the center. This prevents such a piece in a dissection
whose center belongs to one piece's interior.
-/

open Set

namespace Puzzling139335

theorem plane_dist_sq (p q : Plane) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem dist_sq_le_two {p q : Plane} (hp : p ∈ unitSquare) (hq : q ∈ unitSquare) :
    dist p q ^ 2 ≤ 2 := by
  rw [plane_dist_sq]
  have h₀ := sub_sq_le_one_of_mem_Icc hp.1 hq.1
  have h₁ := sub_sq_le_one_of_mem_Icc hp.2 hq.2
  linarith

theorem coord_sub_sq_eq_one_of_dist_sq_eq_two {p q : Plane}
    (hp : p ∈ unitSquare) (hq : q ∈ unitSquare) (h : dist p q ^ 2 = 2) :
    (p 0 - q 0) ^ 2 = 1 ∧ (p 1 - q 1) ^ 2 = 1 := by
  rw [plane_dist_sq] at h
  have h₀ := sub_sq_le_one_of_mem_Icc hp.1 hq.1
  have h₁ := sub_sq_le_one_of_mem_Icc hp.2 hq.2
  constructor <;> linarith

theorem midpoint_eq_squareCenter_of_dist_sq_eq_two {p q : Plane}
    (hp : p ∈ unitSquare) (hq : q ∈ unitSquare) (h : dist p q ^ 2 = 2) :
    midpoint ℝ p q = squareCenter := by
  obtain ⟨h₀, h₁⟩ := coord_sub_sq_eq_one_of_dist_sq_eq_two hp hq h
  have hs₀ := add_eq_one_of_mem_Icc_of_sub_sq_eq_one hp.1 hq.1 h₀
  have hs₁ := add_eq_one_of_mem_Icc_of_sub_sq_eq_one hp.2 hq.2 h₁
  rw [midpoint_eq_smul_add]
  ext i
  fin_cases i
  · change (⅟ (2 : ℝ)) * (p 0 + q 0) = (1 / 2 : ℝ)
    rw [hs₀]
    norm_num
  · change (⅟ (2 : ℝ)) * (p 1 + q 1) = (1 / 2 : ℝ)
    rw [hs₁]
    norm_num

theorem corner_opposite_dist_sq (i : Fin 4) :
    dist (corner i) (corner (i + 2)) ^ 2 = 2 := by
  fin_cases i <;> norm_num [plane_dist_sq, corner, Fin.ext_iff, Fin.val_add]

theorem midpoint_opposite_corners (i : Fin 4) :
    midpoint ℝ (corner i) (corner (i + 2)) = squareCenter :=
  midpoint_eq_squareCenter_of_dist_sq_eq_two (corner_mem_unitSquare i)
    (corner_mem_unitSquare (i + 2)) (corner_opposite_dist_sq i)

theorem affineIsometry_map_squareCenter_of_diameter_pair
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {p q : Plane}
    (hp : p ∈ unitSquare) (hq : q ∈ unitSquare)
    (hep : e p ∈ unitSquare) (heq : e q ∈ unitSquare)
    (h : dist p q ^ 2 = 2) : e squareCenter = squareCenter := by
  have he : dist (e p) (e q) ^ 2 = 2 := by
    rw [e.isometry.dist_eq]
    exact h
  calc
    e squareCenter = e (midpoint ℝ p q) :=
      congrArg e (midpoint_eq_squareCenter_of_dist_sq_eq_two hp hq h).symm
    _ = midpoint ℝ (e p) (e q) := e.toAffineEquiv.map_midpoint p q
    _ = squareCenter := midpoint_eq_squareCenter_of_dist_sq_eq_two hep heq he

/-- A piece in a protected-center dissection cannot contain a diameter pair. -/
theorem SquareDissection.no_diameter_pair (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i : Fin 4) {p q : Plane}
    (hp : p ∈ d.piece i) (hq : q ∈ d.piece i) : dist p q ^ 2 ≠ 2 := by
  intro hd
  obtain ⟨k, hk⟩ := hc
  obtain ⟨e, he⟩ := d.congruent i k
  have hpk : e p ∈ d.piece k := he ▸ mem_image_of_mem e hp
  have hqk : e q ∈ d.piece k := he ▸ mem_image_of_mem e hq
  have hdk : dist (e p) (e q) ^ 2 = 2 := by
    rw [e.isometry.dist_eq]
    exact hd
  have hall (j : Fin 4) : squareCenter ∈ interior (d.piece j) := by
    obtain ⟨f, hf⟩ := d.congruent k j
    have hpj : f (e p) ∈ d.piece j := hf ▸ mem_image_of_mem f hpk
    have hqj : f (e q) ∈ d.piece j := hf ▸ mem_image_of_mem f hqk
    have hfix : f squareCenter = squareCenter :=
      affineIsometry_map_squareCenter_of_diameter_pair f
        (d.piece_subset k hpk) (d.piece_subset k hqk)
        (d.piece_subset j hpj) (d.piece_subset j hqj) hdk
    have himg : f '' interior (d.piece k) = interior (f '' d.piece k) :=
      f.toHomeomorph.image_interior (d.piece k)
    have hfj : f squareCenter ∈ interior (d.piece j) := by
      rw [← hf, ← himg]
      exact mem_image_of_mem f hk
    rwa [hfix] at hfj
  exact Set.disjoint_left.mp
    (d.disjoint_interiors (by decide : (0 : Fin 4) ≠ 1)) (hall 0) (hall 1)

theorem SquareDissection.dist_sq_lt_two_of_mem (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i : Fin 4) {p q : Plane}
    (hp : p ∈ d.piece i) (hq : q ∈ d.piece i) : dist p q ^ 2 < 2 := by
  have hle := dist_sq_le_two (d.piece_subset i hp) (d.piece_subset i hq)
  have hne := d.no_diameter_pair hc i hp hq
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact (hne heq).elim

/-- No tile contains either diagonal pair of square corners. -/
theorem SquareDissection.no_opposite_corners (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i j : Fin 4) :
    ¬ (corner j ∈ d.piece i ∧ corner (j + 2) ∈ d.piece i) := by
  rintro ⟨hp, hq⟩
  exact d.no_diameter_pair hc i hp hq (corner_opposite_dist_sq j)

theorem SquareDissection.opposite_corner_not_mem (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i j : Fin 4) (hj : corner j ∈ d.piece i) :
    corner (j + 2) ∉ d.piece i := by
  intro h
  exact d.no_opposite_corners hc i j ⟨hj, h⟩

end Puzzling139335
