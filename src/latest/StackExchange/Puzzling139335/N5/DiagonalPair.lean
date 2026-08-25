import StackExchange.Puzzling139335.ReflectionSeparation
import StackExchange.Puzzling139335.SquareSymmetry.Dissection

/-!
# The normalized diagonal pair in the five-incidence case

An actual congruence carrying the bottom side's ordered endpoints to the
left side's endpoints, with the bottom-left corner fixed, must be the
diagonal reflection.  No angle or polygonality hypothesis is imposed.
-/

open Set

namespace Puzzling139335.N5

open PlaneIsometries ReflectionSeparation

/-- A square symmetry fixing the bottom-left corner and carrying the
bottom-right corner to the top-left corner is the diagonal reflection. -/
theorem eq_diagonal_of_preserves_square (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hSquare : e '' unitSquare = unitSquare)
    (hBL : e (corner 0) = corner 0) (hBR : e (corner 1) = corner 3) :
    e = ReflectionSeparation.diagonal := by
  have hzero : corner 0 = (0 : Plane) := by
    ext k
    fin_cases k <;> norm_num [corner, Fin.ext_iff]
  have he0 : e 0 = 0 := by
    simpa only [hzero] using hBL
  have hcenter := SquareSymmetry.center_fixed_of_preserves_square e hSquare
  obtain ⟨c, s, _, hform | hform⟩ := affine_coordinate_classification e
  · have hc := congrArg (fun p : Plane => p 0) (hform (corner 1))
    have hs := congrArg (fun p : Plane => p 1) (hform (corner 1))
    have hmid := congrArg (fun p : Plane => p 0) (hform squareCenter)
    rw [hBR] at hc hs
    rw [hcenter] at hmid
    norm_num [he0, directCoordinates, corner, Fin.ext_iff] at hc hs
    norm_num [he0, directCoordinates, squareCenter] at hmid
    linarith
  · have hc := congrArg (fun p : Plane => p 0) (hform (corner 1))
    have hs := congrArg (fun p : Plane => p 1) (hform (corner 1))
    rw [hBR] at hc hs
    norm_num [he0, reversingCoordinates, corner, Fin.ext_iff] at hc hs
    apply AffineIsometryEquiv.ext
    intro p
    rw [hform p, he0, ← hc, ← hs]
    ext k
    fin_cases k <;> simp [reversingCoordinates]

/-- The actual dissection hypotheses determine the congruence from its two
specified endpoint images.  Membership or uniqueness of these endpoints
is not needed for the rigidity step. -/
theorem congruence_eq_diagonal (d : SquareDissection) (i j : Fin 4)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece j)
    (hBL : e (corner 0) = corner 0) (hBR : e (corner 1) = corner 3) :
    e = ReflectionSeparation.diagonal := by
  apply eq_diagonal_of_preserves_square e _ hBL hBR
  apply d.side_congruence_preserves_square i j 0 3 e he
  change e '' {corner 0, corner 1} = {corner 3, corner 0}
  rw [Set.image_pair, hBL, hBR, Set.pair_comm]

/-- The bottom-right corner selects the lower diagonal half-plane, and
reflection places the other piece in the upper half-plane. -/
theorem diagonal_pair_halves (d : SquareDissection) {i j : Fin 4}
    (hij : i ≠ j) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece j)
    (hBL : e (corner 0) = corner 0) (hBR : e (corner 1) = corner 3)
    (hcorner : corner 1 ∈ d.piece i) :
    d.piece i ⊆ {p | p 1 ≤ p 0} ∧ d.piece j ⊆ {p | p 0 ≤ p 1} := by
  have he' : ReflectionSeparation.diagonal '' d.piece i = d.piece j := by
    rwa [congruence_eq_diagonal d i j e he hBL hBR] at he
  have hbelow := diagonal_below_of_bottom_right (d.jordan i) he'
    (d.disjoint_interiors hij) hcorner
  refine ⟨hbelow, ?_⟩
  intro q hq
  rw [← he'] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  change ReflectionSeparation.diagonal p 0 ≤ ReflectionSeparation.diagonal p 1
  have hp' : p 1 ≤ p 0 := hbelow hp
  simpa only [diagonal_apply_zero, diagonal_apply_one] using hp'

/-- Neither member of the normalized diagonal pair can contain the square
center in its interior. -/
theorem center_not_mem_diagonal_pair (d : SquareDissection) {i j : Fin 4}
    (hij : i ≠ j) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece j)
    (hBL : e (corner 0) = corner 0) (hBR : e (corner 1) = corner 3) :
    squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece j) := by
  apply d.center_not_mem_fixed_pair hij e he
  rw [congruence_eq_diagonal d i j e he hBL hBR, diagonal_center]

end Puzzling139335.N5
