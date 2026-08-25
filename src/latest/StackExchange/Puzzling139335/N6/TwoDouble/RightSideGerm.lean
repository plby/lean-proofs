import StackExchange.Puzzling139335.SquareSymmetry.SideRigidity
import StackExchange.Puzzling139335.JordanRegion

/-!
# A matching right-side sample forces a center-fixing congruence

An affine isometry taking the bottom-right corner to the top-right corner
and one positive upward sample to the matching downward sample reverses
the entire right side. When a source with nonempty interior and its image
both fit in the square, the side-rigidity theorem excludes the external
half-turn and forces preservation of the square.

The sample alignment is explicit. No classification of Jordan boundary
germs is assumed in these lemmas.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.RightSideGerm

noncomputable section

/-- The positive vertical unit vector. -/
def up : Plane := !₂[(0 : ℝ), (1 : ℝ)]

private theorem affine_map_add_smul (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (p v : Plane) (t : ℝ) :
    e (p + t • v) = e p + t • e.linearIsometryEquiv v := by
  simpa only [vadd_eq_add, map_smul, add_comm] using e.map_vadd p (t • v)

/-- One nonzero affine sample determines the image of its direction. -/
theorem linear_reverses_of_sample (e : Plane ≃ᵃⁱ[ℝ] Plane)
    {p q v : Plane} (hbase : e p = q) {t : ℝ} (ht : t ≠ 0)
    (hsample : e (p + t • v) = q - t • v) :
    e.linearIsometryEquiv v = -v := by
  have hscaled : t • e.linearIsometryEquiv v = t • (-v) := by
    apply add_left_cancel (a := q)
    simpa only [affine_map_add_smul, hbase, sub_eq_add_neg, smul_neg] using hsample
  exact smul_right_injective _ ht hscaled

/-- The upward unit segment at the bottom-right corner is the right side. -/
theorem bottomRight_add_up : corner 1 + up = corner 2 := by
  ext i
  fin_cases i <;> norm_num [corner, up, Fin.ext_iff]

theorem topRight_sub_up : corner 2 - up = corner 1 := by
  rw [← bottomRight_add_up]
  exact add_sub_cancel_right _ _

/-- Matching one positive right-side sample extends to swapping the full
side endpoints. -/
theorem topRight_image_of_sample (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hbottom : e (corner 1) = corner 2) {t : ℝ} (ht : 0 < t)
    (hsample : e (corner 1 + t • up) = corner 2 - t • up) :
    e (corner 2) = corner 1 := by
  have hlinear := linear_reverses_of_sample e hbottom (ne_of_gt ht) hsample
  calc
    e (corner 2) = e (corner 1 + (1 : ℝ) • up) := by rw [one_smul, bottomRight_add_up]
    _ = e (corner 1) + (1 : ℝ) • e.linearIsometryEquiv up := affine_map_add_smul _ _ _ _
    _ = corner 2 - up := by rw [hbottom, hlinear, one_smul, sub_eq_add_neg]
    _ = corner 1 := topRight_sub_up

/-- The fitting hypothesis chooses the inward isometry, so the whole
square is preserved. The positive sample itself need not be in the source. -/
theorem preserves_square_of_sample (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hbottom : e (corner 1) = corner 2) {t : ℝ} (ht : 0 < t)
    (hsample : e (corner 1 + t • up) = corner 2 - t • up)
    {P : Set Plane} (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hint : (interior P).Nonempty) : e '' unitSquare = unitSquare := by
  apply SquareSymmetry.side_rigidity_either_order e 1 1 ?_ hP heP hint
  right
  constructor
  · simpa using hbottom
  · simpa using topRight_image_of_sample e hbottom ht hsample

/-- An actual fitting congruence with this sample alignment fixes the
center. -/
theorem center_fixed_of_sample (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hbottom : e (corner 1) = corner 2) {t : ℝ} (ht : 0 < t)
    (hsample : e (corner 1 + t • up) = corner 2 - t • up)
    {P : Set Plane} (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hint : (interior P).Nonempty) : e squareCenter = squareCenter :=
  SquareSymmetry.center_fixed_of_preserves_square e
    (preserves_square_of_sample e hbottom ht hsample hP heP hint)

/-- Equivalent coordinate version, convenient for a sampled straight
vertical germ. -/
theorem center_fixed_of_coordinate_sample (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hbottom : e (corner 1) = corner 2) {t : ℝ} (ht : 0 < t)
    (hsample : e (!₂[(1 : ℝ), t]) = !₂[(1 : ℝ), 1 - t])
    {P : Set Plane} (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hint : (interior P).Nonempty) : e squareCenter = squareCenter := by
  apply center_fixed_of_sample e hbottom ht ?_ hP heP hint
  have hsource : corner 1 + t • up = !₂[(1 : ℝ), t] := by
    ext i
    fin_cases i <;> simp [corner, up]
  have htarget : corner 2 - t • up = !₂[(1 : ℝ), 1 - t] := by
    ext i
    fin_cases i <;> simp [corner, up]
  simpa only [hsource, htarget] using hsample

/-- Application to an actual congruence between dissection pieces. -/
theorem dissection_center_fixed_of_sample (d : SquareDissection)
    {i j : Fin 4} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece j)
    (hbottom : e (corner 1) = corner 2) {t : ℝ} (ht : 0 < t)
    (hsample : e (corner 1 + t • up) = corner 2 - t • up) :
    e squareCenter = squareCenter := by
  apply center_fixed_of_sample e hbottom ht hsample (d.piece_subset i) ?_
    (d.jordan i).interior_nonempty
  rw [he]
  exact d.piece_subset j

/-- Distinct pieces related by the matching right-side sample cannot own
the center in their interiors. -/
theorem center_not_mem_pair_of_sample (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece j)
    (hbottom : e (corner 1) = corner 2) {t : ℝ} (ht : 0 < t)
    (hsample : e (corner 1 + t • up) = corner 2 - t • up) :
    squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece j) :=
  d.center_not_mem_fixed_pair hij e he
    (dissection_center_fixed_of_sample d e he hbottom ht hsample)

/-- Coordinate-sample form of the actual two-piece center exclusion. -/
theorem center_not_mem_pair_of_coordinate_sample (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece j)
    (hbottom : e (corner 1) = corner 2) {t : ℝ} (ht : 0 < t)
    (hsample : e (!₂[(1 : ℝ), t]) = !₂[(1 : ℝ), 1 - t]) :
    squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece j) := by
  apply d.center_not_mem_fixed_pair hij e he
  apply center_fixed_of_coordinate_sample e hbottom ht hsample (d.piece_subset i) ?_
    (d.jordan i).interior_nonempty
  rw [he]
  exact d.piece_subset j

end

end Puzzling139335.N6.TwoDouble.RightSideGerm
