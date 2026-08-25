import StackExchange.Puzzling139335.BandMass.Geometry
import StackExchange.Puzzling139335.PackingMass

/-!
# Filling a half-square by two quarter-mass pieces

The packing theorem forces exact coverage of a band once the sum of the
piece masses equals its area. Two original pieces confined to one half-square
would therefore contain the square center between them. A distinct piece
cannot then contain the center in its interior.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Puzzling139335

/-- The generic packing saturation theorem specialized to horizontal bands. -/
theorem jordan_packing_covers_horizontalBand_of_mass_eq {ι : Type*} [Fintype ι]
    (P : ι → Set Plane) (hP : ∀ i, IsJordanRegion (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    {a b : ℝ} (hab : a < b) (hsub : ∀ i, P i ⊆ horizontalBand a b)
    (hmass : ∑ i, weightedMass volume (P i) = ENNReal.ofReal (b - a)) :
    (⋃ i, P i) = horizontalBand a b := by
  apply packing_iUnion_eq_of_mass_saturation P (fun i => (hP i).isClosed)
    (fun i => (hP i).closure_interior) hdis hsub volume
    (closure_interior_horizontalBand hab)
  · rw [volume_horizontalBand]
    exact ENNReal.ofReal_ne_top
  · exact (jordan_regions_tripleContactSet_finite P hP hdis).measure_zero volume
  · rw [volume_horizontalBand, hmass]

private theorem two_quarters_eq_half :
    (1 : ℝ≥0∞) / 4 + 1 / 4 = 1 / 2 := by
  apply (ENNReal.eq_div_iff (by norm_num) (by norm_num)).mpr
  calc
    2 * ((1 : ℝ≥0∞) / 4 + 1 / 4) = 4 * (4 : ℝ≥0∞)⁻¹ := by
      simp only [div_eq_mul_inv, one_mul]
      ring
    _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- Two quarter-mass Jordan pieces packed in any band of height one half
fill the band; coverage is a conclusion. -/
theorem jordan_two_piece_packing_covers_half_band
    (P : Fin 2 → Set Plane) (hP : ∀ i, IsJordanRegion (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    {a b : ℝ} (hheight : b - a = 1 / 2)
    (hsub : ∀ i, P i ⊆ horizontalBand a b)
    (hmass : ∀ i, weightedMass volume (P i) = (1 : ℝ≥0∞) / 4) :
    (⋃ i, P i) = horizontalBand a b := by
  apply jordan_packing_covers_horizontalBand_of_mass_eq P hP hdis
    (by linarith : a < b) hsub
  calc
    ∑ i, weightedMass volume (P i) = (1 : ℝ≥0∞) / 4 + 1 / 4 := by
      simp only [Fin.sum_univ_two, hmass]
    _ = 1 / 2 := two_quarters_eq_half
    _ = ENNReal.ofReal (b - a) := by
      rw [hheight, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num

/-- The half-band saturation statement for two new copies of an original
piece. Their new positions need not come from the original dissection. -/
theorem SquareDissection.congruent_pair_packing_covers_half_band
    (d : SquareDissection) (i : Fin 4) (P : Fin 2 → Set Plane)
    (hP : ∀ j, IsJordanRegion (P j))
    (hdis : Pairwise fun j k => Disjoint (interior (P j)) (interior (P k)))
    {a b : ℝ} (hheight : b - a = 1 / 2)
    (hsub : ∀ j, P j ⊆ horizontalBand a b)
    (hcongr : ∀ j, Congruent (P j) (d.piece i)) :
    (⋃ j, P j) = horizontalBand a b :=
  jordan_two_piece_packing_covers_half_band P hP hdis hheight hsub
    (fun j => d.weightedMass_eq_quarter_of_congruent (hcongr j))

/-- Two distinct original pieces confined to a half-height band fill it. -/
theorem SquareDissection.pair_covers_half_band (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) {a b : ℝ} (hheight : b - a = 1 / 2)
    (hi : d.piece i ⊆ horizontalBand a b) (hj : d.piece j ⊆ horizontalBand a b) :
    d.piece i ∪ d.piece j = horizontalBand a b := by
  let q : Fin 2 → Fin 4 := ![i, j]
  have hq : Function.Injective q := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · rfl
    · exact False.elim (hij hkl)
    · exact False.elim (hij hkl.symm)
    · rfl
  have hdis : Pairwise fun k l : Fin 2 =>
      Disjoint (interior (d.piece (q k))) (interior (d.piece (q l))) := by
    intro k l hkl
    exact d.disjoint_interiors (fun h => hkl (hq h))
  have hsub : ∀ k : Fin 2, d.piece (q k) ⊆ horizontalBand a b := by
    intro k
    fin_cases k
    · exact hi
    · exact hj
  have hcover := jordan_two_piece_packing_covers_half_band
    (fun k => d.piece (q k)) (fun k => d.jordan (q k)) hdis hheight hsub
    (fun k => d.piece_weightedMass_eq_quarter (q k))
  apply Subset.antisymm (union_subset hi hj)
  intro x hx
  have hxcover : x ∈ ⋃ k : Fin 2, d.piece (q k) := by rwa [hcover]
  obtain ⟨k, hk⟩ := mem_iUnion.mp hxcover
  fin_cases k
  · exact Or.inl hk
  · exact Or.inr hk

theorem SquareDissection.pair_covers_lower_half (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j)
    (hi : d.piece i ⊆ horizontalBand 0 (1 / 2))
    (hj : d.piece j ⊆ horizontalBand 0 (1 / 2)) :
    d.piece i ∪ d.piece j = horizontalBand 0 (1 / 2) :=
  d.pair_covers_half_band hij (by norm_num) hi hj

theorem SquareDissection.pair_covers_upper_half (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j)
    (hi : d.piece i ⊆ horizontalBand (1 / 2) 1)
    (hj : d.piece j ⊆ horizontalBand (1 / 2) 1) :
    d.piece i ∪ d.piece j = horizontalBand (1 / 2) 1 :=
  d.pair_covers_half_band hij (by norm_num) hi hj

/-- A third center-interior piece rules out two other pieces in the lower half. -/
theorem SquareDissection.false_of_two_pieces_in_lower_half (d : SquareDissection)
    {c i j : Fin 4} (hc : squareCenter ∈ interior (d.piece c))
    (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j)
    (hi : d.piece i ⊆ horizontalBand 0 (1 / 2))
    (hj : d.piece j ⊆ horizontalBand 0 (1 / 2)) : False := by
  have hcenter : squareCenter ∈ d.piece i ∪ d.piece j := by
    rw [d.pair_covers_lower_half hij hi hj]
    norm_num [horizontalBand, squareCenter]
  rcases hcenter with hcenter | hcenter
  · exact d.not_mem_other_piece hci hc hcenter
  · exact d.not_mem_other_piece hcj hc hcenter

/-- The corresponding statement in the upper half. -/
theorem SquareDissection.false_of_two_pieces_in_upper_half (d : SquareDissection)
    {c i j : Fin 4} (hc : squareCenter ∈ interior (d.piece c))
    (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j)
    (hi : d.piece i ⊆ horizontalBand (1 / 2) 1)
    (hj : d.piece j ⊆ horizontalBand (1 / 2) 1) : False := by
  have hcenter : squareCenter ∈ d.piece i ∪ d.piece j := by
    rw [d.pair_covers_upper_half hij hi hj]
    norm_num [horizontalBand, squareCenter]
  rcases hcenter with hcenter | hcenter
  · exact d.not_mem_other_piece hci hc hcenter
  · exact d.not_mem_other_piece hcj hc hcenter

/-- If one other piece is in the lower half, every remaining non-center piece
has an interior point above the midline. Regular closedness upgrades the
containment contradiction to an actual interior point. -/
theorem SquareDissection.exists_interior_above_of_lower_piece (d : SquareDissection)
    {c i j : Fin 4} (hc : squareCenter ∈ interior (d.piece c))
    (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j)
    (hi : d.piece i ⊆ horizontalBand 0 (1 / 2)) :
    ∃ p ∈ interior (d.piece j), (1 / 2 : ℝ) < p 1 := by
  by_contra hnone
  have hjint : interior (d.piece j) ⊆ horizontalBand 0 (1 / 2) := by
    intro p hp
    have hpS := d.piece_subset j (interior_subset hp)
    exact ⟨hpS.1, hpS.2.1, le_of_not_gt (fun hgt => hnone ⟨p, hp, hgt⟩)⟩
  have hj : d.piece j ⊆ horizontalBand 0 (1 / 2) := by
    rw [← (d.jordan j).closure_interior]
    exact closure_minimal hjint (isClosed_horizontalBand 0 (1 / 2))
  exact d.false_of_two_pieces_in_lower_half hc hci hcj hij hi hj

/-- If one other piece is in the upper half, every remaining non-center piece
has an interior point below the midline. -/
theorem SquareDissection.exists_interior_below_of_upper_piece (d : SquareDissection)
    {c i j : Fin 4} (hc : squareCenter ∈ interior (d.piece c))
    (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j)
    (hi : d.piece i ⊆ horizontalBand (1 / 2) 1) :
    ∃ p ∈ interior (d.piece j), p 1 < (1 / 2 : ℝ) := by
  by_contra hnone
  have hjint : interior (d.piece j) ⊆ horizontalBand (1 / 2) 1 := by
    intro p hp
    have hpS := d.piece_subset j (interior_subset hp)
    exact ⟨hpS.1, le_of_not_gt (fun hlt => hnone ⟨p, hp, hlt⟩), hpS.2.2⟩
  have hj : d.piece j ⊆ horizontalBand (1 / 2) 1 := by
    rw [← (d.jordan j).closure_interior]
    exact closure_minimal hjint (isClosed_horizontalBand (1 / 2) 1)
  exact d.false_of_two_pieces_in_upper_half hc hci hcj hij hi hj

/-- The other middle piece crosses the midline in its interior when there
are lower and upper outer pieces and a distinct center-interior piece. -/
theorem SquareDissection.other_middle_piece_crosses_midline (d : SquareDissection)
    {c i j k : Fin 4} (hc : squareCenter ∈ interior (d.piece c))
    (hci : c ≠ i) (hcj : c ≠ j) (hck : c ≠ k) (hij : i ≠ j) (hkj : k ≠ j)
    (hi : d.piece i ⊆ horizontalBand 0 (1 / 2))
    (hk : d.piece k ⊆ horizontalBand (1 / 2) 1) :
    (∃ p ∈ interior (d.piece j), p 1 < (1 / 2 : ℝ)) ∧
      (∃ p ∈ interior (d.piece j), (1 / 2 : ℝ) < p 1) :=
  ⟨d.exists_interior_below_of_upper_piece hc hck hcj hkj hk,
    d.exists_interior_above_of_lower_piece hc hci hcj hij hi⟩

/-- The center-containing piece itself has interior points strictly on both
sides of the horizontal midline. -/
theorem SquareDissection.center_piece_crosses_midline (d : SquareDissection)
    {c : Fin 4} (hc : squareCenter ∈ interior (d.piece c)) :
    (∃ p ∈ interior (d.piece c), p 1 < (1 / 2 : ℝ)) ∧
      (∃ p ∈ interior (d.piece c), (1 / 2 : ℝ) < p 1) := by
  constructor
  · by_contra hnone
    have hint : interior (d.piece c) ⊆ horizontalBand (1 / 2) 1 := by
      intro p hp
      have hpS := d.piece_subset c (interior_subset hp)
      exact ⟨hpS.1, le_of_not_gt (fun hlt => hnone ⟨p, hp, hlt⟩), hpS.2.2⟩
    have hsub : d.piece c ⊆ horizontalBand (1 / 2) 1 := by
      rw [← (d.jordan c).closure_interior]
      exact closure_minimal hint (isClosed_horizontalBand (1 / 2) 1)
    have hcenter := (mem_interior_horizontalBand_iff (1 / 2) 1 squareCenter).mp
      (interior_mono hsub hc)
    norm_num [squareCenter] at hcenter
  · by_contra hnone
    have hint : interior (d.piece c) ⊆ horizontalBand 0 (1 / 2) := by
      intro p hp
      have hpS := d.piece_subset c (interior_subset hp)
      exact ⟨hpS.1, hpS.2.1, le_of_not_gt (fun hgt => hnone ⟨p, hp, hgt⟩)⟩
    have hsub : d.piece c ⊆ horizontalBand 0 (1 / 2) := by
      rw [← (d.jordan c).closure_interior]
      exact closure_minimal hint (isClosed_horizontalBand 0 (1 / 2))
    have hcenter := (mem_interior_horizontalBand_iff 0 (1 / 2) squareCenter).mp
      (interior_mono hsub hc)
    norm_num [squareCenter] at hcenter

end Puzzling139335
