import StackExchange.Puzzling139335.PackingMass.Jordan
import StackExchange.Puzzling139335.BandMass.Geometry

/-!
# Horizontal cuts occur at integer quarter heights

The selected pieces and their complement are packed into the two bands on
opposite sides of a horizontal cut.  The two weighted-mass bounds force the
height of the cut to equal the selected number of pieces divided by four.
No covering hypothesis is imposed on either selected subfamily.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Puzzling139335

/-- A container holding selected dissection pieces must have volume at least
one quarter of the number of selected pieces. -/
theorem SquareDissection.card_quarter_le_volume_of_piece_subsets
    (d : SquareDissection) (s : Finset (Fin 4)) {S : Set Plane}
    (hsub : ∀ i ∈ s, d.piece i ⊆ S) (hS : MeasurableSet S) :
    (s.card : ℝ≥0∞) / 4 ≤ volume S := by
  let Q : s → Set Plane := fun i => d.piece i.val
  have hdis : Pairwise fun i j : s =>
      Disjoint (interior (Q i)) (interior (Q j)) := by
    intro i j hij
    exact d.disjoint_interiors (fun heq => hij (Subtype.ext heq))
  have hmass := jordan_regions_sum_weightedMass_le_volume Q
    (fun i => d.jordan i.val) hdis (fun i => hsub i.val i.property) hS
  simpa [Q, d.piece_weightedMass_eq_quarter, nsmul_eq_mul, div_eq_mul_inv] using hmass

/-- A horizontal band containing selected pieces has height at least one
quarter of their number. -/
theorem SquareDissection.card_div_four_le_horizontalBand_height
    (d : SquareDissection) (s : Finset (Fin 4)) {a b : ℝ} (hab : a ≤ b)
    (hsub : ∀ i ∈ s, d.piece i ⊆ horizontalBand a b) :
    (s.card : ℝ) / 4 ≤ b - a := by
  have hmass := d.card_quarter_le_volume_of_piece_subsets s hsub
    (measurableSet_horizontalBand a b)
  rw [volume_horizontalBand] at hmass
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using hreal

/-- A horizontal cut separating whole pieces lies at a quarter height
determined by the number of pieces below it.  Neither side is assumed to
be covered by its selected subfamily. -/
theorem SquareDissection.horizontal_cut_height_eq_card_div_four
    (d : SquareDissection) (s : Finset (Fin 4)) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (hbelow : ∀ i ∈ s, d.piece i ⊆ horizontalBand 0 y)
    (habove : ∀ i ∉ s, d.piece i ⊆ horizontalBand y 1) :
    y = (s.card : ℝ) / 4 := by
  have hlo : (s.card : ℝ) / 4 ≤ y := by
    simpa only [sub_zero] using
      d.card_div_four_le_horizontalBand_height s hy.1 hbelow
  have hhi : ((sᶜ).card : ℝ) / 4 ≤ 1 - y :=
    d.card_div_four_le_horizontalBand_height sᶜ hy.2
      (fun i hi => habove i (Finset.mem_compl.mp hi))
  have hcardNat : s.card + (sᶜ).card = 4 := by
    simpa only [Fintype.card_fin] using Finset.card_add_card_compl s
  have hcard : (s.card : ℝ) + ((sᶜ).card : ℝ) = 4 := by
    exact_mod_cast hcardNat
  linarith

end Puzzling139335
