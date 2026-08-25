import StackExchange.Puzzling139335.BandMass

/-!
# A single tile saturates a quarter-height band

A Jordan region contained in a positive-height band fills that band when its
weighted mass equals the band's area.  Applied to one original dissection
piece, this identifies every containing quarter-height band as the piece
itself, including the band boundary.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Puzzling139335

/-- A single Jordan region saturating the weighted-mass bound of a band is
equal to the entire band. -/
theorem IsJordanRegion.eq_horizontalBand_of_mass_eq
    {P : Set Plane} (hP : IsJordanRegion P) {a b : ℝ} (hab : a < b)
    (hsub : P ⊆ horizontalBand a b)
    (hmass : weightedMass volume P = ENNReal.ofReal (b - a)) :
    P = horizontalBand a b := by
  have hdis : Pairwise fun _i _j : Fin 1 => Disjoint (interior P) (interior P) := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))
  have hcover := jordan_packing_covers_horizontalBand_of_mass_eq
    (fun _i : Fin 1 => P) (fun _i => hP) hdis hab (fun _i => hsub)
    (by simpa only [Fin.sum_univ_one] using hmass)
  simpa only [iUnion_const] using hcover

/-- One original tile contained in any band of height one quarter equals
that band.  Band coverage is a conclusion, not a hypothesis. -/
theorem SquareDissection.piece_eq_quarter_band
    (d : SquareDissection) {i : Fin 4} {a b : ℝ} (hheight : b - a = 1 / 4)
    (hsub : d.piece i ⊆ horizontalBand a b) :
    d.piece i = horizontalBand a b := by
  apply (d.jordan i).eq_horizontalBand_of_mass_eq (by linarith : a < b) hsub
  rw [d.piece_weightedMass_eq_quarter, hheight,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  norm_num

/-- The bottom quarter band cannot contain a proper subset that is one of
the four original tiles. -/
theorem SquareDissection.piece_eq_lower_quarter_band
    (d : SquareDissection) {i : Fin 4}
    (hsub : d.piece i ⊆ horizontalBand 0 (1 / 4)) :
    d.piece i = horizontalBand 0 (1 / 4) :=
  d.piece_eq_quarter_band (by norm_num) hsub

/-- The corresponding statement for the top quarter band. -/
theorem SquareDissection.piece_eq_upper_quarter_band
    (d : SquareDissection) {i : Fin 4}
    (hsub : d.piece i ⊆ horizontalBand (3 / 4) 1) :
    d.piece i = horizontalBand (3 / 4) 1 :=
  d.piece_eq_quarter_band (by norm_num) hsub

/-- If a horizontal partition has exactly one selected lower piece, its cut
is at height one quarter and that piece fills the whole lower band. -/
theorem SquareDissection.singleton_lower_partition_eq_band
    (d : SquareDissection) (s : Finset (Fin 4)) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (hcard : s.card = 1)
    (hbelow : ∀ i ∈ s, d.piece i ⊆ horizontalBand 0 y)
    (habove : ∀ i ∉ s, d.piece i ⊆ horizontalBand y 1) :
    y = 1 / 4 ∧ ∃ i ∈ s, d.piece i = horizontalBand 0 y := by
  have hyq : y = 1 / 4 := by
    simpa only [hcard, Nat.cast_one] using
      d.horizontal_cut_height_eq_card_div_four s hy hbelow habove
  obtain ⟨i, hi⟩ : s.Nonempty := Finset.card_pos.mp (by rw [hcard]; norm_num)
  refine ⟨hyq, i, hi, ?_⟩
  exact d.piece_eq_quarter_band (by simpa only [sub_zero] using hyq) (hbelow i hi)

/-- If exactly one piece is above a horizontal partition, the cut is at
height three quarters and that piece fills the whole upper band. -/
theorem SquareDissection.singleton_upper_partition_eq_band
    (d : SquareDissection) (s : Finset (Fin 4)) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (hcard : (sᶜ).card = 1)
    (hbelow : ∀ i ∈ s, d.piece i ⊆ horizontalBand 0 y)
    (habove : ∀ i ∉ s, d.piece i ⊆ horizontalBand y 1) :
    y = 3 / 4 ∧ ∃ i ∉ s, d.piece i = horizontalBand y 1 := by
  have htotal : s.card + (sᶜ).card = 4 := by
    simpa only [Fintype.card_fin] using Finset.card_add_card_compl s
  have hcard' : s.card = 3 := by omega
  have hyq : y = 3 / 4 := by
    simpa only [hcard', Nat.cast_ofNat] using
      d.horizontal_cut_height_eq_card_div_four s hy hbelow habove
  obtain ⟨i, hi⟩ : (sᶜ).Nonempty := Finset.card_pos.mp (by rw [hcard]; norm_num)
  have hinot : i ∉ s := Finset.mem_compl.mp hi
  refine ⟨hyq, i, hinot, ?_⟩
  exact d.piece_eq_quarter_band (by rw [hyq]; norm_num) (habove i hinot)

end Puzzling139335
