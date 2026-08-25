import StackExchange.Puzzling139335.Definitions

/-!
# Rigidity of four pairwise nonacute planar directions

Four planar vectors of squared norm two with pairwise nonpositive inner
products form two perpendicular opposite pairs. This is the equality case
of the four-quadrant bound, proved without angles or a choice of coordinates
adapted to the vectors.
-/

namespace Puzzling139335.CornerSupport

open Schoenflies.Plane (det)

private theorem inner_det_identity (a u v : Plane) :
    inner ℝ a u * inner ℝ a v + det a u * det a v =
      ‖a‖ ^ 2 * inner ℝ u v := by
  simp only [Schoenflies.Plane.inner_eq, det, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_two]
  ring

private theorem zero_of_three_nonpos_products (x y z : ℝ)
    (hxy : x * y ≤ 0) (hxz : x * z ≤ 0) (hyz : y * z ≤ 0) :
    x = 0 ∨ y = 0 ∨ z = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  by_cases hy : y = 0
  · exact Or.inr (Or.inl hy)
  refine Or.inr (Or.inr ?_)
  by_contra hz
  have hxy' : x * y < 0 := lt_of_le_of_ne' hxy (mul_ne_zero hx hy).symm
  have hxz' : x * z < 0 := lt_of_le_of_ne' hxz (mul_ne_zero hx hz).symm
  have hpos : 0 < x ^ 2 * (y * z) := by
    calc
      0 < (x * y) * (x * z) := mul_pos_of_neg_of_neg hxy' hxz'
      _ = x ^ 2 * (y * z) := by ring
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hyz)) hpos

private theorem eq_neg_of_inner_eq_neg_two (u v : Plane)
    (hu : ‖u‖ ^ 2 = (2 : ℝ)) (hv : ‖v‖ ^ 2 = (2 : ℝ))
    (huv : inner ℝ u v = -2) : v = -u := by
  have hsum : ‖u + v‖ ^ 2 = 0 := by
    rw [norm_add_sq_real, hu, hv, huv]
    norm_num
  exact eq_neg_of_add_eq_zero_right (norm_eq_zero.mp (sq_eq_zero_iff.mp hsum))

private theorem eq_neg_of_det_eq_zero (a b : Plane)
    (ha : ‖a‖ ^ 2 = (2 : ℝ)) (hb : ‖b‖ ^ 2 = (2 : ℝ))
    (hab : inner ℝ a b ≤ 0) (hdet : det a b = 0) : b = -a := by
  have hgram := inner_det_identity a b b
  rw [real_inner_self_eq_norm_sq, ha, hb, hdet] at hgram
  have hsq : (inner ℝ a b) ^ 2 = (2 : ℝ) ^ 2 := by nlinarith [hgram]
  have hinner : inner ℝ a b = -2 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · linarith
    · exact h
  exact eq_neg_of_inner_eq_neg_two a b ha hb hinner

private theorem eq_neg_of_perpendicular (a c d : Plane)
    (ha : ‖a‖ ^ 2 = (2 : ℝ)) (hc : ‖c‖ ^ 2 = (2 : ℝ))
    (hd : ‖d‖ ^ 2 = (2 : ℝ))
    (hac : inner ℝ a c = 0) (had : inner ℝ a d = 0)
    (hcd : inner ℝ c d ≤ 0) : d = -c := by
  have hcc := inner_det_identity a c c
  have hdd := inner_det_identity a d d
  have hpair := inner_det_identity a c d
  rw [hac, real_inner_self_eq_norm_sq, ha, hc] at hcc
  rw [had, real_inner_self_eq_norm_sq, ha, hd] at hdd
  rw [hac, had, ha] at hpair
  have hsq : (det a d) ^ 2 = (det a c) ^ 2 := by nlinarith [hcc, hdd]
  have hinner : inner ℝ c d = -2 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · rw [h] at hpair
      nlinarith [hcc, hpair]
    · rw [h] at hpair
      nlinarith [hcc, hpair]
  exact eq_neg_of_inner_eq_neg_two c d hc hd hinner

private theorem other_pair_of_opposite (a b c d : Plane)
    (ha : ‖a‖ ^ 2 = (2 : ℝ)) (hc : ‖c‖ ^ 2 = (2 : ℝ))
    (hd : ‖d‖ ^ 2 = (2 : ℝ)) (hb : b = -a)
    (hac : inner ℝ a c ≤ 0) (had : inner ℝ a d ≤ 0)
    (hbc : inner ℝ b c ≤ 0) (hbd : inner ℝ b d ≤ 0)
    (hcd : inner ℝ c d ≤ 0) : d = -c ∧ inner ℝ a c = 0 := by
  rw [hb, inner_neg_left] at hbc hbd
  have hac' : inner ℝ a c = 0 := le_antisymm hac (neg_nonpos.mp hbc)
  have had' : inner ℝ a d = 0 := le_antisymm had (neg_nonpos.mp hbd)
  exact ⟨eq_neg_of_perpendicular a c d ha hc hd hac' had' hcd, hac'⟩

/-- Four vectors of squared norm two with pairwise nonpositive inner
products form an orthogonal cross. The three alternatives record all
possible ways to pair the four named vectors with their negatives. -/
theorem four_directions_form_orthogonal_cross (a b c d : Plane)
    (ha : ‖a‖ ^ 2 = (2 : ℝ)) (hb : ‖b‖ ^ 2 = (2 : ℝ))
    (hc : ‖c‖ ^ 2 = (2 : ℝ)) (hd : ‖d‖ ^ 2 = (2 : ℝ))
    (hab : inner ℝ a b ≤ 0) (hac : inner ℝ a c ≤ 0)
    (had : inner ℝ a d ≤ 0) (hbc : inner ℝ b c ≤ 0)
    (hbd : inner ℝ b d ≤ 0) (hcd : inner ℝ c d ≤ 0) :
    (b = -a ∧ d = -c ∧ inner ℝ a c = 0) ∨
      (c = -a ∧ d = -b ∧ inner ℝ a b = 0) ∨
      (d = -a ∧ c = -b ∧ inner ℝ a b = 0) := by
  have det_product_nonpos (u v : Plane)
      (hau : inner ℝ a u ≤ 0) (hav : inner ℝ a v ≤ 0)
      (huv : inner ℝ u v ≤ 0) : det a u * det a v ≤ 0 := by
    have hgram := inner_det_identity a u v
    rw [ha] at hgram
    nlinarith [hgram, mul_nonneg_of_nonpos_of_nonpos hau hav]
  have hdetbc := det_product_nonpos b c hab hac hbc
  have hdetbd := det_product_nonpos b d hab had hbd
  have hdetcd := det_product_nonpos c d hac had hcd
  rcases zero_of_three_nonpos_products (det a b) (det a c) (det a d)
      hdetbc hdetbd hdetcd with h | h | h
  · have hba := eq_neg_of_det_eq_zero a b ha hb hab h
    exact Or.inl ⟨hba, other_pair_of_opposite a b c d ha hc hd hba hac had hbc hbd hcd⟩
  · have hca := eq_neg_of_det_eq_zero a c ha hc hac h
    have hcb : inner ℝ c b ≤ 0 := by simpa only [real_inner_comm c b] using hbc
    exact Or.inr (Or.inl
      ⟨hca, other_pair_of_opposite a c b d ha hb hd hca hab had hcb hcd hbd⟩)
  · have hda := eq_neg_of_det_eq_zero a d ha hd had h
    have hdb : inner ℝ d b ≤ 0 := by simpa only [real_inner_comm d b] using hbd
    have hdc : inner ℝ d c ≤ 0 := by simpa only [real_inner_comm d c] using hcd
    exact Or.inr (Or.inr
      ⟨hda, other_pair_of_opposite a d b c ha hb hc hda hab hac hdb hdc hbc⟩)

end Puzzling139335.CornerSupport
