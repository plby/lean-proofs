import StackExchange.Puzzling139335.DoubleCorner.MixedCorner.AxisContact
import StackExchange.Puzzling139335.DoubleCorner.LocalCover
import StackExchange.Puzzling139335.Transform

/-!
# Actual side samples at a two-owner corner

The Jordan axis-contact theorem gives a noncorner point of one incident
side. If the piece avoids the other side away from the corner, this point
lies on the required right side. No straightness or tangent is assumed.
-/

open Set Metric

namespace Puzzling139335.N6.TwoDouble.MixedCornerGeometry

noncomputable section

open SquareSymmetry

theorem exists_normalized_axis_contact (d : SquareDissection)
    {i k j : Fin 4} (hik : i ≠ k) (hi : corner j ∈ d.piece i)
    (hother : ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l) :
    ∃ p ∈ d.piece i, p ≠ corner j ∧
      (cornerFlip j p 0 = 0 ∨ cornerFlip j p 1 = 0) := by
  let f := cornerFlip j
  let d' := d.map f (cornerFlip_image_unitSquare j)
  have hi0 : (0 : Plane) ∈ d'.piece i := ⟨corner j, hi, cornerFlip_corner j⟩
  have hother' : ∀ l, l ≠ i → l ≠ k → (0 : Plane) ∉ d'.piece l := by
    intro l hli hlk hl
    obtain ⟨p, hp, hfp⟩ := hl
    have hpj : p = corner j := f.injective (hfp.trans (cornerFlip_corner j).symm)
    exact hother l hli hlk (hpj ▸ hp)
  obtain ⟨ε, hε, hcover⟩ := d'.two_piece_relative_neighborhood hother'
  obtain ⟨x, hx, hxne, haxis⟩ := DoubleCorner.MixedCorner.exists_axis_contact_of_mem_zero
    (d'.jordan i) (d'.jordan k) (d'.piece_subset i) (d'.piece_subset k)
    (d'.disjoint_interiors hik) hi0 hε hcover
  obtain ⟨p, hp, rfl⟩ := hx
  refine ⟨p, hp, ?_, haxis⟩
  intro hpj
  exact hxne (hpj ▸ cornerFlip_corner j)

theorem right_sample_at_bottom_of_avoidance (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k) (hi : corner 1 ∈ d.piece i)
    (hother : ∀ l, l ≠ i → l ≠ k → corner 1 ∉ d.piece l)
    (hbottom : ∀ p ∈ d.piece i, p 1 = 0 → p = corner 1) :
    ∃ t : ℝ, 0 < t ∧ (!₂[(1 : ℝ), t] : Plane) ∈ d.piece i := by
  obtain ⟨p, hp, hpne, haxis⟩ := exists_normalized_axis_contact d hik hi hother
  have hx : p 0 = 1 := by
    rcases haxis with hx | hy
    · have hx' : 1 - p 0 = 0 := by
        simpa [cornerFlipPoint, corner, Fin.ext_iff] using hx
      linarith only [hx']
    · have hy' : p 1 = 0 := by
        simpa [cornerFlipPoint, corner, Fin.ext_iff] using hy
      exact (hpne (hbottom p hp hy')).elim
  have hy : 0 < p 1 := by
    have hyne : p 1 ≠ 0 := fun h => hpne (hbottom p hp h)
    exact lt_of_le_of_ne (d.piece_subset i hp).2.1 hyne.symm
  refine ⟨p 1, hy, ?_⟩
  have hpeq : p = (!₂[(1 : ℝ), p 1] : Plane) := by
    ext r
    fin_cases r
    · exact hx
    · rfl
  exact hpeq ▸ hp

theorem right_sample_at_top_of_avoidance (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k) (hi : corner 2 ∈ d.piece i)
    (hother : ∀ l, l ≠ i → l ≠ k → corner 2 ∉ d.piece l)
    (htop : ∀ p ∈ d.piece i, p 1 = 1 → p = corner 2) :
    ∃ t : ℝ, 0 < t ∧ (!₂[(1 : ℝ), 1 - t] : Plane) ∈ d.piece i := by
  obtain ⟨p, hp, hpne, haxis⟩ := exists_normalized_axis_contact d hik hi hother
  have hx : p 0 = 1 := by
    rcases haxis with hx | hy
    · have hx' : 1 - p 0 = 0 := by
        simpa [cornerFlipPoint, corner, Fin.ext_iff] using hx
      linarith only [hx']
    · have hy' : p 1 = 1 := by
        have hy'' : 1 - p 1 = 0 := by
          simpa [cornerFlipPoint, corner, Fin.ext_iff] using hy
        linarith only [hy'']
      exact (hpne (htop p hp hy')).elim
  have hy : 0 < 1 - p 1 := by
    have hyne : p 1 ≠ 1 := fun h => hpne (htop p hp h)
    exact sub_pos.mpr (lt_of_le_of_ne (d.piece_subset i hp).2.2 hyne)
  refine ⟨1 - p 1, hy, ?_⟩
  have hpeq : p = (!₂[(1 : ℝ), 1 - (1 - p 1)] : Plane) := by
    ext r
    fin_cases r
    · exact hx
    · simp
  exact hpeq ▸ hp

end

end Puzzling139335.N6.TwoDouble.MixedCornerGeometry
