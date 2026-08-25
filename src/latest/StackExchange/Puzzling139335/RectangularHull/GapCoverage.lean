import StackExchange.Puzzling139335.RectangularHull.SideContact

/-!
# Covering a side gap forces an aligned middle rectangle

Three distinct points in the open gap between the bottom and top pieces must
belong to the two middle pieces.  If both containing rectangle images were
non-axis-aligned, each would have at most one point on the left square side.
-/

namespace Puzzling139335.RectangularHull

open Set PlaneIsometries

theorem three_points_not_mem_union_of_subsingleton {α : Type*} {S T : Set α}
    (hS : S.Subsingleton) (hT : T.Subsingleton) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ S ∪ T) (hb : b ∈ S ∪ T) (hc : c ∈ S ∪ T) : False := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hab (hS ha hb)
  · rcases hc with hc | hc
    · exact hac (hS ha hc)
    · exact hbc (hT hb hc)
  · rcases hc with hc | hc
    · exact hbc (hS hb hc)
    · exact hac (hT ha hc)
  · exact hab (hT ha hb)

/-- Coverage places every point strictly between the outer two pieces in
one of the middle two pieces.  Only the covering field of the dissection is used. -/
theorem gap_point_mem_middle (d : SquareDissection) {h : ℝ}
    (hbottom : ∀ p ∈ d.piece 0, p 1 ≤ h)
    (htop : ∀ p ∈ d.piece 1, 1 - h ≤ p 1)
    {p : Plane} (hpS : p ∈ unitSquare) (hlow : h < p 1) (hhigh : p 1 < 1 - h) :
    p ∈ d.piece 2 ∨ p ∈ d.piece 3 := by
  obtain ⟨i, hi⟩ := d.exists_piece_mem hpS
  fin_cases i
  · have hb := hbottom p hi
    exfalso
    linarith only [hb, hlow]
  · have ht := htop p hi
    exfalso
    linarith only [ht, hhigh]
  · exact Or.inl hi
  · exact Or.inr hi

/-- The actual dissection coverage forces at least one middle containing
rectangle to have an axis-aligned matrix row. -/
theorem gap_coverage_forces_axis_alignment (d : SquareDissection)
    (e f : Plane ≃ᵃⁱ[ℝ] Plane) {h : ℝ} (hh0 : 0 ≤ h) (hhhalf : h < 1 / 2)
    (hbottom : ∀ p ∈ d.piece 0, p 1 ≤ h)
    (htop : ∀ p ∈ d.piece 1, 1 - h ≤ p 1)
    (h2 : d.piece 2 ⊆ e '' axisBox h) (h3 : d.piece 3 ⊆ f '' axisBox h)
    (hefit : e '' axisBox h ⊆ unitSquare) (hffit : f '' axisBox h ⊆ unitSquare) :
    (linearMatrix e 0 0 = 0 ∨ linearMatrix e 0 1 = 0) ∨
      (linearMatrix f 0 0 = 0 ∨ linearMatrix f 0 1 = 0) := by
  by_contra hn
  have he0 : linearMatrix e 0 0 ≠ 0 := fun hz => hn (Or.inl (Or.inl hz))
  have he1 : linearMatrix e 0 1 ≠ 0 := fun hz => hn (Or.inl (Or.inr hz))
  have hf0 : linearMatrix f 0 0 ≠ 0 := fun hz => hn (Or.inr (Or.inl hz))
  have hf1 : linearMatrix f 0 1 ≠ 0 := fun hz => hn (Or.inr (Or.inr hz))
  let E := e '' axisBox h ∩ {p : Plane | p 0 = 0}
  let F := f '' axisBox h ∩ {p : Plane | p 0 = 0}
  have hE : E.Subsingleton := affine_axisBox_left_contact_subsingleton e hefit he0 he1
  have hF : F.Subsingleton := affine_axisBox_left_contact_subsingleton f hffit hf0 hf1
  have hcovered (y : ℝ) (hylow : h < y) (hyhigh : y < 1 - h) :
      !₂[0, y] ∈ E ∪ F := by
    have hpS : !₂[0, y] ∈ unitSquare := by
      change (0 : ℝ) ∈ Icc (0 : ℝ) 1 ∧ y ∈ Icc (0 : ℝ) 1
      refine ⟨⟨le_rfl, zero_le_one⟩, ⟨hh0.trans hylow.le, ?_⟩⟩
      linarith only [hh0, hyhigh]
    rcases gap_point_mem_middle d hbottom htop hpS hylow hyhigh with hp2 | hp3
    · exact Or.inl ⟨h2 hp2, rfl⟩
    · exact Or.inr ⟨h3 hp3, rfl⟩
  let a : Plane := !₂[0, (1 + 2 * h) / 4]
  let b : Plane := !₂[0, (1 / 2 : ℝ)]
  let c : Plane := !₂[0, (3 - 2 * h) / 4]
  have ha : a ∈ E ∪ F :=
    hcovered ((1 + 2 * h) / 4) (by linarith only [hhhalf]) (by linarith only [hhhalf])
  have hb : b ∈ E ∪ F :=
    hcovered (1 / 2) (by linarith only [hhhalf]) (by linarith only [hhhalf])
  have hc : c ∈ E ∪ F :=
    hcovered ((3 - 2 * h) / 4) (by linarith only [hhhalf]) (by linarith only [hhhalf])
  have hab : a 1 < b 1 := by
    change (1 + 2 * h) / 4 < (1 / 2 : ℝ)
    linarith only [hhhalf]
  have hbc : b 1 < c 1 := by
    change (1 / 2 : ℝ) < (3 - 2 * h) / 4
    linarith only [hhhalf]
  refine three_points_not_mem_union_of_subsingleton hE hF ?_ ?_ ?_ ha hb hc
  · intro heq
    exact (ne_of_lt hab) (congrArg (fun p : Plane => p 1) heq)
  · intro heq
    exact (ne_of_lt (hab.trans hbc)) (congrArg (fun p : Plane => p 1) heq)
  · intro heq
    exact (ne_of_lt hbc) (congrArg (fun p : Plane => p 1) heq)

end Puzzling139335.RectangularHull
