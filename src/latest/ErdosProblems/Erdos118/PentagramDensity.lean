import ErdosProblems.Erdos118.PentagramPattern
import ErdosProblems.Erdos118.Imported591.ExactDensity

/-! Every full-order subset contains Larson's eleven-segment pattern.
Two level crossings on the earlier word use the proved extraction slack. -/

namespace Erdos118.Pentagram

open Set Ordinal Negative Negative.Exact Levels

theorem exists_pattern (W : Set G) (hW : typeLT W = ω ^ (ω ^ 2)) :
    ∃ x ∈ W, ∃ y ∈ W, Nonempty (Witness (sequence x) (sequence y)) := by
  obtain ⟨m, _, hM⟩ := OuterLevels.exists_large_fiber_above_pow W hW 0 6
  have hMroot : ∀ x ∈ OuterLevels.Fiber W m, x.1.length = m := fun _ hx ↦ hx.2
  have hMlarge : continuationBound (4 + 2) ≤ typeLT (OuterLevels.Fiber W m) := by
    simpa only [continuationBound_eq_theta_pow] using hM
  obtain ⟨U, hUM, ⟨sx0⟩⟩ :=
    exists_state_from_large_set (OuterLevels.Fiber W m) hMroot 4 2 hMlarge
  obtain ⟨n, hn, hN⟩ :=
    OuterLevels.exists_large_fiber_above_pow W hW (coordinateBound sx0.fragment) 2
  have hNroot : ∀ x ∈ OuterLevels.Fiber W n, x.1.length = n := fun _ hx ↦ hx.2
  have hNlarge : continuationBound (0 + 2) ≤ typeLT (OuterLevels.Fiber W n) := by
    simpa only [continuationBound_eq_theta_pow] using hN
  obtain ⟨V, hVN, ⟨sy0⟩⟩ :=
    exists_state_from_large_set (OuterLevels.Fiber W n) hNroot 0 4 hNlarge
  have hX0Y0 : AllLT sx0.fragment sy0.fragment := by
    intro a ha b hb
    exact (value_le_coordinateBound ha).trans_lt
      (hn.trans_le (sy0.root_le_value (by decide) b hb))
  obtain ⟨sx1, X1, hX1ne, hX1no, hY0X1, hx1⟩ :=
    sx0.advance (j := 1) (by decide) (coordinateBound sy0.fragment)
  obtain ⟨sy1, Y1, hY1ne, hY1no, hX1Y1, hy1⟩ :=
    sy0.advance (j := 3) (by decide) (coordinateBound X1)
  obtain ⟨U2, hU2U, sx2, X2, hX2ne, hX2box, hY1X2, hx2⟩ :=
    sx1.cross_level (r := 2) (j := 1) (by decide) (by decide) (coordinateBound Y1)
  obtain ⟨sy2, Y2, hY2ne, hY2no, hX2Y2, hy2⟩ :=
    sy1.advance (j := 2) (by decide) (coordinateBound X2)
  obtain ⟨U3, hU3U2, sx3, X3, hX3ne, hX3box, hY2X3, hx3⟩ :=
    sx2.cross_level (r := 0) (j := 2) (by decide) (by decide) (coordinateBound Y2)
  obtain ⟨sy3, Y3, hY3ne, hY3no, hX3Y3, hy3⟩ :=
    sy2.advance (j := 1) (by decide) (coordinateBound X3)
  obtain ⟨sx4, X4, hX4ne, hX4no, hY3X4, hx4⟩ :=
    sx3.advance (j := 1) (by decide) (coordinateBound Y3)
  obtain ⟨y, hyV, Y4, hY4ne, hY4box, hX4Y4, hyEnd⟩ :=
    sy3.finish (by decide) (coordinateBound X4)
  obtain ⟨x, hxU3, X5, hX5ne, hX5box, hY4X5, hxEnd⟩ :=
    sx4.finish (by decide) (coordinateBound Y4)
  have hxW : x ∈ W := (hUM (hU2U (hU3U2 hxU3))).1
  have hyW : y ∈ W := (hVN hyV).1
  have hxseq : sequence x = sx0.fragment ++ X1 ++ X2 ++ X3 ++ X4 ++ X5 := by
    simpa only [hx4, hx3, hx2, hx1, List.append_assoc] using hxEnd
  have hyseq : sequence y = sy0.fragment ++ Y1 ++ Y2 ++ Y3 ++ Y4 := by
    simpa only [hy3, hy2, hy1, List.append_assoc] using hyEnd
  let splitX : Split6 (sequence x) := {
    p0 := sx0.fragment, p1 := X1, p2 := X2, p3 := X3, p4 := X4, p5 := X5
    eq_append := hxseq, ne0 := sx0.fragment_ne_nil, ne1 := hX1ne
    ne2 := hX2ne, ne3 := hX3ne, ne4 := hX4ne, ne5 := hX5ne }
  let splitY : Split5 (sequence y) := {
    p0 := sy0.fragment, p1 := Y1, p2 := Y2, p3 := Y3, p4 := Y4
    eq_append := hyseq, ne0 := sy0.fragment_ne_nil, ne1 := hY1ne
    ne2 := hY2ne, ne3 := hY3ne, ne4 := hY4ne }
  exact ⟨x, hxW, y, hyW, ⟨{
    X := splitX, Y := splitY, x0_y0 := hX0Y0
    y0_x1 := allLT_of_above_bound _ _ hY0X1
    x1_y1 := allLT_of_above_bound _ _ hX1Y1
    y1_x2 := allLT_of_above_bound _ _ hY1X2
    x2_y2 := allLT_of_above_bound _ _ hX2Y2
    y2_x3 := allLT_of_above_bound _ _ hY2X3
    x3_y3 := allLT_of_above_bound _ _ hX3Y3
    y3_x4 := allLT_of_above_bound _ _ hY3X4
    x4_y4 := allLT_of_above_bound _ _ hX4Y4
    y4_x5 := allLT_of_above_bound _ _ hY4X5
    box_x0 := sx0.fragment_hasBox, box_x2 := hX2box, box_x3 := hX3box, box_x5 := hX5box
    box_y0 := sy0.fragment_hasBox, box_y4 := hY4box
    noBox_x1 := hX1no, noBox_x4 := hX4no
    noBox_y1 := hY1no, noBox_y2 := hY2no, noBox_y3 := hY3no }⟩⟩

/-- The sharper graph meets every set with the full ordinal order type. -/
theorem exists_edge_of_full_type (W : Set G) (hW : typeLT W = ω ^ (ω ^ 2)) :
    ∃ x ∈ W, ∃ y ∈ W, graph.Adj x y := by
  obtain ⟨x, hx, y, hy, ⟨w⟩⟩ := exists_pattern W hW
  have hxy : x ≠ y := by
    intro he
    have h := w.firstValue_lt
    rw [he] at h
    exact (lt_irrefl _ h)
  exact ⟨x, hx, y, hy, (graphOf_adj sequence x y).mpr ⟨hxy, Or.inl ⟨w⟩⟩⟩

end Erdos118.Pentagram
