import ErdosProblems.Erdos591.LevelCrossing

open Set Ordinal

namespace Erdos591.Negative.Exact

open Levels

theorem continuationBound_eq_theta_pow (r : ℕ) :
    continuationBound r = (ω ^ ω : Ordinal.{0}) ^ r := by
  rw [continuationBound, Ordinal.opow_mul, Ordinal.opow_natCast]

/-- The alternating-pair construction on the literal good-sequence
carrier.  Every full-order-type set contains the required nine segments. -/
theorem exists_interlacing_pair (W : Set G)
    (hW : typeLT W = ω ^ (ω ^ 2)) :
    ∃ x ∈ W, ∃ y ∈ W, Nonempty (InterlacingWitness (sequence x) (sequence y)) := by
  obtain ⟨m, _, hM⟩ := OuterLevels.exists_large_fiber_above W hW 0
  have hMroot : ∀ x ∈ OuterLevels.Fiber W m, x.1.length = m := fun _ hx ↦ hx.2
  have hMlarge : continuationBound (2 + 2) ≤ typeLT (OuterLevels.Fiber W m) := by
    simpa only [continuationBound_eq_theta_pow] using hM
  obtain ⟨U, hUM, ⟨sx0⟩⟩ :=
    exists_state_from_large_set (OuterLevels.Fiber W m) hMroot 2 4 hMlarge
  obtain ⟨n, hn, hN⟩ :=
    OuterLevels.exists_large_fiber_above W hW (coordinateBound sx0.fragment)
  have hNroot : ∀ x ∈ OuterLevels.Fiber W n, x.1.length = n := fun _ hx ↦ hx.2
  have hNlarge : continuationBound (2 + 2) ≤ typeLT (OuterLevels.Fiber W n) := by
    simpa only [continuationBound_eq_theta_pow] using hN
  obtain ⟨V, hVN, ⟨sy0⟩⟩ :=
    exists_state_from_large_set (OuterLevels.Fiber W n) hNroot 2 6 hNlarge
  have hX0Y0 : AllLT sx0.fragment sy0.fragment := by
    intro a ha b hb
    exact (value_le_coordinateBound ha).trans_lt
      (hn.trans_le (sy0.root_le_value (by decide) b hb))
  obtain ⟨sx1, X1, hX1ne, hX1no, hY0X1, hx1⟩ :=
    sx0.advance (j := 3) (by decide) (coordinateBound sy0.fragment)
  obtain ⟨sy1, Y1, hY1ne, hY1no, hX1Y1, hy1⟩ :=
    sy0.advance (j := 5) (by decide) (coordinateBound X1)
  obtain ⟨U2, hU2U, sx2, X2, hX2ne, hX2box, hY1X2, hx2⟩ :=
    sx1.cross_level (r := 0) (j := 4) (by decide) (by decide) (coordinateBound Y1)
  obtain ⟨sy2, Y2, hY2ne, hY2no, hX2Y2, hy2⟩ :=
    sy1.advance (j := 4) (by decide) (coordinateBound X2)
  obtain ⟨sx3, X3, hX3ne, hX3no, hY2X3, hx3⟩ :=
    sx2.advance (j := 3) (by decide) (coordinateBound Y2)
  obtain ⟨y, hyV, Y3, hY3ne, hY3box, hX3Y3, hyEnd⟩ :=
    sy2.finish (by decide) (coordinateBound X3)
  obtain ⟨x, hxU2, X4, hX4ne, hX4box, hY3X4, hxEnd⟩ :=
    sx3.finish (by decide) (coordinateBound Y3)
  have hxW : x ∈ W := (hUM (hU2U hxU2)).1
  have hyW : y ∈ W := (hVN hyV).1
  have hxseq : sequence x = sx0.fragment ++ X1 ++ X2 ++ X3 ++ X4 := by
    simpa only [hx3, hx2, hx1, List.append_assoc] using hxEnd
  have hyseq : sequence y = sy0.fragment ++ Y1 ++ Y2 ++ Y3 := by
    simpa only [hy2, hy1, List.append_assoc] using hyEnd
  let splitX : Split5 (sequence x) :=
      { p0 := sx0.fragment
        p1 := X1
        p2 := X2
        p3 := X3
        p4 := X4
        eq_append := hxseq
        ne0 := sx0.fragment_ne_nil
        ne1 := hX1ne
        ne2 := hX2ne
        ne3 := hX3ne
        ne4 := hX4ne }
  let splitY : Split4 (sequence y) :=
      { p0 := sy0.fragment
        p1 := Y1
        p2 := Y2
        p3 := Y3
        eq_append := hyseq
        ne0 := sy0.fragment_ne_nil
        ne1 := hY1ne
        ne2 := hY2ne
        ne3 := hY3ne }
  exact ⟨x, hxW, y, hyW, ⟨
    { X := splitX
      Y := splitY
      x0_y0 := hX0Y0
      y0_x1 := allLT_of_above_bound _ _ hY0X1
      x1_y1 := allLT_of_above_bound _ _ hX1Y1
      y1_x2 := allLT_of_above_bound _ _ hY1X2
      x2_y2 := allLT_of_above_bound _ _ hX2Y2
      y2_x3 := allLT_of_above_bound _ _ hY2X3
      x3_y3 := allLT_of_above_bound _ _ hX3Y3
      y3_x4 := allLT_of_above_bound _ _ hY3X4
      box_x0 := sx0.fragment_hasBox
      box_x2 := hX2box
      box_x4 := hX4box
      box_y0 := sy0.fragment_hasBox
      box_y3 := hY3box
      noBox_x1 := hX1no
      noBox_x3 := hX3no
      noBox_y1 := hY1no
      noBox_y2 := hY2no }⟩⟩

/-- Every full-order-type subset of the exact carrier contains an edge. -/
theorem exists_edge_of_full_type (W : Set G)
    (hW : typeLT W = ω ^ (ω ^ 2)) :
    ∃ x ∈ W, ∃ y ∈ W, graph.Adj x y := by
  obtain ⟨x, hx, y, hy, ⟨w⟩⟩ := exists_interlacing_pair W hW
  have hxy : x ≠ y := by
    intro heq
    have hfirst := w.firstValue_lt
    rw [heq] at hfirst
    exact (lt_irrefl _ hfirst)
  exact ⟨x, hx, y, hy, (interlacingGraph_adj sequence x y).mpr
    ⟨hxy, Or.inl ⟨w⟩⟩⟩

theorem graph_meets_every_full_set :
    MeetsEveryFullSet ((· < ·) : G → G → Prop) (ω ^ (ω ^ 2)) graph := by
  intro f
  let e : (ω ^ (ω ^ 2)).ToType ↪o G :=
    OrderEmbedding.ofStrictMono f (fun _ _ hxy ↦ f.map_rel_iff.mpr hxy)
  have htype : typeLT (Set.range e) = ω ^ (ω ^ 2) := by
    have h := OrderIso.ordinalType_congr e.orderIso
    simpa only [Ordinal.type_toType] using h.symm
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_edge_of_full_type (Set.range e) htype
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a, b, ?_, hxy⟩
  intro hab
  exact hxy.ne (congrArg e hab)

/-- The explicit Hajnal--Larson counter-relation at `omega^(omega^2)`. -/
theorem handbook_negative_six :
    ¬ OrdinalCardinalRamsey (ω ^ (ω ^ 2) : Ordinal.{0})
      (ω ^ (ω ^ 2) : Ordinal.{0}) (6 : Cardinal.{0}) :=
  negative_six_of_density graph_meets_every_full_set

end Erdos591.Negative.Exact

#print axioms Erdos591.Negative.Exact.handbook_negative_six
