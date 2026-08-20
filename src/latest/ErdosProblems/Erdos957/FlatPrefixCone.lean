import ErdosProblems.Erdos957.CollisionGlue

/-!
# Flat-prefix cone bounds for Erdős 957

The locality argument only needed the endpoint after four almost-horizontal
hull edges.  Collision analysis also needs the same cone inequality at each
earlier endpoint.  This file derives all four prefix estimates from the
checked polar data of `FlatAlignedFrameData`; it contains no arrival or
capacity hypothesis.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957FlatPrefixCone

open Erdos957GeometryCore

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}

private lemma zeroPolar (p : ℝ × ℝ) :
    Erdos957Locality.IsPolarEdge p p 0 0 := by
  simp [Erdos957Locality.IsPolarEdge]

private theorem polar_prefix_flat_cone
    (p : ℕ → ℝ × ℝ) (r θ : Fin 4 → ℝ)
    (hp0 : p 0 = (0, 0))
    (he : ∀ k : Fin 4,
      Erdos957Locality.IsPolarEdge (p k.1) (p (k.1 + 1)) (r k) (θ k))
    (hr : ∀ k : Fin 4, 0 ≤ r k)
    (ha : ∀ k : Fin 4, |θ k| ≤ Real.pi / 45)
    (k : Fin 4) : -(p (k.1 + 1)).2 ≤ (p (k.1 + 1)).1 / 10 := by
  fin_cases k
  · apply Erdos957Locality.four_polar_edges_flat_cone
      (p₀ := p 0) (p₁ := p 1) (p₂ := p 1) (p₃ := p 1) (p₄ := p 1)
      (r₀ := r 0) (r₁ := 0) (r₂ := 0) (r₃ := 0)
      (θ₀ := θ 0) (θ₁ := 0) (θ₂ := 0) (θ₃ := 0)
    · exact hp0
    · exact he 0
    · exact zeroPolar _
    · exact zeroPolar _
    · exact zeroPolar _
    · exact hr 0
    · norm_num
    · norm_num
    · norm_num
    · exact ha 0
    · norm_num; positivity
    · norm_num; positivity
    · norm_num; positivity
  · apply Erdos957Locality.four_polar_edges_flat_cone
      (p₀ := p 0) (p₁ := p 1) (p₂ := p 2) (p₃ := p 2) (p₄ := p 2)
      (r₀ := r 0) (r₁ := r 1) (r₂ := 0) (r₃ := 0)
      (θ₀ := θ 0) (θ₁ := θ 1) (θ₂ := 0) (θ₃ := 0)
    · exact hp0
    · exact he 0
    · exact he 1
    · exact zeroPolar _
    · exact zeroPolar _
    · exact hr 0
    · exact hr 1
    · norm_num
    · norm_num
    · exact ha 0
    · exact ha 1
    · norm_num; positivity
    · norm_num; positivity
  · apply Erdos957Locality.four_polar_edges_flat_cone
      (p₀ := p 0) (p₁ := p 1) (p₂ := p 2) (p₃ := p 3) (p₄ := p 3)
      (r₀ := r 0) (r₁ := r 1) (r₂ := r 2) (r₃ := 0)
      (θ₀ := θ 0) (θ₁ := θ 1) (θ₂ := θ 2) (θ₃ := 0)
    · exact hp0
    · exact he 0
    · exact he 1
    · exact he 2
    · exact zeroPolar _
    · exact hr 0
    · exact hr 1
    · exact hr 2
    · norm_num
    · exact ha 0
    · exact ha 1
    · exact ha 2
    · norm_num; positivity
  · apply Erdos957Locality.four_polar_edges_flat_cone
      (p₀ := p 0) (p₁ := p 1) (p₂ := p 2) (p₃ := p 3) (p₄ := p 4)
      (r₀ := r 0) (r₁ := r 1) (r₂ := r 2) (r₃ := r 3)
      (θ₀ := θ 0) (θ₁ := θ 1) (θ₂ := θ 2) (θ₃ := θ 3)
    · exact hp0
    · exact he 0
    · exact he 1
    · exact he 2
    · exact he 3
    · exact hr 0
    · exact hr 1
    · exact hr 2
    · exact hr 3
    · exact ha 0
    · exact ha 1
    · exact ha 2
    · exact ha 3

/-- Every nonempty prefix of the first four forward edges lies above
`y = -x/10` in the genuine bisector chart. -/
theorem right_flat_prefix_cone
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H}) (hi : P.IsFlat i)
    (k : Fin 4) :
    -(F.chart.rightOrbitCoord P i (k.1 + 1)).2 ≤
      (F.chart.rightOrbitCoord P i (k.1 + 1)).1 / 10 := by
  obtain ⟨h0, h1, h2, h3⟩ := F.rightFlatAngles i hi
  have ha := Erdos957Locality.four_edge_angles_near_horizontal h0 h1 h2 h3
  apply polar_prefix_flat_cone
      (p := F.chart.rightOrbitCoord P i)
      (r := F.rightRadius i) (θ := F.rightAngle i) (k := k)
  · simp
  · exact F.rightPolar i
  · intro j
    linarith [F.rightRadius_ge_one i j]
  · intro j
    fin_cases j <;> simp_all

/-- Reflected backward prefixes satisfy the identical cone estimate. -/
theorem left_flat_prefix_cone
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H}) (hi : P.IsFlat i)
    (k : Fin 4) :
    -(F.chart.leftOrbitReflectedCoord P i (k.1 + 1)).2 ≤
      (F.chart.leftOrbitReflectedCoord P i (k.1 + 1)).1 / 10 := by
  obtain ⟨h0, h1, h2, h3⟩ := F.leftFlatAngles i hi
  have ha := Erdos957Locality.four_edge_angles_near_horizontal h0 h1 h2 h3
  apply polar_prefix_flat_cone
      (p := F.chart.leftOrbitReflectedCoord P i)
      (r := F.leftRadius i) (θ := F.leftAngle i) (k := k)
  · simp
  · exact F.leftPolar i
  · intro j
    linarith [F.leftRadius_ge_one i j]
  · intro j
    fin_cases j <;> simp_all

/-- Three forward flat hull edges advance by more than `29/10` in the
bisector chart.  This leaves ample margin when rotating to a normalized
incident-edge chart. -/
theorem right_three_steps_exit_twenty_nine_tenths
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H}) (hi : P.IsFlat i) :
    (29 / 10 : ℝ) < (F.chart.rightOrbitCoord P i 3).1 := by
  obtain ⟨h0, h1, h2, h3⟩ := F.rightFlatAngles i hi
  obtain ⟨ha0, ha1, ha2, _ha3⟩ :=
    Erdos957Locality.four_edge_angles_near_horizontal h0 h1 h2 h3
  have hx0 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.rightRadius_ge_one i 0) ha0 (F.rightPolar i 0).1
  have hx1 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.rightRadius_ge_one i 1) ha1 (F.rightPolar i 1).1
  have hx2 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.rightRadius_ge_one i 2) ha2 (F.rightPolar i 2).1
  norm_num at hx0 hx1 hx2
  have hz : (F.chart.rightOrbitCoord P i 0).1 = 0 := by simp
  linarith

/-- Reflected backward version of
`right_three_steps_exit_twenty_nine_tenths`. -/
theorem left_three_steps_exit_twenty_nine_tenths
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H}) (hi : P.IsFlat i) :
    (29 / 10 : ℝ) < (F.chart.leftOrbitReflectedCoord P i 3).1 := by
  obtain ⟨h0, h1, h2, h3⟩ := F.leftFlatAngles i hi
  obtain ⟨ha0, ha1, ha2, _ha3⟩ :=
    Erdos957Locality.four_edge_angles_near_horizontal h0 h1 h2 h3
  have hx0 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.leftRadius_ge_one i 0) ha0 (F.leftPolar i 0).1
  have hx1 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.leftRadius_ge_one i 1) ha1 (F.leftPolar i 1).1
  have hx2 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.leftRadius_ge_one i 2) ha2 (F.leftPolar i 2).1
  norm_num at hx0 hx1 hx2
  have hz : (F.chart.leftOrbitReflectedCoord P i 0).1 = 0 := by simp
  linarith

end Erdos957FlatPrefixCone

#print axioms Erdos957FlatPrefixCone.right_flat_prefix_cone
#print axioms Erdos957FlatPrefixCone.left_flat_prefix_cone
#print axioms Erdos957FlatPrefixCone.right_three_steps_exit_twenty_nine_tenths
#print axioms Erdos957FlatPrefixCone.left_three_steps_exit_twenty_nine_tenths
