import ErdosProblems.Erdos633.OneTwentyGeometry

/-!
# Congruent refinement of the 120-degree trapezoid template

The three similar pieces are refined to one common tile size. In particular,
integer sides `a,b,c` give `(ab)²(2c²-ab)` congruent tiles in the template
when the common tile has scale `1/(ab)`.
-/

namespace Erdos633

noncomputable def OneTwentyShape.smallTile (S : OneTwentyShape) (ε : ℝ) (hε : 0 < ε) :
    Triangle := S.reference.mapSimilarity 0 (ε : ℂ) (by exact_mod_cast ne_of_gt hε)

theorem OneTwentyShape.templateTiling (S : OneTwentyShape) (ε : ℝ) (hε : 0 < ε)
    (na nb nc : ℕ) (hna : 0 < na) (hnb : 0 < nb) (hnc : 0 < nc)
    (ha : (na : ℝ) * ε = S.a) (hb : (nb : ℝ) * ε = S.b)
    (hc : (nc : ℝ) * ε = S.c) :
    Nonempty (RegionTiling (hexCoordinates '' S.fan.region) (S.smallTile ε hε)
      ((Fin (nb ^ 2) ⊕ Fin (nc ^ 2)) ⊕ Fin (na ^ 2))) := by
  obtain ⟨el, hel⟩ := S.left_congruent
  obtain ⟨ec, hec⟩ := S.center_congruent
  obtain ⟨er, her⟩ := S.right_congruent
  let Tl := ((S.reference.scaleTiling ε S.b hε S.b_pos nb hnb hb).mapIsometry el)
    |>.of_carrier_eq ((Triangle.mapIsometry_carrier _ el).trans hel)
  let Tc := ((S.reference.scaleTiling ε S.c hε S.c_pos nc hnc hc).mapIsometry ec)
    |>.of_carrier_eq ((Triangle.mapIsometry_carrier _ ec).trans hec)
  let Tr := ((S.reference.scaleTiling ε S.a hε S.a_pos na hna ha).mapIsometry er)
    |>.of_carrier_eq ((Triangle.mapIsometry_carrier _ er).trans her)
  exact ⟨S.fan.glueAffineTilings hexCoordinates Tl Tc Tr⟩

def OneTwentyShape.ofIntegers (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) : OneTwentyShape where
  a := a
  b := b
  c := c
  a_pos := by exact_mod_cast ha
  b_pos := by exact_mod_cast hb
  c_pos := by exact_mod_cast hc
  conic := by exact_mod_cast h

theorem oneTwenty_integer_template (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let S := OneTwentyShape.ofIntegers a b c ha hb hc h
    ∃ (ε : ℝ) (hε : 0 < ε), ε = 1 / (a * b : ℕ) ∧
      Nonempty (RegionTiling (hexCoordinates '' S.fan.region) (S.smallTile ε hε)
        ((Fin ((b * (a * b)) ^ 2) ⊕ Fin ((c * (a * b)) ^ 2)) ⊕
          Fin ((a * (a * b)) ^ 2))) := by
  let S := OneTwentyShape.ofIntegers a b c ha hb hc h
  let ε : ℝ := 1 / ((a : ℝ) * b)
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have ha0 := ne_of_gt haR
  have hb0 := ne_of_gt hbR
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, hε, by simp [ε], ?_⟩
  apply S.templateTiling ε hε (a * (a * b)) (b * (a * b)) (c * (a * b))
  · positivity
  · positivity
  · positivity
  all_goals dsimp [S, OneTwentyShape.ofIntegers, ε]
  all_goals push_cast
  all_goals field_simp

theorem oneTwenty_integer_template_card (a b c : ℕ)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Fintype.card ((Fin ((b * (a * b)) ^ 2) ⊕ Fin ((c * (a * b)) ^ 2)) ⊕
      Fin ((a * (a * b)) ^ 2)) = (a * b) ^ 2 * (2 * c ^ 2 - a * b) := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  have hsub : 2 * c ^ 2 - a * b = a ^ 2 + b ^ 2 + c ^ 2 := by omega
  rw [hsub]
  ring

/-- The `3,5,7` tile supplies a certified 18675-tile trapezoid template. -/
theorem oneTwenty_three_five_seven_template :
    let S := OneTwentyShape.ofIntegers 3 5 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    ∃ (ε : ℝ) (hε : 0 < ε), ε = 1 / 15 ∧
      Nonempty (RegionTiling (hexCoordinates '' S.fan.region) (S.smallTile ε hε)
        ((Fin (75 ^ 2) ⊕ Fin (105 ^ 2)) ⊕ Fin (45 ^ 2))) := by
  simpa using oneTwenty_integer_template 3 5 7 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end Erdos633
