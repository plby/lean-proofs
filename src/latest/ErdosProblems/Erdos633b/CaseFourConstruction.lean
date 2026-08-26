import ErdosProblems.Erdos633b.SixtyCorner

/-! The integer geometric construction for case (4); arithmetic nonsquareness is separate. -/

namespace Erdos633b.Sixty

def commonScale (a b : ℕ) : ℕ := 3 * GroupTwoDimensions.scale a b

theorem commonScale_pos (a b : ℕ) : 0 < commonScale a b :=
  mul_pos (by decide) (GroupTwoDimensions.scale_pos a b)

noncomputable def caseFourOuter (d : ℝ) (hd : 0 < d) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) : Triangle :=
  cornerTriangle d hd ((commonScale a b * b : ℕ) * ((a : ℝ) + b))
    ((commonScale a b * b : ℕ) * (a : ℝ))
    (mul_pos (by exact_mod_cast mul_pos (commonScale_pos a b) hb)
      (add_pos (by exact_mod_cast ha) (by exact_mod_cast hb)))
    (mul_pos (by exact_mod_cast mul_pos (commonScale_pos a b) hb) (by exact_mod_cast ha))

noncomputable def case_four_integer_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
      (caseFourOuter d hd a b ha hb).support
      (commonScale a b ^ 2 * b * (a + b)) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  let k := commonScale a b * b
  have hk : 0 < k := mul_pos (commonScale_pos a b) hb
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  let x : ℝ := k * ((a : ℝ) + b)
  let y : ℝ := k * (a : ℝ)
  have hx : 0 < x := mul_pos hkr (add_pos har hbr)
  have hy : 0 < y := mul_pos hkr har
  have hyx : y < x := by dsimp only [x, y]; nlinarith [mul_pos hkr hbr]
  let T := cornerTriangle d hd x y hx hy
  let R := groupTwoReference d hd a b har hbr
  let E := T.edgeFirst (y / x) (div_pos hy hx)
  let S := T.edgeSecond (y / x) ((div_lt_one hx).mpr hyx)
  have first : Patch R E.support (9 * GroupTwoDimensions.scale a b ^ 2 * (a * b)) := by
    apply (group_two_equilateral_patch d hd he a b c ha hb hc hrel).transportSides E
    intro i
    rw [equilateralOuter_side d hd he, corner_equilateral_sides d hd he]
    dsimp only [y, k, commonScale, trapezoidSize]
    push_cast
    ring
  let S' : Triangle := S.reindex (Equiv.swap 0 2)
  have hsides (i : Fin 3) : S'.side i = (k : ℝ) * R.side i := by
    exact corner_remainder_sides d hd he a b c k har hbr hkr (by exact_mod_cast hrel) i
  have second : Patch R S.support (k ^ 2) := by
    have result := quadratic_patch_congruent R S' k hk hsides
    simpa only [S', Triangle.support_reindex] using result
  have result := first.glueTwo second (T.edgeParts_disjoint_interiors (y / x)
    (div_pos hy hx) ((div_lt_one hx).mpr hyx))
  rw [T.edgeParts_cover (y / x) (div_pos hy hx) ((div_lt_one hx).mpr hyx)] at result
  have hcount : 9 * GroupTwoDimensions.scale a b ^ 2 * (a * b) + k ^ 2 =
      commonScale a b ^ 2 * b * (a + b) := by
    dsimp only [k, commonScale]
    ring
  rwa [hcount] at result

noncomputable def case_four_integer_tiling (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Tiling (caseFourOuter d hd a b ha hb) (commonScale a b ^ 2 * b * (a + b)) :=
  (case_four_integer_patch d hd he a b c ha hb hc hrel).toTiling

end Erdos633b.Sixty
