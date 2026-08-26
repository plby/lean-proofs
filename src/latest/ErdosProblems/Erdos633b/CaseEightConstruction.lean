import ErdosProblems.Erdos633b.SixtyBisected
import ErdosProblems.Erdos633b.CaseTwo

/-! The exact integer geometric construction for case (8). -/

namespace Erdos633b.Sixty

theorem commonScale_comm (a b : ℕ) : commonScale a b = commonScale b a := by
  simp only [commonScale, GroupTwoDimensions.scale, Nat.add_comm a b]

noncomputable def caseEightOuter (d : ℝ) (hd : 0 < d) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) : Triangle :=
  bisectedTriangle d hd ((commonScale a b * (a + b) : ℕ) * (a : ℝ))
    (commonScale a b * a * b : ℕ) ((commonScale a b * (a + b) : ℕ) * (b : ℝ))
    (mul_pos (by exact_mod_cast mul_pos (commonScale_pos a b) (add_pos ha hb))
      (by exact_mod_cast ha))
    (by exact_mod_cast mul_pos (mul_pos (commonScale_pos a b) ha) hb)
    (mul_pos (by exact_mod_cast mul_pos (commonScale_pos a b) (add_pos ha hb))
      (by exact_mod_cast hb))

noncomputable def case_eight_integer_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
      (caseEightOuter d hd a b ha hb).support
      (commonScale a b ^ 2 * (a + b) * (2 * a + b)) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hrelr : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + a * b + (b : ℝ) ^ 2 := by exact_mod_cast hrel
  have hrel' : c ^ 2 = b ^ 2 + b * a + a ^ 2 := by nlinarith
  have hrelr' : (c : ℝ) ^ 2 = (b : ℝ) ^ 2 + b * a + (a : ℝ) ^ 2 := by exact_mod_cast hrel'
  let k := commonScale a b * (a + b)
  have hk : 0 < k := mul_pos (commonScale_pos a b) (add_pos ha hb)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  let x : ℝ := k * (a : ℝ)
  let y : ℝ := (commonScale a b * a * b : ℕ)
  let z : ℝ := k * (b : ℝ)
  have hx : 0 < x := mul_pos hkr har
  have hy : 0 < y := by
    dsimp only [y]
    exact_mod_cast mul_pos (mul_pos (commonScale_pos a b) ha) hb
  have hz : 0 < z := mul_pos hkr hbr
  let T := bisectedTriangle d hd x y z hx hy hz
  let R := groupTwoReference d hd a b har hbr
  let F := T.edgeFirst (z / (y + z)) (bisected_weight_bounds y z hy hz).1
  let F' : Triangle := F.reindex (Equiv.swap 0 2)
  let S := T.edgeSecond (z / (y + z)) (bisected_weight_bounds y z hy hz).2
  have first : Patch R F.support (k ^ 2) := by
    have hs (i : Fin 3) : F'.side i = (k : ℝ) * R.side i :=
      bisected_first_sides d hd he a b c k y har hbr hkr hy hrelr i
    have result := quadratic_patch_congruent R F' k hk hs
    simpa only [F', Triangle.support_reindex] using result
  let U := caseFourOuter d hd b a hb ha
  have hcorner : cornerTriangle d hd x y hx hy = U := by
    apply Affine.Simplex.ext
    intro i
    have hup : U.points = ![point d 0 0,
        point d ((commonScale b a * a : ℕ) * ((b : ℝ) + a)) 0,
        point d 0 ((commonScale b a * a : ℕ) * (b : ℝ))] := rfl
    rw [cornerTriangle_points, hup, commonScale_comm b a]
    fin_cases i
    · rfl
    · change point d x 0 = point d ((commonScale a b * a : ℕ) * ((b : ℝ) + a)) 0
      congr 1
      dsimp only [x, k]
      push_cast
      ring
    · change point d 0 y = point d 0 ((commonScale a b * a : ℕ) * (b : ℝ))
      congr 1
      dsimp only [y]
      push_cast
      ring
  have hsupport : S.support = U.support :=
    (bisected_second_support d hd x y z hx hy hz).trans (congrArg Triangle.support hcorner)
  let R0 := groupTwoReference d hd b a hbr har
  let R1 : Triangle := R0.reindex (Equiv.swap 1 2)
  have second : Patch R S.support (commonScale a b ^ 2 * a * (a + b)) := by
    have base := case_four_integer_patch d hd he b a c hb ha hc hrel'
    have reordered : Patch R1 U.support (commonScale b a ^ 2 * a * (b + a)) :=
      base.changeTile (R0.support_reindex (Equiv.swap 1 2)).symm
    have hs (i : Fin 3) : R.side i = R1.side i := by
      rw [Triangle.side_reindex, reference_sides d hd he a b c har hbr hcr hrelr,
        reference_sides d hd he b a c hbr har hcr hrelr']
      fin_cases i <;> rfl
    have result := reordered.changeTileBySides R hs
    rw [commonScale_comm b a, Nat.add_comm b a] at result
    rwa [← hsupport] at result
  have result := first.glueTwo second (T.edgeParts_disjoint_interiors (z / (y + z))
    (bisected_weight_bounds y z hy hz).1 (bisected_weight_bounds y z hy hz).2)
  rw [T.edgeParts_cover (z / (y + z)) (bisected_weight_bounds y z hy hz).1
    (bisected_weight_bounds y z hy hz).2] at result
  have hcount : k ^ 2 + commonScale a b ^ 2 * a * (a + b) =
      commonScale a b ^ 2 * (a + b) * (2 * a + b) := by
    dsimp only [k]
    ring
  rwa [hcount] at result

noncomputable def case_eight_integer_tiling (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Tiling (caseEightOuter d hd a b ha hb) (commonScale a b ^ 2 * (a + b) * (2 * a + b)) :=
  (case_eight_integer_patch d hd he a b c ha hb hc hrel).toTiling

end Erdos633b.Sixty
