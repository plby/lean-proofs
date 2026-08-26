import ErdosProblems.Erdos633.RightGeometry
import ErdosProblems.Erdos633.VTiling

/-!
# Right-triangle tilings with a sum-of-two-squares count

The altitude pieces have scales `m/c` and `n/c`. Subdividing them into
`m²` and `n²` triangles produces copies of the same `1/c`-scaled reference.
-/

namespace Erdos633

def RightShape.ofLegs (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : RightShape where
  x := m
  y := n
  x_pos := by exact_mod_cast hm
  y_pos := by exact_mod_cast hn

/-- Actual congruent tilings with `m²+n²` pieces for integer legs `m,n`. -/
theorem RightShape.tiling_of_integer_legs (v : RightShape) (m n : ℕ)
    (hx : v.x = (m : ℝ)) (hy : v.y = (n : ℝ)) :
    ∃ R : Triangle, Nonempty (CongruentTiling v.triangle R (m ^ 2 + n ^ 2)) := by
  have hm : 0 < m := by exact_mod_cast (hx ▸ v.x_pos)
  have hn : 0 < n := by exact_mod_cast (hy ▸ v.y_pos)
  let ε : ℝ := 1 / v.c
  have hε : 0 < ε := one_div_pos.mpr v.c_pos
  have hmx : (m : ℝ) * ε = v.x / v.c := by rw [hx]; dsimp [ε]; ring
  have hny : (n : ℝ) * ε = v.y / v.c := by rw [hy]; dsimp [ε]; ring
  let TX := v.triangle.scaleTiling ε (v.x / v.c) hε (div_pos v.x_pos v.c_pos) m hm hmx
  let TY := v.triangle.scaleTiling ε (v.y / v.c) hε (div_pos v.y_pos v.c_pos) n hn hny
  obtain ⟨e₁, he₁⟩ := v.first_congruent
  obtain ⟨e₂, he₂⟩ := v.second_congruent
  let T₁ := (TX.mapIsometry e₁).of_carrier_eq
    ((Triangle.mapIsometry_carrier _ e₁).trans he₁)
  let T₂ := (TY.mapIsometry e₂).of_carrier_eq
    ((Triangle.mapIsometry_carrier _ e₂).trans he₂)
  exact ⟨_, ⟨v.triangle.glueSplitTilings v.r v.r_pos v.r_lt_one T₁ T₂⟩⟩

theorem RightShape.admitsNonsquareTiling_of_integer_legs (v : RightShape) (m n : ℕ)
    (hx : v.x = (m : ℝ)) (hy : v.y = (n : ℝ)) (hns : ¬ IsSquare (m ^ 2 + n ^ 2)) :
    AdmitsNonsquareTiling v.triangle := by
  obtain ⟨R, hR⟩ := v.tiling_of_integer_legs m n hx hy
  exact ⟨m ^ 2 + n ^ 2, R, hns, hR⟩

theorem rationalRight_admitsNonsquareTiling (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hns : ¬ IsSquare (m ^ 2 + n ^ 2)) :
    AdmitsNonsquareTiling (RightShape.ofLegs m n hm hn).triangle :=
  (RightShape.ofLegs m n hm hn).admitsNonsquareTiling_of_integer_legs m n rfl rfl hns

/-- The rational-leg sufficient criterion is invariant under position,
reflection, and arbitrary positive scale. -/
theorem Triangle.admitsNonsquareTiling_of_right_sides (P : Triangle)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hns : ¬ IsSquare (m ^ 2 + n ^ 2))
    (q : ℝ) (hq : 0 < q)
    (hab : Complex.normSq (P.b - P.a) = q ^ 2 * (m : ℝ) ^ 2)
    (hac : Complex.normSq (P.c - P.a) = q ^ 2 * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2))
    (hbc : Complex.normSq (P.c - P.b) = q ^ 2 * (n : ℝ) ^ 2) :
    AdmitsNonsquareTiling P := by
  let v := RightShape.ofLegs m n hm hn
  have hQ := admitsNonsquareTiling_mapSimilarity
    (rationalRight_admitsNonsquareTiling m n hm hn hns) 0 (q : ℂ)
    (by exact_mod_cast ne_of_gt hq)
  apply admitsNonsquareTiling_of_congruent hQ
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + (q : ℂ) * v.triangle.b) -
      (0 + (q : ℂ) * v.triangle.a)) = _
    rw [normSq_similarity_sub, v.side_squares.1, Complex.normSq_ofReal, hab]
    change q * q * (m : ℝ) ^ 2 = q ^ 2 * (m : ℝ) ^ 2
    ring
  · change Complex.normSq ((0 + (q : ℂ) * v.triangle.c) -
      (0 + (q : ℂ) * v.triangle.a)) = _
    rw [normSq_similarity_sub, v.side_squares.2.1, Complex.normSq_ofReal, hac]
    change q * q * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) =
      q ^ 2 * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)
    ring
  · change Complex.normSq ((0 + (q : ℂ) * v.triangle.c) -
      (0 + (q : ℂ) * v.triangle.b)) = _
    rw [normSq_similarity_sub, v.side_squares.2.2, Complex.normSq_ofReal, hbc]
    change q * q * (n : ℝ) ^ 2 = q ^ 2 * (n : ℝ) ^ 2
    ring

theorem right_two_three_tiling :
    ∃ R : Triangle, Nonempty (CongruentTiling
      (RightShape.ofLegs 2 3 (by norm_num) (by norm_num)).triangle R 13) := by
  have h := (RightShape.ofLegs 2 3 (by norm_num) (by norm_num)).tiling_of_integer_legs
    2 3 rfl rfl
  norm_num at h
  exact h

end Erdos633
