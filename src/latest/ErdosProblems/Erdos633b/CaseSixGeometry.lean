import ErdosProblems.Erdos633b.CaseSixConstruction
import ErdosProblems.Erdos633b.GroupTwoParameters

/-! Every case-(6) input has the positive geometric construction; nonsquareness is separate. -/

namespace Erdos633b

theorem group_one_integer_data (s : ℝ) (hs : 0 < s) (hs1 : s < 1) (hrat : IsRational s) :
    ∃ a b c j : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < j ∧ a < c ∧
      b + j = c ∧ j * c = a ^ 2 ∧ (a : ℝ) / c = s := by
  obtain ⟨q, hq⟩ := hrat
  obtain ⟨m, n, hm, hn, hqv⟩ := GroupTwoParameters.positive_parts q (by rwa [hq]) (by rwa [hq])
  let k := m + n
  have hk : 0 < k := by dsimp only [k]; omega
  have hmk : m < k := by dsimp only [k]; omega
  let a := m * k
  let c := k ^ 2
  let j := m ^ 2
  let b := c - j
  have ha : 0 < a := mul_pos hm hk
  have hc : 0 < c := pow_pos hk 2
  have hj : 0 < j := pow_pos hm 2
  have hjc : j < c := by dsimp only [j, c]; nlinarith
  have hb : 0 < b := Nat.sub_pos_of_lt hjc
  have hac : a < c := by
    dsimp only [a, c]
    nlinarith
  have hbj : b + j = c := Nat.sub_add_cancel hjc.le
  have hcj : j * c = a ^ 2 := by dsimp only [j, c, a]; ring
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hratio : (a : ℝ) / c = (m : ℝ) / k := by
    dsimp only [a, c]
    push_cast
    field_simp
  refine ⟨a, b, c, j, ha, hb, hc, hj, hac, hbj, hcj, ?_⟩
  rw [hratio]
  have hqv' : (q : ℝ) = (m : ℝ) / k := by simpa only [k, Nat.cast_add] using hqv
  exact hqv'.symm.trans hq

theorem case_six_geometric_counts (T : Triangle) (hB : T.angle 1 = 2 * T.angle 0)
    (hrat : IsRational (Real.sin (T.angle 0 / 2))) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a < c ∧
      b * c + a ^ 2 = c ^ 2 ∧ Nonempty (Tiling T ((c + b) * (2 * c + b))) := by
  have hA : T.angle 0 < Real.pi / 3 := by linarith [T.angle_sum, T.angle_pos 2]
  have hs : 0 < 2 * Real.sin (T.angle 0 / 2) := mul_pos (by norm_num)
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [T.angle_pos 0])
      (by linarith [T.angle_lt_pi 0, Real.pi_pos]))
  have hs1 : 2 * Real.sin (T.angle 0 / 2) < 1 := by
    have hh := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [T.angle_pos 0, Real.pi_pos] : -(Real.pi / 2) ≤ T.angle 0 / 2)
      (by linarith [Real.pi_pos] : Real.pi / 6 ≤ Real.pi / 2)
      (by linarith : T.angle 0 / 2 < Real.pi / 6)
    rw [Real.sin_pi_div_six] at hh
    linarith
  have hrat' : IsRational (2 * Real.sin (T.angle 0 / 2)) := by
    obtain ⟨q, hq⟩ := hrat
    refine ⟨2 * q, ?_⟩
    push_cast
    rw [hq]
  obtain ⟨a, b, c, j, ha, hb, hc, hj, hac, hbj, hcj, hparam⟩ :=
    group_one_integer_data _ hs hs1 hrat'
  let U := CaseSixCoordinates.rationalOuter a c ha hac
  let V : Triangle := U.reindex (Equiv.swap 0 1)
  have hu := CaseSixCoordinates.rationalOuter_relations a c ha hac
  have hone : U.angle 1 = T.angle 0 := by
    have hsin : Real.sin (U.angle 1 / 2) = Real.sin (T.angle 0 / 2) := by linarith [hu.2]
    have heq := Real.injOn_sin
      (show U.angle 1 / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [U.angle_pos 1, Real.pi_pos], by linarith [U.angle_lt_pi 1]⟩)
      (show T.angle 0 / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [T.angle_pos 0, Real.pi_pos], by linarith [T.angle_lt_pi 0]⟩) hsin
    linarith
  have hv0 : V.angle 0 = T.angle 0 := by rw [Triangle.angle_reindex]; exact hone
  have hv1 : V.angle 1 = T.angle 1 := by
    rw [Triangle.angle_reindex]
    change U.angle 0 = T.angle 1
    linarith [hu.1]
  have hv2 : V.angle 2 = T.angle 2 := by linarith [V.angle_sum, T.angle_sum]
  have hangs : ∀ i, V.angle i = T.angle i := by
    intro i
    fin_cases i
    · exact hv0
    · exact hv1
    · exact hv2
  have hrelation : b * c + a ^ 2 = c ^ 2 := by rw [← hcj, ← hbj]; ring
  refine ⟨a, b, c, ha, hb, hc, hac, hrelation, ⟨?_⟩⟩
  exact ((CaseSixCoordinates.integer_tiling a b c j ha hb hj hac hbj hcj).reindexOuter
    (Equiv.swap 0 1)).transportAngles hangs

theorem case_six_geometric_counts_reindexed (T : Triangle) (e : Equiv.Perm (Fin 3))
    (hB : T.angle (e 1) = 2 * T.angle (e 0))
    (hrat : IsRational (Real.sin (T.angle (e 0) / 2))) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a < c ∧
      b * c + a ^ 2 = c ^ 2 ∧ Nonempty (Tiling T ((c + b) * (2 * c + b))) := by
  obtain ⟨a, b, c, ha, hb, hc, hac, hrel, ⟨d⟩⟩ :=
    case_six_geometric_counts (T.reindex e.symm)
      (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hB)
      (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hrat)
  refine ⟨a, b, c, ha, hb, hc, hac, hrel, ⟨?_⟩⟩
  exact { tile := d.tile
          place := d.place
          covers := by simpa only [Triangle.support_reindex] using d.covers
          disjoint_interiors := d.disjoint_interiors }

end Erdos633b
