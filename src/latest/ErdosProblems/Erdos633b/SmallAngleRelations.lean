import ErdosProblems.Erdos633b.LargeMiddleNecessity

/-! Exact separation of seven local-relation families from a region
where the smallest reference angle and its corner count are bounded. -/

namespace Erdos633b

def smallAngleRelationTriples : Finset (ℤ × ℤ × ℤ) :=
  {(0, 3, 1), (0, 5, 2), (1, -3, -1), (1, 5, 2), (1, 6, 2), (2, 3, 1), (3, 3, 1)}

def SmallAngleLocalRelation (α β : ℝ) : Prop :=
  ∃ t ∈ smallAngleRelationTriples,
    (t.1 : ℝ) * α + (t.2.1 : ℝ) * β = (t.2.2 : ℝ) * Real.pi

theorem smallAngleRelationTriples_card : smallAngleRelationTriples.card = 7 := by decide

theorem angle_lower_of_relation_outside_seven (α β γ : ℝ)
    (hs : α + β + γ = Real.pi) (hβ : β ≤ 2 * Real.pi / 5)
    (hγ : γ ≤ 2 * Real.pi / 3) (t : ℤ × ℤ × ℤ)
    (ht : t ∈ orderedNonrightRelationTriples) (hne : t ∉ smallAngleRelationTriples)
    (he : (t.1 : ℝ) * α + (t.2.1 : ℝ) * β = (t.2.2 : ℝ) * Real.pi) :
    Real.pi / 21 ≤ α := by
  obtain ⟨hnotright, ht⟩ := Finset.mem_erase.mp ht
  simp only [orderedRelationTriples, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals first
    | exact False.elim (hne (by decide))
    | exact False.elim (hnotright rfl)
    | norm_num at he; linarith [Real.pi_pos]

theorem local_relation_small_or_angle_lower (α β γ : ℝ)
    (hs : α + β + γ = Real.pi) (hβ : β ≤ 2 * Real.pi / 5)
    (hγ : γ ≤ 2 * Real.pi / 3) (hrel : OrderedNonrightLocalRelation α β) :
    SmallAngleLocalRelation α β ∨ Real.pi / 21 ≤ α := by
  obtain ⟨t, ht, he⟩ := hrel
  by_cases hm : t ∈ smallAngleRelationTriples
  · exact Or.inl ⟨t, hm, he⟩
  · exact Or.inr (angle_lower_of_relation_outside_seven α β γ hs hβ hγ t ht hm he)

namespace Tiling

theorem corner_column_le_twenty_one_of_angle_lower {T : Triangle} {n : ℕ} (d : Tiling T n)
    (j : Fin 3) (hj : Real.pi / 21 ≤ d.tile.angle j) : d.cornerColumnCount j ≤ 21 := by
  have hsingle : (d.cornerColumnCount j : ℝ) * d.tile.angle j ≤ Real.pi := by
    rw [← d.corner_column_angle_sum]
    exact Finset.single_le_sum (fun i _ => mul_nonneg (Nat.cast_nonneg _)
      (d.tile.angle_pos i).le) (Finset.mem_univ j)
  by_contra hn
  have hh : (22 : ℝ) ≤ d.cornerColumnCount j := by
    exact_mod_cast (show 22 ≤ d.cornerColumnCount j by omega)
  have hm := mul_le_mul_of_nonneg_right hh (d.tile.angle_pos j).le
  linarith [Real.pi_pos]

theorem counterexample_small_relation_or_bounded_corners {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2) :
    SmallAngleLocalRelation (d.tile.angle 0) (d.tile.angle 1) ∨
      Real.pi / 21 ≤ d.tile.angle 0 ∧ d.cornerColumnCount 0 ≤ 21 := by
  have hβ := d.middle_angle_le_two_pi_fifths_of_counterexample hn hnot h01 h12
  have hγ := d.tile_angle_le_two_pi_thirds_of_counterexample hn hnot 2
  have hne := d.tile_angle_ne_pi_half_of_counterexample hn hnot 2
  have hscalene := (d.rational_angles_of_counterexample hn hnot).2.2.1
  have hrep := (d.rational_angles_of_counterexample hn hnot).2.2.2
  have hrel := nonright_relation_of_local_relation _ _ _ d.tile.angle_sum hne
    (d.ordered_local_relation h01 h12 hγ hscalene hrep)
  rcases local_relation_small_or_angle_lower _ _ _ d.tile.angle_sum hβ hγ hrel with hs | hb
  · exact Or.inl hs
  · exact Or.inr ⟨hb, d.corner_column_le_twenty_one_of_angle_lower 0 hb⟩

end Tiling
end Erdos633b
