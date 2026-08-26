import ErdosProblems.Erdos633b.Similarity
import ErdosProblems.Erdos633b.TriquadraticCase

/-! Sufficiency of case (7) for an arbitrary nondegenerate Euclidean triangle. -/

namespace Erdos633b

theorem case_seven_sufficient (T : Triangle)
    (hrel : T.angle 2 = T.angle 0 / 2 + T.angle 1)
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hparam : 2 * Real.sin (T.angle 0 / 4) = (m : ℝ) / k)
    (hn : ¬ IsSquare (2 * (k : ℤ) ^ 2 - (m : ℤ) ^ 2)) : HasNonsquareTiling T := by
  have hA : T.angle 0 < 2 * Real.pi / 3 := by
    linarith [T.angle_sum, T.angle_pos 1]
  have hslt : 2 * Real.sin (T.angle 0 / 4) < 1 := by
    have hh := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [Real.pi_pos, T.angle_pos 0] : -(Real.pi / 2) ≤ T.angle 0 / 4)
      (by linarith [Real.pi_pos] : Real.pi / 6 ≤ Real.pi / 2)
      (by linarith : T.angle 0 / 4 < Real.pi / 6)
    rw [Real.sin_pi_div_six] at hh
    linarith
  have hmk : m < k := by
    rw [hparam] at hslt
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    exact_mod_cast (div_lt_one hkr).mp hslt
  obtain ⟨S, hSrel, hSparam, hS⟩ :=
    TriquadraticCoordinates.case_seven_representative m k hm hmk hn
  have hsin : Real.sin (S.angle 0 / 4) = Real.sin (T.angle 0 / 4) := by
    linarith
  have hzero : S.angle 0 = T.angle 0 := by
    have heq := Real.injOn_sin
      (show S.angle 0 / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos, S.angle_pos 0], by linarith [Real.pi_pos, S.angle_lt_pi 0]⟩)
      (show T.angle 0 / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos, T.angle_pos 0], by linarith [Real.pi_pos, T.angle_lt_pi 0]⟩)
      hsin
    linarith
  have hone : S.angle 1 = T.angle 1 := by linarith [S.angle_sum, T.angle_sum]
  have htwo : S.angle 2 = T.angle 2 := by linarith
  apply hasNonsquareTiling_of_angle_eq (T := S) (S := T) _ hS
  intro i
  fin_cases i
  · exact hzero
  · exact hone
  · exact htwo

theorem fin_three_other_indices (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (a = b + 1 ∧ c = b + 2) ∨ (a = b + 2 ∧ c = b + 1) := by
  decide +revert

theorem Triangle.angle_reindex (T : Triangle) (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    Triangle.angle (T.reindex e) i = T.angle (e.symm i) := by
  have hab : e.symm (i + 1) ≠ e.symm i := e.symm.injective.ne (by fin_cases i <;> decide)
  have hbc : e.symm i ≠ e.symm (i + 2) := e.symm.injective.ne (by fin_cases i <;> decide)
  have hac : e.symm (i + 1) ≠ e.symm (i + 2) := e.symm.injective.ne (by fin_cases i <;> decide)
  change EuclideanGeometry.angle (T.points (e.symm (i + 1))) (T.points (e.symm i))
      (T.points (e.symm (i + 2))) =
    EuclideanGeometry.angle (T.points (e.symm i + 1)) (T.points (e.symm i))
      (T.points (e.symm i + 2))
  obtain ⟨ha, hc⟩ | ⟨ha, hc⟩ := fin_three_other_indices _ _ _ hab hbc hac
  · rw [ha, hc]
  · rw [ha, hc, EuclideanGeometry.angle_comm]

theorem hasNonsquareTiling_of_support_eq {T S : Triangle} (h : T.support = S.support)
    (hT : HasNonsquareTiling T) : HasNonsquareTiling S := by
  obtain ⟨n, hn, ⟨d⟩⟩ := hT
  let d' : Tiling S n :=
    { tile := d.tile
      place := d.place
      covers := d.covers.trans h
      disjoint_interiors := d.disjoint_interiors }
  exact ⟨n, hn, ⟨d'⟩⟩

/-- The full existential ordering in the seventh case of the eight-case classification. -/
theorem case_seven_sufficient_reindexed (T : Triangle) (e : Equiv.Perm (Fin 3))
    (hrel : T.angle (e 2) = T.angle (e 0) / 2 + T.angle (e 1))
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hparam : 2 * Real.sin (T.angle (e 0) / 4) = (m : ℝ) / k)
    (hn : ¬ IsSquare (2 * (k : ℤ) ^ 2 - (m : ℤ) ^ 2)) : HasNonsquareTiling T := by
  have hang (i : Fin 3) : Triangle.angle (T.reindex e.symm) i = T.angle (e i) := by
    simp only [Triangle.angle_reindex, Equiv.symm_symm]
  have result := case_seven_sufficient (T.reindex e.symm)
    (by simpa only [hang] using hrel) m k hm hk
    (by simpa only [hang] using hparam) hn
  exact hasNonsquareTiling_of_support_eq (T.support_reindex e.symm) result

end Erdos633b
