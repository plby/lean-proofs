import ErdosProblems.Erdos1148.PeriodGap

/-!
# The period group and its positive generator

The trace gap isolates zero in the additive group of integral flow
periods. Pell's equation makes the group nontrivial for the integral
nonsquare-discriminant trajectories. Such a trajectory therefore has
a least positive period, and all periods are its integer multiples.
-/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma integral_flow_relation_neg {g : SL(2, ℝ)} {γ : SL(2, ℤ)} {T : ℝ}
    (hγ : (γ : SL(2, ℝ)) * g = g * diagonalFlow T) :
    ((γ⁻¹ : SL(2, ℤ)) : SL(2, ℝ)) * g = g * diagonalFlow (-T) := by
  have hinv : ((γ⁻¹ : SL(2, ℤ)) : SL(2, ℝ)) = (γ : SL(2, ℝ))⁻¹ :=
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)).map_inv γ
  calc
    ((γ⁻¹ : SL(2, ℤ)) : SL(2, ℝ)) * g =
        ((γ⁻¹ : SL(2, ℤ)) : SL(2, ℝ)) * (g * diagonalFlow T) * (diagonalFlow T)⁻¹ := by
      simp [mul_assoc]
    _ = ((γ⁻¹ : SL(2, ℤ)) : SL(2, ℝ)) * ((γ : SL(2, ℝ)) * g) *
        (diagonalFlow T)⁻¹ := by rw [hγ]
    _ = g * (diagonalFlow T)⁻¹ := by rw [hinv, ← mul_assoc, inv_mul_cancel, one_mul]
    _ = g * diagonalFlow (-T) := by rw [diagonalFlow_neg]

def flowPeriodGroup (g : SL(2, ℝ)) : AddSubgroup ℝ where
  carrier := {T | ∃ γ : SL(2, ℤ), (γ : SL(2, ℝ)) * g = g * diagonalFlow T}
  zero_mem' := by
    refine ⟨1, ?_⟩
    simp [diagonalFlow_zero]
  add_mem' := by
    rintro T U ⟨γ, hγ⟩ ⟨δ, hδ⟩
    refine ⟨γ * δ, ?_⟩
    change Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (γ * δ) * g =
      g * diagonalFlow (T + U)
    rw [map_mul, mul_assoc, hδ, ← mul_assoc, hγ, mul_assoc, ← diagonalFlow_add]
  neg_mem' := by
    rintro T ⟨γ, hγ⟩
    exact ⟨γ⁻¹, integral_flow_relation_neg hγ⟩

lemma flowPeriodGroup_disjoint_gap (g : SL(2, ℝ)) :
    Disjoint (flowPeriodGroup g : Set ℝ) (Set.Ioo 0 (2 * Real.log (3 / 2 : ℝ))) := by
  apply Set.disjoint_left.mpr
  rintro T ⟨γ, hγ⟩ ⟨hT0, hTgap⟩
  have hgap := integral_flow_period_gap g γ hT0.ne' hγ
  rw [abs_of_pos hT0] at hgap
  exact (not_lt_of_ge hgap) hTgap

lemma flowPeriodGroup_ne_bot {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (g : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) t) : flowPeriodGroup g ≠ ⊥ := by
  obtain ⟨T, hT, γ, hγ⟩ := exists_positive_integral_flow_period hd hns ht g hg
  intro hbot
  have hmem : T ∈ flowPeriodGroup g := ⟨γ, hγ⟩
  rw [hbot, AddSubgroup.mem_bot] at hmem
  exact hT.ne' hmem

theorem exists_least_positive_flow_period {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (g : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) t) :
    ∃ T : ℝ, 0 < T ∧ flowPeriodGroup g = AddSubgroup.zmultiples T ∧
      IsLeast {s : ℝ | s ∈ flowPeriodGroup g ∧ 0 < s} T := by
  obtain ⟨T, hT⟩ := AddSubgroup.exists_isLeast_pos
    (flowPeriodGroup_ne_bot hd hns ht g hg) period_gap_pos (flowPeriodGroup_disjoint_gap g)
  refine ⟨T, hT.1.2, ?_, hT⟩
  rw [AddSubgroup.zmultiples_eq_closure]
  exact AddSubgroup.cyclic_of_min hT

end Erdos1148.DukeArithmetic
