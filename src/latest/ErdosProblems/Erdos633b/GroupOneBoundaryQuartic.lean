import ErdosProblems.Erdos633b.CaseSixMetric
import ErdosProblems.Erdos633b.CosineLowDegree

/-! Actual boundary rows force a nonzero quartic relation in the
first group-1 sine parameter. No existence of a tiling is assumed abstractly. -/

namespace Erdos633b

noncomputable def groupOneBoundaryRow (m : Fin 3 → ℕ) (s : ℝ) : ℝ :=
  (m 0 : ℝ) * s + m 1 * (1 - s ^ 2) + m 2

noncomputable def groupOneFirstCoeffs (m : Fin 3 → Fin 3 → ℕ) : Fin 5 → ℚ :=
  ![2 * (m 0 1 : ℚ) + 2 * m 0 2 - m 1 1 - m 1 2,
    2 * (m 0 0 : ℚ) - m 1 0, (m 1 1 : ℚ) - 3 * m 0 1 - m 0 2,
    -(m 0 0 : ℚ), (m 0 1 : ℚ)]

noncomputable def groupOneSecondCoeffs (m : Fin 3 → Fin 3 → ℕ) : Fin 5 → ℚ :=
  ![3 * (m 0 2 : ℚ) - m 2 1 - m 2 2, -(m 2 0 : ℚ),
    (m 2 1 : ℚ) - 4 * m 0 2, 0, (m 0 2 : ℚ)]

theorem groupOne_first_quartic (m : Fin 3 → Fin 3 → ℕ) (s : ℝ)
    (h : groupOneBoundaryRow (m 1) s = groupOneBoundaryRow (m 0) s * (2 - s ^ 2)) :
    let a := groupOneFirstCoeffs m
    (a 0 : ℝ) + a 1 * s + a 2 * s ^ 2 + a 3 * s ^ 3 + a 4 * s ^ 4 = 0 := by
  dsimp [groupOneFirstCoeffs]
  push_cast
  dsimp only [groupOneBoundaryRow] at h
  linear_combination -h

theorem groupOne_second_quartic (m : Fin 3 → Fin 3 → ℕ) (s : ℝ)
    (hp : m 0 0 = 0) (hq : m 0 1 = 0)
    (h : groupOneBoundaryRow (m 2) s =
      groupOneBoundaryRow (m 0) s * (1 - s ^ 2) * (3 - s ^ 2)) :
    let a := groupOneSecondCoeffs m
    (a 0 : ℝ) + a 1 * s + a 2 * s ^ 2 + a 3 * s ^ 3 + a 4 * s ^ 4 = 0 := by
  dsimp [groupOneSecondCoeffs]
  push_cast
  dsimp only [groupOneBoundaryRow] at h
  rw [hp, hq] at h
  push_cast at h
  linear_combination -h

namespace Tiling

theorem groupOne_normalized_boundary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi) (i : Fin 3) :
    T.side i / d.tile.side 2 =
      groupOneBoundaryRow (d.boundarySideCount i) (2 * Real.sin (d.tile.angle 0 / 2)) := by
  obtain ⟨ha, hb⟩ := d.tile.groupOne_side_ratios hrel
  rw [d.side_eq_three_counts i, add_div, add_div, mul_div_assoc, mul_div_assoc,
    mul_div_assoc, ha, hb, div_self (d.tile.side_pos 2).ne', mul_one]
  rfl

theorem groupOne_first_boundary_equations {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 2 * d.tile.angle 1) :
    let s := 2 * Real.sin (d.tile.angle 0 / 2)
    groupOneBoundaryRow (d.boundarySideCount 1) s =
      groupOneBoundaryRow (d.boundarySideCount 0) s * (2 - s ^ 2) ∧
    groupOneBoundaryRow (d.boundarySideCount 2) s =
      groupOneBoundaryRow (d.boundarySideCount 0) s * (1 - s ^ 2) * (3 - s ^ 2) := by
  have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith
  obtain ⟨ha, hb⟩ := d.tile.caseSix_normalized_sides T hrel h0 h1 h2
  simpa only [d.groupOne_normalized_boundary hrel] using And.intro ha hb

theorem groupOne_first_nonzero_quartic {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 2 * d.tile.angle 1) :
    ∃ a : Fin 5 → ℚ, (∃ i, a i ≠ 0) ∧
      let s := 2 * Real.sin (d.tile.angle 0 / 2)
      (a 0 : ℝ) + a 1 * s + a 2 * s ^ 2 + a 3 * s ^ 3 + a 4 * s ^ 4 = 0 := by
  obtain ⟨hY, hZ⟩ := d.groupOne_first_boundary_equations h0 h1 h2
  by_cases hp : d.boundarySideCount 0 0 = 0
  · by_cases hq : d.boundarySideCount 0 1 = 0
    · have hr : d.boundarySideCount 0 2 ≠ 0 := by
        intro hr
        have hh := d.side_eq_three_counts 0
        simp only [hp, hq, hr, Nat.cast_zero, zero_mul, zero_add] at hh
        exact (T.side_pos 0).ne' hh
      refine ⟨groupOneSecondCoeffs d.boundarySideCount, ⟨4, ?_⟩,
        groupOne_second_quartic _ _ hp hq hZ⟩
      simpa [groupOneSecondCoeffs] using hr
    · refine ⟨groupOneFirstCoeffs d.boundarySideCount, ⟨4, ?_⟩,
        groupOne_first_quartic _ _ hY⟩
      simpa [groupOneFirstCoeffs] using hq
  · refine ⟨groupOneFirstCoeffs d.boundarySideCount, ⟨3, ?_⟩,
      groupOne_first_quartic _ _ hY⟩
    simpa [groupOneFirstCoeffs] using hp

theorem groupOne_first_parameter_not_large_degree {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 2 * d.tile.angle 1)
    (M k : ℕ) (hM : 0 < M) (hk : k.Coprime M) (hdeg : 8 < M.totient) :
    2 * Real.sin (d.tile.angle 0 / 2) ≠ 2 * Real.cos (2 * Real.pi * k / M) := by
  intro he
  obtain ⟨a, ⟨i, hi⟩, ha⟩ := d.groupOne_first_nonzero_quartic h0 h1 h2
  dsimp only at ha
  rw [he] at ha
  exact hi (quartic_cosine_independent M k hM hk hdeg a ha i)

end Tiling
end Erdos633b
