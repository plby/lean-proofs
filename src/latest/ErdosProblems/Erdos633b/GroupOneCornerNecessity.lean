import ErdosProblems.Erdos633b.CaseSixUnconditional
import ErdosProblems.Erdos633b.CaseSevenUnconditional
import ErdosProblems.Erdos633b.CornerPairOrdering

/-! The exact corner-column pattern (3,2,0) reduces to reptiling
or one of the two now-unconditional group-1 branches. -/

namespace Erdos633b

theorem sorted_groupOne_pairs (p₀ q₀ p₁ q₁ p₂ q₂ : ℕ)
    (hn₀ : 0 < p₀ + q₀) (hn₁ : 0 < p₁ + q₁) (hn₂ : 0 < p₂ + q₂)
    (h₀₁ : p₀ < p₁ ∨ p₀ = p₁ ∧ q₀ < q₁)
    (h₁₂ : p₁ < p₂ ∨ p₁ = p₂ ∧ q₁ < q₂)
    (hP : p₀ + p₁ + p₂ = 3) (hQ : q₀ + q₁ + q₂ = 2) :
    (p₀ = 0 ∧ q₀ = 1 ∧ p₁ = 1 ∧ q₁ = 0 ∧ p₂ = 2 ∧ q₂ = 1) ∨
    (p₀ = 0 ∧ q₀ = 1 ∧ p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 2 ∧ q₂ = 0) ∨
    (p₀ = 0 ∧ q₀ = 2 ∧ p₁ = 1 ∧ q₁ = 0 ∧ p₂ = 2 ∧ q₂ = 0) := by omega

namespace Tiling

theorem groupOne_corner_columns_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hscalene : Function.Injective T.angle)
    (hP : d.cornerColumnCount 0 = 3) (hQ : d.cornerColumnCount 1 = 2)
    (hR : d.cornerColumnCount 2 = 0) : EightCases T := by
  obtain ⟨e, he01, he12⟩ := three_corner_pairs_ordered
    (fun i => d.cornerAngleCount i 0) (fun i => d.cornerAngleCount i 1)
    (fun i => (d.corner_count_le_column i 1).trans (by omega))
    (d.corner_pair_injective hR hscalene)
  have hpairs := sorted_groupOne_pairs _ _ _ _ _ _
    (d.corner_pair_nonzero hR (e 0)) (d.corner_pair_nonzero hR (e 1))
    (d.corner_pair_nonzero hR (e 2)) he01 he12
    ((d.corner_column_reorder e 0).trans hP) ((d.corner_column_reorder e 1).trans hQ)
  have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
    have hh := d.corner_column_angle_sum
    rw [Fin.sum_univ_three, hP, hQ, hR] at hh
    simpa using hh
  let U : Triangle := T.reindex e.symm
  let d' : Tiling U n := d.reindexOuter e.symm
  have hrow (i : Fin 3) : U.angle i = (d.cornerAngleCount (e i) 0 : ℝ) * d.tile.angle 0 +
      (d.cornerAngleCount (e i) 1 : ℝ) * d.tile.angle 1 := by
    simpa only [U, Triangle.angle_reindex, Equiv.symm_symm] using d.corner_two_angle_row hR (e i)
  apply eightCases_of_reindex T e.symm
  change EightCases U
  rcases hpairs with ⟨h00, h01, h10, h11, h20, h21⟩ |
    ⟨h00, h01, h10, h11, h20, h21⟩ | ⟨h00, h01, h10, h11, h20, h21⟩
  all_goals
    have h0 := hrow 0
    have h1 := hrow 1
    have h2 := hrow 2
    norm_num only [h00, h01, h10, h11, h20, h21, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, zero_mul, one_mul, zero_add, add_zero] at h0 h1 h2
  · apply d'.reptiling_necessary hn
    refine ⟨Equiv.swap 0 1, ?_⟩
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · change U.angle 2 = d.tile.angle 2
      linarith [d.tile.angle_sum]
  · apply d'.caseSeven_necessary_unconditional_reindex hn (Equiv.refl _)
      ((Equiv.swap 0 1).trans (Equiv.swap 0 2))
    · exact h2
    · exact h0
    · exact h1
  · apply d'.caseSix_necessary_unconditional_reindex hn (Equiv.refl _)
      ((Equiv.swap 0 2).trans (Equiv.swap 0 1))
    · exact h1
    · exact h2
    · exact h0

end Tiling
end Erdos633b
