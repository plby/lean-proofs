import ErdosProblems.Erdos633b.SixAngleShapes
import ErdosProblems.Erdos633b.CornerPairEnumeration
import Mathlib.Tactic.Linarith

/-! Explicit angle permutations group the seventeen proved coefficient
patterns into reptilings and the six non-reptiling shapes. -/

namespace Erdos633b

theorem angle_shapes_of_corner_pattern (S T : Triangle) (x₀ x₁ x₂ : ℕ × ℕ)
    (hm : (x₀, x₁, x₂) ∈ cornerPairPatterns)
    (h₀ : T.angle 0 = (x₀.1 : ℝ) * S.angle 0 + (x₀.2 : ℝ) * S.angle 1)
    (h₁ : T.angle 1 = (x₁.1 : ℝ) * S.angle 0 + (x₁.2 : ℝ) * S.angle 1)
    (h₂ : T.angle 2 = (x₂.1 : ℝ) * S.angle 0 + (x₂.2 : ℝ) * S.angle 1) :
    ReptilingAngles S T ∨ SixAngleShapes S T := by
  have hS := S.angle_sum
  have hT := T.angle_sum
  simp only [cornerPairPatterns, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    left
    refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2), ?_⟩
    intro i
    fin_cases i
    · change T.angle 0 = S.angle 1
      linarith
    · change T.angle 1 = S.angle 2
      linarith
    · change T.angle 2 = S.angle 0
      linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    left
    refine ⟨Equiv.swap 0 1, ?_⟩
    intro i
    fin_cases i
    · change T.angle 0 = S.angle 1
      linarith
    · change T.angle 1 = S.angle 0
      linarith
    · change T.angle 2 = S.angle 2
      linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    right
    refine ⟨Equiv.swap 0 1, (Equiv.refl _).symm, ?_⟩
    left
    refine ⟨?_, ?_⟩
    · simp only [Triangle.angle_reindex]
      change 3 * S.angle 1 + 2 * S.angle 0 = Real.pi
      linarith
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · simp only [Triangle.angle_reindex]
        change T.angle 0 = S.angle 1
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 1 = 2 * S.angle 1
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 2 = 2 * S.angle 0
        linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    left
    refine ⟨Equiv.swap 0 1, ?_⟩
    intro i
    fin_cases i
    · change T.angle 0 = S.angle 1
      linarith
    · change T.angle 1 = S.angle 0
      linarith
    · change T.angle 2 = S.angle 2
      linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    right
    refine ⟨Equiv.swap 0 1, (Equiv.refl _).symm, ?_⟩
    left
    refine ⟨?_, ?_⟩
    · simp only [Triangle.angle_reindex]
      change 3 * S.angle 1 + 2 * S.angle 0 = Real.pi
      linarith
    · refine Or.inr (⟨?_, ?_, ?_⟩)
      · simp only [Triangle.angle_reindex]
        change T.angle 0 = 2 * S.angle 1
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 1 = S.angle 0
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 2 = S.angle 1 + S.angle 0
        linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    left
    refine ⟨Equiv.swap 0 1, ?_⟩
    intro i
    fin_cases i
    · change T.angle 0 = S.angle 1
      linarith
    · change T.angle 1 = S.angle 0
      linarith
    · change T.angle 2 = S.angle 2
      linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    left
    refine ⟨Equiv.swap 0 1, ?_⟩
    intro i
    fin_cases i
    · change T.angle 0 = S.angle 1
      linarith
    · change T.angle 1 = S.angle 0
      linarith
    · change T.angle 2 = S.angle 2
      linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    right
    refine ⟨Equiv.refl _, ((Equiv.swap 0 1).trans (Equiv.swap 1 2)).symm, ?_⟩
    left
    refine ⟨?_, ?_⟩
    · simp only [Triangle.angle_reindex]
      change 3 * S.angle 0 + 2 * S.angle 1 = Real.pi
      linarith
    · refine Or.inr (⟨?_, ?_, ?_⟩)
      · simp only [Triangle.angle_reindex]
        change T.angle 2 = 2 * S.angle 0
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 0 = S.angle 1
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 1 = S.angle 0 + S.angle 1
        linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    right
    refine ⟨Equiv.refl _, ((Equiv.swap 0 1).trans (Equiv.swap 0 2)).symm, ?_⟩
    left
    refine ⟨?_, ?_⟩
    · simp only [Triangle.angle_reindex]
      change 3 * S.angle 0 + 2 * S.angle 1 = Real.pi
      linarith
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · simp only [Triangle.angle_reindex]
        change T.angle 1 = S.angle 0
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 2 = 2 * S.angle 0
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 0 = 2 * S.angle 1
        linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    right
    refine ⟨Equiv.swap 0 1, (Equiv.refl _).symm, ?_⟩
    right
    refine ⟨?_, ?_⟩
    · simp only [Triangle.angle_reindex]
      change S.angle 2 = 2 * Real.pi / 3
      linarith
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · simp only [Triangle.angle_reindex]
        change T.angle 0 = S.angle 1
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 1 = 2 * S.angle 1
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 2 = 3 * S.angle 0
        linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    left
    refine ⟨Equiv.swap 0 1, ?_⟩
    intro i
    fin_cases i
    · change T.angle 0 = S.angle 1
      linarith
    · change T.angle 1 = S.angle 0
      linarith
    · change T.angle 2 = S.angle 2
      linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    right
    refine ⟨Equiv.swap 0 1, (Equiv.refl _).symm, ?_⟩
    right
    refine ⟨?_, ?_⟩
    · simp only [Triangle.angle_reindex]
      change S.angle 2 = 2 * Real.pi / 3
      linarith
    · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))
      · simp only [Triangle.angle_reindex]
        change T.angle 0 = S.angle 1
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 1 = S.angle 1 + S.angle 0
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 2 = S.angle 1 + 2 * S.angle 0
        linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    right
    refine ⟨Equiv.swap 0 1, (Equiv.swap 1 2).symm, ?_⟩
    right
    refine ⟨?_, ?_⟩
    · simp only [Triangle.angle_reindex]
      change S.angle 2 = 2 * Real.pi / 3
      linarith
    · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
      · simp only [Triangle.angle_reindex]
        change T.angle 0 = S.angle 1
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 2 = 2 * S.angle 0
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 1 = 2 * S.angle 1 + S.angle 0
        linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    right
    refine ⟨Equiv.refl _, (Equiv.swap 0 1).symm, ?_⟩
    right
    refine ⟨?_, ?_⟩
    · simp only [Triangle.angle_reindex]
      change S.angle 2 = 2 * Real.pi / 3
      linarith
    · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
      · simp only [Triangle.angle_reindex]
        change T.angle 1 = S.angle 0
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 0 = 2 * S.angle 1
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 2 = 2 * S.angle 0 + S.angle 1
        linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    right
    refine ⟨Equiv.refl _, ((Equiv.swap 0 1).trans (Equiv.swap 1 2)).symm, ?_⟩
    right
    refine ⟨?_, ?_⟩
    · simp only [Triangle.angle_reindex]
      change S.angle 2 = 2 * Real.pi / 3
      linarith
    · refine Or.inr (Or.inr (Or.inr (⟨?_, ?_, ?_⟩)))
      · simp only [Triangle.angle_reindex]
        change T.angle 2 = 2 * S.angle 0
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 0 = 2 * S.angle 1
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 1 = S.angle 0 + S.angle 1
        linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    right
    refine ⟨Equiv.refl _, ((Equiv.swap 0 1).trans (Equiv.swap 0 2)).symm, ?_⟩
    right
    refine ⟨?_, ?_⟩
    · simp only [Triangle.angle_reindex]
      change S.angle 2 = 2 * Real.pi / 3
      linarith
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · simp only [Triangle.angle_reindex]
        change T.angle 1 = S.angle 0
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 2 = 2 * S.angle 0
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 0 = 3 * S.angle 1
        linarith
  · rcases h with ⟨rfl, rfl, rfl⟩
    norm_num at h₀ h₁ h₂
    right
    refine ⟨Equiv.refl _, (Equiv.refl _).symm, ?_⟩
    right
    refine ⟨?_, ?_⟩
    · simp only [Triangle.angle_reindex]
      change S.angle 2 = 2 * Real.pi / 3
      linarith
    · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))
      · simp only [Triangle.angle_reindex]
        change T.angle 0 = S.angle 0
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 1 = S.angle 0 + S.angle 1
        linarith
      · simp only [Triangle.angle_reindex]
        change T.angle 2 = S.angle 0 + 2 * S.angle 1
        linarith

end Erdos633b
