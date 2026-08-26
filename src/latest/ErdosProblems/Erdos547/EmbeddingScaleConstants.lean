import ErdosProblems.Erdos547.ReservoirNumbers

/-!
# Shrub size chosen after the regularity bound
-/

namespace Erdos547

namespace EmbeddingConstants

variable {a : ℝ} (k : EmbeddingConstants a)

noncomputable def errorFraction : ℝ := k.slack * k.theta * k.treeEta / 100

theorem errorFraction_pos : 0 < k.errorFraction := by
  unfold errorFraction
  exact div_pos (mul_pos (mul_pos k.slack_pos k.theta_pos) k.treeEta_pos) (by norm_num)

theorem exists_shrub_fraction (B : ℝ) (hB : 0 < B) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ k.treeEta ∧ 16 * ρ * B ≤ k.epsilon ∧
      1024 * ρ * B ^ 2 ≤ k.slack ^ 2 * k.treeEta * k.theta ∧
      256 * ρ * B ^ 2 < k.errorFraction ^ 2 := by
  let x := min k.treeEta (min (k.epsilon / (16 * B))
    (min (k.slack ^ 2 * k.treeEta * k.theta / (1024 * B ^ 2))
      (k.errorFraction ^ 2 / (256 * B ^ 2))))
  have hx : 0 < x := by
    dsimp only [x]
    have hε := k.epsilon_pos
    have hs := k.slack_pos
    have hη := k.treeEta_pos
    have hθ := k.theta_pos
    have herr := k.errorFraction_pos
    positivity
  have hη : x ≤ k.treeEta := min_le_left _ _
  have hε : x ≤ k.epsilon / (16 * B) := (min_le_right _ _).trans (min_le_left _ _)
  have htarget : x ≤ k.slack ^ 2 * k.treeEta * k.theta / (1024 * B ^ 2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have herr : x ≤ k.errorFraction ^ 2 / (256 * B ^ 2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨x / 2, by positivity, (by linarith only [hx, hη]), ?_, ?_, ?_⟩
  · have hh := (le_div_iff₀ (show 0 < 16 * B by positivity)).mp hε
    have hp := mul_pos hx hB
    nlinarith only [hh, hp]
  · have hh := (le_div_iff₀ (show 0 < 1024 * B ^ 2 by positivity)).mp htarget
    have hp := mul_pos hx (sq_pos_of_pos hB)
    nlinarith only [hh, hp]
  · have hh := (le_div_iff₀ (show 0 < 256 * B ^ 2 by positivity)).mp herr
    have hp := mul_pos hx (sq_pos_of_pos hB)
    nlinarith only [hh, hp]

end EmbeddingConstants

end Erdos547

#print axioms Erdos547.EmbeddingConstants.exists_shrub_fraction
