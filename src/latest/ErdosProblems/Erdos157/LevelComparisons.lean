import ErdosProblems.Erdos157.BlockTraces

/-! Both the larger and the smaller levels of an equal pair sum are close. -/

namespace Erdos157.Elementary

open AuxiliaryModuli PolynomialCharacters

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

theorem shorter_level_le_add_three (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K) (h₁₂ : f₂.level ≤ f₁.level)
    (hmax : f₁.level ≤ f₃.level + 1)
    (heq : encoded K τ ω f₁ + encoded K τ ω f₂ = encoded K τ ω f₃ + encoded K τ ω f₄) :
    f₂.level ≤ f₄.level + 3 := by
  by_contra h
  let i := f₄.level + 2
  have hi₁ : i < f₁.level := by dsimp only [i]; omega
  have hi₂ : i < f₂.level := by dsimp only [i]; omega
  have hi₃ : i < f₃.level := by dsimp only [i]; omega
  have htrace := congrArg (fun n => blockTrace K n i) heq
  rw [blockTrace_pair K τ ω f₁ f₂ i hi₁ hi₂,
    blockTrace_long_short K τ ω f₃ f₄ i hi₃ (by exact le_rfl)] at htrace
  exact block_encode_ne_pair_encode K i (τ i) (labelResidue K f₃ i)
    (labelResidue K f₁ i) (labelResidue K f₂ i) (ω.block f₃ i) (ω.block f₁ i) (ω.block f₂ i)
    htrace.symm

theorem shorter_levels_close_of_encoded_pair_eq (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K) (h₁₂ : f₂.level ≤ f₁.level) (h₃₄ : f₄.level ≤ f₃.level)
    (heq : encoded K τ ω f₁ + encoded K τ ω f₂ = encoded K τ ω f₃ + encoded K τ ω f₄) :
    f₂.level ≤ f₄.level + 3 ∧ f₄.level ≤ f₂.level + 3 := by
  have hmax := maximal_levels_close_of_encoded_pair_eq K τ ω f₁ f₂ f₃ f₄ h₁₂ h₃₄ heq
  exact ⟨shorter_level_le_add_three K τ ω f₁ f₂ f₃ f₄ h₁₂ hmax.1 heq,
    shorter_level_le_add_three K τ ω f₃ f₄ f₁ f₂ h₃₄ hmax.2 heq.symm⟩

theorem clean_residue_eq_of_encoded_pair_eq (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K) (i : ℕ)
    (hi₁ : i < f₁.level) (hi₃ : i < f₃.level)
    (hi₂ : f₂.level + 2 ≤ i) (hi₄ : f₄.level + 2 ≤ i)
    (heq : encoded K τ ω f₁ + encoded K τ ω f₂ = encoded K τ ω f₃ + encoded K τ ω f₄) :
    labelResidue K f₁ i = labelResidue K f₃ i := by
  have htrace := congrArg (fun n => blockTrace K n i) heq
  rw [blockTrace_long_short K τ ω f₁ f₂ i hi₁ hi₂,
    blockTrace_long_short K τ ω f₃ f₄ i hi₃ hi₄] at htrace
  exact block_residue_eq_of_encode_eq K i (τ i) _ _ _ _ htrace

end Erdos157.Elementary
