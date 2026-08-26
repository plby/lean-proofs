import ErdosProblems.Erdos157b.CleanModuli
import ErdosProblems.Erdos157b.PairCoincidences
import ErdosProblems.Erdos157.SidonDegreeBounds

/-! The tagged integer encoding is Sidon for every choice of masks, tags, and digits. -/

namespace Erdos157.Binary

open Erdos157.Elementary

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

theorem encoded_pair_unique_ordered (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K) (h₁₂ : f₂.level ≤ f₁.level) (h₃₄ : f₄.level ≤ f₃.level)
    (heq : encoded K τ ω f₁ + encoded K τ ω f₂ = encoded K τ ω f₃ + encoded K τ ω f₄) :
    (encoded K τ ω f₁ = encoded K τ ω f₃ ∧ encoded K τ ω f₂ = encoded K τ ω f₄) ∨
      (encoded K τ ω f₁ = encoded K τ ω f₄ ∧ encoded K τ ω f₂ = encoded K τ ω f₃) := by
  by_contra hne
  have hlabels : ¬((f₁ = f₃ ∧ f₂ = f₄) ∨ (f₁ = f₄ ∧ f₂ = f₃)) := by
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact hne (by simp)
  have hsingle : f₁ ≠ f₃ := by
    intro h
    subst f₃
    exact hne (Or.inl ⟨rfl, Nat.add_left_cancel heq⟩)
  have hmax := maximal_levels_close_of_encoded_pair_eq K τ ω f₁ f₂ f₃ f₄ h₁₂ h₃₄ heq
  have hshort := shorter_levels_close_of_encoded_pair_eq K τ ω f₁ f₂ f₃ f₄ h₁₂ h₃₄ heq
  have hprod := common_modulus_degree_le_of_nontrivial_pair K τ ω f₁ f₂ f₃ f₄
    (min f₂.level f₄.level) (by omega) (Nat.min_le_left _ _) (by omega) (Nat.min_le_right _ _) hlabels heq
  have hclean := clean_segment_degree_le_of_distinct K τ ω f₁ f₂ f₃ f₄ hsingle heq
  rw [segmentProduct_natDegree] at hclean
  exact four_level_degree_contradiction f₁.level f₂.level f₃.level f₄.level
    f₁.level_ge f₂.level_ge f₃.level_ge f₄.level_ge h₁₂ hmax.1 hmax.2 hshort.1 hshort.2 hprod hclean

theorem encoded_pair_unique (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K)
    (heq : encoded K τ ω f₁ + encoded K τ ω f₂ = encoded K τ ω f₃ + encoded K τ ω f₄) :
    (encoded K τ ω f₁ = encoded K τ ω f₃ ∧ encoded K τ ω f₂ = encoded K τ ω f₄) ∨
      (encoded K τ ω f₁ = encoded K τ ω f₄ ∧ encoded K τ ω f₂ = encoded K τ ω f₃) := by
  rcases le_total f₂.level f₁.level with h₁₂ | h₂₁
  · rcases le_total f₄.level f₃.level with h₃₄ | h₄₃
    · exact encoded_pair_unique_ordered K τ ω f₁ f₂ f₃ f₄ h₁₂ h₃₄ heq
    · have h := encoded_pair_unique_ordered K τ ω f₁ f₂ f₄ f₃ h₁₂ h₄₃ (by omega)
      tauto
  · rcases le_total f₄.level f₃.level with h₃₄ | h₄₃
    · have h := encoded_pair_unique_ordered K τ ω f₂ f₁ f₃ f₄ h₂₁ h₃₄ (by omega)
      tauto
    · have h := encoded_pair_unique_ordered K τ ω f₂ f₁ f₄ f₃ h₂₁ h₄₃ (by omega)
      tauto

noncomputable def encodedSet (τ : MaskChoice K) (ω : IntegerParameters K) : Set ℕ :=
  Set.range (encoded K τ ω)

/-- No probability or distribution hypothesis is needed for the Sidon property. -/
theorem encodedSet_isSidon (τ : MaskChoice K) (ω : IntegerParameters K) : IsSidon (encodedSet K τ ω) := by
  intro a b c d ha hb hc hd heq
  obtain ⟨f₁, rfl⟩ := ha
  obtain ⟨f₂, rfl⟩ := hb
  obtain ⟨f₃, rfl⟩ := hc
  obtain ⟨f₄, rfl⟩ := hd
  exact encoded_pair_unique K τ ω f₁ f₂ f₃ f₄ heq

end Erdos157.Binary
