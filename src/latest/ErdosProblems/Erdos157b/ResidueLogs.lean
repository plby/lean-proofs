import ErdosProblems.Erdos157.ResidueLogs
import ErdosProblems.Erdos157b.TagFields

namespace Erdos157.Binary

open Erdos157.Elementary AuxiliaryModuli

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

noncomputable def maskedLog (i : ℕ) (τ : TagField i → LogDigit K i)
    (t : TagField i) (u : (ResidueField K i)ˣ) : LogDigit K i := CyclicLog.log u + τ t

/-- The two tag moments determine the masks in a pair sum. Hence equality
of the masked logarithm sums recovers the product residue. -/
theorem maskedLog_pair_decoding (i : ℕ) (τ : TagField i → LogDigit K i)
    (t₁ t₂ t₃ t₄ : TagField i) (u₁ u₂ u₃ u₄ : (ResidueField K i)ˣ)
    (htag : ∀ j, tagCoordinates i t₁ j + tagCoordinates i t₂ j =
      tagCoordinates i t₃ j + tagCoordinates i t₄ j)
    (hsquare : ∀ j, tagCoordinates i (t₁ ^ 2) j + tagCoordinates i (t₂ ^ 2) j =
      tagCoordinates i (t₃ ^ 2) j + tagCoordinates i (t₄ ^ 2) j)
    (hlog : maskedLog K i τ t₁ u₁ + maskedLog K i τ t₂ u₂ =
      maskedLog K i τ t₃ u₃ + maskedLog K i τ t₄ u₄) : u₁ * u₂ = u₃ * u₄ := by
  have hmask : τ t₁ + τ t₂ = τ t₃ + τ t₄ := by
    rcases tag_pair_decoding i t₁ t₂ t₃ t₄ htag hsquare with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact add_comm _ _
  apply CyclicLog.log_injective
  rw [CyclicLog.log_mul, CyclicLog.log_mul]
  dsimp only [maskedLog] at hlog
  linear_combination hlog - hmask

end Erdos157.Binary
