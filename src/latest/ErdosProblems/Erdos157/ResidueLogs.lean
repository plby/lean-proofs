import ErdosProblems.Erdos157.QuotientPrefixes
import ErdosProblems.Erdos157.TagFields
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Discrete logarithms and cancellation of the tag-dependent masks. -/

namespace Erdos157.Elementary

namespace CyclicLog

variable {G : Type*} [Group G] [IsCyclic G]

noncomputable def log (u : G) : ZMod (Nat.card G) :=
  Multiplicative.toAdd ((zmodCyclicMulEquiv (G := G) inferInstance).symm u)

noncomputable def ofLog (a : ZMod (Nat.card G)) : G :=
  zmodCyclicMulEquiv (G := G) inferInstance (Multiplicative.ofAdd a)

theorem log_mul (u v : G) : log (u * v) = log u + log v := by
  change Multiplicative.toAdd ((zmodCyclicMulEquiv (G := G) inferInstance).symm (u * v)) = _
  rw [map_mul]
  rfl

theorem log_injective : Function.Injective (log (G := G)) := by
  intro u v h
  apply (zmodCyclicMulEquiv (G := G) inferInstance).symm.injective
  exact h

theorem log_ofLog (a : ZMod (Nat.card G)) : log (ofLog (G := G) a) = a := by
  simp only [log, ofLog, MulEquiv.symm_apply_apply]
  rfl

theorem ofLog_log (u : G) : ofLog (log u) = u := by
  change (zmodCyclicMulEquiv (G := G) inferInstance)
    ((zmodCyclicMulEquiv (G := G) inferInstance).symm u) = u
  exact MulEquiv.apply_symm_apply _ _

noncomputable def equiv : G ≃ ZMod (Nat.card G) where
  toFun := log
  invFun := ofLog
  left_inv := ofLog_log
  right_inv := log_ofLog

end CyclicLog

open AuxiliaryModuli

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

abbrev LogDigit (i : ℕ) := ZMod (Nat.card (ResidueField K i)ˣ)

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

end Erdos157.Elementary
