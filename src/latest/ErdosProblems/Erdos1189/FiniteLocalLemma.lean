/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The asymmetric local lemma for events in a finite uniform probability space.
Informal argument: cardinality identities instantiate the avoidance recurrence.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.LocalLemma

namespace Erdos1189

open Finset

variable {α Ω : Type*} [Fintype Ω]

noncomputable def finiteProbability (S : Finset Ω) : ℝ := S.card / (Fintype.card Ω : ℝ)

lemma finiteProbability_nonneg (S : Finset Ω) : 0 ≤ finiteProbability S := by
  unfold finiteProbability
  positivity

lemma finiteProbability_mono {S T : Finset Ω} (h : S ⊆ T) :
    finiteProbability S ≤ finiteProbability T := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card h) (Nat.cast_nonneg _)

lemma finiteProbability_univ [Nonempty Ω] : finiteProbability (univ : Finset Ω) = 1 := by
  rw [finiteProbability, card_univ, div_self]
  exact_mod_cast Fintype.card_ne_zero

lemma finiteProbability_pos_iff [Nonempty Ω] (S : Finset Ω) :
    0 < finiteProbability S ↔ S.Nonempty := by
  have hc : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [finiteProbability, div_pos_iff_of_pos_right hc, Nat.cast_pos, card_pos]

noncomputable def avoidingEvents (E : α → Finset Ω) (S : Finset α) : Finset Ω := by
  classical
  exact univ.filter fun ω => ∀ a ∈ S, ω ∉ E a

lemma mem_avoidingEvents {E : α → Finset Ω} {S : Finset α} {ω : Ω} :
    ω ∈ avoidingEvents E S ↔ ∀ a ∈ S, ω ∉ E a := by
  classical
  simp [avoidingEvents]

lemma avoidingEvents_empty (E : α → Finset Ω) : avoidingEvents E ∅ = univ := by
  classical
  ext ω
  simp [mem_avoidingEvents]

lemma avoidingEvents_insert [DecidableEq α] [DecidableEq Ω]
    (E : α → Finset Ω) (S : Finset α) (a : α) :
    avoidingEvents E (insert a S) = avoidingEvents E S \ E a := by
  ext ω
  simp only [mem_avoidingEvents, mem_sdiff, mem_insert, forall_eq_or_imp]
  tauto

lemma avoidingEvents_antitone (E : α → Finset Ω) : Antitone (avoidingEvents E) := by
  intro S T hST ω hω
  exact mem_avoidingEvents.mpr fun a ha => mem_avoidingEvents.mp hω a (hST ha)

lemma finiteProbability_avoidance_difference [DecidableEq α] [DecidableEq Ω]
    (E : α → Finset Ω) (S : Finset α) (a : α) :
    finiteProbability (avoidingEvents E S) - finiteProbability (avoidingEvents E (insert a S)) =
      finiteProbability (E a ∩ avoidingEvents E S) := by
  rw [avoidingEvents_insert]
  have hcard := card_sdiff_add_card_inter (avoidingEvents E S) (E a)
  have hreal : ((avoidingEvents E S \ E a).card : ℝ) +
      ((E a ∩ avoidingEvents E S).card : ℝ) = (avoidingEvents E S).card := by
    rw [inter_comm]
    exact_mod_cast hcard
  unfold finiteProbability
  rw [← sub_div]
  congr 1
  linarith

/-- Finite-space local lemma, with independence expressed as the exact cardinality identity. -/
theorem finite_local_lemma [DecidableEq Ω] [Nonempty Ω] (A : Finset α) (N : α → Finset α)
    (E : α → Finset Ω) (x : α → ℝ)
    (hN : ∀ a ∈ A, N a ⊆ A) (hx : ∀ a ∈ A, 0 ≤ x a ∧ x a < 1)
    (hind : ∀ a ∈ A, ∀ T ⊆ A, a ∉ T → Disjoint T (N a) →
      (E a ∩ avoidingEvents E T).card * Fintype.card Ω =
        (E a).card * (avoidingEvents E T).card)
    (hprob : ∀ a ∈ A, finiteProbability (E a) ≤ x a * ∏ b ∈ N a, (1 - x b)) :
    ∃ ω : Ω, ∀ a ∈ A, ω ∉ E a := by
  classical
  have hpos := localLemma_avoidance_positive A N
    (fun S => finiteProbability (avoidingEvents E S)) (fun a => finiteProbability (E a)) x
    (by rw [avoidingEvents_empty, finiteProbability_univ]; norm_num)
    (fun S => finiteProbability_nonneg _) hN hx
    (fun a _ S _ T hTS => by
      rw [finiteProbability_avoidance_difference, finiteProbability_avoidance_difference]
      exact finiteProbability_mono (inter_subset_inter_left ((avoidingEvents_antitone E) hTS)))
    (fun a ha T hTA haT hdisj => by
      rw [finiteProbability_avoidance_difference]
      apply le_of_eq
      have hcard : ((E a ∩ avoidingEvents E T).card : ℝ) * Fintype.card Ω =
          (E a).card * (avoidingEvents E T).card := by
        exact_mod_cast hind a ha T hTA haT hdisj
      have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      unfold finiteProbability
      field_simp
      exact hcard)
    hprob
  obtain ⟨ω, hω⟩ := (finiteProbability_pos_iff _).mp hpos
  exact ⟨ω, mem_avoidingEvents.mp hω⟩

end Erdos1189
