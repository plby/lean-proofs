/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Exact independence identities for events depending on separate product factors.
Informal argument: such events are rectangles, so their cardinalities multiply.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FiniteLocalLemma
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Prod

namespace Erdos1189

open Finset

lemma product_event_card_independent {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (S T : Finset (β × γ))
    (hS : ∀ b c c', (b, c) ∈ S ↔ (b, c') ∈ S)
    (hT : ∀ b b' c, (b, c) ∈ T ↔ (b', c) ∈ T) :
    (S ∩ T).card * Fintype.card (β × γ) = S.card * T.card := by
  have hSrect : S = S.image Prod.fst ×ˢ (univ : Finset γ) := by
    ext ⟨b, c⟩
    simp only [mem_product, mem_univ, and_true]
    constructor
    · intro h
      exact mem_image.mpr ⟨(b, c), h, rfl⟩
    · intro h
      obtain ⟨⟨b', c'⟩, hmem, heq⟩ := mem_image.mp h
      dsimp only at heq
      subst b'
      exact (hS b c' c).mp hmem
  have hTrect : T = (univ : Finset β) ×ˢ T.image Prod.snd := by
    ext ⟨b, c⟩
    simp only [mem_product, mem_univ, true_and]
    constructor
    · intro h
      exact mem_image.mpr ⟨(b, c), h, rfl⟩
    · intro h
      obtain ⟨⟨b', c'⟩, hmem, heq⟩ := mem_image.mp h
      dsimp only at heq
      subst c'
      exact (hT b' b c).mp hmem
  have hinter : S ∩ T = S.image Prod.fst ×ˢ T.image Prod.snd := by
    calc
      S ∩ T = (S.image Prod.fst ×ˢ (univ : Finset γ)) ∩
          ((univ : Finset β) ×ˢ T.image Prod.snd) := congrArg₂ (· ∩ ·) hSrect hTrect
      _ = _ := by ext ⟨b, c⟩; simp
  have hScard := congrArg Finset.card hSrect
  have hTcard := congrArg Finset.card hTrect
  simp only [card_product, card_univ] at hScard hTcard
  rw [hinter, card_product, Fintype.card_prod, hScard, hTcard]
  ring

lemma equiv_event_card_independent {Ω β γ : Type*}
    [Fintype Ω] [Finite β] [Finite γ] [DecidableEq Ω]
    (e : Ω ≃ β × γ) (S T : Finset Ω)
    (hS : ∀ u v, (e u).1 = (e v).1 → (u ∈ S ↔ v ∈ S))
    (hT : ∀ u v, (e u).2 = (e v).2 → (u ∈ T ↔ v ∈ T)) :
    (S ∩ T).card * Fintype.card Ω = S.card * T.card := by
  classical
  let : Fintype β := Fintype.ofFinite β
  let : Fintype γ := Fintype.ofFinite γ
  have hmem : ∀ (U : Finset Ω) y, y ∈ U.map e.toEmbedding ↔ e.symm y ∈ U := by
    intro U y
    simp only [mem_map_equiv]
  have h := product_event_card_independent (S.map e.toEmbedding) (T.map e.toEmbedding)
    (fun b c c' => by
      rw [hmem, hmem]
      exact hS _ _ (by simp))
    (fun b b' c => by
      rw [hmem, hmem]
      exact hT _ _ (by simp))
  rw [← map_inter, card_map, card_map, card_map, ← Fintype.card_congr e] at h
  exact h

end Erdos1189
