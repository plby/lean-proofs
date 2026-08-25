import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Counting paired occurrences of two kinds

For a finite fixed-point-free involution, suppose no orbit contains two
exterior occurrences.  Each orbit then contributes either two internal
occurrences or one occurrence of each kind.
-/

namespace Puzzling139335

/-- Count the internal occurrences by separating wholly internal pairs
from the pairs containing one exterior occurrence. -/
theorem colored_pair_card_with_internal_count {α : Type*} (s : Finset α)
    (τ : α → α) (E : α → Prop) [DecidablePred E]
    (hmap : ∀ a ∈ s, τ a ∈ s)
    (hinv : ∀ a ∈ s, τ (τ a) = a)
    (hfree : ∀ a ∈ s, τ a ≠ a)
    (hexterior : ∀ a ∈ s, E a → ¬ E (τ a)) :
    ∃ k : ℕ,
      (s.filter fun a => ¬ E a ∧ ¬ E (τ a)).card = 2 * k ∧
      (s.filter fun a => ¬ E a).card = 2 * k + (s.filter E).card := by
  classical
  revert hmap hinv hfree hexterior
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro hmap hinv hfree hexterior
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨0, by simp, by simp⟩
    let b := τ a
    have hb : b ∈ s := hmap a ha
    have hba : b ≠ a := hfree a ha
    have hτa : τ a = b := rfl
    have hτb : τ b = a := hinv a ha
    let u := (s.erase a).erase b
    have hmem (x : α) : x ∈ u ↔ x ≠ b ∧ x ≠ a ∧ x ∈ s := by
      simp only [u, Finset.mem_erase]
    have hua : a ∉ u := by simp [u]
    have hub : b ∉ u := by simp [u]
    have hus : u ⊆ s := fun x hx => ((hmem x).mp hx).2.2
    have huss : u ⊂ s := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hus, ?_⟩
      intro h
      exact (h ▸ hua) ha
    have hmapu : ∀ x ∈ u, τ x ∈ u := by
      intro x hx
      obtain ⟨hxb, hxa, hxs⟩ := (hmem x).mp hx
      apply (hmem (τ x)).mpr
      refine ⟨?_, ?_, hmap x hxs⟩
      · intro h
        apply hxa
        calc
          x = τ (τ x) := (hinv x hxs).symm
          _ = τ b := congrArg τ h
          _ = a := hτb
      · intro h
        apply hxb
        calc
          x = τ (τ x) := (hinv x hxs).symm
          _ = τ a := congrArg τ h
          _ = b := hτa
    obtain ⟨k, hkII, hk⟩ := ih u huss hmapu
      (fun x hx => hinv x (hus hx))
      (fun x hx => hfree x (hus hx))
      (fun x hx => hexterior x (hus hx))
    have heq : s = insert a (insert b u) := by
      dsimp only [u]
      rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨hba, hb⟩),
        Finset.insert_erase ha]
    have hcard (P : α → Prop) [DecidablePred P] :
        (s.filter P).card = (u.filter P).card +
          (if P b then 1 else 0) + (if P a then 1 else 0) := by
      rw [heq]
      by_cases hPa : P a <;> by_cases hPb : P b <;>
        simp [Finset.filter_insert, hPa, hPb, hua, hub, hba.symm]
    have hII := hcard (fun x => ¬ E x ∧ ¬ E (τ x))
    have hI := hcard (fun x => ¬ E x)
    have hE := hcard E
    by_cases hEa : E a
    · have hEb : ¬ E b := hexterior a ha hEa
      simp [hτa, hτb, hEa, hEb] at hII hI hE
      exact ⟨k, by omega, by omega⟩
    · by_cases hEb : E b
      · simp [hτa, hτb, hEa, hEb] at hII hI hE
        exact ⟨k, by omega, by omega⟩
      · simp [hτa, hτb, hEa, hEb] at hII hI hE
        exact ⟨k + 1, by omega, by omega⟩

/-- The number of internal occurrences is twice a number of internal
pairs, plus the number of exterior occurrences. -/
theorem colored_pair_card {α : Type*} (s : Finset α)
    (τ : α → α) (E : α → Prop) [DecidablePred E]
    (hmap : ∀ a ∈ s, τ a ∈ s)
    (hinv : ∀ a ∈ s, τ (τ a) = a)
    (hfree : ∀ a ∈ s, τ a ≠ a)
    (hexterior : ∀ a ∈ s, E a → ¬ E (τ a)) :
    ∃ k : ℕ, (s.filter fun a => ¬ E a).card = 2 * k + (s.filter E).card := by
  obtain ⟨k, -, hk⟩ := colored_pair_card_with_internal_count s τ E
    hmap hinv hfree hexterior
  exact ⟨k, hk⟩

/-- The internal-pair count can be taken to be half the number of
occurrences whose mates are also internal. -/
theorem colored_pair_card_explicit {α : Type*} (s : Finset α)
    (τ : α → α) (E : α → Prop) [DecidablePred E]
    (hmap : ∀ a ∈ s, τ a ∈ s)
    (hinv : ∀ a ∈ s, τ (τ a) = a)
    (hfree : ∀ a ∈ s, τ a ≠ a)
    (hexterior : ∀ a ∈ s, E a → ¬ E (τ a)) :
    (s.filter fun a => ¬ E a).card =
      2 * ((s.filter fun a => ¬ E a ∧ ¬ E (τ a)).card / 2) + (s.filter E).card := by
  obtain ⟨k, hkII, hk⟩ := colored_pair_card_with_internal_count s τ E
    hmap hinv hfree hexterior
  omega

end Puzzling139335
