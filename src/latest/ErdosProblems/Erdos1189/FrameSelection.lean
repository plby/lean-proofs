/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Truncating and selecting the good frame families at first exploration entries.
Informal source: BBMST Lemmas 4.6--4.8.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ExplorationWeights
import ErdosProblems.Erdos1189.ExplorationFrame

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]
variable {H : α → Box q} {lam ε δ : ℝ}

def GoodSelection (e : ExplorationEntry H lam ε δ) (F : Finset α) : Prop :=
  F ⊆ e.family ∧ F.card ≤ q e.label - 1 ∧
    ∀ a ∈ F, e.label ∈ fixed (project e.active (H a)) ∧
      δ < boxMeasureOn (univ.erase e.label) (project e.active (H a))

def BadSelection (e : ExplorationEntry H lam ε δ) (G : Finset α) : Prop :=
  G ⊆ e.family ∧ (q e.label : ℝ) / lam ≤
    ∑ a ∈ G, (5 / 6 : ℝ) ^ (fixed (project e.active (H a))).card ∧
      ∀ a ∈ G, e.label ∈ fixed (project e.active (H a))

lemma ExplorationEntry.exists_selection (e : ExplorationEntry H lam ε δ)
    (hε : 0 ≤ ε) (hq : 1 ≤ q e.label) :
    ∃ F G : Finset α, GoodSelection e F ∧
      ((1 - ε) * ((q e.label : ℝ) - 1) ≤ (F.card : ℝ) ∨ BadSelection e G) := by
  classical
  have hcap : (1 - ε) * ((q e.label : ℝ) - 1) ≤ ((q e.label - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hq, Nat.cast_one]
    have hq' : (1 : ℝ) ≤ q e.label := by exact_mod_cast hq
    nlinarith
  rcases e.step.alternative with ⟨F, hF, hcard, hprops⟩ | ⟨G, hG, hweight, hprops⟩
  · by_cases hsmall : F.card ≤ q e.label - 1
    · exact ⟨F, ∅, ⟨hF, hsmall, hprops⟩, Or.inl hcard⟩
    · obtain ⟨F', hF'F, hF'card⟩ := exists_subset_card_eq (le_of_not_ge hsmall)
      refine ⟨F', ∅, ⟨hF'F.trans hF, hF'card.le, fun a ha => hprops a (hF'F ha)⟩, Or.inl ?_⟩
      simpa only [hF'card] using hcap
  · exact ⟨∅, G, ⟨empty_subset _, by simp, by simp⟩,
      Or.inr ⟨hG, hweight, fun a ha => (hprops a ha).1⟩⟩

lemma ExplorationTree.exists_large_selection {A : Finset α} {I : Finset ι}
    (tree : ExplorationTree H lam ε δ A I) (hlam : 0 < lam) (hε : 0 ≤ ε)
    (hq : ∀ i, 1 ≤ q i) :
    ∃ F : I → Finset α, (∀ i, GoodSelection (tree.firstEntry i) (F i)) ∧
      (1 - ε) * (∑ i : I, ((q i : ℝ) - 1)) - 6 * lam * A.card ≤
        ∑ i : I, ((F i).card : ℝ) := by
  classical
  have hex : ∀ i : I, ∃ F G : Finset α, GoodSelection (tree.firstEntry i) F ∧
      ((1 - ε) * ((q i : ℝ) - 1) ≤ (F.card : ℝ) ∨ BadSelection (tree.firstEntry i) G) := by
    intro i
    simpa only [tree.firstEntry_label] using
      (tree.firstEntry i).exists_selection hε (hq _)
  choose F G hF hAlt using hex
  let B : Finset I := univ.filter fun i => ¬ ((1 - ε) * ((q i : ℝ) - 1) ≤ ((F i).card : ℝ))
  have hB : ∀ i ∈ B, BadSelection (tree.firstEntry i) (G i) :=
    fun i hi => (hAlt i).resolve_left (mem_filter.mp hi).2
  have hbad := tree.bad_coordinate_sum_le B G hlam
    (fun i hi => (hB i hi).1)
    (fun i hi a ha => by simpa only [tree.firstEntry_label] using (hB i hi).2.2 a ha)
    (fun i hi => by simpa only [tree.firstEntry_label] using (hB i hi).2.1)
  have hsum : (1 - ε) * (∑ i : I, ((q i : ℝ) - 1)) ≤
      (∑ i : I, ((F i).card : ℝ)) + ∑ i ∈ B, (q i : ℝ) := by
    have hsumB : (∑ i ∈ B, (q i : ℝ)) = ∑ i : I, if i ∈ B then (q i : ℝ) else 0 := by
      have hf : (univ : Finset I).filter (fun i => i ∈ B) = B := by ext i; simp
      rw [← sum_filter, hf]
    rw [mul_sum, hsumB, ← sum_add_distrib]
    apply sum_le_sum
    intro i _
    by_cases hi : i ∈ B
    · rw [if_pos hi]
      have hq' : (1 : ℝ) ≤ q i := by exact_mod_cast hq i
      have hcard : (0 : ℝ) ≤ (F i).card := by positivity
      nlinarith
    · rw [if_neg hi, add_zero]
      exact not_not.mp (by simpa only [B, mem_filter, mem_univ, true_and] using hi)
  exact ⟨F, hF, by linarith⟩

end Erdos1189.Grid
