/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Existence of a finite exploration tree for every minimal finite box cover.
Informal source: BBMST Lemma 3.3, using strict decrease of the active coordinate set.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ExplorationStep

namespace Erdos1189.Grid

universe u v

variable {ι : Type u} {α : Type v} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]

/-- Empty active sets are leaves; every other node carries the proved slice operation. -/
inductive ExplorationTree (H : α → Box q) (lam ε δ : ℝ) :
    Finset α → Finset ι → Type (max u v)
  | leaf (A : Finset α) : ExplorationTree H lam ε δ A ∅
  | node {A : Finset α} {I : Finset ι} (step : ExplorationStep H A I lam ε δ)
      (children : (s : Fin (q step.coordinate)) →
        ExplorationTree H lam ε δ (step.slices s) (step.active s)) :
      ExplorationTree H lam ε δ A I

lemma nonempty_explorationTree_of_steps (H : α → Box q) (lam ε δ : ℝ)
    (hstep : ∀ A I, I.Nonempty →
      MinimalCoverOn (fun a => project I (H a)) A Set.univ →
      familyFixed (fun a => project I (H a)) A = I →
      Nonempty (ExplorationStep H A I lam ε δ)) :
    ∀ I A, MinimalCoverOn (fun a => project I (H a)) A Set.univ →
      familyFixed (fun a => project I (H a)) A = I →
      Nonempty (ExplorationTree H lam ε δ A I) := by
  classical
  intro I
  induction I using Finset.strongInduction with
  | H I ih =>
    intro A hA hI
    by_cases hEmpty : I = ∅
    · subst I
      exact ⟨ExplorationTree.leaf A⟩
    · obtain ⟨step⟩ := hstep A I (Finset.nonempty_iff_ne_empty.mpr hEmpty) hA hI
      have hchildren : ∀ s, Nonempty
          (ExplorationTree H lam ε δ (step.slices s) (step.active s)) := by
        intro s
        have hproper : step.active s ⊂ I := Finset.ssubset_iff_subset_ne.mpr
          ⟨(step.active_subset s).trans (Finset.erase_subset _ _), fun heq => by
            have hlt := step.active_card_lt s
            rw [heq] at hlt
            exact Nat.lt_irrefl _ hlt⟩
        exact ih (step.active s) hproper (step.slices s) (step.minimal s) (step.fixed_eq s)
      exact ⟨ExplorationTree.node step (fun s => Classical.choice (hchildren s))⟩

end Erdos1189.Grid

namespace Erdos1189

/-- Uniform exploration trees, with no assumed local lemma or structural theorem. -/
theorem exists_uniform_exploration_trees {lam ε : ℝ}
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (ι α : Type) [Fintype ι] [DecidableEq ι] (q : ι → ℕ)
        (H : α → Grid.Box q) (A : Finset α) (I : Finset ι),
        (∀ i, 2 ≤ q i) →
        Grid.MinimalCoverOn (fun a => Grid.project I (H a)) A Set.univ →
        Grid.familyFixed (fun a => Grid.project I (H a)) A = I →
        Nonempty (Grid.ExplorationTree H lam ε δ A I) := by
  obtain ⟨δ, hδ, hδ1, hstep⟩ := exists_uniform_exploration_steps hlam hε hε1
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro ι α _ _ q H A I hq hA hI
  exact Grid.nonempty_explorationTree_of_steps H lam ε δ
    (fun A I hINe hA hI => hstep ι α q H A I hq hINe hA hI) I A hA hI

end Erdos1189
