/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
One fully justified recursive step in the exploration of a minimal cover.
Informal source: BBMST Lemma 3.3 and its induction step.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ProjectedSlices

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]

structure ExplorationStep (H : α → Box q) (A : Finset α) (I : Finset ι) (lam ε δ : ℝ) where
  coordinate : ι
  coordinate_mem : coordinate ∈ I
  alternative : CoordinateAlternativeAt (fun a => project I (H a)) A lam ε δ coordinate
  slices : Fin (q coordinate) → Finset α
  active : Fin (q coordinate) → Finset ι
  slice_subset : ∀ s, slices s ⊆ A
  active_subset : ∀ s, active s ⊆ I.erase coordinate
  active_card_lt : ∀ s, (active s).card < I.card
  minimal : ∀ s, MinimalCoverOn (fun a => project (active s) (H a)) (slices s) Set.univ
  fixed_eq : ∀ s, familyFixed (fun a => project (active s) (H a)) (slices s) = active s
  compatible : ∀ s, ∀ a ∈ slices s, Compatible (H a) coordinate s
  original_fixed_subset : ∀ s, familyFixed H (slices s) ⊆
    (familyFixed H A \ I) ∪ insert coordinate (active s)
  active_union : univ.biUnion active = I.erase coordinate

lemma nonempty_explorationStep_of_alternative {H : α → Box q} {A : Finset α} {I : Finset ι}
    {lam ε δ : ℝ} (hlam : 0 < lam) (hε : ε < 1) (hq : ∀ i, 2 ≤ q i)
    (hA : MinimalCoverOn (fun a => project I (H a)) A Set.univ)
    (hI : familyFixed (fun a => project I (H a)) A = I)
    (hAlt : CoordinateAlternative (fun a => project I (H a)) A lam ε δ) :
    Nonempty (ExplorationStep H A I lam ε δ) := by
  obtain ⟨i, hiAlt⟩ := hAlt
  have hi : i ∈ I := hI ▸ hiAlt.mem_familyFixed hlam hε (hq i)
  obtain ⟨B, J, hB, hUnion⟩ := hA.projected_slices hI hi
  exact ⟨{
    coordinate := i
    coordinate_mem := hi
    alternative := hiAlt
    slices := B
    active := J
    slice_subset := fun s => (hB s).1
    active_subset := fun s => (hB s).2.1
    active_card_lt := fun s => (card_le_card (hB s).2.1).trans_lt (card_erase_lt_of_mem hi)
    minimal := fun s => (hB s).2.2.1
    fixed_eq := fun s => (hB s).2.2.2.1
    compatible := fun s => (hB s).2.2.2.2.1
    original_fixed_subset := fun s => (hB s).2.2.2.2.2
    active_union := hUnion }⟩

end Erdos1189.Grid

namespace Erdos1189

/-- The same cutoff works at every recursive stage, regardless of the active grid. -/
theorem exists_uniform_exploration_steps {lam ε : ℝ}
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (ι α : Type) [Fintype ι] [DecidableEq ι] (q : ι → ℕ)
        (H : α → Grid.Box q) (A : Finset α) (I : Finset ι),
        (∀ i, 2 ≤ q i) → I.Nonempty →
        Grid.MinimalCoverOn (fun a => Grid.project I (H a)) A Set.univ →
        Grid.familyFixed (fun a => Grid.project I (H a)) A = I →
        Nonempty (Grid.ExplorationStep H A I lam ε δ) := by
  obtain ⟨δ, hδ, hδ1, hAlt⟩ := exists_uniform_coordinate_dichotomy hlam hε hε1.le
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro ι α _ _ q H A I hq hINe hA hI
  have hfixed := hA.fixed_nonempty (hI.symm ▸ hINe)
  exact Grid.nonempty_explorationStep_of_alternative hlam hε1 hq hA hI
    (hAlt ι α q (fun a => Grid.project I (H a)) A hq hfixed hA.1)

end Erdos1189
