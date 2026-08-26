/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The recursive slice operation on an active coordinate set.
Informal source: BBMST Lemma 3.4(a) and the exploration-tree induction.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.GridProjection

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]

lemma MinimalCoverOn.projected_slices {H : α → Box q} {A : Finset α} {I : Finset ι}
    (hA : MinimalCoverOn (fun a => project I (H a)) A Set.univ)
    (hI : familyFixed (fun a => project I (H a)) A = I) {i : ι} (hi : i ∈ I) :
    ∃ B : Fin (q i) → Finset α, ∃ J : Fin (q i) → Finset ι,
      (∀ s, B s ⊆ A ∧ J s ⊆ I.erase i ∧
        MinimalCoverOn (fun a => project (J s) (H a)) (B s) Set.univ ∧
        familyFixed (fun a => project (J s) (H a)) (B s) = J s ∧
        (∀ a ∈ B s, Compatible (H a) i s) ∧
        familyFixed H (B s) ⊆ (familyFixed H A \ I) ∪ insert i (J s)) ∧
      univ.biUnion J = I.erase i := by
  classical
  obtain ⟨B, hB, hUnion⟩ := hA.exists_exploration_slices i
  let J := fun s => familyFixed (fun a => project (I.erase i) (H a)) (B s)
  have hdrop : (fun a => drop i (project I (H a))) = (fun a => project (I.erase i) (H a)) := by
    funext a
    exact project_drop I (H a) i
  rw [hdrop] at hB hUnion
  refine ⟨B, J, ?_, ?_⟩
  · intro s
    have hJs : J s ⊆ I.erase i := by
      dsimp only [J]
      rw [familyFixed_project]
      exact inter_subset_right
    have heq : ∀ a ∈ B s, project (I.erase i) (H a) = project (J s) (H a) :=
      fun a ha => (project_projected_familyFixed_member (I.erase i) H ha).symm
    refine ⟨(hB s).1, hJs, (hB s).2.1.congr_boxes heq, ?_, ?_, ?_⟩
    · exact (familyFixed_congr heq).symm
    · intro a ha
      have hc := (hB s).2.2 a ha
      simpa only [Compatible, project_apply_of_mem hi] using hc
    · intro j hj
      by_cases hjI : j ∈ I
      · apply mem_union_right
        by_cases hji : j = i
        · exact mem_insert.mpr (Or.inl hji)
        · apply mem_insert_of_mem
          dsimp only [J]
          rw [familyFixed_project]
          exact mem_inter.mpr ⟨hj, mem_erase.mpr ⟨hji, hjI⟩⟩
      · exact mem_union_left _ (mem_sdiff.mpr
          ⟨familyFixed_mono H (hB s).1 hj, hjI⟩)
  · simpa only [hI] using hUnion

end Erdos1189.Grid
