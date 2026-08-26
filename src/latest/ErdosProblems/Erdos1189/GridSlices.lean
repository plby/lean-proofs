/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Minimal slices and the coordinate-union identity for exploration trees.
Informal source: BBMST Lemma 3.7 and the construction preceding it.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.Grid

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ}

/-- Arbitrary minimal subcovers of all slices together retain every original member. -/
lemma MinimalCoverOn.slice_union [DecidableEq α] {H : α → Box q} {A : Finset α} {i : ι}
    (hA : MinimalCoverOn H A Set.univ) (B : Fin (q i) → Finset α)
    (hBA : ∀ s, B s ⊆ A) (hB : ∀ s, CoversOn H (B s) {x | x i = s}) :
    univ.biUnion B = A := by
  classical
  apply subset_antisymm
  · intro a ha
    obtain ⟨s, _, ha⟩ := mem_biUnion.mp ha
    exact hBA s ha
  · intro a ha
    obtain ⟨x, _, _, hprivate⟩ := hA.private_witness ha
    obtain ⟨b, hb, hbx⟩ := hB (x i) x rfl
    have hba : b = a := by
      by_contra hne
      exact hprivate b (hBA (x i) hb) hne hbx
    exact mem_biUnion.mpr ⟨x i, mem_univ _, hba ▸ hb⟩

lemma MinimalCoverOn.exists_minimal_slices [DecidableEq α] {H : α → Box q} {A : Finset α}
    (hA : MinimalCoverOn H A Set.univ) (i : ι) :
    ∃ B : Fin (q i) → Finset α,
      (∀ s, B s ⊆ A ∧ MinimalCoverOn H (B s) {x | x i = s}) ∧ univ.biUnion B = A := by
  classical
  have hex : ∀ s : Fin (q i), ∃ B ⊆ A, MinimalCoverOn H B {x | x i = s} := by
    intro s
    have hslice : CoversOn H A {x | x i = s} := fun x _ => hA.1 x (Set.mem_univ _)
    exact hslice.exists_minimal_subcover
  choose B hBA hB using hex
  exact ⟨B, fun s => ⟨hBA s, hB s⟩,
    hA.slice_union B hBA (fun s => (hB s).1)⟩

lemma familyFixed_biUnion [Fintype ι] [DecidableEq ι] [DecidableEq α]
    {σ : Type*} (H : α → Box q) (S : Finset σ) (B : σ → Finset α) :
    familyFixed H (S.biUnion B) = S.biUnion (fun s => familyFixed H (B s)) := by
  ext i
  simp only [mem_familyFixed, mem_biUnion]
  aesop

/-- The successor fixed-coordinate sets cover all coordinates except the explored one. -/
lemma MinimalCoverOn.exists_exploration_slices [Fintype ι] [DecidableEq ι]
    {H : α → Box q} {A : Finset α} (hA : MinimalCoverOn H A Set.univ) (i : ι) :
    ∃ B : Fin (q i) → Finset α,
      (∀ s, B s ⊆ A ∧ MinimalCoverOn (fun a => drop i (H a)) (B s) Set.univ ∧
        ∀ a ∈ B s, Compatible (H a) i s) ∧
      univ.biUnion (fun s => familyFixed (fun a => drop i (H a)) (B s)) =
        (familyFixed H A).erase i := by
  classical
  obtain ⟨B, hB, hUnion⟩ := hA.exists_minimal_slices i
  refine ⟨B, fun s => ⟨(hB s).1, (hB s).2.drop_slice,
    fun a ha => (hB s).2.compatible_slice ha⟩, ?_⟩
  rw [← familyFixed_biUnion, hUnion, familyFixed_drop]

end Erdos1189.Grid
