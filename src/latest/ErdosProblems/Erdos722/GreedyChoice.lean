/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# A finite greedy compatible-choice lemma

Several stages in the short proof expose the same deterministic core.  Each
root has a finite set of possible extensions; any already chosen extension
forbids at most `M` possibilities for the next root.  If every candidate set
has more than `|roots| M` elements, sequential choice succeeds.  The theorem
below packages that argument without probability or asymptotic notation.
-/

namespace Erdos722.GreedyChoice

open Finset

noncomputable section

variable {R Q : Type*} [DecidableEq R] [DecidableEq Q] [Nonempty Q]

/-- A choice function selects an allowed candidate at every declared root. -/
def ChoosesOn (roots : Finset R) (candidates : R → Finset Q)
    (choice : R → Q) : Prop :=
  ∀ a ∈ roots, choice a ∈ candidates a

/-- Chosen candidates at different roots do not conflict. -/
def PairwiseCompatibleOn (roots : Finset R) (conflict : Q → Q → Prop)
    (choice : R → Q) : Prop :=
  ∀ a ∈ roots, ∀ b ∈ roots, a ≠ b → ¬ conflict (choice a) (choice b)

private lemma card_biUnion_le_mul
    (S : Finset R) (F : R → Finset Q) (M : ℕ)
    (hF : ∀ a ∈ S, (F a).card ≤ M) :
    (S.biUnion F).card ≤ S.card * M := by
  calc
    (S.biUnion F).card ≤ ∑ a ∈ S, (F a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ S, M := by
      apply Finset.sum_le_sum
      intro a ha
      exact hF a ha
    _ = S.card * M := by simp

/-- Finite greedy compatible choice.  The conflict relation is assumed
symmetric because compatibility is an unordered condition. -/
theorem exists_pairwiseCompatible_choice
    (roots : Finset R) (candidates : R → Finset Q)
    (conflict : Q → Q → Prop) [DecidableRel conflict]
    (hsymm : Symmetric conflict) (M : ℕ)
    (hlarge : ∀ a ∈ roots, roots.card * M < (candidates a).card)
    (hconflict : ∀ a ∈ roots, ∀ q : Q,
      ((candidates a).filter fun x ↦ conflict x q).card ≤ M) :
    ∃ choice : R → Q,
      ChoosesOn roots candidates choice ∧
        PairwiseCompatibleOn roots conflict choice := by
  classical
  induction roots using Finset.induction_on with
  | empty =>
      let q₀ : Q := Classical.choice (inferInstance : Nonempty Q)
      exact ⟨fun _ ↦ q₀, by simp [ChoosesOn, PairwiseCompatibleOn]⟩
  | @insert a S ha ih =>
      have hlargeS : ∀ b ∈ S, S.card * M < (candidates b).card := by
        intro b hb
        exact (Nat.mul_le_mul_right M
          (Finset.card_le_card (Finset.subset_insert a S))).trans_lt
            (hlarge b (Finset.mem_insert_of_mem hb))
      have hconflictS : ∀ b ∈ S, ∀ q : Q,
          ((candidates b).filter fun x ↦ conflict x q).card ≤ M := by
        intro b hb q
        exact hconflict b (Finset.mem_insert_of_mem hb) q
      obtain ⟨f, hfchoose, hfcompat⟩ := ih hlargeS hconflictS
      let forbidden : Finset Q := S.biUnion fun b ↦
        (candidates a).filter fun x ↦ conflict x (f b)
      have hforbidden : forbidden.card ≤ S.card * M := by
        exact card_biUnion_le_mul S
          (fun b ↦ (candidates a).filter fun x ↦ conflict x (f b)) M
          (fun b hb ↦ hconflict a (Finset.mem_insert_self a S) (f b))
      have hroom : forbidden.card < (candidates a).card := by
        exact hforbidden.trans_lt ((Nat.mul_le_mul_right M
          (Finset.card_le_card (Finset.subset_insert a S))).trans_lt
            (hlarge a (Finset.mem_insert_self a S)))
      have hdiff : (candidates a \ forbidden).Nonempty := by
        rw [Finset.sdiff_nonempty]
        intro hsub
        exact (not_lt_of_ge (Finset.card_le_card hsub)) hroom
      let qa := hdiff.choose
      have hqa := Finset.mem_sdiff.mp hdiff.choose_spec
      let g : R → Q := fun b ↦ if b = a then qa else f b
      refine ⟨g, ?_, ?_⟩
      · intro b hb
        rcases Finset.mem_insert.mp hb with hba | hb
        · subst b
          simpa [g] using hqa.1
        · have hba : b ≠ a := fun h ↦ ha (h ▸ hb)
          simpa [g, hba] using hfchoose b hb
      · intro b hb c hc hbc
        rcases Finset.mem_insert.mp hb with hbaEq | hbS
        · subst b
          have hcS : c ∈ S := (Finset.mem_insert.mp hc).resolve_left
            (fun h ↦ hbc h.symm)
          have hnot : ¬ conflict qa (f c) := by
            intro hbad
            apply hqa.2
            apply Finset.mem_biUnion.mpr
            exact ⟨c, hcS, Finset.mem_filter.mpr ⟨hqa.1, hbad⟩⟩
          have hca : c ≠ a := fun h ↦ ha (h ▸ hcS)
          simpa [g, hca] using hnot
        · rcases Finset.mem_insert.mp hc with hcaEq | hcS
          · subst c
            have hnot : ¬ conflict qa (f b) := by
              intro hbad
              apply hqa.2
              apply Finset.mem_biUnion.mpr
              exact ⟨b, hbS, Finset.mem_filter.mpr ⟨hqa.1, hbad⟩⟩
            have hba : b ≠ a := fun h ↦ ha (h ▸ hbS)
            simpa [g, hba] using fun h ↦ hnot (hsymm h)
          · have hba : b ≠ a := fun h ↦ ha (h ▸ hbS)
            have hca : c ≠ a := fun h ↦ ha (h ▸ hcS)
            simpa [g, hba, hca] using hfcompat b hbS c hcS hbc

end

end Erdos722.GreedyChoice
