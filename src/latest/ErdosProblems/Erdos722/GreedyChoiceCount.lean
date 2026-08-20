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
import ErdosProblems.Erdos722.GreedyChoice
import Mathlib

/-!
# Counting greedy compatible choices

The existence lemma in `GreedyChoice` has a quantitative companion.  If,
even after paying for all earlier conflicts, at least `L` candidates remain
at every root, then there are at least `L ^ roots.card` compatible choice
functions.  We keep functions canonical away from the current root set in
the induction; this makes the extension map injective.
-/

namespace Erdos722.GreedyChoiceCount

open Finset
open Erdos722.GreedyChoice

noncomputable section

variable {R Q : Type*} [Fintype R] [Fintype Q]
  [DecidableEq R] [DecidableEq Q] [Nonempty Q]

/-- A full function is canonical off the roots on which choices have been
made. -/
def CanonicalOutside (q₀ : Q) (roots : Finset R) (choice : R → Q) : Prop :=
  ∀ a, a ∉ roots → choice a = q₀

/-- Compatible choices, with a fixed canonical value away from `roots`. -/
def canonicalCompatibleChoices (q₀ : Q) (roots : Finset R)
    (candidates : R → Finset Q) (conflict : Q → Q → Prop)
    [DecidableRel conflict] : Finset (R → Q) := by
  classical
  exact Finset.univ.filter fun choice ↦
    ChoosesOn roots candidates choice ∧
      PairwiseCompatibleOn roots conflict choice ∧
        CanonicalOutside q₀ roots choice

theorem mem_canonicalCompatibleChoices_iff
    (q₀ : Q) (roots : Finset R)
    (candidates : R → Finset Q) (conflict : Q → Q → Prop)
    [DecidableRel conflict] (choice : R → Q) :
    choice ∈ canonicalCompatibleChoices q₀ roots candidates conflict ↔
      ChoosesOn roots candidates choice ∧
        PairwiseCompatibleOn roots conflict choice ∧
          CanonicalOutside q₀ roots choice := by
  simp [canonicalCompatibleChoices]

private theorem card_biUnion_le_mul
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

/-- Counted finite greedy choice.  The displayed lower bound reserves `L`
choices at every insertion after the worst-case conflict loss from all
other roots has been paid. -/
theorem pow_card_le_card_canonicalCompatibleChoices
    (q₀ : Q) (roots : Finset R) (candidates : R → Finset Q)
    (conflict : Q → Q → Prop) [DecidableRel conflict]
    (hsymm : Std.Symm conflict) (M L : ℕ)
    (hlarge : ∀ a ∈ roots,
      L + roots.card * M ≤ (candidates a).card)
    (hconflict : ∀ a ∈ roots, ∀ q : Q,
      ((candidates a).filter fun x ↦ conflict x q).card ≤ M) :
    L ^ roots.card ≤
      (canonicalCompatibleChoices q₀ roots candidates conflict).card := by
  classical
  induction roots using Finset.induction_on with
  | empty =>
      let f : R → Q := fun _ ↦ q₀
      have hf : f ∈ canonicalCompatibleChoices q₀ ∅ candidates conflict := by
        rw [mem_canonicalCompatibleChoices_iff]
        exact ⟨by simp [ChoosesOn], by simp [PairwiseCompatibleOn], by
          intro a ha
          rfl⟩
      have hpos : 0 <
          (canonicalCompatibleChoices q₀ ∅ candidates conflict).card :=
        Finset.card_pos.mpr ⟨f, hf⟩
      simpa using hpos
  | @insert a S ha ih =>
      have hlargeS : ∀ b ∈ S,
          L + S.card * M ≤ (candidates b).card := by
        intro b hb
        exact (Nat.add_le_add_left
          (Nat.mul_le_mul_right M
            (Finset.card_le_card (Finset.subset_insert a S))) L).trans
          (hlarge b (Finset.mem_insert_of_mem hb))
      have hconflictS : ∀ b ∈ S, ∀ q : Q,
          ((candidates b).filter fun x ↦ conflict x q).card ≤ M := by
        intro b hb q
        exact hconflict b (Finset.mem_insert_of_mem hb) q
      let old := canonicalCompatibleChoices q₀ S candidates conflict
      have hold : L ^ S.card ≤ old.card := by
        simpa [old] using ih hlargeS hconflictS
      let forbidden : (R → Q) → Finset Q := fun f ↦
        S.biUnion fun b ↦ (candidates a).filter fun x ↦ conflict x (f b)
      let eligible : (R → Q) → Finset Q := fun f ↦
        candidates a \ forbidden f
      have hforbidden : ∀ f : R → Q,
          (forbidden f).card ≤ S.card * M := by
        intro f
        apply card_biUnion_le_mul S
          (fun b ↦ (candidates a).filter fun x ↦ conflict x (f b)) M
        intro b hb
        exact hconflict a (Finset.mem_insert_self a S) (f b)
      have heligible : ∀ f : R → Q, L ≤ (eligible f).card := by
        intro f
        have hsplit := Finset.card_sdiff_add_card_inter
          (candidates a) (forbidden f)
        have hinter : ((candidates a) ∩ forbidden f).card ≤
            (forbidden f).card :=
          Finset.card_le_card Finset.inter_subset_right
        have hcandidate : L + S.card * M ≤ (candidates a).card := by
          have h := hlarge a (Finset.mem_insert_self a S)
          rw [Finset.card_insert_of_notMem ha] at h
          exact (Nat.add_le_add_left
            (Nat.mul_le_mul_right M (Nat.le_succ S.card)) L).trans h
        have hforbiddenF := hforbidden f
        change L ≤ (candidates a \ forbidden f).card
        omega
      let pick : (f : R → Q) → Fin L ↪ ↑(eligible f) := fun f ↦
        (Fin.castLEEmb (by simpa using heligible f)).trans
          (eligible f).equivFin.symm.toEmbedding
      have hpick_mem : ∀ f (i : Fin L), (pick f i).1 ∈ eligible f := by
        intro f i
        exact (pick f i).property
      let extend : (R → Q) × Fin L → R → Q := fun z ↦
        Function.update z.1 a (pick z.1 z.2).1
      let domain : Finset ((R → Q) × Fin L) := old ×ˢ Finset.univ
      have hextend_injective : Set.InjOn extend ↑domain := by
        rintro ⟨f, i⟩ hfi ⟨g, j⟩ hgj heq
        have hfiData := Finset.mem_product.mp hfi
        have hgjData := Finset.mem_product.mp hgj
        have hfold : f ∈ old → f a = q₀ := by
          intro hf
          have hfdata := (mem_canonicalCompatibleChoices_iff
            q₀ S candidates conflict f).mp (by simpa [old] using hf)
          exact hfdata.2.2 a ha
        have hgold : g ∈ old → g a = q₀ := by
          intro hg
          have hgdata := (mem_canonicalCompatibleChoices_iff
            q₀ S candidates conflict g).mp (by simpa [old] using hg)
          exact hgdata.2.2 a ha
        have hfOld : f ∈ old := hfiData.1
        have hgOld : g ∈ old := hgjData.1
        have hfg : f = g := by
          funext b
          by_cases hba : b = a
          · subst b
            exact (hfold hfOld).trans (hgold hgOld).symm
          · have hb := congrFun heq b
            simpa [extend, hba] using hb
        subst g
        have hij : (pick f i).1 = (pick f j).1 := by
          have hb := congrFun heq a
          simpa [extend] using hb
        have : i = j := (pick f).injective (Subtype.ext hij)
        subst j
        rfl
      let imageChoices : Finset (R → Q) := domain.image extend
      have hdomainCard : domain.card = old.card * L := by
        simp [domain]
      have himageCard : imageChoices.card = old.card * L := by
        rw [show imageChoices.card = domain.card by
          exact Finset.card_image_iff.mpr hextend_injective]
        exact hdomainCard
      have himageSubset : imageChoices ⊆
          canonicalCompatibleChoices q₀ (insert a S) candidates conflict := by
        intro g hg
        obtain ⟨⟨f, i⟩, hz, rfl⟩ := Finset.mem_image.mp hg
        have hzdata := Finset.mem_product.mp hz
        have hfOld : f ∈ old := hzdata.1
        have hfdata := (mem_canonicalCompatibleChoices_iff
          q₀ S candidates conflict f).mp (by simpa [old] using hfOld)
        have hqi := hpick_mem f i
        have hqiCandidate : (pick f i).1 ∈ candidates a :=
          (Finset.mem_sdiff.mp hqi).1
        have hqiForbidden : (pick f i).1 ∉ forbidden f :=
          (Finset.mem_sdiff.mp hqi).2
        rw [mem_canonicalCompatibleChoices_iff]
        refine ⟨?_, ?_, ?_⟩
        · intro b hb
          rcases Finset.mem_insert.mp hb with hbaEq | hb
          · subst b
            simpa [extend] using hqiCandidate
          · have hba : b ≠ a := fun h ↦ ha (h ▸ hb)
            simpa [extend, hba] using hfdata.1 b hb
        · intro b hb c hc hbc
          rcases Finset.mem_insert.mp hb with hbaEq | hbS
          · subst b
            have hcS : c ∈ S :=
              (Finset.mem_insert.mp hc).resolve_left (fun h ↦ hbc h.symm)
            have hca : c ≠ a := fun h ↦ ha (h ▸ hcS)
            have hnot : ¬ conflict (pick f i).1 (f c) := by
              intro hbad
              apply hqiForbidden
              apply Finset.mem_biUnion.mpr
              exact ⟨c, hcS,
                Finset.mem_filter.mpr ⟨hqiCandidate, hbad⟩⟩
            simpa [extend, hca] using hnot
          · rcases Finset.mem_insert.mp hc with hcaEq | hcS
            · subst c
              have hba : b ≠ a := fun h ↦ ha (h ▸ hbS)
              have hnot : ¬ conflict (pick f i).1 (f b) := by
                intro hbad
                apply hqiForbidden
                apply Finset.mem_biUnion.mpr
                exact ⟨b, hbS,
                  Finset.mem_filter.mpr ⟨hqiCandidate, hbad⟩⟩
              simpa [extend, hba] using fun h ↦
                hnot (hsymm.symm _ _ h)
            · have hba : b ≠ a := fun h ↦ ha (h ▸ hbS)
              have hca : c ≠ a := fun h ↦ ha (h ▸ hcS)
              simpa [extend, hba, hca] using
                  hfdata.2.1 b hbS c hcS hbc
        · intro b hb
          have hba : b ≠ a := fun h ↦ hb (h ▸ Finset.mem_insert_self a S)
          have hbS : b ∉ S := fun hbS ↦
            hb (Finset.mem_insert_of_mem hbS)
          simpa [extend, hba] using
            hfdata.2.2 b hbS
      have himageLe : old.card * L ≤
          (canonicalCompatibleChoices q₀ (insert a S)
            candidates conflict).card := by
        rw [← himageCard]
        exact Finset.card_le_card himageSubset
      rw [Finset.card_insert_of_notMem ha, pow_succ]
      exact (Nat.mul_le_mul_right L hold).trans (by
        simpa [Nat.mul_comm] using himageLe)

/-- Dropping the canonical-off-root condition only enlarges the family. -/
theorem pow_card_le_card_compatibleChoices
    (q₀ : Q) (roots : Finset R) (candidates : R → Finset Q)
    (conflict : Q → Q → Prop) [DecidableRel conflict]
    (hsymm : Std.Symm conflict) (M L : ℕ)
    (hlarge : ∀ a ∈ roots,
      L + roots.card * M ≤ (candidates a).card)
    (hconflict : ∀ a ∈ roots, ∀ q : Q,
      ((candidates a).filter fun x ↦ conflict x q).card ≤ M) :
    L ^ roots.card ≤ (by
      classical
      exact (Finset.univ.filter fun choice : R → Q ↦
        ChoosesOn roots candidates choice ∧
          PairwiseCompatibleOn roots conflict choice).card) := by
  classical
  apply (pow_card_le_card_canonicalCompatibleChoices q₀ roots candidates
    conflict hsymm M L hlarge hconflict).trans
  apply Finset.card_le_card
  intro f hf
  have hfdata := (mem_canonicalCompatibleChoices_iff
    q₀ roots candidates conflict f).mp hf
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfdata.1, hfdata.2.1⟩

end

end Erdos722.GreedyChoiceCount
