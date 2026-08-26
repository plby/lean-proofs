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
import ErdosProblems.Erdos19.Pippenger.PippengerSpencerInnerSurvival

/-!
# Sequential counting of anchored matching families

This module packages the finite counting induction used by the all-order
inner-nibble estimate.  The recursive tree chooses one nonexceptional edge
at each anchor and deletes choices conflicting with the edges already
chosen.  Its leaves are matching families with exactly the prescribed
anchor set.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteHypergraph

universe uV uE

variable {V : Type uV} {E : Type uE}
  [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Choices at anchor `v` which are nonexceptional and conflict with none
of the previously chosen edges in `G`. -/
def availableSingleMeetingAt (H : FiniteHypergraph V E)
    (A : Finset V) (v : V) (G : Finset E) : Finset E :=
  (H.singleMeetingAt A v).filter fun e ↦
    ∀ f ∈ G, ¬H.Conflicts e f

@[simp] lemma mem_availableSingleMeetingAt
    (H : FiniteHypergraph V E) (A : Finset V) (v : V)
    (G : Finset E) (e : E) :
    e ∈ H.availableSingleMeetingAt A v G ↔
      e ∈ H.singleMeetingAt A v ∧
        ∀ f ∈ G, ¬H.Conflicts e f := by
  simp [availableSingleMeetingAt]

/-- The finite tree of matching edge families obtained by processing an
ordered list of distinct anchors. -/
def anchorFamilyTree (H : FiniteHypergraph V E)
    (A : Finset V) : List V → Finset (Finset E)
  | [] => {∅}
  | v :: l => (H.anchorFamilyTree A l).biUnion fun G ↦
      (H.availableSingleMeetingAt A v G).image fun e ↦ insert e G

/-- Vertices of `A` used as anchors by a family. -/
def anchorSet (H : FiniteHypergraph V E)
    (A : Finset V) (G : Finset E) : Finset V :=
  G.biUnion fun e ↦ H.support e ∩ A

@[simp] lemma mem_anchorSet
    (H : FiniteHypergraph V E) (A : Finset V) (G : Finset E) (v : V) :
    v ∈ H.anchorSet A G ↔
      ∃ e ∈ G, v ∈ H.support e ∧ v ∈ A := by
  simp [anchorSet, and_assoc]

/-- Every leaf of the recursive tree is a matching family of
nonexceptional edges, with one edge per listed anchor and no other anchor. -/
theorem mem_anchorFamilyTree_spec
    (H : FiniteHypergraph V E) (A : Finset V) :
    ∀ (l : List V), l.Nodup → (∀ v ∈ l, v ∈ A) →
      ∀ G ∈ H.anchorFamilyTree A l,
        H.IsMatching G ∧ G ⊆ H.singleMeetingEdges A ∧
          G.card = l.length ∧ H.anchorSet A G = l.toFinset := by
  intro l
  induction l with
  | nil =>
      intro _ _ G hG
      have hGempty : G = ∅ := by simpa [anchorFamilyTree] using hG
      subst G
      exact ⟨H.empty_isMatching, by simp, by simp, by simp [anchorSet]⟩
  | cons v l ih =>
      intro hnodup hmem G hG
      have hvNot : v ∉ l := (List.nodup_cons.mp hnodup).1
      have hlNodup : l.Nodup := (List.nodup_cons.mp hnodup).2
      have hvA : v ∈ A := hmem v (by simp)
      have hlA : ∀ u ∈ l, u ∈ A := by
        intro u hu
        exact hmem u (by simp [hu])
      rw [anchorFamilyTree] at hG
      obtain ⟨K, hKtree, hGK⟩ := mem_biUnion.mp hG
      obtain ⟨e, heAvail, rfl⟩ := mem_image.mp hGK
      have hK := ih hlNodup hlA K hKtree
      have heData := (H.mem_availableSingleMeetingAt A v K e).1 heAvail
      have heAt := (H.mem_singleMeetingAt A v e).1 heData.1
      have hvK : ∀ f ∈ K, v ∉ H.support f := by
        intro f hf hvf
        have hvAnchor : v ∈ H.anchorSet A K :=
          (H.mem_anchorSet A K v).2 ⟨f, hf, hvf, hvA⟩
        rw [hK.2.2.2] at hvAnchor
        exact hvNot (List.mem_toFinset.mp hvAnchor)
      have heNotK : e ∉ K := fun heK ↦ hvK e heK heAt.1
      have heDisjoint : ∀ f ∈ K,
          Disjoint (H.support e) (H.support f) := by
        intro f hf
        have hef : e ≠ f := fun hef ↦ heNotK (hef ▸ hf)
        by_contra hnot
        exact heData.2 f hf ⟨hef, hnot⟩
      have hmatching : H.IsMatching (insert e K) := by
        rw [IsMatching]
        intro x hx y hy hxy
        simp only [Finset.mem_coe, mem_insert] at hx hy
        rcases hx with rfl | hx
        · rcases hy with rfl | hy
          · exact (hxy rfl).elim
          · exact heDisjoint y hy
        · rcases hy with rfl | hy
          · exact (heDisjoint x hx).symm
          · exact hK.1 hx hy hxy
      have hsubset : insert e K ⊆ H.singleMeetingEdges A := by
        intro f hf
        rcases mem_insert.mp hf with rfl | hf
        · exact heAt.2
        · exact hK.2.1 hf
      have hcard : (insert e K).card = (v :: l).length := by
        rw [card_insert_of_notMem heNotK, hK.2.2.1]
        simp
      have hinter : H.support e ∩ A = {v} := by
        apply eq_singleton_iff_unique_mem.mpr
        refine ⟨mem_inter.mpr ⟨heAt.1, hvA⟩, ?_⟩
        intro u hu
        have huniq := H.existsUnique_anchor_of_mem_singleMeetingEdges A heAt.2
        have hu' := mem_inter.mp hu
        exact huniq.unique ⟨hu'.2, hu'.1⟩ ⟨hvA, heAt.1⟩
      have hanchors : H.anchorSet A (insert e K) = (v :: l).toFinset := by
        simp only [anchorSet, biUnion_insert, hinter, singleton_union,
          List.toFinset_cons]
        exact congrArg (insert v) hK.2.2.2
      exact ⟨hmatching, hsubset, hcard, hanchors⟩

/-- A uniform lower bound on every sequential availability set gives the
corresponding power lower bound on the number of tree leaves.  The parameter
`m` bounds the number of previously chosen edges at every step. -/
theorem pow_le_card_anchorFamilyTree
    (H : FiniteHypergraph V E) (A : Finset V)
    {k C q m : ℕ} (hunif : H.IsUniform k)
    (hpair : ∀ u ∈ H.vertexSet, ∀ z ∈ H.vertexSet, u ≠ z →
      H.edgePairDegree u z ≤ C) :
    ∀ (l : List V), l.Nodup → (∀ v ∈ l, v ∈ A) →
      (∀ v ∈ l, v ∈ H.vertexSet) → l.length ≤ m + 1 →
      (∀ v ∈ l,
        q ≤ H.edgeDegree v - (A.card - 1) * C - m * (k * C)) →
      q ^ l.length ≤ (H.anchorFamilyTree A l).card := by
  intro l
  induction l with
  | nil =>
      intro _ _ _ _ _
      simp [anchorFamilyTree]
  | cons v l ih =>
      intro hnodup hmem hvertex hlength hq
      have hvNot : v ∉ l := (List.nodup_cons.mp hnodup).1
      have hlNodup : l.Nodup := (List.nodup_cons.mp hnodup).2
      have hvA : v ∈ A := hmem v (by simp)
      have hvV : v ∈ H.vertexSet := hvertex v (by simp)
      have hlA : ∀ u ∈ l, u ∈ A := by
        intro u hu
        exact hmem u (by simp [hu])
      have hlV : ∀ u ∈ l, u ∈ H.vertexSet := by
        intro u hu
        exact hvertex u (by simp [hu])
      have hlLength : l.length ≤ m := by
        simpa using hlength
      have hlLength' : l.length ≤ m + 1 := hlLength.trans (Nat.le_succ m)
      have hlq : ∀ u ∈ l,
          q ≤ H.edgeDegree u - (A.card - 1) * C - m * (k * C) := by
        intro u hu
        exact hq u (by simp [hu])
      have htreeLower : q ^ l.length ≤ (H.anchorFamilyTree A l).card :=
        ih hlNodup hlA hlV hlLength' hlq
      let branch : Finset E → Finset (Finset E) := fun G ↦
        (H.availableSingleMeetingAt A v G).image fun e ↦ insert e G
      have hspec (G : Finset E) (hG : G ∈ H.anchorFamilyTree A l) :
          H.IsMatching G ∧ G ⊆ H.singleMeetingEdges A ∧
            G.card = l.length ∧ H.anchorSet A G = l.toFinset :=
        H.mem_anchorFamilyTree_spec A l hlNodup hlA G hG
      have hvOld (G : Finset E) (hG : G ∈ H.anchorFamilyTree A l) :
          ∀ e ∈ G, v ∉ H.support e := by
        intro e he hve
        have hvAnchor : v ∈ H.anchorSet A G :=
          (H.mem_anchorSet A G v).2 ⟨e, he, hve, hvA⟩
        rw [(hspec G hG).2.2.2] at hvAnchor
        exact hvNot (List.mem_toFinset.mp hvAnchor)
      have havailable (G : Finset E) (hG : G ∈ H.anchorFamilyTree A l) :
          q ≤ (H.availableSingleMeetingAt A v G).card := by
        have hraw :=
          H.edgeDegree_sub_pairError_sub_familyConflict_le_availableSingleMeetingAt
            A G hunif hpair hvA hvV (hvOld G hG)
        have hGcard : G.card = l.length := (hspec G hG).2.2.1
        have hmul : G.card * (k * C) ≤ m * (k * C) := by
          exact Nat.mul_le_mul_right (k * C) (hGcard.le.trans hlLength)
        have hsub :
            H.edgeDegree v - (A.card - 1) * C - m * (k * C) ≤
              H.edgeDegree v - (A.card - 1) * C - G.card * (k * C) := by
          omega
        exact (hq v (by simp)).trans (hsub.trans (by
          simpa [availableSingleMeetingAt] using hraw))
      have hbranchCard (G : Finset E) (hG : G ∈ H.anchorFamilyTree A l) :
          (branch G).card = (H.availableSingleMeetingAt A v G).card := by
        apply card_image_iff.mpr
        intro e he f hf hef
        have heAt := (H.mem_availableSingleMeetingAt A v G e).1 he |>.1
        have heData := (H.mem_singleMeetingAt A v e).1 heAt
        have heNotG : e ∉ G := fun heG ↦ hvOld G hG e heG heData.1
        exact (insert_inj heNotG).1 hef
      have hbranchDisjoint :
          ∀ G ∈ H.anchorFamilyTree A l,
            ∀ K ∈ H.anchorFamilyTree A l, G ≠ K →
              Disjoint (branch G) (branch K) := by
        intro G hG K hK hGK
        rw [disjoint_left]
        intro Q hQG hQK
        obtain ⟨e, heAvail, hQe⟩ := mem_image.mp hQG
        obtain ⟨f, hfAvail, hQf⟩ := mem_image.mp hQK
        have heAt := (H.mem_availableSingleMeetingAt A v G e).1 heAvail |>.1
        have hfAt := (H.mem_availableSingleMeetingAt A v K f).1 hfAvail |>.1
        have hve := (H.mem_singleMeetingAt A v e).1 heAt |>.1
        have hvf := (H.mem_singleMeetingAt A v f).1 hfAt |>.1
        have heNotG : e ∉ G := fun heG ↦ hvOld G hG e heG hve
        have hfNotK : f ∉ K := fun hfK ↦ hvOld K hK f hfK hvf
        have hEq : insert e G = insert f K := hQe.trans hQf.symm
        have hef : e = f := by
          have heRight : e ∈ insert f K := by
            rw [← hEq]
            exact mem_insert_self e G
          rcases mem_insert.mp heRight with hef | heK
          · exact hef
          · exact (hvOld K hK e heK hve).elim
        subst f
        have hKG : G = K := by
          have hErase := congrArg (fun R : Finset E ↦ R.erase e) hEq
          simpa [heNotG, hfNotK] using hErase
        exact hGK hKG
      change q ^ (v :: l).length ≤
        ((H.anchorFamilyTree A l).biUnion branch).card
      rw [card_biUnion hbranchDisjoint]
      calc
        q ^ (v :: l).length = q ^ l.length * q := by simp [pow_succ]
        _ ≤ (H.anchorFamilyTree A l).card * q :=
          Nat.mul_le_mul_right q htreeLower
        _ = ∑ _G ∈ H.anchorFamilyTree A l, q := by simp
        _ ≤ ∑ G ∈ H.anchorFamilyTree A l, (branch G).card := by
          apply sum_le_sum
          intro G hG
          rw [hbranchCard G hG]
          exact havailable G hG

/-- Parameter-specialized lower bound for a fixed anchor set.  The base is
exactly the sequential choice count
`degreeLower - (|A|-1)C - (j-1)kC` requested by the nibble hierarchy. -/
theorem sequentialChoiceBase_pow_le_card_anchorFamilyTree_toList
    (H : FiniteHypergraph V E) (A B : Finset V)
    {k C degreeLower j : ℕ} (hj : 0 < j)
    (hBsub : B ⊆ A) (hBvertex : B ⊆ H.vertexSet) (hBcard : B.card = j)
    (hunif : H.IsUniform k)
    (hlow : ∀ v ∈ A, degreeLower ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ z ∈ H.vertexSet, u ≠ z →
      H.edgePairDegree u z ≤ C) :
    (degreeLower - (A.card - 1) * C - (j - 1) * (k * C)) ^ j ≤
      (H.anchorFamilyTree A B.toList).card := by
  let q := degreeLower - (A.card - 1) * C - (j - 1) * (k * C)
  have hlength : B.toList.length = j := by simpa [hBcard]
  have hmemA : ∀ v ∈ B.toList, v ∈ A := by
    intro v hv
    exact hBsub (by simpa using hv)
  have hmemV : ∀ v ∈ B.toList, v ∈ H.vertexSet := by
    intro v hv
    exact hBvertex (by simpa using hv)
  have hq : ∀ v ∈ B.toList,
      q ≤ H.edgeDegree v - (A.card - 1) * C - (j - 1) * (k * C) := by
    intro v hv
    have hvA := hmemA v hv
    have := hlow v hvA
    dsimp only [q]
    omega
  have hmain := H.pow_le_card_anchorFamilyTree A hunif hpair B.toList
    B.nodup_toList hmemA hmemV (m := j - 1) (q := q) (by
      rw [hlength]
      omega) hq
  simpa [q, hlength] using hmain

/-- Every family counted by the preceding fixed-anchor tree has exactly the
specified good-family data. -/
theorem mem_anchorFamilyTree_toList_spec
    (H : FiniteHypergraph V E) (A B : Finset V) (hBsub : B ⊆ A)
    {G : Finset E} (hG : G ∈ H.anchorFamilyTree A B.toList) :
    H.IsMatching G ∧ G ⊆ H.singleMeetingEdges A ∧
      G.card = B.card ∧ H.anchorSet A G = B := by
  have hmemA : ∀ v ∈ B.toList, v ∈ A := by
    intro v hv
    exact hBsub (by simpa using hv)
  have hspec := H.mem_anchorFamilyTree_spec A B.toList B.nodup_toList
    hmemA G hG
  simpa using hspec

end FiniteHypergraph

end

end Erdos76
