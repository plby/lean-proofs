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
import ErdosProblems.Erdos722.CandidateCliqueRotation
import ErdosProblems.Erdos722.ExchangePattern
import ErdosProblems.Erdos722.GreedyChoiceCount
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Candidate embeddings with all distinguished exchange cliques fixed

Keevash's Lemma 6.3(iv) first chooses the images of the distinguished
negative cliques of the exchange and only then uses fresh rotations on the
remaining blocks.  This file packages that restricted family of full rooted
embeddings and proves the geometric fact needed by the rotation estimate:
every remaining exchange block has a proper (less than `r`) trace on the
root.
-/

namespace Erdos722.SpecialCliqueCandidates

open Finset
open Erdos722.Transversal
open Erdos722.Exchange
open Erdos722.ExchangePattern
open Erdos722.RootedEmbedding
open Erdos722.GreedyChoice
open Erdos722.GreedyChoiceCount
open Erdos722.Typicality

noncomputable section

/-- The family of distinguished negative blocks. -/
def specialBlocks (E : RelabeledFullExchange q r) :
    Finset (Finset (Fin E.v)) :=
  Finset.univ.image E.special

/-- Exchange blocks still requiring fresh monochromatic-clique rotations
after the special negative blocks have been fixed.  The positive root is
already prescribed, so it is omitted as well. -/
def remainingBlocks (E : RelabeledFullExchange q r) :
    Finset (Finset (Fin E.v)) :=
  (E.positive.erase E.pattern.root) ∪ (E.negative \ specialBlocks E)

/-- Full rooted embeddings for which every distinguished negative block
has already landed in its prescribed family of good host cliques. -/
def specialGoodEmbeddings (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n))) :
    Finset (Fin E.v ↪ Fin n) :=
  (rootedEmbeddings E.pattern.root request).filter fun φ ↦
    ∀ e, mapEdge φ (E.special e) ∈ U e

theorem mem_specialGoodEmbeddings_iff
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (φ : Fin E.v ↪ Fin n) :
    φ ∈ specialGoodEmbeddings E request U ↔
      ExtendsRequest E.pattern.root request φ ∧
        ∀ e, mapEdge φ (E.special e) ∈ U e := by
  simp [specialGoodEmbeddings, mem_rootedEmbeddings]

theorem specialGoodEmbeddings_extends
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    {φ : Fin E.v ↪ Fin n} (hφ : φ ∈ specialGoodEmbeddings E request U) :
    ExtendsRequest E.pattern.root request φ :=
  (mem_specialGoodEmbeddings_iff E request U φ).mp hφ |>.1

theorem specialGoodEmbeddings_special
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    {φ : Fin E.v ↪ Fin n} (hφ : φ ∈ specialGoodEmbeddings E request U)
    (e : RootEdge q r) :
    mapEdge φ (E.special e) ∈ U e :=
  (mem_specialGoodEmbeddings_iff E request U φ).mp hφ |>.2 e

theorem mem_specialBlocks (E : RelabeledFullExchange q r)
    (e : RootEdge q r) : E.special e ∈ specialBlocks E := by
  exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩

/-- Every remaining block is a `q`-set. -/
theorem remainingBlocks_uniform (E : RelabeledFullExchange q r)
    {B : Finset (Fin E.v)} (hB : B ∈ remainingBlocks E) :
    B.card = q := by
  rcases Finset.mem_union.mp hB with hB | hB
  · exact E.positive_decomp.1 B (Finset.mem_erase.mp hB).2
  · exact E.negative_decomp.1 B (Finset.mem_sdiff.mp hB).1

/-- A block different from the positive root has a proper trace on the
root.  This is immediate from uniqueness of the positive decomposition. -/
theorem positive_erase_inter_root_card_lt
    (E : RelabeledFullExchange q r)
    {B : Finset (Fin E.v)}
    (hB : B ∈ E.positive.erase E.pattern.root) :
    (B ∩ E.pattern.root).card < r := by
  classical
  by_contra hnot
  have hrle : r ≤ (B ∩ E.pattern.root).card := by omega
  obtain ⟨g, hgsub, hgcard⟩ := Finset.exists_subset_card_eq hrle
  have hgB : g ∈ B.powersetCard r :=
    Finset.mem_powersetCard.mpr
      ⟨hgsub.trans Finset.inter_subset_left, hgcard⟩
  have hgroot : g ∈ E.pattern.root.powersetCard r :=
    Finset.mem_powersetCard.mpr
      ⟨hgsub.trans Finset.inter_subset_right, hgcard⟩
  have hrootMem : E.pattern.root ∈ E.positive := by
    simpa [E.root_eq] using E.root_mem
  have hEq := E.positive_decomp.blocks_eq_of_common_edge
    (Finset.mem_erase.mp hB).2 hrootMem hgB hgroot
  exact (Finset.mem_erase.mp hB).1 hEq

/-- An `r`-set in the relabelled root is the mapped image of a unique
labelled root edge. -/
theorem exists_rootEdge_mapped_eq
    (E : RelabeledFullExchange q r)
    {g : Finset (Fin E.v)}
    (hgsub : g ⊆ E.pattern.root) (hgcard : g.card = r) :
    ∃ e : RootEdge q r, mappedRootEdge E.rootEmbedding e.1 = g := by
  classical
  let a : Finset (Fin q) :=
    g.preimage E.rootEmbedding E.rootEmbedding.injective.injOn
  have hgsubMap : g ⊆ mappedRoot E.rootEmbedding := by
    simpa [E.root_eq] using hgsub
  have hamap : a.map E.rootEmbedding = g := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
      rw [← hyx]
      exact Finset.mem_preimage.mp hy
    · intro hx
      obtain ⟨y, _hy, hyx⟩ := Finset.mem_map.mp (hgsubMap hx)
      apply Finset.mem_map.mpr
      refine ⟨y, Finset.mem_preimage.mpr ?_, hyx⟩
      simpa [hyx] using hx
  have hasub : a ⊆ (Finset.univ : Finset (Fin q)) :=
    Finset.subset_univ _
  have hacard : a.card = r := by
    rw [← Finset.card_map E.rootEmbedding, hamap, hgcard]
  let e : RootEdge q r :=
    ⟨a, Finset.mem_powersetCard.mpr ⟨hasub, hacard⟩⟩
  exact ⟨e, by simpa [e, mappedRootEdge] using hamap⟩

/-- A negative block not among the distinguished special blocks has a
proper trace on the root. -/
theorem negative_nonSpecial_inter_root_card_lt
    (E : RelabeledFullExchange q r)
    {B : Finset (Fin E.v)}
    (hB : B ∈ E.negative \ specialBlocks E) :
    (B ∩ E.pattern.root).card < r := by
  classical
  by_contra hnot
  have hrle : r ≤ (B ∩ E.pattern.root).card := by omega
  obtain ⟨g, hgsub, hgcard⟩ := Finset.exists_subset_card_eq hrle
  have hgB : g ∈ B.powersetCard r :=
    Finset.mem_powersetCard.mpr
      ⟨hgsub.trans Finset.inter_subset_left, hgcard⟩
  have hgrootSub : g ⊆ E.pattern.root :=
    hgsub.trans Finset.inter_subset_right
  obtain ⟨e, he⟩ := exists_rootEdge_mapped_eq E hgrootSub hgcard
  have hgSpecialSub : g ⊆ E.special e := by
    intro x hx
    have hxMapped : x ∈ mappedRootEdge E.rootEmbedding e.1 := by
      simpa [he] using hx
    have hxInter : x ∈ E.special e ∩ mappedRoot E.rootEmbedding := by
      rw [E.special_inter_root e]
      exact hxMapped
    exact (Finset.mem_inter.mp hxInter).1
  have hgSpecial : g ∈ (E.special e).powersetCard r :=
    Finset.mem_powersetCard.mpr ⟨hgSpecialSub, hgcard⟩
  have hEq := E.negative_decomp.blocks_eq_of_common_edge
    (Finset.mem_sdiff.mp hB).1 (E.special_mem e) hgB hgSpecial
  exact (Finset.mem_sdiff.mp hB).2 (by
    rw [hEq]
    exact mem_specialBlocks E e)

/-- Every block left for fresh clique rotations meets the root in fewer
than `r` vertices. -/
theorem remainingBlocks_inter_root_card_lt
    (E : RelabeledFullExchange q r)
    {B : Finset (Fin E.v)} (hB : B ∈ remainingBlocks E) :
    (B ∩ E.pattern.root).card < r := by
  rcases Finset.mem_union.mp hB with hB | hB
  · exact positive_erase_inter_root_card_lt E hB
  · exact negative_nonSpecial_inter_root_card_lt E hB

/-! ## Many pairwise compatible special-clique images -/

/-- Host `q`-sets which contain a prescribed `r`-edge and introduce no
other vertex from the already embedded root. -/
def anchoredCandidates {n : ℕ}
    (U : Finset (Finset (Fin n))) (edge rootImage : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  U.filter fun Q ↦ edge ⊆ Q ∧ Q ∩ rootImage = edge

/-- Two special-clique images conflict when their vertices outside the
embedded root overlap. -/
def outerConflict {n : ℕ} (rootImage Q Q' : Finset (Fin n)) : Prop :=
  ¬Disjoint (Q \ rootImage) (Q' \ rootImage)

theorem outerConflict_symm {n : ℕ} (rootImage : Finset (Fin n)) :
    Std.Symm (outerConflict rootImage) := by
  constructor
  intro Q Q' h
  exact fun hd ↦ h hd.symm

/-- Symmetric conflict relation which is false off the uniform families.
This harmless guard lets the abstract counted-greedy lemma quantify over
all values of the ambient function type. -/
def uniformOuterConflict {n : ℕ} (q : ℕ)
    (rootImage Q Q' : Finset (Fin n)) : Prop :=
  Q.card = q ∧ Q'.card = q ∧ outerConflict rootImage Q Q'

theorem uniformOuterConflict_symm {n q : ℕ}
    (rootImage : Finset (Fin n)) :
    Std.Symm (uniformOuterConflict q rootImage) := by
  constructor
  rintro Q Q' ⟨hQ, hQ', hconflict⟩
  exact ⟨hQ', hQ, (outerConflict_symm rootImage).symm _ _ hconflict⟩

/-- Crude but exponent-sharp bound for uniform supersets of `A` which hit
a disjoint forbidden vertex set. -/
theorem card_uniformSupersets_meeting_le
    {n q r : ℕ} (hrq : r < q)
    {A W : Finset (Fin n)} (hAcard : A.card = r)
    (hdisj : Disjoint A W) :
    (((uniformEdges n q).filter fun Q ↦ A ⊆ Q).filter fun Q ↦
        ¬Disjoint Q W).card ≤ W.card * n ^ (q - r - 1) := by
  classical
  let through : Fin n → Finset (Finset (Fin n)) := fun x ↦
    (uniformEdges n q).filter fun Q ↦ insert x A ⊆ Q
  have hcover :
      ((uniformEdges n q).filter fun Q ↦ A ⊆ Q).filter (fun Q ↦
          ¬Disjoint Q W) ⊆ W.biUnion through := by
    intro Q hQ
    have hQdata := Finset.mem_filter.mp hQ
    have hQinner := Finset.mem_filter.mp hQdata.1
    rw [Finset.not_disjoint_iff] at hQdata
    obtain ⟨x, hxQ, hxW⟩ := hQdata.2
    apply Finset.mem_biUnion.mpr
    refine ⟨x, hxW, Finset.mem_filter.mpr ⟨hQinner.1, ?_⟩⟩
    exact Finset.insert_subset hxQ hQinner.2
  have hthrough : ∀ x ∈ W,
      (through x).card ≤ n ^ (q - r - 1) := by
    intro x hxW
    have hxA : x ∉ A := fun hxA ↦ Finset.disjoint_left.mp hdisj hxA hxW
    have hcardInsert : (insert x A).card = r + 1 := by
      rw [Finset.card_insert_of_notMem hxA, hAcard]
    have hleq : r + 1 ≤ q := by omega
    have heq : (through x).card =
        Nat.choose (n - (r + 1)) (q - (r + 1)) := by
      dsimp [through]
      rw [uniformEdges,
        Finset.card_filter_powersetCard_subset (insert x A) Finset.univ q
          (Finset.subset_univ _) (by simpa [hcardInsert] using hleq),
        hcardInsert]
      simp
    rw [heq]
    calc
      Nat.choose (n - (r + 1)) (q - (r + 1)) ≤
          (n - (r + 1)) ^ (q - (r + 1)) := Nat.choose_le_pow _ _
      _ ≤ n ^ (q - (r + 1)) := by gcongr; omega
      _ = n ^ (q - r - 1) := by congr 1 <;> omega
  calc
    (((uniformEdges n q).filter fun Q ↦ A ⊆ Q).filter fun Q ↦
        ¬Disjoint Q W).card ≤ (W.biUnion through).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ x ∈ W, (through x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ W, n ^ (q - r - 1) := by
      apply Finset.sum_le_sum
      intro x hx
      exact hthrough x hx
    _ = W.card * n ^ (q - r - 1) := by simp

/-- Imposing the exact root intersection deletes at most one
`q * n^(q-r-1)` error term from a through-edge family. -/
theorem anchoredCandidates_card_lower
    {n q r G : ℕ} (hrq : r < q)
    {U : Finset (Finset (Fin n))}
    (hU : ∀ Q ∈ U, Q.card = q)
    {edge rootImage : Finset (Fin n)}
    (hedge : edge.card = r) (hroot : rootImage.card = q)
    (hsub : edge ⊆ rootImage)
    (hlower : G ≤ (U.filter fun Q ↦ edge ⊆ Q).card) :
    G - q * n ^ (q - r - 1) ≤
      (anchoredCandidates U edge rootImage).card := by
  classical
  let all := U.filter fun Q ↦ edge ⊆ Q
  let bad := all.filter fun Q ↦ ¬Disjoint Q (rootImage \ edge)
  have hdisj : Disjoint edge (rootImage \ edge) := by
    apply Finset.disjoint_left.mpr
    intro x hxEdge hxDiff
    exact (Finset.mem_sdiff.mp hxDiff).2 hxEdge
  have hbadAmbient : bad ⊆
      ((uniformEdges n q).filter fun Q ↦ edge ⊆ Q).filter fun Q ↦
        ¬Disjoint Q (rootImage \ edge) := by
    intro Q hQ
    have hQdata := Finset.mem_filter.mp hQ
    have hQall := Finset.mem_filter.mp hQdata.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, hQall.2⟩, hQdata.2⟩
    exact mem_uniformEdges.mpr (hU Q hQall.1)
  have hbad : bad.card ≤ q * n ^ (q - r - 1) := by
    calc
      bad.card ≤
          (((uniformEdges n q).filter fun Q ↦ edge ⊆ Q).filter fun Q ↦
            ¬Disjoint Q (rootImage \ edge)).card :=
        Finset.card_le_card hbadAmbient
      _ ≤ (rootImage \ edge).card * n ^ (q - r - 1) :=
        card_uniformSupersets_meeting_le hrq hedge hdisj
      _ ≤ q * n ^ (q - r - 1) := by
        gcongr
        rw [Finset.card_sdiff_of_subset hsub, hroot]
        omega
  have hgoodEq : all \ bad = anchoredCandidates U edge rootImage := by
    ext Q
    constructor
    · intro hQ
      have hQsdiff := Finset.mem_sdiff.mp hQ
      let hQall := hQsdiff.1
      let hnotBad := hQsdiff.2
      have hQallData := Finset.mem_filter.mp hQall
      let hQU := hQallData.1
      let hedgeQ := hQallData.2
      have hdisjQ : Disjoint Q (rootImage \ edge) := by
        by_contra hnot
        apply hnotBad
        exact Finset.mem_filter.mpr ⟨hQall, hnot⟩
      have hinter : Q ∩ rootImage = edge := by
        apply Finset.Subset.antisymm
        · intro x hx
          have hxQ := (Finset.mem_inter.mp hx).1
          have hxRoot := (Finset.mem_inter.mp hx).2
          by_contra hxEdge
          exact Finset.disjoint_left.mp hdisjQ hxQ
            (Finset.mem_sdiff.mpr ⟨hxRoot, hxEdge⟩)
        · intro x hx
          exact Finset.mem_inter.mpr ⟨hedgeQ hx, hsub hx⟩
      exact Finset.mem_filter.mpr ⟨hQU, hedgeQ, hinter⟩
    · intro hQ
      have hQdata := Finset.mem_filter.mp hQ
      let hQU := hQdata.1
      let hedgeQ := hQdata.2.1
      let hinter := hQdata.2.2
      have hQall : Q ∈ all := Finset.mem_filter.mpr ⟨hQU, hedgeQ⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨hQall, ?_⟩
      intro hbadQ
      have hnotDisj := (Finset.mem_filter.mp hbadQ).2
      rw [Finset.not_disjoint_iff] at hnotDisj
      obtain ⟨x, hxQ, hxRoot⟩ := hnotDisj
      have hxInter : x ∈ Q ∩ rootImage :=
        Finset.mem_inter.mpr ⟨hxQ, (Finset.mem_sdiff.mp hxRoot).1⟩
      exact (Finset.mem_sdiff.mp hxRoot).2 (by simpa [hinter] using hxInter)
  have hsplit := Finset.card_sdiff_add_card_inter all bad
  have hinterLe : (all ∩ bad).card ≤ bad.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hlowerAll : G ≤ all.card := by simpa [all] using hlower
  rw [← hgoodEq]
  omega

/-- For one fixed other clique, at most `q * n^(q-r-1)` anchored
candidates conflict outside the embedded root. -/
theorem anchoredCandidates_conflict_card_le
    {n q r : ℕ} (hrq : r < q)
    {U : Finset (Finset (Fin n))}
    (hU : ∀ Q ∈ U, Q.card = q)
    {edge rootImage Q' : Finset (Fin n)}
    (hedge : edge.card = r) (hsub : edge ⊆ rootImage)
    (hQ' : Q'.card = q) :
    (by
      classical
      exact ((anchoredCandidates U edge rootImage).filter fun Q ↦
        outerConflict rootImage Q Q').card) ≤
          q * n ^ (q - r - 1) := by
  classical
  have hdisj : Disjoint edge (Q' \ rootImage) := by
    apply Finset.disjoint_left.mpr
    intro x hxEdge hxOuter
    exact (Finset.mem_sdiff.mp hxOuter).2 (hsub hxEdge)
  have hsubset :
      ((anchoredCandidates U edge rootImage).filter fun Q ↦
          outerConflict rootImage Q Q') ⊆
        ((uniformEdges n q).filter fun Q ↦ edge ⊆ Q).filter fun Q ↦
          ¬Disjoint Q (Q' \ rootImage) := by
    intro Q hQ
    have hQdata := Finset.mem_filter.mp hQ
    have hAnchor := Finset.mem_filter.mp hQdata.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, hAnchor.2.1⟩, ?_⟩
    · exact mem_uniformEdges.mpr (hU Q hAnchor.1)
    · intro hd
      apply hQdata.2
      exact hd.mono (fun x hx ↦ (Finset.mem_sdiff.mp hx).1)
        Finset.Subset.rfl
  calc
    ((anchoredCandidates U edge rootImage).filter fun Q ↦
        outerConflict rootImage Q Q').card ≤
        (((uniformEdges n q).filter fun Q ↦ edge ⊆ Q).filter fun Q ↦
          ¬Disjoint Q (Q' \ rootImage)).card :=
      Finset.card_le_card hsubset
    _ ≤ (Q' \ rootImage).card * n ^ (q - r - 1) :=
      card_uniformSupersets_meeting_le hrq hedge hdisj
    _ ≤ q * n ^ (q - r - 1) := by
      gcongr
      exact (Finset.card_le_card (fun x hx ↦
        (Finset.mem_sdiff.mp hx).1)).trans_eq hQ'

/-- The counted greedy specialization used for the distinguished exchange
cliques. -/
theorem many_compatible_anchoredChoices
    {n q r G : ℕ} (hrq : r < q)
    {I : Type*} [Fintype I] [DecidableEq I]
    (U : I → Finset (Finset (Fin n)))
    (edge : I → Finset (Fin n)) (rootImage : Finset (Fin n))
    (hU : ∀ i, ∀ Q ∈ U i, Q.card = q)
    (hedge : ∀ i, (edge i).card = r)
    (hroot : rootImage.card = q)
    (hsub : ∀ i, edge i ⊆ rootImage)
    (hlower : ∀ i,
      G ≤ ((U i).filter fun Q ↦ edge i ⊆ Q).card)
    (hroom : (Fintype.card I + 1) *
      (q * n ^ (q - r - 1)) ≤ G) :
    let M := q * n ^ (q - r - 1)
    let L := G - (Fintype.card I + 1) * M
    L ^ Fintype.card I ≤ (by
      classical
      exact (Finset.univ.filter fun choice : I → Finset (Fin n) ↦
          ChoosesOn Finset.univ
            (fun i ↦ anchoredCandidates (U i) (edge i) rootImage) choice ∧
          PairwiseCompatibleOn Finset.univ
            (uniformOuterConflict q rootImage)
            choice).card) := by
  classical
  let M := q * n ^ (q - r - 1)
  let L := G - (Fintype.card I + 1) * M
  let candidates := fun i ↦ anchoredCandidates (U i) (edge i) rootImage
  have hcandidate : ∀ i,
      G - M ≤ (candidates i).card := by
    intro i
    simpa [M, candidates] using anchoredCandidates_card_lower hrq
      (hU i) (hedge i) hroot (hsub i) (hlower i)
  apply pow_card_le_card_compatibleChoices (Classical.choice inferInstance)
    Finset.univ candidates (uniformOuterConflict q rootImage)
      (uniformOuterConflict_symm rootImage) M L
  · intro i hi
    have hiCard := hcandidate i
    simp only [Finset.card_univ]
    have hmul : (Fintype.card I + 1) * M =
        Fintype.card I * M + M := by ring
    have hroom' : (Fintype.card I + 1) * M ≤ G := by
      simpa [M] using hroom
    have heq : L + Fintype.card I * M = G - M := by
      dsimp [L]
      rw [hmul]
      omega
    rw [heq]
    exact hiCard
  · intro i hi Q
    by_cases hQ : Q.card = q
    · apply (Finset.card_le_card ?_).trans
          (anchoredCandidates_conflict_card_le hrq (hU i)
            (hedge i) (hsub i) hQ)
      intro X hX
      have hXdata := Finset.mem_filter.mp hX
      exact Finset.mem_filter.mpr ⟨hXdata.1, hXdata.2.2.2⟩
    · simp [uniformOuterConflict, hQ]

/-! ## From compatible clique images to full pattern embeddings -/

/-- Vertices of one distinguished clique outside the positive root. -/
def specialOuter (E : RelabeledFullExchange q r) (e : RootEdge q r) :
    Finset (Fin E.v) :=
  E.special e \ E.pattern.root

/-- The root together with all distinguished negative cliques. -/
def specialSupport (E : RelabeledFullExchange q r) : Finset (Fin E.v) :=
  E.pattern.root ∪
    (Finset.univ : Finset (RootEdge q r)).biUnion (specialOuter E)

@[simp] theorem card_rootEdge (q r : ℕ) :
    Fintype.card (RootEdge q r) = Nat.choose q r := by
  change Fintype.card
      {e // e ∈ (Finset.univ : Finset (Fin q)).powersetCard r} = _
  rw [Fintype.card_coe, Finset.card_powersetCard]
  simp

theorem specialOuter_card (E : RelabeledFullExchange q r)
    (e : RootEdge q r) :
    (specialOuter E e).card = q - r := by
  have hspecial : (E.special e).card = q :=
    E.negative_decomp.1 (E.special e) (E.special_mem e)
  have hinter : E.pattern.root ∩ E.special e =
      mappedRootEdge E.rootEmbedding e.1 := by
    rw [Finset.inter_comm, E.root_eq, E.special_inter_root e]
  simp only [specialOuter, Finset.card_sdiff]
  rw [hinter, hspecial, card_mappedRootEdge, RootEdge.card]

theorem specialOuter_pairwiseDisjoint
    (E : RelabeledFullExchange q r) :
    (↑(Finset.univ : Finset (RootEdge q r)) : Set (RootEdge q r)).PairwiseDisjoint
      (specialOuter E) := by
  intro e he e' he' hne
  change Disjoint (specialOuter E e) (specialOuter E e')
  simpa [specialOuter, E.root_eq] using E.special_outer_disjoint e e' hne

theorem root_disjoint_specialOuter
    (E : RelabeledFullExchange q r) (e : RootEdge q r) :
    Disjoint E.pattern.root (specialOuter E e) := by
  apply Finset.disjoint_left.mpr
  intro x hxRoot hxOuter
  exact (Finset.mem_sdiff.mp hxOuter).2 hxRoot

theorem specialSupport_card (E : RelabeledFullExchange q r) :
    (specialSupport E).card =
      q + Nat.choose q r * (q - r) := by
  let petals := (Finset.univ : Finset (RootEdge q r)).biUnion
    (specialOuter E)
  have hrootPetals : Disjoint E.pattern.root petals := by
    rw [Finset.disjoint_biUnion_right]
    intro e he
    exact root_disjoint_specialOuter E e
  have hpetals : petals.card = Nat.choose q r * (q - r) := by
    calc
      petals.card = ∑ e ∈ (Finset.univ : Finset (RootEdge q r)),
          (specialOuter E e).card :=
        Finset.card_biUnion (specialOuter_pairwiseDisjoint E)
      _ = Nat.choose q r * (q - r) := by
        simp [specialOuter_card, card_rootEdge]
  rw [specialSupport, Finset.card_union_of_disjoint hrootPetals,
    E.root_card, hpetals]

theorem specialOuter_mem_support
    (E : RelabeledFullExchange q r) (e : RootEdge q r) :
    specialOuter E e ⊆ specialSupport E := by
  intro x hx
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨e, Finset.mem_univ _, hx⟩

theorem root_mem_specialSupport
    (E : RelabeledFullExchange q r) :
    E.pattern.root ⊆ specialSupport E :=
  Finset.subset_union_left

/-- The image of one labelled root edge under a root request. -/
def requestedRootEdge (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root) (e : RootEdge q r) :
    Finset (Fin n) :=
  (mappedRootEdge E.rootEmbedding e.1).image request.map

theorem requestedRootEdge_card
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root) (e : RootEdge q r) :
    (requestedRootEdge E request e).card = r := by
  have hsub : mappedRootEdge E.rootEmbedding e.1 ⊆ E.pattern.root := by
    rw [E.root_eq]
    exact mappedRootEdge_subset_mappedRoot E.rootEmbedding e.1
  rw [requestedRootEdge, Finset.card_image_of_injOn (request.injOn.mono hsub),
    card_mappedRootEdge, RootEdge.card]

theorem requestedRootEdge_subset_requestImage
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root) (e : RootEdge q r) :
    requestedRootEdge E request e ⊆
      requestImage E.pattern.root request := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_image.mpr
  refine ⟨y, ?_, rfl⟩
  rw [E.root_eq]
  exact mappedRootEdge_subset_mappedRoot E.rootEmbedding e.1 hy

@[simp] theorem requestImage_card_exchangeRoot
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root) :
    (requestImage E.pattern.root request).card = q := by
  rw [card_requestImage, E.root_card]

/-- The exact finite set of compatible special-clique image tuples. -/
def compatibleSpecialChoices
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n))) :
    Finset (RootEdge q r → Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun choice ↦
    ChoosesOn Finset.univ
      (fun e ↦ anchoredCandidates (U e)
        (requestedRootEdge E request e)
        (requestImage E.pattern.root request)) choice ∧
    PairwiseCompatibleOn Finset.univ
      (outerConflict (requestImage E.pattern.root request)) choice

theorem mem_compatibleSpecialChoices_iff
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (choice : RootEdge q r → Finset (Fin n)) :
    choice ∈ compatibleSpecialChoices E request U ↔
      (∀ e, choice e ∈ anchoredCandidates (U e)
        (requestedRootEdge E request e)
        (requestImage E.pattern.root request)) ∧
      (∀ e e', e ≠ e' →
        Disjoint (choice e \ requestImage E.pattern.root request)
          (choice e' \ requestImage E.pattern.root request)) := by
  classical
  rw [compatibleSpecialChoices]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hchoose, hpair⟩
    refine ⟨fun e ↦ hchoose e (Finset.mem_univ _), ?_⟩
    intro e e' hne
    have hnot := hpair e (Finset.mem_univ _) e' (Finset.mem_univ _) hne
    by_contra hd
    exact hnot hd
  · rintro ⟨hchoose, hpair⟩
    refine ⟨fun e he ↦ hchoose e, ?_⟩
    intro e he e' he' hne
    intro hconflict
    exact hconflict (hpair e e' hne)

/-- Local through-edge abundance gives many mutually compatible choices
of all distinguished special cliques. -/
theorem many_compatibleSpecialChoices
    (E : RelabeledFullExchange q r) (hrq : r < q)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    {G : ℕ}
    (hlower : ∀ e, G ≤ ((U e).filter fun Q ↦
      requestedRootEdge E request e ⊆ Q).card)
    (hroom : (Nat.choose q r + 1) *
      (q * n ^ (q - r - 1)) ≤ G) :
    let M := q * n ^ (q - r - 1)
    let L := G - (Nat.choose q r + 1) * M
    L ^ Nat.choose q r ≤
      (compatibleSpecialChoices E request U).card := by
  classical
  let rootImage := requestImage E.pattern.root request
  let edges := requestedRootEdge E request
  let candidates := fun e ↦
    anchoredCandidates (U e) (edges e) rootImage
  let uniformChoices : Finset (RootEdge q r → Finset (Fin n)) :=
    Finset.univ.filter fun choice ↦
      ChoosesOn Finset.univ candidates choice ∧
      PairwiseCompatibleOn Finset.univ
        (uniformOuterConflict q rootImage) choice
  have hlowerChoices :
      (G - (Fintype.card (RootEdge q r) + 1) *
          (q * n ^ (q - r - 1))) ^
            Fintype.card (RootEdge q r) ≤ uniformChoices.card := by
    simpa [uniformChoices, candidates, rootImage, edges] using
      many_compatible_anchoredChoices hrq U edges rootImage hU
        (requestedRootEdge_card E request)
        (requestImage_card_exchangeRoot E request)
        (requestedRootEdge_subset_requestImage E request) hlower (by
          simpa [card_rootEdge] using hroom)
  have hsubset : uniformChoices ⊆ compatibleSpecialChoices E request U := by
    intro choice hchoice
    have hdata := Finset.mem_filter.mp hchoice
    rw [mem_compatibleSpecialChoices_iff]
    refine ⟨fun e ↦ hdata.2.1 e (Finset.mem_univ _), ?_⟩
    intro e e' hne
    have hnot := hdata.2.2 e (Finset.mem_univ _) e' (Finset.mem_univ _) hne
    have heAnchor := Finset.mem_filter.mp
      (hdata.2.1 e (Finset.mem_univ _))
    have he'Anchor := Finset.mem_filter.mp
      (hdata.2.1 e' (Finset.mem_univ _))
    have heCard := hU e (choice e) heAnchor.1
    have he'Card := hU e' (choice e') he'Anchor.1
    by_contra hconflict
    exact hnot ⟨heCard, he'Card, hconflict⟩
  have hcard := Finset.card_le_card hsubset
  simpa [card_rootEdge] using hlowerChoices.trans hcard

theorem compatibleSpecialChoice_card
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    {choice : RootEdge q r → Finset (Fin n)}
    (hchoice : choice ∈ compatibleSpecialChoices E request U)
    (e : RootEdge q r) :
    (choice e \ requestImage E.pattern.root request).card = q - r := by
  have hdata := (mem_compatibleSpecialChoices_iff E request U choice).mp
    hchoice
  have hanchor := Finset.mem_filter.mp (hdata.1 e)
  have hQcard := hU e (choice e) hanchor.1
  have hinter : requestImage E.pattern.root request ∩ choice e =
      requestedRootEdge E request e := by
    rw [Finset.inter_comm, hanchor.2.2]
  rw [Finset.card_sdiff, hinter, hQcard,
    requestedRootEdge_card E request e]

/-- A canonical bijection between the vertices of one abstract special
petal and the vertices of its chosen host image outside the root. -/
noncomputable def specialPetalEquiv
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U)
    (e : RootEdge q r) :
    ↑(specialOuter E e) ≃
      ↑(choice e \ requestImage E.pattern.root request) :=
  Finset.equivOfCardEq ((specialOuter_card E e).trans
    (compatibleSpecialChoice_card E request U hU hchoice e).symm)

/-- The partial map on the root and all special petals determined by a
compatible choice tuple. -/
noncomputable def specialPartialMap
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U) :
    Fin E.v → Fin n := fun x ↦
  if hx : x ∈ E.pattern.root then request.map x
  else if hp : ∃ e : RootEdge q r, x ∈ specialOuter E e then
    let e := Classical.choose hp
    (specialPetalEquiv E request U hU choice hchoice e
      ⟨x, Classical.choose_spec hp⟩).1
  else request.map x

private theorem dependent_proof_apply_eq
    {ι α : Type*} {P : ι → Prop} (F : (i : ι) → P i → α)
    {i j : ι} (hij : i = j) (hi : P i) (hj : P j) :
    F i hi = F j hj := by
  subst j
  rfl

theorem specialOuter_owner_unique
    (E : RelabeledFullExchange q r)
    {x : Fin E.v} {e e' : RootEdge q r}
    (hxe : x ∈ specialOuter E e) (hxe' : x ∈ specialOuter E e') :
    e = e' := by
  by_contra hne
  exact Finset.disjoint_left.mp
    ((specialOuter_pairwiseDisjoint E) (Finset.mem_univ e)
      (Finset.mem_univ e') hne) hxe hxe'

theorem specialPartialMap_root
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U)
    {x : Fin E.v} (hx : x ∈ E.pattern.root) :
    specialPartialMap E request U hU choice hchoice x = request.map x := by
  simp [specialPartialMap, hx]

theorem specialPartialMap_outer_mem
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U)
    (e : RootEdge q r) {x : Fin E.v} (hx : x ∈ specialOuter E e) :
    specialPartialMap E request U hU choice hchoice x ∈
      choice e \ requestImage E.pattern.root request := by
  have hxroot : x ∉ E.pattern.root := (Finset.mem_sdiff.mp hx).2
  let hp : ∃ e' : RootEdge q r, x ∈ specialOuter E e' := ⟨e, hx⟩
  have howner : Classical.choose hp = e :=
    specialOuter_owner_unique E (Classical.choose_spec hp) hx
  rw [specialPartialMap]
  simp only [dif_neg hxroot, dif_pos hp]
  have hprop := (specialPetalEquiv E request U hU choice hchoice
    (Classical.choose hp) ⟨x, Classical.choose_spec hp⟩).property
  simpa only [howner] using hprop

theorem specialPartialMap_outer_eq
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U)
    (e : RootEdge q r) {x : Fin E.v} (hx : x ∈ specialOuter E e) :
    specialPartialMap E request U hU choice hchoice x =
      (specialPetalEquiv E request U hU choice hchoice e ⟨x, hx⟩).1 := by
  have hxroot : x ∉ E.pattern.root := (Finset.mem_sdiff.mp hx).2
  let hp : ∃ e' : RootEdge q r, x ∈ specialOuter E e' := ⟨e, hx⟩
  have howner : Classical.choose hp = e :=
    specialOuter_owner_unique E (Classical.choose_spec hp) hx
  rw [specialPartialMap]
  simp only [dif_neg hxroot, dif_pos hp]
  exact dependent_proof_apply_eq
    (fun e he ↦ (specialPetalEquiv E request U hU choice hchoice e
      ⟨x, he⟩).1) howner (Classical.choose_spec hp) hx

theorem specialPartialMap_outer_injective
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U)
    (e : RootEdge q r) :
    Set.InjOn (specialPartialMap E request U hU choice hchoice)
      (↑(specialOuter E e) : Set (Fin E.v)) := by
  intro x hx y hy hxy
  have hxroot : x ∉ E.pattern.root := (Finset.mem_sdiff.mp hx).2
  have hyroot : y ∉ E.pattern.root := (Finset.mem_sdiff.mp hy).2
  let hpx : ∃ e' : RootEdge q r, x ∈ specialOuter E e' := ⟨e, hx⟩
  let hpy : ∃ e' : RootEdge q r, y ∈ specialOuter E e' := ⟨e, hy⟩
  have hownerX : Classical.choose hpx = e :=
    specialOuter_owner_unique E (Classical.choose_spec hpx) hx
  have hownerY : Classical.choose hpy = e :=
    specialOuter_owner_unique E (Classical.choose_spec hpy) hy
  have hxEq := specialPartialMap_outer_eq E request U hU choice hchoice e hx
  have hyEq := specialPartialMap_outer_eq E request U hU choice hchoice e hy
  have hxy' :
      specialPetalEquiv E request U hU choice hchoice e ⟨x, hx⟩ =
        specialPetalEquiv E request U hU choice hchoice e ⟨y, hy⟩ := by
    apply Subtype.ext
    exact hxEq.symm.trans (hxy.trans hyEq)
  exact congrArg Subtype.val
    ((specialPetalEquiv E request U hU choice hchoice e).injective hxy')

theorem specialPartialMap_injOn_support
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U) :
    Set.InjOn (specialPartialMap E request U hU choice hchoice)
      (↑(specialSupport E) : Set (Fin E.v)) := by
  intro x hx y hy hxy
  have hchoiceData :=
    (mem_compatibleSpecialChoices_iff E request U choice).mp hchoice
  by_cases hxroot : x ∈ E.pattern.root
  · by_cases hyroot : y ∈ E.pattern.root
    · apply request.injOn hxroot hyroot
      rw [← specialPartialMap_root E request U hU choice hchoice hxroot,
        ← specialPartialMap_root E request U hU choice hchoice hyroot]
      exact hxy
    · have hyPetals : y ∈
          (Finset.univ : Finset (RootEdge q r)).biUnion (specialOuter E) := by
        have hyData := Finset.mem_union.mp hy
        exact hyData.resolve_left hyroot
      obtain ⟨e, he, hye⟩ := Finset.mem_biUnion.mp hyPetals
      have hxImage : specialPartialMap E request U hU choice hchoice x ∈
          requestImage E.pattern.root request := by
        rw [specialPartialMap_root E request U hU choice hchoice hxroot]
        exact Finset.mem_image.mpr ⟨x, hxroot, rfl⟩
      have hyImage := specialPartialMap_outer_mem E request U hU choice
        hchoice e hye
      exfalso
      exact (Finset.mem_sdiff.mp hyImage).2 (hxy ▸ hxImage)
  · have hxPetals : x ∈
        (Finset.univ : Finset (RootEdge q r)).biUnion (specialOuter E) := by
      have hxData := Finset.mem_union.mp hx
      exact hxData.resolve_left hxroot
    obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hxPetals
    by_cases hyroot : y ∈ E.pattern.root
    · have hyImage : specialPartialMap E request U hU choice hchoice y ∈
          requestImage E.pattern.root request := by
        rw [specialPartialMap_root E request U hU choice hchoice hyroot]
        exact Finset.mem_image.mpr ⟨y, hyroot, rfl⟩
      have hxImage := specialPartialMap_outer_mem E request U hU choice
        hchoice e hxe
      exfalso
      exact (Finset.mem_sdiff.mp hxImage).2 (hxy.symm ▸ hyImage)
    · have hyPetals : y ∈
          (Finset.univ : Finset (RootEdge q r)).biUnion (specialOuter E) := by
        have hyData := Finset.mem_union.mp hy
        exact hyData.resolve_left hyroot
      obtain ⟨e', he', hye'⟩ := Finset.mem_biUnion.mp hyPetals
      by_cases heq : e = e'
      · subst e'
        exact specialPartialMap_outer_injective E request U hU choice
          hchoice e hxe hye' hxy
      · have hxImage := specialPartialMap_outer_mem E request U hU choice
          hchoice e hxe
        have hyImage := specialPartialMap_outer_mem E request U hU choice
          hchoice e' hye'
        have hdisj := hchoiceData.2 e e' heq
        exfalso
        exact Finset.disjoint_left.mp hdisj hxImage (hxy ▸ hyImage)

/-- The enlarged root request obtained from a compatible tuple of special
clique images. -/
noncomputable def specialPartialRequest
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U) :
    RootRequest E.v n (specialSupport E) where
  map := specialPartialMap E request U hU choice hchoice
  injOn := specialPartialMap_injOn_support E request U hU choice hchoice

theorem specialPartialRequest_extends_original
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U) :
    ∀ x ∈ E.pattern.root,
      (specialPartialRequest E request U hU choice hchoice).map x =
        request.map x := by
  intro x hx
  exact specialPartialMap_root E request U hU choice hchoice hx

theorem image_specialOuter_specialPartialMap
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U)
    (e : RootEdge q r) :
    (specialOuter E e).image
        (specialPartialMap E request U hU choice hchoice) =
      choice e \ requestImage E.pattern.root request := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact specialPartialMap_outer_mem E request U hU choice hchoice e hx
  · intro y hy
    let ye : ↑(choice e \ requestImage E.pattern.root request) := ⟨y, hy⟩
    let xe := (specialPetalEquiv E request U hU choice hchoice e).symm ye
    apply Finset.mem_image.mpr
    refine ⟨xe.1, xe.property, ?_⟩
    rw [specialPartialMap_outer_eq E request U hU choice hchoice e xe.property]
    exact congrArg Subtype.val
      ((specialPetalEquiv E request U hU choice hchoice e).apply_symm_apply ye)

theorem image_specialRootPart_specialPartialMap
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U)
    (e : RootEdge q r) :
    (E.special e ∩ E.pattern.root).image
        (specialPartialMap E request U hU choice hchoice) =
      requestedRootEdge E request e := by
  have hinter : E.special e ∩ E.pattern.root =
      mappedRootEdge E.rootEmbedding e.1 := by
    rw [E.root_eq, E.special_inter_root e]
  rw [hinter]
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hxroot : x ∈ E.pattern.root := by
      rw [E.root_eq]
      exact mappedRootEdge_subset_mappedRoot E.rootEmbedding e.1 hx
    rw [specialPartialMap_root E request U hU choice hchoice hxroot]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hxroot : x ∈ E.pattern.root := by
      rw [E.root_eq]
      exact mappedRootEdge_subset_mappedRoot E.rootEmbedding e.1 hx
    apply Finset.mem_image.mpr
    refine ⟨x, hx, ?_⟩
    exact specialPartialMap_root E request U hU choice hchoice hxroot

theorem special_subset_specialSupport
    (E : RelabeledFullExchange q r) (e : RootEdge q r) :
    E.special e ⊆ specialSupport E := by
  intro x hx
  by_cases hxroot : x ∈ E.pattern.root
  · exact root_mem_specialSupport E hxroot
  · exact specialOuter_mem_support E e
      (Finset.mem_sdiff.mpr ⟨hx, hxroot⟩)

theorem image_special_specialPartialMap
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U)
    (e : RootEdge q r) :
    (E.special e).image
        (specialPartialMap E request U hU choice hchoice) = choice e := by
  have hsplit : E.special e =
      (E.special e ∩ E.pattern.root) ∪ specialOuter E e := by
    ext x
    simp only [specialOuter, Finset.mem_union, Finset.mem_inter,
      Finset.mem_sdiff]
    tauto
  have hanchor := Finset.mem_filter.mp
    (((mem_compatibleSpecialChoices_iff E request U choice).mp hchoice).1 e)
  have hchoiceSplit : requestedRootEdge E request e ∪
      (choice e \ requestImage E.pattern.root request) = choice e := by
    apply Finset.Subset.antisymm
    · apply Finset.union_subset
      · exact hanchor.2.1
      · intro x hx
        exact (Finset.mem_sdiff.mp hx).1
    · intro x hx
      by_cases hxroot : x ∈ requestImage E.pattern.root request
      · apply Finset.mem_union_left
        have hxinter : x ∈ choice e ∩ requestImage E.pattern.root request :=
          Finset.mem_inter.mpr ⟨hx, hxroot⟩
        simpa [hanchor.2.2] using hxinter
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxroot⟩)
  rw [hsplit, Finset.image_union,
    image_specialRootPart_specialPartialMap E request U hU choice hchoice e,
    image_specialOuter_specialPartialMap E request U hU choice hchoice e,
    hchoiceSplit]

theorem mapEdge_special_of_extends_specialPartialRequest
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U)
    {φ : Fin E.v ↪ Fin n}
    (hext : ExtendsRequest (specialSupport E)
      (specialPartialRequest E request U hU choice hchoice) φ)
    (e : RootEdge q r) :
    mapEdge φ (E.special e) = choice e := by
  rw [mapEdge, Finset.map_eq_image]
  calc
    (E.special e).image φ =
        (E.special e).image
          (specialPartialMap E request U hU choice hchoice) := by
      apply Finset.image_congr
      intro x hx
      exact hext x (special_subset_specialSupport E e hx)
    _ = choice e :=
      image_special_specialPartialMap E request U hU choice hchoice e

theorem extends_original_of_extends_specialPartialRequest
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U)
    {φ : Fin E.v ↪ Fin n}
    (hext : ExtendsRequest (specialSupport E)
      (specialPartialRequest E request U hU choice hchoice) φ) :
    ExtendsRequest E.pattern.root request φ := by
  intro x hx
  exact (hext x (root_mem_specialSupport E hx)).trans
    (specialPartialRequest_extends_original E request U hU choice hchoice x hx)

theorem mem_specialGood_of_extends_specialPartialRequest
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    (choice : RootEdge q r → Finset (Fin n))
    (hchoice : choice ∈ compatibleSpecialChoices E request U)
    {φ : Fin E.v ↪ Fin n}
    (hext : ExtendsRequest (specialSupport E)
      (specialPartialRequest E request U hU choice hchoice) φ) :
    φ ∈ specialGoodEmbeddings E request U := by
  rw [mem_specialGoodEmbeddings_iff]
  refine ⟨extends_original_of_extends_specialPartialRequest
    E request U hU choice hchoice hext, ?_⟩
  intro e
  rw [mapEdge_special_of_extends_specialPartialRequest
    E request U hU choice hchoice hext e]
  have hanchor := Finset.mem_filter.mp
    (((mem_compatibleSpecialChoices_iff E request U choice).mp hchoice).1 e)
  exact hanchor.1

/-- A compatible tuple contributes a full falling-factorial fiber of
embeddings, and distinct tuples give disjoint fibers because the images of
the labelled special cliques recover the tuple. -/
theorem compatibleChoices_mul_descFactorial_le_specialGood
    (E : RelabeledFullExchange q r)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q) :
    (compatibleSpecialChoices E request U).card *
        (n - (specialSupport E).card).descFactorial
          (E.v - (specialSupport E).card) ≤
      (specialGoodEmbeddings E request U).card := by
  classical
  let choicesTy : Type :=
    {c : RootEdge q r → Finset (Fin n) //
      c ∈ compatibleSpecialChoices E request U}
  let partialReq : choicesTy → RootRequest E.v n (specialSupport E) := fun c ↦
    specialPartialRequest E request U hU c.1 c.2
  let domainTy : Type := Sigma fun c : choicesTy ↦
    {φ : Fin E.v ↪ Fin n //
      φ ∈ rootedEmbeddings (specialSupport E) (partialReq c)}
  let toGood : domainTy →
      {φ : Fin E.v ↪ Fin n // φ ∈ specialGoodEmbeddings E request U} := fun z ↦
    ⟨z.2.1, mem_specialGood_of_extends_specialPartialRequest
      E request U hU z.1.1 z.1.2
        (mem_rootedEmbeddings.mp z.2.2)⟩
  have htoGood : Function.Injective toGood := by
    intro a b hab
    have hφ0 := congrArg
      (fun z : {φ : Fin E.v ↪ Fin n //
        φ ∈ specialGoodEmbeddings E request U} ↦ z.1) hab
    have hφ : a.2.1 = b.2.1 := by
      exact hφ0
    have hchoiceVal : a.1.1 = b.1.1 := by
      funext e
      have haext : ExtendsRequest (specialSupport E) (partialReq a.1) a.2.1 :=
        mem_rootedEmbeddings.mp a.2.2
      have hbext : ExtendsRequest (specialSupport E) (partialReq b.1) b.2.1 :=
        mem_rootedEmbeddings.mp b.2.2
      have ha := mapEdge_special_of_extends_specialPartialRequest
        E request U hU a.1.1 a.1.2 haext e
      have hb := mapEdge_special_of_extends_specialPartialRequest
        E request U hU b.1.1 b.1.2 hbext e
      rw [← ha, ← hb, hφ]
    have hchoice : a.1 = b.1 := Subtype.ext hchoiceVal
    apply Sigma.ext hchoice
    apply (Subtype.heq_iff_coe_eq (fun φ ↦ by
      simpa only [hchoice])).2
    exact hφ
  have hfiber : ∀ c : choicesTy,
      (n - (specialSupport E).card).descFactorial
          (E.v - (specialSupport E).card) ≤
        Fintype.card ↑(rootedEmbeddings (specialSupport E) (partialReq c)) := by
    intro c
    simpa [Fintype.card_coe] using
      descFactorial_le_card_rootedEmbeddings (specialSupport E) (partialReq c)
  have hdomainLower :
      (compatibleSpecialChoices E request U).card *
          (n - (specialSupport E).card).descFactorial
            (E.v - (specialSupport E).card) ≤ Fintype.card domainTy := by
    rw [show Fintype.card domainTy =
        ∑ c : choicesTy,
          Fintype.card ↑(rootedEmbeddings (specialSupport E) (partialReq c)) by
      exact Fintype.card_sigma]
    calc
      (compatibleSpecialChoices E request U).card *
            (n - (specialSupport E).card).descFactorial
              (E.v - (specialSupport E).card) =
          ∑ _c : choicesTy,
            (n - (specialSupport E).card).descFactorial
              (E.v - (specialSupport E).card) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp [choicesTy, Nat.mul_comm]
      _ ≤ ∑ c : choicesTy,
          Fintype.card ↑(rootedEmbeddings (specialSupport E) (partialReq c)) := by
        apply Finset.sum_le_sum
        intro c hc
        exact hfiber c
  exact hdomainLower.trans (by
    simpa [Fintype.card_coe] using Fintype.card_le_of_injective toGood htoGood)

/-- Complete finite abundance bound for the restricted candidate family. -/
theorem many_specialGoodEmbeddings
    (E : RelabeledFullExchange q r) (hrq : r < q)
    (request : RootRequest E.v n E.pattern.root)
    (U : RootEdge q r → Finset (Finset (Fin n)))
    (hU : ∀ e, ∀ Q ∈ U e, Q.card = q)
    {G : ℕ}
    (hlower : ∀ e, G ≤ ((U e).filter fun Q ↦
      requestedRootEdge E request e ⊆ Q).card)
    (hroom : (Nat.choose q r + 1) *
      (q * n ^ (q - r - 1)) ≤ G) :
    let L := G - (Nat.choose q r + 1) *
      (q * n ^ (q - r - 1))
    L ^ Nat.choose q r *
        (n - (q + Nat.choose q r * (q - r))).descFactorial
          (E.v - (q + Nat.choose q r * (q - r))) ≤
      (specialGoodEmbeddings E request U).card := by
  let L := G - (Nat.choose q r + 1) *
    (q * n ^ (q - r - 1))
  have hchoices := many_compatibleSpecialChoices E hrq request U hU
    hlower hroom
  have hfibers := compatibleChoices_mul_descFactorial_le_specialGood
    E request U hU
  rw [specialSupport_card E] at hfibers
  exact (Nat.mul_le_mul_right _ hchoices).trans hfibers

end

end Erdos722.SpecialCliqueCandidates
