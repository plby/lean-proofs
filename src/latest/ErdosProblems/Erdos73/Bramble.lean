/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.Foundations
import ErdosProblems.Erdos73.Menger

/-!
# Erdős Problem 73: linked terminals for the controlled structural step

The unchanged elementary development is imported from `Erdos73.Foundations`.
The finite vertex-Menger theorem is fully proved in `Erdos73.Menger`.
This module connects its ordinary disjoint paths to the bramble and tangle
language used by the remaining controlled-wall construction. The final
unconditional theorem is not yet asserted.
-/

namespace Erdos73

open Erdos73Infrastructure.SimpleGraph

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
lemma not_induce_compl_reachable_of_STSeparator
    {S T J : Finset V} (hsep : STSeparator G S T J)
    {s t : V} (hs : s ∈ S) (ht : t ∈ T) (hsJ : s ∉ J) (htJ : t ∉ J) :
    ¬ (G.induce {v : V | v ∉ J}).Reachable ⟨s, hsJ⟩ ⟨t, htJ⟩ := by
  rintro ⟨W⟩
  let e : G.induce {v : V | v ∉ J} →g G :=
    (SimpleGraph.Embedding.induce (G := G) {v : V | v ∉ J}).toHom
  let W' : G.Walk s t := W.map e
  let P : GraphPath G := GraphPath.ofWalk W'
  obtain ⟨v, hvP, hvJ⟩ := hsep P (Or.inl ⟨hs, ht⟩)
  have hvW' : v ∈ W'.support.toFinset := GraphPath.ofWalk_vertexSet_subset W' hvP
  have hvList : v ∈ (W.map e).support := List.mem_toFinset.mp hvW'
  rw [SimpleGraph.Walk.support_map] at hvList
  obtain ⟨w, _, hwv⟩ := List.mem_map.mp hvList
  change (w : V) = v at hwv
  exact (hwv ▸ w.2) hvJ

theorem exists_vertexSeparation_of_STSeparator
    {S T J : Finset V} (hsep : STSeparator G S T J) :
    ∃ A B : Finset V, IsVertexSeparation G A B ∧ A ∩ B = J ∧ S ⊆ A ∧ T ⊆ B := by
  let K := G.induce {v : V | v ∉ J}
  let R : Finset V := Finset.univ.filter fun v ↦
    ∃ hv : v ∉ J, ∃ s : {v : V // v ∉ J}, s.1 ∈ S ∧ K.Reachable s ⟨v, hv⟩
  have hR (v : V) : v ∈ R ↔
      ∃ hv : v ∉ J, ∃ s : {v : V // v ∉ J}, s.1 ∈ S ∧ K.Reachable s ⟨v, hv⟩ := by
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
  have hRJ {v : V} (hv : v ∈ R) : v ∉ J := (hR v).mp hv |>.choose
  have hST {t : V} (ht : t ∈ T) : t ∉ R := by
    intro htR
    obtain ⟨htJ, s, hs, hst⟩ := (hR t).mp htR
    exact not_induce_compl_reachable_of_STSeparator hsep hs ht s.2 htJ hst
  refine ⟨R ∪ J, Finset.univ \ R, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  · intro a b ha haB hb hbA hab
    have haR : a ∈ R := by
      simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using haB
    have hbJ : b ∉ J := fun hbJ ↦ hbA (Finset.mem_union.mpr (Or.inr hbJ))
    obtain ⟨haJ, s, hs, hsa⟩ := (hR a).mp haR
    have hbR : b ∈ R := (hR b).mpr ⟨hbJ, s, hs,
      hsa.trans (SimpleGraph.Adj.reachable (show K.Adj ⟨a, haJ⟩ ⟨b, hbJ⟩ from hab))⟩
    exact (Finset.mem_sdiff.mp hb).2 hbR
  · ext v
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hvR | hvJ, hvnR⟩
      · exact (hvnR hvR).elim
      · exact hvJ
    · intro hvJ
      exact ⟨Or.inr hvJ, fun hvR ↦ hRJ hvR hvJ⟩
  · intro s hs
    by_cases hsJ : s ∈ J
    · exact Finset.mem_union.mpr (Or.inr hsJ)
    · exact Finset.mem_union.mpr (Or.inl ((hR s).mpr
        ⟨hsJ, ⟨s, hsJ⟩, hs, SimpleGraph.Reachable.refl _⟩))
  · intro t ht
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, hST ht⟩

theorem IsCutLinkedSet.hasDisjointSTPaths {X S T : Finset V}
    (hX : IsCutLinkedSet G X) (hS : S ⊆ X) (hT : T ⊆ X) {p : ℕ}
    (hpS : p ≤ S.card) (hpT : p ≤ T.card) : HasDisjointSTPaths G S T p := by
  rcases Menger.finite_vertex_menger_sharp G S T p with hpaths | ⟨J, hJ, hsep⟩
  · exact hpaths
  · obtain ⟨A, B, hAB, hsepEq, hSA, hTB⟩ := exists_vertexSeparation_of_STSeparator hsep
    have hA : p ≤ (X ∩ A).card := hpS.trans (Finset.card_le_card
      (show S ⊆ X ∩ A from fun v hv ↦ Finset.mem_inter.mpr ⟨hS hv, hSA hv⟩))
    have hB : p ≤ (X ∩ B).card := hpT.trans (Finset.card_le_card
      (show T ⊆ X ∩ B from fun v hv ↦ Finset.mem_inter.mpr ⟨hT hv, hTB hv⟩))
    rcases hX A B hAB with h | h <;> rw [hsepEq] at h <;> omega

/-- The separation form of well-linkedness supplies the path-family form,
with the exact smaller terminal cardinality. -/
theorem IsCutLinkedSet.nodeWellLinkedIn {X : Finset V}
    (hX : IsCutLinkedSet G X) : NodeWellLinkedIn G Finset.univ X := by
  refine ⟨Finset.subset_univ X, ?_⟩
  intro S T hS hT _
  obtain ⟨P, hP⟩ := HasAtLeastDisjointPaths.exists_exact
    (hX.hasDisjointSTPaths hS hT (Nat.min_le_left _ _) (Nat.min_le_right _ _))
  exact ⟨P, hP, fun _ ↦ Finset.subset_univ _⟩

/-- Equal-size subsets of a cut-linked set have a perfect linkage, even
when the terminal sets overlap (trivial paths account for their overlap). -/
theorem IsCutLinkedSet.exists_perfectPathPacking {X S T : Finset V}
    (hX : IsCutLinkedSet G X) (hS : S ⊆ X) (hT : T ⊆ X)
    (hcard : S.card = T.card) : Nonempty (PerfectPathPacking G S T) := by
  obtain ⟨P, hP⟩ := HasAtLeastDisjointPaths.exists_exact
    (hX.hasDisjointSTPaths hS hT le_rfl hcard.le)
  exact ⟨P.toPerfectOfCardEq hP (hP.trans hcard)⟩

/-- A large bramble supplies a large minimum transversal with actual
disjoint-path linkages, retaining its role as a bramble hitting set. -/
theorem exists_nodeWellLinked_minimumBrambleHittingSet {β : Finset (Finset V)}
    (hβ : IsFiniteBramble G β) {q : ℕ} (horder : BrambleOrderAtLeast q β) :
    ∃ X : Finset V, q ≤ X.card ∧ IsMinimumBrambleHittingSet β X ∧
      NodeWellLinkedIn G Finset.univ X := by
  obtain ⟨X, hX⟩ := exists_minimumBrambleHittingSet hβ
  have hcut : IsCutLinkedSet G X :=
    fun _ _ hsep ↦ minimumBrambleHittingSet_cutLinked hβ hX hsep
  exact ⟨X, horder X hX.1, hX, hcut.nodeWellLinkedIn⟩

end

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

local instance (priority := high) (Z : Finset V) :
    DecidableEq {v : V // v ∉ Z} := Classical.decEq _

def liftDeletedSide (Z : Finset V) (A : Finset {v : V // v ∉ Z}) : Finset V :=
  A.map (Function.Embedding.subtype _) ∪ Z

omit [Fintype V] in
lemma mem_liftDeletedSide {Z : Finset V} {A : Finset {v : V // v ∉ Z}} {v : V} :
    v ∈ liftDeletedSide Z A ↔ v ∈ Z ∨ ∃ hv : v ∉ Z, (⟨v, hv⟩ : {v // v ∉ Z}) ∈ A := by
  simp only [liftDeletedSide, Finset.mem_union, Finset.mem_map,
    Function.Embedding.subtype_apply]
  constructor
  · rintro (⟨⟨a, ha⟩, hA, rfl⟩ | hZ)
    · exact Or.inr ⟨ha, hA⟩
    · exact Or.inl hZ
  · rintro (hZ | ⟨hv, hA⟩)
    · exact Or.inr hZ
    · exact Or.inl ⟨⟨v, hv⟩, hA, rfl⟩

lemma isVertexSeparation_liftDeletedSide {Z : Finset V}
    {A B : Finset {v : V // v ∉ Z}}
    (hsep : IsVertexSeparation (G.induce {v : V | v ∉ Z}) A B) :
    IsVertexSeparation G (liftDeletedSide Z A) (liftDeletedSide Z B) := by
  constructor
  · ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hvZ : v ∈ Z
    · exact Or.inl (mem_liftDeletedSide.mpr (Or.inl hvZ))
    · have hvAB : (⟨v, hvZ⟩ : {v // v ∉ Z}) ∈ A ∪ B := by rw [hsep.1]; simp
      rcases Finset.mem_union.mp hvAB with hvA | hvB
      · exact Or.inl (mem_liftDeletedSide.mpr (Or.inr ⟨hvZ, hvA⟩))
      · exact Or.inr (mem_liftDeletedSide.mpr (Or.inr ⟨hvZ, hvB⟩))
  · intro a b haA haB hbB hbA hab
    have haZ : a ∉ Z := fun h ↦ haB (mem_liftDeletedSide.mpr (Or.inl h))
    have hbZ : b ∉ Z := fun h ↦ hbA (mem_liftDeletedSide.mpr (Or.inl h))
    have haA' : (⟨a, haZ⟩ : {v // v ∉ Z}) ∈ A := by
      obtain ⟨_, h⟩ := (mem_liftDeletedSide.mp haA).resolve_left haZ
      exact h
    have hbB' : (⟨b, hbZ⟩ : {v // v ∉ Z}) ∈ B := by
      obtain ⟨_, h⟩ := (mem_liftDeletedSide.mp hbB).resolve_left hbZ
      exact h
    exact hsep.2 haA' (fun h ↦ haB (mem_liftDeletedSide.mpr (Or.inr ⟨haZ, h⟩)))
      hbB' (fun h ↦ hbA (mem_liftDeletedSide.mpr (Or.inr ⟨hbZ, h⟩))) hab

omit [Fintype V] in
lemma liftDeletedSide_inter_card (Z : Finset V)
    (A B : Finset {v : V // v ∉ Z}) :
    (liftDeletedSide Z A ∩ liftDeletedSide Z B).card = (A ∩ B).card + Z.card := by
  have heq : liftDeletedSide Z A ∩ liftDeletedSide Z B =
      (A ∩ B).map (Function.Embedding.subtype _) ∪ Z := by
    ext v
    simp only [liftDeletedSide, Finset.mem_inter, Finset.mem_union,
      Finset.mem_map]
    constructor
    · rintro ⟨ha | hz, hb | hz'⟩
      · obtain ⟨a, ha, rfl⟩ := ha
        obtain ⟨b, hb, hab⟩ := hb
        have hba : b = a := (Function.Embedding.subtype _).injective hab
        subst b
        exact Or.inl ⟨a, ⟨ha, hb⟩, rfl⟩
      · exact Or.inr hz'
      · exact Or.inr hz
      · exact Or.inr hz
    · rintro (⟨a, ⟨ha, hb⟩, rfl⟩ | hz)
      · exact ⟨Or.inl ⟨a, ha, rfl⟩, Or.inl ⟨a, hb, rfl⟩⟩
      · exact ⟨Or.inr hz, Or.inr hz⟩
  have hdisj : Disjoint ((A ∩ B).map (Function.Embedding.subtype _)) Z := by
    rw [Finset.disjoint_left]
    intro v hv hZ
    obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hv
    exact w.2 hZ
  rw [heq, Finset.card_union_of_disjoint hdisj, Finset.card_map]

lemma liftDeletedSide_triple_cover {Z : Finset V}
    {A B C : Finset {v : V // v ∉ Z}} (hcover : (A ∪ B) ∪ C = Finset.univ) :
    (liftDeletedSide Z A ∪ liftDeletedSide Z B) ∪ liftDeletedSide Z C = Finset.univ := by
  ext v
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  by_cases hvZ : v ∈ Z
  · exact Or.inl (Or.inl (mem_liftDeletedSide.mpr (Or.inl hvZ)))
  · have hmem : (⟨v, hvZ⟩ : {v // v ∉ Z}) ∈ (A ∪ B) ∪ C := by rw [hcover]; simp
    simp only [Finset.mem_union] at hmem
    rcases hmem with (ha | hb) | hc
    · exact Or.inl (Or.inl (mem_liftDeletedSide.mpr (Or.inr ⟨hvZ, ha⟩)))
    · exact Or.inl (Or.inr (mem_liftDeletedSide.mpr (Or.inr ⟨hvZ, hb⟩)))
    · exact Or.inr (mem_liftDeletedSide.mpr (Or.inr ⟨hvZ, hc⟩))

def VertexTangle.delete {q r : ℕ} (τ : VertexTangle G q) (Z : Finset V)
    (hqr : r + Z.card ≤ q) : VertexTangle (G.induce {v : V | v ∉ Z}) r where
  towards A B := IsVertexSeparation (G.induce {v : V | v ∉ Z}) A B ∧
    (@Inter.inter (Finset _) (@Finset.instInter _ (Classical.decEq _)) A B).card < r ∧
      τ.towards (liftDeletedSide Z A) (liftDeletedSide Z B)
  valid h := ⟨h.1, h.2.1⟩
  orients := by
    intro A B hsep hsmall
    have hlt : (liftDeletedSide Z A ∩ liftDeletedSide Z B).card < q := by
      rw [liftDeletedSide_inter_card]
      omega
    rcases τ.orients (isVertexSeparation_liftDeletedSide hsep) hlt with hAB | hBA
    · exact Or.inl ⟨⟨hsep, hsmall, hAB.1⟩, fun h ↦ hAB.2 h.2.2⟩
    · exact Or.inr ⟨⟨hsep.flip, by simpa only [Finset.inter_comm] using hsmall,
        hBA.1⟩, fun h ↦ hBA.2 h.2.2⟩
  no_triple_cover h₁ h₂ h₃ hcover :=
    τ.no_triple_cover h₁.2.2 h₂.2.2 h₃.2.2 (liftDeletedSide_triple_cover hcover)

end

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
lemma FinsetTouches.mono {A B C D : Finset V} (h : FinsetTouches G A B)
    (hAC : A ⊆ C) (hBD : B ⊆ D) : FinsetTouches G C D := by
  rcases h with h | ⟨a, ha, b, hb, hab⟩
  · exact Or.inl (fun hCD ↦ h (hCD.mono hAC hBD))
  · exact Or.inr ⟨a, hAC ha, b, hBD hb, hab⟩

lemma connected_subset_of_touches_of_externalNeighborhood_subset
    {C T X : Finset V} (hT : (G.induce (T : Set V)).Connected)
    (hTX : Disjoint T X) (hCX : externalNeighborhood G C ⊆ X)
    (hCT : FinsetTouches G C T) : T ⊆ C := by
  have hclose {a b : T} (hab : (G.induce (T : Set V)).Adj a b)
      (ha : a.1 ∈ C) : b.1 ∈ C := by
    by_contra hb
    have hbX := hCX ((mem_externalNeighborhood G C b.1).mpr
      ⟨hb, a.1, ha, hab.symm⟩)
    exact Finset.disjoint_left.mp hTX b.2 hbX
  have hreach {a b : T} (hab : (G.induce (T : Set V)).Reachable a b) :
      a.1 ∈ C → b.1 ∈ C := by
    obtain ⟨p⟩ := hab
    induction p with
    | nil => exact id
    | cons hab p ih => exact fun ha ↦ ih (hclose hab ha)
  have hmeet : ∃ t ∈ T, t ∈ C := by
    rcases hCT with h | ⟨c, hc, t, ht, hct⟩
    · obtain ⟨t, htC, htT⟩ := Finset.not_disjoint_iff.mp h
      exact ⟨t, htT, htC⟩
    · refine ⟨t, ht, ?_⟩
      by_contra htC
      exact Finset.disjoint_left.mp hTX ht
        (hCX ((mem_externalNeighborhood G C t).mpr ⟨htC, c, hc, hct.symm⟩))
  obtain ⟨t, htT, htC⟩ := hmeet
  intro v hv
  exact hreach (hT.preconnected ⟨t, htT⟩ ⟨v, hv⟩) htC

lemma exists_componentVertices_containing_connected
    {T X : Finset V} (hT : (G.induce (T : Set V)).Connected)
    (hTX : Disjoint T X) :
    ∃ c : (G.induce (X : Set V)ᶜ).ConnectedComponent,
      T ⊆ componentVertices G X c := by
  obtain ⟨t⟩ := hT.nonempty
  let f : G.induce (T : Set V) →g G.induce (X : Set V)ᶜ :=
    SimpleGraph.induceHom SimpleGraph.Hom.id (by
      intro v hv
      exact Finset.disjoint_left.mp hTX hv)
  let c := (G.induce (X : Set V)ᶜ).connectedComponentMk (f t)
  refine ⟨c, ?_⟩
  intro v hv
  change v ∈ (componentVertices G X c : Set V)
  rw [coe_componentVertices]
  refine ⟨f ⟨v, hv⟩, ?_, rfl⟩
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff c _).mpr
    (SimpleGraph.ConnectedComponent.sound ((hT.preconnected t ⟨v, hv⟩).map f)).symm

omit [Fintype V] in
lemma bramble_exists_avoiding_set {β : Finset (Finset V)} {q : ℕ}
    (horder : BrambleOrderAtLeast q β) {X : Finset V} (hX : X.card < q) :
    ∃ T ∈ β, Disjoint T X := by
  by_contra hnone
  have hhit : ∀ T ∈ β, ¬ Disjoint X T := by
    intro T hT hXT
    exact hnone ⟨T, hT, hXT.symm⟩
  exact (horder X hhit).not_gt hX

lemma bramble_exists_component {β : Finset (Finset V)}
    (hβ : IsFiniteBramble G β) {q : ℕ} (horder : BrambleOrderAtLeast q β)
    {X : Finset V} (hX : X.card < q) :
    ∃ c : (G.induce (X : Set V)ᶜ).ConnectedComponent,
      ∃ T ∈ β, T ⊆ componentVertices G X c := by
  obtain ⟨T, hT, hTX⟩ := bramble_exists_avoiding_set horder hX
  obtain ⟨c, hc⟩ := exists_componentVertices_containing_connected (hβ.1 T hT) hTX
  exact ⟨c, T, hT, hc⟩

lemma bramble_supersets_touch {β : Finset (Finset V)}
    (hβ : IsFiniteBramble G β) {C D : Finset V}
    (hC : ∃ T ∈ β, T ⊆ C) (hD : ∃ T ∈ β, T ⊆ D) : FinsetTouches G C D := by
  obtain ⟨S, hS, hSC⟩ := hC
  obtain ⟨T, hT, hTD⟩ := hD
  by_cases hST : S = T
  · subst T
    obtain ⟨s⟩ := (hβ.1 S hS).nonempty
    exact Or.inl (fun h ↦ Finset.disjoint_left.mp h (hSC s.2) (hTD s.2))
  · exact (hβ.2 S hS T hT hST).mono hSC hTD

structure BrambleHaven (G : SimpleGraph V) (β : Finset (Finset V)) (q : ℕ) where
  region : {X : Finset V // X.card < q} → Finset V
  connected : ∀ X, (G.induce (region X : Set V)).Connected
  avoids : ∀ X, Disjoint (region X) X.1
  boundary : ∀ X, externalNeighborhood G (region X) ⊆ X.1
  contains : ∀ X, ∃ T ∈ β, T ⊆ region X
  touches : ∀ X Y, FinsetTouches G (region X) (region Y)
  antitone : ∀ X Y, X.1 ⊆ Y.1 → region Y ⊆ region X

theorem exists_brambleHaven {β : Finset (Finset V)} (hβ : IsFiniteBramble G β)
    {q : ℕ} (horder : BrambleOrderAtLeast q β) : Nonempty (BrambleHaven G β q) := by
  let c (X : {X : Finset V // X.card < q}) :=
    Classical.choose (bramble_exists_component hβ horder X.2)
  have hc (X : {X : Finset V // X.card < q}) :
      ∃ T ∈ β, T ⊆ componentVertices G X.1 (c X) :=
    Classical.choose_spec (bramble_exists_component hβ horder X.2)
  refine ⟨{
    region := fun X ↦ componentVertices G X.1 (c X)
    connected := fun X ↦ componentVertices_connected G X.1 (c X)
    avoids := fun X ↦ componentVertices_disjoint_delete G X.1 (c X)
    boundary := fun X ↦ component_externalNeighborhood_subset_delete G X.1 (c X)
    contains := hc
    touches := fun X Y ↦ bramble_supersets_touch hβ (hc X) (hc Y)
    antitone := ?_
  }⟩
  intro X Y hXY
  exact connected_subset_of_touches_of_externalNeighborhood_subset
    (componentVertices_connected G Y.1 (c Y))
    ((componentVertices_disjoint_delete G Y.1 (c Y)).mono_right hXY)
    (component_externalNeighborhood_subset_delete G X.1 (c X))
    (bramble_supersets_touch hβ (hc X) (hc Y))

end

end Erdos73

#print axioms Erdos73Infrastructure.SimpleGraph.Menger.finite_vertex_menger_sharp
#print axioms Erdos73.IsCutLinkedSet.hasDisjointSTPaths
#print axioms Erdos73.exists_nodeWellLinked_minimumBrambleHittingSet
#print axioms Erdos73.VertexTangle.delete
#print axioms Erdos73.exists_brambleHaven
