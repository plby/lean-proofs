/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AvailablePairDegree

/-!
# The three pair stars through an available triangle

Distinct pair stars through one triangle intersect only in that triangle.
Thus, if every nonempty available pair star has size at least `δ`, the union
of the three stars has size at least `3δ - 2`.  This supplies the factor three
in the edge-extension drift equation.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Lower cutoff imposed only on nonempty available pair stars (covered pairs
have empty stars and are irrelevant). -/
def HasAvailablePairFloor
    {V : Type*} [Fintype V] [DecidableEq V]
    (δ : ℕ) (S : GreedyStateOn V) : Prop :=
  ∀ P : Finset V, P.card = 2 →
    (availableTrianglesContainingPair S P).Nonempty →
      δ ≤ (availableTrianglesContainingPair S P).card

/-- If two prescribed pairs together form `U`, then their available extension
stars intersect only at `U`. -/
lemma pairStar_inter_pairStar_subset_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (U : TripleOn V)
    {P Q : Finset V} (hunion : P ∪ Q = U.1) :
    availableTrianglesContainingPair S P ∩
        availableTrianglesContainingPair S Q ⊆ {U} := by
  intro T hT
  have hTP := (mem_availableTrianglesContainingPair_iff.mp
    (mem_inter.mp hT).1).2
  have hTQ := (mem_availableTrianglesContainingPair_iff.mp
    (mem_inter.mp hT).2).2
  have hUT : U.1 ⊆ T.1 := by
    rw [← hunion]
    exact union_subset hTP hTQ
  have hval : U.1 = T.1 :=
    eq_of_subset_of_card_le hUT (by rw [U.2, T.2])
  have hsubtype : T = U := by
    apply Subtype.ext
    exact hval.symm
  simpa [hsubtype]

/-- The three pair stars through an available triangle have union cardinality
at least `3δ - 2`, written without natural-number subtraction. -/
theorem three_mul_pairFloor_le_pairSharing_card_add_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {S : GreedyStateOn V} {δ : ℕ}
    (hfloor : HasAvailablePairFloor δ S)
    {U : TripleOn V} (hU : U ∈ S.available) :
    3 * δ ≤ (S.available ∩ triplesSharingPair U).card + 2 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hUval⟩ := card_eq_three.mp U.2
  let Pxy : Finset V := {x, y}
  let Pxz : Finset V := {x, z}
  let Pyz : Finset V := {y, z}
  let Axy := availableTrianglesContainingPair S Pxy
  let Axz := availableTrianglesContainingPair S Pxz
  let Ayz := availableTrianglesContainingPair S Pyz
  have hPxyCard : Pxy.card = 2 := by simp [Pxy, hxy]
  have hPxzCard : Pxz.card = 2 := by simp [Pxz, hxz]
  have hPyzCard : Pyz.card = 2 := by simp [Pyz, hyz]
  have hPxyU : Pxy ⊆ U.1 := by
    rw [hUval]
    simp [Pxy]
  have hPxzU : Pxz ⊆ U.1 := by
    rw [hUval]
    simp [Pxz]
  have hPyzU : Pyz ⊆ U.1 := by
    rw [hUval]
    simp [Pyz]
  have hUAxy : U ∈ Axy :=
    mem_availableTrianglesContainingPair_iff.mpr ⟨hU, hPxyU⟩
  have hUAxz : U ∈ Axz :=
    mem_availableTrianglesContainingPair_iff.mpr ⟨hU, hPxzU⟩
  have hUAyz : U ∈ Ayz :=
    mem_availableTrianglesContainingPair_iff.mpr ⟨hU, hPyzU⟩
  have hAxyFloor : δ ≤ Axy.card :=
    hfloor Pxy hPxyCard ⟨U, hUAxy⟩
  have hAxzFloor : δ ≤ Axz.card :=
    hfloor Pxz hPxzCard ⟨U, hUAxz⟩
  have hAyzFloor : δ ≤ Ayz.card :=
    hfloor Pyz hPyzCard ⟨U, hUAyz⟩
  have hxy_xz_union : Pxy ∪ Pxz = U.1 := by
    rw [hUval]
    ext w
    simp only [Pxy, Pxz, mem_union, mem_insert, mem_singleton]
    tauto
  have hxy_yz_union : Pxy ∪ Pyz = U.1 := by
    rw [hUval]
    ext w
    simp only [Pxy, Pyz, mem_union, mem_insert, mem_singleton]
    tauto
  have hxz_yz_union : Pxz ∪ Pyz = U.1 := by
    rw [hUval]
    ext w
    simp only [Pxz, Pyz, mem_union, mem_insert, mem_singleton]
    tauto
  have hinterOne : (Axy ∩ Axz).card ≤ 1 := by
    calc
      (Axy ∩ Axz).card ≤ ({U} : Finset (TripleOn V)).card :=
        card_le_card (pairStar_inter_pairStar_subset_singleton
          S U hxy_xz_union)
      _ = 1 := card_singleton U
  have hinterTwo : ((Axy ∪ Axz) ∩ Ayz).card ≤ 1 := by
    apply (card_le_card ?_).trans (show ({U} : Finset (TripleOn V)).card ≤ 1 by simp)
    intro T hT
    rcases mem_union.mp (mem_inter.mp hT).1 with hTAxy | hTAxz
    · exact pairStar_inter_pairStar_subset_singleton S U hxy_yz_union
        (mem_inter.mpr ⟨hTAxy, (mem_inter.mp hT).2⟩)
    · exact pairStar_inter_pairStar_subset_singleton S U hxz_yz_union
        (mem_inter.mpr ⟨hTAxz, (mem_inter.mp hT).2⟩)
  have hunionSub : (Axy ∪ Axz) ∪ Ayz ⊆
      S.available ∩ triplesSharingPair U := by
    intro T hT
    have onePair :
        (T ∈ Axy ∧ Pxy.card = 2 ∧ Pxy ⊆ U.1) ∨
        (T ∈ Axz ∧ Pxz.card = 2 ∧ Pxz ⊆ U.1) ∨
        (T ∈ Ayz ∧ Pyz.card = 2 ∧ Pyz ⊆ U.1) := by
      rcases mem_union.mp hT with hTAB | hTC
      · rcases mem_union.mp hTAB with hTA | hTB
        · exact Or.inl ⟨hTA, hPxyCard, hPxyU⟩
        · exact Or.inr (Or.inl ⟨hTB, hPxzCard, hPxzU⟩)
      · exact Or.inr (Or.inr ⟨hTC, hPyzCard, hPyzU⟩)
    rcases onePair with ⟨hTA, hPcard, hPU⟩ |
        ⟨hTA, hPcard, hPU⟩ | ⟨hTA, hPcard, hPU⟩
    all_goals
      have hmem := mem_availableTrianglesContainingPair_iff.mp hTA
      apply mem_inter.mpr
      refine ⟨hmem.1, mem_triplesSharingPair_iff.mpr ?_⟩
      calc
        2 = _ := hPcard.symm
        _ ≤ (U.1 ∩ T.1).card := card_le_card fun w hw ↦
          mem_inter.mpr ⟨hPU hw, hmem.2 hw⟩
  have hABeq := card_union_add_card_inter Axy Axz
  have hABCeq := card_union_add_card_inter (Axy ∪ Axz) Ayz
  have hunionCard := card_le_card hunionSub
  omega

end

end Erdos207
