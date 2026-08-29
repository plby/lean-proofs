/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteAugmentationEndpointComponent
import ErdosProblems.Erdos599.SliceCandidate

/-!
# A finite endpoint-colour imbalance forces a cross-coloured member

The mixed component in the singular residual exchange contains one more
target-coloured terminal than designated-coloured initial.  This elementary
finite counting lemma turns that imbalance into an actual member: some path
whose initial is not designated has a target-coloured terminal.

The statement is deliberately about one finite warp and arbitrary endpoint
colours.  It is the local Hall-counting step needed before the ordered
selective switch; no ambient separation or safety assertion is hidden here.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteEndpointColourImbalance

open DWeb
open SliceCandidate
open SingularFiniteAugmentationEndpointComponent

universe u

variable {V : Type u}

/-- A finite path family has finite terminal frontier. -/
theorem terminalFrontier_finite_of_finite
    (G : DWeb V) {Y : Set G.DPath} (hY : Y.Finite) :
    (G.terminalFrontier Y).Finite := by
  have himage : (G.terminal? '' Y).Finite := hY.image G.terminal?
  have hpreimage : (some ⁻¹' (G.terminal? '' Y)).Finite :=
    himage.preimage
      (Set.injOn_of_injective (Option.some_injective V))
  apply hpreimage.subset
  rintro x ⟨p, hpY, hpx⟩
  exact ⟨p, hpY, hpx⟩

/-- The terminal frontier of the members starting in `A` is precisely the
part of the whole terminal frontier contributed by such members.  This
small identity is useful when endpoint colours are counted. -/
theorem terminalFrontier_initialPart_eq_image
    (G : DWeb V) (Y : Set G.DPath) (A : Set V) :
    G.terminalFrontier (initialPart G Y A) =
      {x | ∃ p ∈ Y, p.initial ∈ A ∧ G.terminal? p = some x} := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    exact ⟨p, hp.1, hp.2, hpx⟩
  · rintro ⟨p, hpY, hpA, hpx⟩
    exact ⟨p, ⟨hpY, hpA⟩, hpx⟩

/-- If every member ending in the colour `B` starts in the colour `A`, then
there cannot be more `B`-terminals than `A`-initials. -/
theorem ncard_terminalColour_le_initialColour_of_no_cross
    {G : DWeb V} {Y : Set G.DPath} {A B : Set V}
    (hYwarp : G.IsWarp Y) (hYcharacter : G.HasFiniteCharacter Y)
    (hYfinite : Y.Finite)
    (hnoCross : ∀ p ∈ Y, p.initial ∉ A →
      ∀ x, G.terminal? p = some x → x ∉ B) :
    (G.terminalFrontier Y ∩ B).ncard ≤
      (G.initialSet Y ∩ A).ncard := by
  let YA := initialPart G Y A
  have hYAwarp : G.IsWarp YA := fun p hp q hq hpq ↦
    hYwarp hp.1 hq.1 hpq
  have hYAcharacter : G.HasFiniteCharacter YA := fun {_p} hp ↦
    hYcharacter hp.1
  have hterminalSub : G.terminalFrontier Y ∩ B ⊆
      G.terminalFrontier YA := by
    rintro x ⟨⟨p, hpY, hpx⟩, hxB⟩
    have hpA : p.initial ∈ A := by
      by_contra hpA
      exact hnoCross p hpY hpA x hpx hxB
    exact ⟨p, ⟨hpY, hpA⟩, hpx⟩
  have hterminalFinite : (G.terminalFrontier YA).Finite := by
    have hYAfinite : YA.Finite := hYfinite.subset (fun _ hp ↦ hp.1)
    exact terminalFrontier_finite_of_finite G hYAfinite
  have hsubCard : (G.terminalFrontier Y ∩ B).ncard ≤
      (G.terminalFrontier YA).ncard :=
    Set.ncard_le_ncard hterminalSub hterminalFinite
  calc
    (G.terminalFrontier Y ∩ B).ncard
        ≤ (G.terminalFrontier YA).ncard := hsubCard
    _ = (G.initialSet YA).ncard :=
      (ncard_initialSet_eq_terminalFrontier hYAwarp hYAcharacter).symm
    _ = (G.initialSet Y ∩ A).ncard := by
      rw [initialSet_initialPart]

/-- Strict endpoint-colour imbalance produces a concrete cross-coloured
finite member. -/
theorem exists_crossColouredPath_of_ncard_lt
    {G : DWeb V} {Y : Set G.DPath} {A B : Set V}
    (hYwarp : G.IsWarp Y) (hYcharacter : G.HasFiniteCharacter Y)
    (hYfinite : Y.Finite)
    (hcard : (G.initialSet Y ∩ A).ncard <
      (G.terminalFrontier Y ∩ B).ncard) :
    ∃ p ∈ Y, p.initial ∉ A ∧
      ∃ q : DirectedPath.FinitePath G.graph,
        p = .inl q ∧ q.finish ∈ B := by
  by_contra hcross
  push_neg at hcross
  have hnoCross : ∀ p ∈ Y, p.initial ∉ A →
      ∀ x, G.terminal? p = some x → x ∉ B := by
    intro p hpY hpA x hpx hxB
    obtain ⟨q, rfl⟩ := hYcharacter hpY
    exact hcross (.inl q) hpY hpA q rfl
      (Option.some.inj hpx ▸ hxB)
  exact (not_lt_of_ge
    (ncard_terminalColour_le_initialColour_of_no_cross
      hYwarp hYcharacter hYfinite hnoCross)) hcard

/-- With equal numbers of `A`-initials and `B`-terminals, a path crossing
from `A` to the complement of `B` forces a path crossing in the opposite
direction. -/
theorem exists_oppositeCrossColouredPath_of_ncard_eq
    {G : DWeb V} {Y : Set G.DPath} {A B : Set V}
    (hYwarp : G.IsWarp Y) (hYcharacter : G.HasFiniteCharacter Y)
    (hYfinite : Y.Finite)
    (hcard : (G.initialSet Y ∩ A).ncard =
      (G.terminalFrontier Y ∩ B).ncard)
    (hbad : ∃ p ∈ Y, p.initial ∈ A ∧
      ∃ q : DirectedPath.FinitePath G.graph,
        p = .inl q ∧ q.finish ∉ B) :
    ∃ p ∈ Y, p.initial ∉ A ∧
      ∃ q : DirectedPath.FinitePath G.graph,
        p = .inl q ∧ q.finish ∈ B := by
  by_contra hcross
  push_neg at hcross
  let YA := initialPart G Y A
  have hYAwarp : G.IsWarp YA := fun p hp q hq hpq ↦
    hYwarp hp.1 hq.1 hpq
  have hYAcharacter : G.HasFiniteCharacter YA := fun {_p} hp ↦
    hYcharacter hp.1
  have hYAfinite : YA.Finite := hYfinite.subset (fun _ hp ↦ hp.1)
  have hterminalEq : G.terminalFrontier Y ∩ B =
      G.terminalFrontier YA ∩ B := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨p, hpY, hpx⟩, hxB⟩
      have hpA : p.initial ∈ A := by
        by_contra hpA
        obtain ⟨q, rfl⟩ := hYcharacter hpY
        exact hcross (.inl q) hpY hpA q rfl
          (Option.some.inj hpx ▸ hxB)
      exact ⟨⟨p, ⟨hpY, hpA⟩, hpx⟩, hxB⟩
    · rintro x ⟨⟨p, hpYA, hpx⟩, hxB⟩
      exact ⟨⟨p, hpYA.1, hpx⟩, hxB⟩
  obtain ⟨p, hpY, hpA, q, rfl, hqNotB⟩ := hbad
  have hqTerminal : q.finish ∈ G.terminalFrontier YA :=
    ⟨.inl q, ⟨hpY, hpA⟩, rfl⟩
  have hproper : G.terminalFrontier YA ∩ B ⊂
      G.terminalFrontier YA := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_left, ?_⟩
    intro heq
    have : q.finish ∈ G.terminalFrontier YA ∩ B := heq.symm ▸ hqTerminal
    exact hqNotB this.2
  have htermLt : (G.terminalFrontier YA ∩ B).ncard <
      (G.terminalFrontier YA).ncard :=
    Set.ncard_lt_ncard hproper
      (terminalFrontier_finite_of_finite G hYAfinite)
  have hinitEq : G.initialSet YA = G.initialSet Y ∩ A :=
    initialSet_initialPart G Y A
  have hcountYA : (G.initialSet Y ∩ A).ncard =
      (G.terminalFrontier YA).ncard := by
    rw [← hinitEq]
    exact ncard_initialSet_eq_terminalFrontier hYAwarp hYAcharacter
  have hcontradiction : (G.terminalFrontier Y ∩ B).ncard <
      (G.initialSet Y ∩ A).ncard := by
    rw [hterminalEq, hcountYA]
    exact htermLt
  rw [hcard] at hcontradiction
  exact (lt_irrefl _ hcontradiction)

/-- Adding one fresh initial outside `A` and one fresh terminal outside `B`
preserves the equality of the two coloured endpoint counts.  Consequently a
new `A`-to-non-`B` member forces a non-`A`-to-`B` member. -/
theorem exists_oppositeCrossColouredPath_of_fresh_boundary
    {G : DWeb V} {W Y : Set G.DPath} {A B : Set V} {a b : V}
    (hYwarp : G.IsWarp Y) (hYcharacter : G.HasFiniteCharacter Y)
    (hYfinite : Y.Finite)
    (haA : a ∉ A) (hbB : b ∉ B)
    (hinitial : G.initialSet Y = insert a (G.initialSet W))
    (hterminal : G.terminalFrontier Y =
      insert b (G.terminalFrontier W))
    (hOldCount : (G.initialSet W ∩ A).ncard =
      (G.terminalFrontier W ∩ B).ncard)
    (hbad : ∃ p ∈ Y, p.initial ∈ A ∧
      ∃ q : DirectedPath.FinitePath G.graph,
        p = .inl q ∧ q.finish ∉ B) :
    ∃ p ∈ Y, p.initial ∉ A ∧
      ∃ q : DirectedPath.FinitePath G.graph,
        p = .inl q ∧ q.finish ∈ B := by
  have hinitColour : G.initialSet Y ∩ A =
      G.initialSet W ∩ A := by
    rw [hinitial]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨rfl | hxW, hxA⟩
      · exact False.elim (haA hxA)
      · exact ⟨hxW, hxA⟩
    · rintro ⟨hxW, hxA⟩
      exact ⟨Or.inr hxW, hxA⟩
  have hterminalColour : G.terminalFrontier Y ∩ B =
      G.terminalFrontier W ∩ B := by
    rw [hterminal]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨rfl | hxW, hxB⟩
      · exact False.elim (hbB hxB)
      · exact ⟨hxW, hxB⟩
    · rintro ⟨hxW, hxB⟩
      exact ⟨Or.inr hxW, hxB⟩
  apply exists_oppositeCrossColouredPath_of_ncard_eq
    hYwarp hYcharacter hYfinite
  · rw [hinitColour, hterminalColour]
    exact hOldCount
  · exact hbad

#print axioms terminalFrontier_initialPart_eq_image
#print axioms ncard_terminalColour_le_initialColour_of_no_cross
#print axioms exists_crossColouredPath_of_ncard_lt
#print axioms exists_oppositeCrossColouredPath_of_ncard_eq
#print axioms exists_oppositeCrossColouredPath_of_fresh_boundary

end SingularFiniteEndpointColourImbalance
end CardinalInduction
end Erdos599
