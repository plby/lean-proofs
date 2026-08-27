/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedTwoAwayWitness
import ErdosProblems.Erdos207.SelectedWitnessImage

/-! # Localized deleted vertices are an image of selected two-away witnesses -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def localizedTwoAwayThirdVertex
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {T : TripleOn V} {a b : V} {U : Finset V}
    (w : LocalizedTwoAwayWitness V F T a b U) : V := Classical.choose w.2.2.2

theorem localizedTwoAwayThirdVertex_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {T : TripleOn V} {a b : V} {U : Finset V}
    (hab : a ≠ b) (w : LocalizedTwoAwayWitness V F T a b U)
    (u : V) (hu : u ∈ w.1.1.2.1) (hua : u ≠ a) (hub : u ≠ b) :
    localizedTwoAwayThirdVertex w = u := by
  have hx := Classical.choose_spec w.2.2.2
  have h₁ := thirdVertexTriple_eq_of_mem hab w.1.1.2 w.2.1 w.2.2.1 hx.1 hx.2.2.1 hx.2.2.2
  have h₂ := thirdVertexTriple_eq_of_mem hab w.1.1.2 w.2.1 w.2.2.1 hu hua hub
  exact congrArg Subtype.val (thirdVertexTriple_injective hab (h₁.trans h₂.symm))

def localizedTwoAwaySelectedVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (T : TripleOn V)
    (a b : V) (U : Finset V) : Finset V :=
  selectedWitnessImage
    (fun w : LocalizedTwoAwayWitness V F T a b U ↦ localizedTwoAwayRemainder w)
    localizedTwoAwayThirdVertex P

theorem mem_localizedTwoAwaySelectedVertices_of_twoAway
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V} {T T' : TripleOn V}
    {a b u : V} {U : Finset V} (hab : a ≠ b)
    (haT : a ∈ T'.1) (hbT : b ∈ T'.1) (huT : u ∈ T'.1)
    (huU : u ∈ U) (hua : u ≠ a) (hub : u ≠ b)
    (htwo : T' ∈ twoAwayForbiddenTriangles F P T) :
    u ∈ localizedTwoAwaySelectedVertices F P T a b U := by
  obtain ⟨hne, C, hCF, hT'C, hTC, hrem⟩ := mem_twoAwayForbiddenTriangles_iff.mp htwo
  let w : LocalizedTwoAwayWitness V F T a b U :=
    ⟨⟨(C, T'), hCF, hT'C, hTC, hne⟩, haT, hbT, u, huT, huU, hua, hub⟩
  exact mem_selectedWitnessImage.mpr ⟨w, hrem, localizedTwoAwayThirdVertex_eq hab w u huT hua hub⟩

theorem card_localizedTwoAwaySelectedVertices_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (T : TripleOn V)
    (a b : V) (U : Finset V) :
    ((localizedTwoAwaySelectedVertices F P T a b U).card : ℝ≥0) ≤
      selectedCount (fun w : LocalizedTwoAwayWitness V F T a b U ↦ localizedTwoAwayRemainder w) P :=
  card_selectedWitnessImage_le_selectedCount _ _ P

end

end Erdos207
