/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceWord

/-!
# Finitely many coloured occurrence words on a finite carrier

Repeated vertices are allowed, but colour-edge freshness gives a uniform
length bound. Recording the length and padded vertex/direction arrays then
embeds all words on a finite carrier into one finite type. This is the
local finite-branching input for the safe-prefix tree, not a claim that
ordinary unsafe chronological prefixes preserve interval safety.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

private def directionCode : Direction → Bool
  | .forward => true
  | .backward => false

private theorem directionCode_injective : Function.Injective directionCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [directionCode]

/-- Same-colour edge freshness bounds length by the finite coloured
ordered-pair alphabet of the carrier. -/
theorem length_le_card_colouredCarrier
    (C : Set V) [Fintype C] (Q : FiniteColouredOccurrenceWord W Y)
    (hQ : Q.vertexSet ⊆ C) :
    Q.length ≤ Fintype.card (Bool × C × C) := by
  let f : Fin Q.length → Bool × C × C := fun i ↦
    (directionCode (Q.direction i),
      ⟨Q.vertex i.castSucc, hQ ⟨i.castSucc, rfl⟩⟩,
      ⟨Q.vertex i.succ, hQ ⟨i.succ, rfl⟩⟩)
  have hf : Function.Injective f := by
    intro i j hij
    have hd : Q.direction i = Q.direction j :=
      directionCode_injective (congrArg Prod.fst hij)
    have hleft : Q.vertex i.castSucc = Q.vertex j.castSucc :=
      congrArg (fun z : Bool × C × C ↦ z.2.1.1) hij
    have hright : Q.vertex i.succ = Q.vertex j.succ :=
      congrArg (fun z : Bool × C × C ↦ z.2.2.1) hij
    apply Q.occurrence_injective
    apply Prod.ext hd
    change Q.actualEdge i = Q.actualEdge j
    simp only [actualEdge, hd, hleft, hright]
  simpa using Fintype.card_le_of_injective f hf

/-- Finiteness of the carrier implies finiteness of the set of all literal
coloured occurrence words supported there, without vertex injectivity. -/
theorem finite_setOf_vertexSet_subset
    (C : Set V) (hC : C.Finite) :
    {Q : FiniteColouredOccurrenceWord W Y | Q.vertexSet ⊆ C}.Finite := by
  classical
  let : Fintype C := hC.fintype
  let N := Fintype.card (Bool × C × C)
  let Words := {Q : FiniteColouredOccurrenceWord W Y // Q.vertexSet ⊆ C}
  let Code := Fin (N + 1) ×
    (Fin (N + 1) → Option C) × (Fin (N + 1) → Option Bool)
  let encode : Words → Code := fun Q ↦
    (⟨Q.1.length, Nat.lt_succ_iff.mpr
        (length_le_card_colouredCarrier C Q.1 Q.2)⟩,
      (fun i ↦ if hi : i.1 < Q.1.length + 1 then
        some ⟨Q.1.vertex ⟨i.1, hi⟩, Q.2 ⟨⟨i.1, hi⟩, rfl⟩⟩ else none),
      (fun i ↦ if hi : i.1 < Q.1.length then
        some (directionCode (Q.1.direction ⟨i.1, hi⟩)) else none))
  have hencode : Function.Injective encode := by
    rintro ⟨⟨n, v, d, hs, hi⟩, hvC⟩ ⟨⟨m, w, e, ht, hj⟩, hwC⟩ h
    have hnm : n = m := congrArg (fun z : Code ↦ z.1.1) h
    subst m
    have hnN : n ≤ N :=
      length_le_card_colouredCarrier C ⟨n, v, d, hs, hi⟩ hvC
    have hvw : v = w := by
      funext i
      let j : Fin (N + 1) := ⟨i.1,
        i.2.trans_le (Nat.add_le_add_right hnN 1)⟩
      have hentry := congrArg (fun z : Code ↦ z.2.1 j) h
      dsimp only [encode] at hentry
      simp only [j, dif_pos i.2] at hentry
      exact congrArg Subtype.val (Option.some.inj hentry)
    have hde : d = e := by
      funext i
      let j : Fin (N + 1) := ⟨i.1, i.2.trans (Nat.lt_succ_of_le hnN)⟩
      have hentry := congrArg (fun z : Code ↦ z.2.2 j) h
      dsimp only [encode] at hentry
      simp only [j, dif_pos i.2] at hentry
      exact directionCode_injective (Option.some.inj hentry)
    subst w
    subst e
    rfl
  change Finite Words
  exact Finite.of_injective encode hencode

#print axioms length_le_card_colouredCarrier
#print axioms finite_setOf_vertexSet_subset

end Erdos599.Alternating.FiniteColouredOccurrenceWord
