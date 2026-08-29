/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteCompleteWordInteriorDefect

/-!
# Exact finite counting of aggregate safe-word defects

For a finite complete safe-word family the union forward and backward
balances have equal total sum. Every nonzero difference is `1` or `-1`.
Consequently the positive and negative defect counts are equal, including
their partition into reference-interior and exterior vertices.

The exterior Hall inequality is therefore equivalent to the opposite
interior-defect inequality. This file does not supply that nonlocal
inequality or silently assume the required saturation exchange argument.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

def familyDefect (A : Set (FiniteColouredOccurrenceWord W Y)) (x : V) : Int :=
  edgeBalance (familyForwardEdges A) x - edgeBalance (familyBackwardEdges A) x

private theorem balance_cases (E : Set (V × V)) (x : V) :
    edgeBalance E x = -1 ∨ edgeBalance E x = 0 ∨ edgeBalance E x = 1 := by
  by_cases hout : HasOutgoing E x <;> by_cases hin : HasIncoming E x <;>
    simp [edgeBalance, propInt, hout, hin]

/-- Completeness removes the possible magnitude-two difference at removed
boundaries; this is not true for arbitrary families of unfinished prefixes. -/
theorem familyDefect_cases
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {A : Set (FiniteColouredOccurrenceWord W Y)}
    (hsafe : ∀ Q ∈ A, Q.IsIntervalSafe)
    (hends : ∀ Q ∈ A, Q.vertex 0 ∉ Gamma.vertexSet Y ∧
      Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y) (x : V) :
    familyDefect A x = -1 ∨ familyDefect A x = 0 ∨ familyDefect A x = 1 := by
  rcases balance_cases (familyBackwardEdges A) x with hR | hR | hR
  · have hF := family_forward_negative_of_backward_negative hW hY hYfin hsafe hends hR
    exact Or.inr (Or.inl (by simp [familyDefect, hF, hR]))
  · simpa only [familyDefect, hR, sub_zero] using balance_cases (familyForwardEdges A) x
  · have hF := family_forward_positive_of_backward_positive hW hY hYfin hsafe hends hR
    exact Or.inr (Or.inl (by simp [familyDefect, hF, hR]))

/-- The balance difference has zero sum on any finite carrier of all the
actual forward and removed edges. -/
theorem sum_familyDefect_eq_zero
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {A : Set (FiniteColouredOccurrenceWord W Y)} (hA : A.Finite)
    (C : Finset V)
    (hC : ∀ e ∈ familyForwardEdges A ∪ familyBackwardEdges A,
      e.1 ∈ C ∧ e.2 ∈ C) : ∑ x ∈ C, familyDefect A x = 0 := by
  simp only [familyDefect, Finset.sum_sub_distrib]
  rw [sum_edgeBalance_eq_zero (familyForwardEdges_finite hA)
      (familyForwardEdges_biUnique hW A) C (fun e he ↦ hC e (Or.inl he)),
    sum_edgeBalance_eq_zero (familyBackwardEdges_finite hA)
      (familyBackwardEdges_biUnique hY A) C (fun e he ↦ hC e (Or.inr he))]
  rfl

private theorem sum_indicator_eq_card (C : Finset V) (P : V → Prop) [DecidablePred P] :
    (∑ x ∈ C, propInt (P x)) = ((C.filter P).card : Int) := by
  classical
  induction C using Finset.induction_on with
  | empty => simp
  | @insert x C hx ih =>
      rw [Finset.sum_insert hx, Finset.filter_insert]
      by_cases hP : P x
      · rw [if_pos hP, Finset.card_insert_of_notMem
          (fun h ↦ hx (Finset.mem_filter.mp h).1), ih]
        simp [propInt, hP]
        omega
      · rw [if_neg hP, ih]
        simp [propInt, hP]

/-- Positive and negative aggregate defects have exactly equal cardinality
on the finite carrier. -/
theorem card_positiveDefect_eq_card_negativeDefect
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {A : Set (FiniteColouredOccurrenceWord W Y)} (hA : A.Finite)
    (hsafe : ∀ Q ∈ A, Q.IsIntervalSafe)
    (hends : ∀ Q ∈ A, Q.vertex 0 ∉ Gamma.vertexSet Y ∧
      Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y)
    (C : Finset V)
    (hC : ∀ e ∈ familyForwardEdges A ∪ familyBackwardEdges A,
      e.1 ∈ C ∧ e.2 ∈ C) :
    (C.filter (fun x ↦ familyDefect A x = 1)).card =
      (C.filter (fun x ↦ familyDefect A x = -1)).card := by
  classical
  have hsum := sum_familyDefect_eq_zero hW hY hA C hC
  have hpoint : ∀ x, familyDefect A x =
      propInt (familyDefect A x = 1) - propInt (familyDefect A x = -1) := by
    intro x
    rcases familyDefect_cases hW hY hYfin hsafe hends x with hx | hx | hx <;>
      simp [hx, propInt]
  have hcounts : (∑ x ∈ C, familyDefect A x) =
      ((C.filter (fun x ↦ familyDefect A x = 1)).card : Int) -
        ((C.filter (fun x ↦ familyDefect A x = -1)).card : Int) := by
    calc
      _ = ∑ x ∈ C,
          (propInt (familyDefect A x = 1) - propInt (familyDefect A x = -1)) := by
        exact Finset.sum_congr rfl (fun x _ ↦ hpoint x)
      _ = _ := by
        rw [Finset.sum_sub_distrib, sum_indicator_eq_card, sum_indicator_eq_card]
  omega

/-- There is an actual finite carrier of every nonzero defect, obtained
from the endpoints of the finite union edge relation. -/
theorem exists_finite_defectCarrier
    {A : Set (FiniteColouredOccurrenceWord W Y)} (hA : A.Finite) :
    ∃ C : Finset V,
      (∀ e ∈ familyForwardEdges A ∪ familyBackwardEdges A,
        e.1 ∈ C ∧ e.2 ∈ C) ∧
      (∀ x, x ∉ C → familyDefect A x = 0) := by
  classical
  let E := familyForwardEdges A ∪ familyBackwardEdges A
  have hE : E.Finite := (familyForwardEdges_finite hA).union (familyBackwardEdges_finite hA)
  let C := (hE.image Prod.fst).toFinset ∪ (hE.image Prod.snd).toFinset
  have hC : ∀ e ∈ E, e.1 ∈ C ∧ e.2 ∈ C := by
    intro e he
    constructor
    · apply Finset.mem_union_left
      simpa using (show e.1 ∈ Prod.fst '' E from ⟨e, he, rfl⟩)
    · apply Finset.mem_union_right
      simpa using (show e.2 ∈ Prod.snd '' E from ⟨e, he, rfl⟩)
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hzero : ∀ K : Set (V × V), K ⊆ E → edgeBalance K x = 0 := by
    intro K hKE
    have hout : ¬HasOutgoing K x := by
      rintro ⟨y, hy⟩
      exact hx (hC (x, y) (hKE hy)).1
    have hin : ¬HasIncoming K x := by
      rintro ⟨y, hy⟩
      exact hx (hC (y, x) (hKE hy)).2
    simp [edgeBalance, hout, hin]
  simp only [familyDefect, hzero _ Set.subset_union_left,
    hzero _ Set.subset_union_right, sub_self]

/-- Exact decomposition of the equal positive/negative counts into an
arbitrary interior set and its exterior. In the Hall application `S` is
the reference carrier. -/
theorem split_defect_card_identity
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {A : Set (FiniteColouredOccurrenceWord W Y)} (hA : A.Finite)
    (hsafe : ∀ Q ∈ A, Q.IsIntervalSafe)
    (hends : ∀ Q ∈ A, Q.vertex 0 ∉ Gamma.vertexSet Y ∧
      Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y)
    (C : Finset V)
    (hC : ∀ e ∈ familyForwardEdges A ∪ familyBackwardEdges A,
      e.1 ∈ C ∧ e.2 ∈ C)
    (S : Set V) [DecidablePred (· ∈ S)] :
    let P := C.filter (fun x ↦ familyDefect A x = 1)
    let N := C.filter (fun x ↦ familyDefect A x = -1)
    (P.filter (fun x ↦ x ∉ S)).card + (P.filter (fun x ↦ x ∈ S)).card =
      (N.filter (fun x ↦ x ∉ S)).card + (N.filter (fun x ↦ x ∈ S)).card := by
  classical
  dsimp only
  let P := C.filter (fun x ↦ familyDefect A x = 1)
  let N := C.filter (fun x ↦ familyDefect A x = -1)
  have hP := Finset.card_filter_add_card_filter_not (s := P) (fun x ↦ x ∈ S)
  have hN := Finset.card_filter_add_card_filter_not (s := N) (fun x ↦ x ∈ S)
  have hPN : P.card = N.card :=
    card_positiveDefect_eq_card_negativeDefect hW hY hYfin hA hsafe hends C hC
  change (P.filter (fun x ↦ x ∉ S)).card + (P.filter (fun x ↦ x ∈ S)).card =
    (N.filter (fun x ↦ x ∉ S)).card + (N.filter (fun x ↦ x ∈ S)).card
  omega

/-- Counting alone reduces the exterior Hall inequality to the reverse
inequality on interior defects. The latter is not assumed to hold. -/
theorem exterior_defect_inequality_iff_interior
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {A : Set (FiniteColouredOccurrenceWord W Y)} (hA : A.Finite)
    (hsafe : ∀ Q ∈ A, Q.IsIntervalSafe)
    (hends : ∀ Q ∈ A, Q.vertex 0 ∉ Gamma.vertexSet Y ∧
      Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y)
    (C : Finset V)
    (hC : ∀ e ∈ familyForwardEdges A ∪ familyBackwardEdges A,
      e.1 ∈ C ∧ e.2 ∈ C)
    (S : Set V) [DecidablePred (· ∈ S)] :
    let P := C.filter (fun x ↦ familyDefect A x = 1)
    let N := C.filter (fun x ↦ familyDefect A x = -1)
    (P.filter (fun x ↦ x ∉ S)).card ≤ (N.filter (fun x ↦ x ∉ S)).card ↔
      (N.filter (fun x ↦ x ∈ S)).card ≤ (P.filter (fun x ↦ x ∈ S)).card := by
  have h := split_defect_card_identity hW hY hYfin hA hsafe hends C hC S
  dsimp only at h ⊢
  omega

#print axioms familyDefect_cases
#print axioms sum_familyDefect_eq_zero
#print axioms card_positiveDefect_eq_card_negativeDefect
#print axioms exists_finite_defectCarrier
#print axioms split_defect_card_identity
#print axioms exterior_defect_inequality_iff_interior

end Erdos599.Alternating.FiniteColouredOccurrenceWord
