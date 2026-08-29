/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceResidualRoute
import ErdosProblems.Erdos599.FiniteColouredOccurrenceCrossSplice

/-!
# Source-changing cross-splice at a residual inherited edge

At an inherited edge, a later reduced-warp word traverses the edge forward
while the raw reverse residual route traverses it backward.  Cutting just
before/after these opposite occurrences and swapping suffixes removes both
occurrences and exchanges the two outer terminals.

The certified residual reduction automatically supplies all forward-colour
freshness.  The two genuinely nonlocal obligations are left explicit: no
backward-colour collision may cross either cut.  These are exactly the
conditions which an extremal-pivot/owner-gap argument must establish; no
interval-safeness conclusion is postulated here.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath
open ColouredResidualPortReduction

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {W U Y : Set Gamma.DPath}

private abbrev residualRoute
    (P : FinitePath (residualPortDigraph W Y)) :=
  ofResidualReductionPath P

private theorem familyEdges_subset_union_left
    (W U : Set Gamma.DPath) : familyEdges W ⊆ familyEdges (W ∪ U) := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hp, hep⟩ := he
  exact ⟨p, Or.inl hp, hep⟩

private theorem familyEdges_subset_union_right
    (W U : Set Gamma.DPath) : familyEdges U ⊆ familyEdges (W ∪ U) := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hp, hep⟩ := he
  exact ⟨p, Or.inr hp, hep⟩

private theorem pivot_meets_left
    (P : FinitePath (residualPortDigraph W Y))
    (Q : FiniteColouredOccurrenceWord U Y)
    (i : Fin Q.length) (k : (residualRoute P).BackwardIndex)
    (hi : Q.direction i = .forward)
    (he : Q.actualEdge i = (residualRoute P).backwardEdge k) :
    Q.vertex i.castSucc = (residualRoute P).vertex k.1.succ := by
  have hpair :
      (Q.vertex i.castSucc, Q.vertex i.succ) =
        ((residualRoute P).vertex k.1.succ,
          (residualRoute P).vertex k.1.castSucc) := by
    simpa [FiniteColouredOccurrenceWord.actualEdge,
      FiniteColouredOccurrenceWord.backwardEdge, hi,
      (residualRoute P).backwardIndex_direction k] using he
  exact congrArg Prod.fst hpair

private theorem pivot_meets_right
    (P : FinitePath (residualPortDigraph W Y))
    (Q : FiniteColouredOccurrenceWord U Y)
    (i : Fin Q.length) (k : (residualRoute P).BackwardIndex)
    (hi : Q.direction i = .forward)
    (he : Q.actualEdge i = (residualRoute P).backwardEdge k) :
    (residualRoute P).vertex k.1.castSucc = Q.vertex i.succ := by
  have hpair :
      (Q.vertex i.castSucc, Q.vertex i.succ) =
        ((residualRoute P).vertex k.1.succ,
          (residualRoute P).vertex k.1.castSucc) := by
    simpa [FiniteColouredOccurrenceWord.actualEdge,
      FiniteColouredOccurrenceWord.backwardEdge, hi,
      (residualRoute P).backwardIndex_direction k] using he
  exact (congrArg Prod.snd hpair).symm

/-- Keep the later word's prefix before the inherited forward occurrence and
attach the residual route after its opposite backward occurrence. -/
def residualPivotLeft
    (P : FinitePath (residualPortDigraph W Y))
    (Q : FiniteColouredOccurrenceWord U Y)
    (hUE : familyEdges U ⊆
      (familyEdges W \ ColouredResidualPortReduction.backwardEdges P) ∪
        ColouredResidualPortReduction.forwardEdges P)
    (i : Fin Q.length) (k : (residualRoute P).BackwardIndex)
    (hi : Q.direction i = .forward)
    (he : Q.actualEdge i = (residualRoute P).backwardEdge k)
    (hbackward : Disjoint (Q.prefixAt i.castSucc).backwardEdges
      ((residualRoute P).suffixFrom k.1.succ).backwardEdges) :
    FiniteColouredOccurrenceWord (W ∪ U) Y :=
  let Qpre : FiniteColouredOccurrenceWord (W ∪ U) Y :=
    (Q.prefixAt i.castSucc).retypeForward
      ((Q.prefixAt_forwardEdges_subset i.castSucc).trans
        (Q.forwardEdges_subset_familyEdges.trans
          (familyEdges_subset_union_right W U)))
  let Hsuf : FiniteColouredOccurrenceWord (W ∪ U) Y :=
    ((residualRoute P).suffixFrom k.1.succ).retypeForward
      (((residualRoute P).suffixFrom_forwardEdges_subset k.1.succ).trans
        ((residualRoute P).forwardEdges_subset_familyEdges.trans
          (familyEdges_subset_union_left W U)))
  Qpre.append Hsuf
    (by
      change (Q.prefixAt i.castSucc).vertex
          (Fin.last (Q.prefixAt i.castSucc).length) =
        ((residualRoute P).suffixFrom k.1.succ).vertex 0
      rw [prefixAt_last, suffixFrom_first]
      exact pivot_meets_left P Q i k hi he)
    (by
      simpa [Qpre, Hsuf] using
        (ofResidualReductionPath_forwardEdges_disjoint_later P Q hUE).symm.mono
          (Q.prefixAt_forwardEdges_subset i.castSucc)
          ((residualRoute P).suffixFrom_forwardEdges_subset k.1.succ))
    (by simpa [Qpre, Hsuf] using hbackward)

/-- Keep the residual route's prefix before the opposite backward occurrence
and attach the later word after its inherited forward occurrence. -/
def residualPivotRight
    (P : FinitePath (residualPortDigraph W Y))
    (Q : FiniteColouredOccurrenceWord U Y)
    (hUE : familyEdges U ⊆
      (familyEdges W \ ColouredResidualPortReduction.backwardEdges P) ∪
        ColouredResidualPortReduction.forwardEdges P)
    (i : Fin Q.length) (k : (residualRoute P).BackwardIndex)
    (hi : Q.direction i = .forward)
    (he : Q.actualEdge i = (residualRoute P).backwardEdge k)
    (hbackward : Disjoint
      ((residualRoute P).prefixAt k.1.castSucc).backwardEdges
      (Q.suffixFrom i.succ).backwardEdges) :
    FiniteColouredOccurrenceWord (W ∪ U) Y :=
  let Hpre : FiniteColouredOccurrenceWord (W ∪ U) Y :=
    ((residualRoute P).prefixAt k.1.castSucc).retypeForward
      (((residualRoute P).prefixAt_forwardEdges_subset k.1.castSucc).trans
        ((residualRoute P).forwardEdges_subset_familyEdges.trans
          (familyEdges_subset_union_left W U)))
  let Qsuf : FiniteColouredOccurrenceWord (W ∪ U) Y :=
    (Q.suffixFrom i.succ).retypeForward
      ((Q.suffixFrom_forwardEdges_subset i.succ).trans
        (Q.forwardEdges_subset_familyEdges.trans
          (familyEdges_subset_union_right W U)))
  Hpre.append Qsuf
    (by
      change ((residualRoute P).prefixAt k.1.castSucc).vertex
          (Fin.last ((residualRoute P).prefixAt k.1.castSucc).length) =
        (Q.suffixFrom i.succ).vertex 0
      rw [prefixAt_last, suffixFrom_first]
      exact pivot_meets_right P Q i k hi he)
    (by
      simpa [Hpre, Qsuf] using
        (ofResidualReductionPath_forwardEdges_disjoint_later P Q hUE).mono
          ((residualRoute P).prefixAt_forwardEdges_subset k.1.castSucc)
          (Q.suffixFrom_forwardEdges_subset i.succ))
    (by simpa [Hpre, Qsuf] using hbackward)

#print axioms residualPivotLeft
#print axioms residualPivotRight

end Erdos599.Alternating.FiniteColouredOccurrenceWord
