/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.NondegenerateHammockRows
import ErdosProblems.Erdos599.HalfwayMovingGlobalClosure

/-!
# Small dynamic ordinary and nondegenerate hammock closure

Starting from a small seed inside a global reservoir, this module closes
simultaneously under ordinary maximal hammocks, filtered nondegenerate
maximal hammocks, and full reference paths.  Endpoint pairs are selected
from the current omega stage, so pairs which become eligible later are not
missed.  No uniform containment of arbitrary safe paths is assumed.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

private theorem joint_mk_iUnion_le_of_le {I X : Type u} {f : I → Set X}
    (hkappa : aleph0 ≤ kappa) (hI : #I ≤ kappa)
    (hf : ∀ i, #(f i) ≤ kappa) : #(⋃ i, f i) ≤ kappa := by
  refine (Cardinal.mk_iUnion_le f).trans ?_
  exact Cardinal.mul_le_of_le hkappa hI (ciSup_le' hf)

private theorem joint_mk_union_le_of_le {A B : Set V}
    (hkappa : aleph0 ≤ kappa) (hA : #A ≤ kappa) (hB : #B ≤ kappa) :
    #(A ∪ B : Set V) ≤ kappa :=
  (Cardinal.mk_union_le A B).trans
    (Cardinal.add_le_of_le hkappa hA hB)

/-- The jointly closed small carrier extracted from a globally closed
reservoir. -/
structure JointDynamicHammockClosure
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (globalZ X0 innerRoof roof : Set V) where
  closedSet : Set V
  seed_subset : X0 ⊆ closedSet
  subset_global : closedSet ⊆ globalZ
  card_le : #closedSet ≤ kappa
  hammock_closed : HammockClosedUpTo Gamma Y closedSet closedSet
    innerRoof roof kappa
  nondegenerate_closed : NondegenerateHammockClosedUpTo Gamma Y closedSet
    closedSet innerRoof roof kappa
  reference_closed : ClosedUnderPaths Gamma Y closedSet

namespace JointDynamicHammockClosure

/-- Extract a small dynamic subclosure from a reservoir which already
contains both kinds of selected maximal hammocks and is reference-closed. -/
theorem exists_of_globalClosures
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (globalZ X0 innerRoof roof : Set V)
    (hkappa : aleph0 ≤ kappa)
    (hY : Gamma.IsWarp Y)
    (hGlobalHammocks : HammockClosedUpTo Gamma Y globalZ globalZ
      innerRoof roof kappa)
    (hGlobalNondegenerate : NondegenerateHammockClosedUpTo Gamma Y
      globalZ globalZ innerRoof roof kappa)
    (hGlobalReferenceClosed : ClosedUnderPaths Gamma Y globalZ)
    (hX0global : X0 ⊆ globalZ)
    (hX0card : #X0 ≤ kappa) :
    Nonempty (JointDynamicHammockClosure Gamma Y kappa globalZ X0
      innerRoof roof) := by
  let ordinarySelected : EligiblePair globalZ innerRoof roof →
      Set (AltPath Gamma.graph) := fun q ↦
    Classical.choose (hGlobalHammocks q.1.1 q.1.2 q.2)
  have ordinarySelected_spec (q : EligiblePair globalZ innerRoof roof) :
      HammockMaximalUpTo Gamma Y q.1.1 q.1.2 kappa
          (ordinarySelected q) ∧
        HammockContained (ordinarySelected q) globalZ :=
    Classical.choose_spec (hGlobalHammocks q.1.1 q.1.2 q.2)
  let filteredSelected : EligiblePair globalZ innerRoof roof →
      Set (AltPath Gamma.graph) := fun q ↦
    Classical.choose (hGlobalNondegenerate q.1.1 q.1.2 q.2)
  have filteredSelected_spec (q : EligiblePair globalZ innerRoof roof) :
      NondegenerateHammockMaximalUpTo Gamma Y q.1.1 q.1.2 kappa
          (filteredSelected q) ∧
        HammockContained (filteredSelected q) globalZ :=
    Classical.choose_spec (hGlobalNondegenerate q.1.1 q.1.2 q.2)
  let ordinaryVertices : Set V → Set V := fun X ↦
    ⋃ q : ActiveGlobalHammockPair globalZ innerRoof roof X,
      hammockVertexSet (ordinarySelected q.toGlobal)
  let filteredVertices : Set V → Set V := fun X ↦
    ⋃ q : ActiveGlobalHammockPair globalZ innerRoof roof X,
      hammockVertexSet (filteredSelected q.toGlobal)
  let selectedVertices : Set V → Set V := fun X ↦
    ordinaryVertices X ∪ filteredVertices X
  let step : Set V → Set V := fun X ↦
    (X ∪ selectedVertices X) ∪ meetingVertices Gamma Y X
  let X : Set V := omegaClosure step X0
  have hOrdinaryOne (q : EligiblePair globalZ innerRoof roof) :
      #(hammockVertexSet (ordinarySelected q)) ≤ kappa := by
    have heq : hammockVertexSet (ordinarySelected q) =
        ⋃ Q : ordinarySelected q, Q.1.vertexSet := by
      ext x
      simp only [hammockVertexSet, Set.mem_iUnion]
      constructor
      · rintro ⟨Q, hQ, hxQ⟩
        exact ⟨⟨Q, hQ⟩, hxQ⟩
      · rintro ⟨Q, hxQ⟩
        exact ⟨Q.1, Q.2, hxQ⟩
    rw [heq]
    apply joint_mk_iUnion_le_of_le hkappa
    · exact (ordinarySelected_spec q).1.card_le
    · intro Q
      exact (altPath_vertexSet_countable Q.1).le_aleph0.trans hkappa
  have hFilteredOne (q : EligiblePair globalZ innerRoof roof) :
      #(hammockVertexSet (filteredSelected q)) ≤ kappa := by
    have heq : hammockVertexSet (filteredSelected q) =
        ⋃ Q : filteredSelected q, Q.1.vertexSet := by
      ext x
      simp only [hammockVertexSet, Set.mem_iUnion]
      constructor
      · rintro ⟨Q, hQ, hxQ⟩
        exact ⟨⟨Q, hQ⟩, hxQ⟩
      · rintro ⟨Q, hxQ⟩
        exact ⟨Q.1, Q.2, hxQ⟩
    rw [heq]
    apply joint_mk_iUnion_le_of_le hkappa
    · exact (filteredSelected_spec q).1.card_le
    · intro Q
      exact (altPath_vertexSet_countable Q.1).le_aleph0.trans hkappa
  have hOrdinaryCard (S : Set V) (hScard : #S ≤ kappa) :
      #(ordinaryVertices S) ≤ kappa := by
    apply joint_mk_iUnion_le_of_le hkappa
    · exact (Cardinal.mk_le_of_injective
          ActiveGlobalHammockPair.toCurrent_injective).trans
        (mk_eligiblePair_le hkappa hScard)
    · intro q
      exact hOrdinaryOne q.toGlobal
  have hFilteredCard (S : Set V) (hScard : #S ≤ kappa) :
      #(filteredVertices S) ≤ kappa := by
    apply joint_mk_iUnion_le_of_le hkappa
    · exact (Cardinal.mk_le_of_injective
          ActiveGlobalHammockPair.toCurrent_injective).trans
        (mk_eligiblePair_le hkappa hScard)
    · intro q
      exact hFilteredOne q.toGlobal
  have hSelectedCard (S : Set V) (hScard : #S ≤ kappa) :
      #(selectedVertices S) ≤ kappa :=
    joint_mk_union_le_of_le hkappa (hOrdinaryCard S hScard)
      (hFilteredCard S hScard)
  have hstepCard (S : Set V) (hScard : #S ≤ kappa) :
      #(step S) ≤ kappa := by
    apply joint_mk_union_le_of_le hkappa
    · exact joint_mk_union_le_of_le hkappa hScard
        (hSelectedCard S hScard)
    · exact mk_meetingVertices_le Gamma Y S hY hkappa hScard
  have hOrdinaryGlobal (S : Set V) : ordinaryVertices S ⊆ globalZ := by
    intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.1 hx
    exact (ordinarySelected_spec q.toGlobal).2 hxq
  have hFilteredGlobal (S : Set V) : filteredVertices S ⊆ globalZ := by
    intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.1 hx
    exact (filteredSelected_spec q.toGlobal).2 hxq
  have hSelectedGlobal (S : Set V) : selectedVertices S ⊆ globalZ := by
    rintro x (hx | hx)
    · exact hOrdinaryGlobal S hx
    · exact hFilteredGlobal S hx
  have hMeetingGlobal (S : Set V) (hSglobal : S ⊆ globalZ) :
      meetingVertices Gamma Y S ⊆ globalZ := by
    intro x hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.1 hx
    apply hGlobalReferenceClosed p.1 p.2.1
    · obtain ⟨z, hzp, hzS⟩ := p.2.2
      exact ⟨z, hzp, hSglobal hzS⟩
    · exact hxp
  have hstepGlobal (S : Set V) (hSglobal : S ⊆ globalZ) :
      step S ⊆ globalZ := by
    rintro x ((hx | hx) | hx)
    · exact hSglobal hx
    · exact hSelectedGlobal S hx
    · exact hMeetingGlobal S hSglobal hx
  have hstageGlobal : ∀ n, closureStage step X0 n ⊆ globalZ :=
    closureStage_subset_roof hX0global hstepGlobal
  have hXglobal : X ⊆ globalZ := by
    intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
    exact hstageGlobal n hxn
  have hstageCard : ∀ n, #(closureStage step X0 n) ≤ kappa :=
    mk_closureStage_le hX0card hstepCard
  have hXcard : #X ≤ kappa := by
    change #(⋃ n, closureStage step X0 n) ≤ kappa
    let stages : ULift.{u} ℕ → Set V :=
      fun n ↦ closureStage step X0 n.down
    have heq : (⋃ n, closureStage step X0 n) = ⋃ i, stages i := by
      ext x
      simp [stages]
    rw [heq]
    apply joint_mk_iUnion_le_of_le hkappa
    · simpa [Cardinal.mk_nat] using hkappa
    · intro i
      exact hstageCard i.down
  have hXclosed : ClosedUnderPaths Gamma Y X := by
    intro p hpY hpMeet
    obtain ⟨x, hxp, hxX⟩ := hpMeet
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hxX
    intro y hyp
    apply closureStage_subset_omegaClosure step X0 (n + 1)
    exact Or.inr (Set.mem_iUnion.2
      ⟨⟨p, hpY, ⟨x, hxp, hxn⟩⟩, hyp⟩)
  have hstepInflation (S : Set V) : S ⊆ step S := by
    intro x hx
    exact Or.inl (Or.inl hx)
  have hstageMono : Monotone (closureStage step X0) := by
    apply monotone_nat_of_le_succ
    intro n
    exact hstepInflation (closureStage step X0 n)
  have hOrdinaryClosed : HammockClosedUpTo Gamma Y X X innerRoof roof kappa := by
    intro u e helig
    cases e with
    | infinity =>
        obtain ⟨n, hun⟩ := Set.mem_iUnion.1 helig.1.1
        let qCurrent : EligiblePair X innerRoof roof :=
          ⟨(u, .infinity), helig⟩
        let q : ActiveGlobalHammockPair globalZ innerRoof roof X :=
          ⟨qCurrent, hXglobal helig.1.1, trivial⟩
        have heligStage : HammockEligible (closureStage step X0 n)
            innerRoof roof u .infinity := ⟨⟨hun, helig.1.2⟩, trivial⟩
        let qStageCurrent : EligiblePair (closureStage step X0 n)
            innerRoof roof := ⟨(u, .infinity), heligStage⟩
        let qStage : ActiveGlobalHammockPair globalZ innerRoof roof
            (closureStage step X0 n) :=
          ⟨qStageCurrent, hXglobal helig.1.1, trivial⟩
        have hq : q.toGlobal = qStage.toGlobal := Subtype.ext rfl
        refine ⟨ordinarySelected q.toGlobal,
          (ordinarySelected_spec q.toGlobal).1, ?_⟩
        intro x hx
        apply closureStage_subset_omegaClosure step X0 (n + 1)
        exact Or.inl (Or.inr (Or.inl
          (Set.mem_iUnion.2 ⟨qStage, by rw [← hq]; exact hx⟩)))
    | vertex v =>
        obtain ⟨nu, hun⟩ := Set.mem_iUnion.1 helig.1.1
        obtain ⟨nv, hvn⟩ := Set.mem_iUnion.1 helig.2.1
        let n := max nu nv
        have hun' := hstageMono (Nat.le_max_left nu nv) hun
        have hvn' := hstageMono (Nat.le_max_right nu nv) hvn
        let qCurrent : EligiblePair X innerRoof roof :=
          ⟨(u, .vertex v), helig⟩
        let q : ActiveGlobalHammockPair globalZ innerRoof roof X :=
          ⟨qCurrent, hXglobal helig.1.1, hXglobal helig.2.1⟩
        have heligStage : HammockEligible (closureStage step X0 n)
            innerRoof roof u (.vertex v) :=
          ⟨⟨hun', helig.1.2⟩, ⟨hvn', helig.2.2⟩⟩
        let qStageCurrent : EligiblePair (closureStage step X0 n)
            innerRoof roof := ⟨(u, .vertex v), heligStage⟩
        let qStage : ActiveGlobalHammockPair globalZ innerRoof roof
            (closureStage step X0 n) :=
          ⟨qStageCurrent, hXglobal helig.1.1, hXglobal helig.2.1⟩
        have hq : q.toGlobal = qStage.toGlobal := Subtype.ext rfl
        refine ⟨ordinarySelected q.toGlobal,
          (ordinarySelected_spec q.toGlobal).1, ?_⟩
        intro x hx
        apply closureStage_subset_omegaClosure step X0 (n + 1)
        exact Or.inl (Or.inr (Or.inl
          (Set.mem_iUnion.2 ⟨qStage, by rw [← hq]; exact hx⟩)))
  have hFilteredClosed : NondegenerateHammockClosedUpTo Gamma Y X X
      innerRoof roof kappa := by
    intro u e helig
    cases e with
    | infinity =>
        obtain ⟨n, hun⟩ := Set.mem_iUnion.1 helig.1.1
        let qCurrent : EligiblePair X innerRoof roof :=
          ⟨(u, .infinity), helig⟩
        let q : ActiveGlobalHammockPair globalZ innerRoof roof X :=
          ⟨qCurrent, hXglobal helig.1.1, trivial⟩
        have heligStage : HammockEligible (closureStage step X0 n)
            innerRoof roof u .infinity := ⟨⟨hun, helig.1.2⟩, trivial⟩
        let qStageCurrent : EligiblePair (closureStage step X0 n)
            innerRoof roof := ⟨(u, .infinity), heligStage⟩
        let qStage : ActiveGlobalHammockPair globalZ innerRoof roof
            (closureStage step X0 n) :=
          ⟨qStageCurrent, hXglobal helig.1.1, trivial⟩
        have hq : q.toGlobal = qStage.toGlobal := Subtype.ext rfl
        refine ⟨filteredSelected q.toGlobal,
          (filteredSelected_spec q.toGlobal).1, ?_⟩
        intro x hx
        apply closureStage_subset_omegaClosure step X0 (n + 1)
        exact Or.inl (Or.inr (Or.inr
          (Set.mem_iUnion.2 ⟨qStage, by rw [← hq]; exact hx⟩)))
    | vertex v =>
        obtain ⟨nu, hun⟩ := Set.mem_iUnion.1 helig.1.1
        obtain ⟨nv, hvn⟩ := Set.mem_iUnion.1 helig.2.1
        let n := max nu nv
        have hun' := hstageMono (Nat.le_max_left nu nv) hun
        have hvn' := hstageMono (Nat.le_max_right nu nv) hvn
        let qCurrent : EligiblePair X innerRoof roof :=
          ⟨(u, .vertex v), helig⟩
        let q : ActiveGlobalHammockPair globalZ innerRoof roof X :=
          ⟨qCurrent, hXglobal helig.1.1, hXglobal helig.2.1⟩
        have heligStage : HammockEligible (closureStage step X0 n)
            innerRoof roof u (.vertex v) :=
          ⟨⟨hun', helig.1.2⟩, ⟨hvn', helig.2.2⟩⟩
        let qStageCurrent : EligiblePair (closureStage step X0 n)
            innerRoof roof := ⟨(u, .vertex v), heligStage⟩
        let qStage : ActiveGlobalHammockPair globalZ innerRoof roof
            (closureStage step X0 n) :=
          ⟨qStageCurrent, hXglobal helig.1.1, hXglobal helig.2.1⟩
        have hq : q.toGlobal = qStage.toGlobal := Subtype.ext rfl
        refine ⟨filteredSelected q.toGlobal,
          (filteredSelected_spec q.toGlobal).1, ?_⟩
        intro x hx
        apply closureStage_subset_omegaClosure step X0 (n + 1)
        exact Or.inl (Or.inr (Or.inr
          (Set.mem_iUnion.2 ⟨qStage, by rw [← hq]; exact hx⟩)))
  exact ⟨{
    closedSet := X
    seed_subset := closureStage_subset_omegaClosure step X0 0
    subset_global := hXglobal
    card_le := hXcard
    hammock_closed := hOrdinaryClosed
    nondegenerate_closed := hFilteredClosed
    reference_closed := hXclosed
  }⟩

end JointDynamicHammockClosure

#print axioms JointDynamicHammockClosure.exists_of_globalClosures

end Erdos599.Blueprint.LinkageBlueprint
