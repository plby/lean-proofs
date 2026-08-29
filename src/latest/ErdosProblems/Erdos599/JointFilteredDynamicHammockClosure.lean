/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FilteredNondegenerateHammockClosure
import ErdosProblems.Erdos599.HalfwayMovingGlobalClosure

/-!
# Small dynamic ordinary and filtered hammock closure

This is the finite, filtered counterpart of `JointDynamicHammockClosure`.
The filtered selector is indexed only by genuinely finite, distinct endpoint
pairs.  The intended filter is `fun Q => Q.vertexSet ⊆ limitRoof`; the
construction is stated for an arbitrary fixed predicate so it does not infer
roof containment from safeness.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

private theorem jointFiltered_mk_iUnion_le_of_le
    {I X : Type u} {f : I → Set X}
    (hkappa : aleph0 ≤ kappa) (hI : #I ≤ kappa)
    (hf : ∀ i, #(f i) ≤ kappa) : #(⋃ i, f i) ≤ kappa := by
  refine (Cardinal.mk_iUnion_le f).trans ?_
  exact Cardinal.mul_le_of_le hkappa hI (ciSup_le' hf)

private theorem jointFiltered_mk_union_le_of_le {A B : Set V}
    (hkappa : aleph0 ≤ kappa) (hA : #A ≤ kappa) (hB : #B ≤ kappa) :
    #(A ∪ B : Set V) ≤ kappa :=
  (Cardinal.mk_union_le A B).trans
    (Cardinal.add_le_of_le hkappa hA hB)

/-- A finite eligible pair with distinct endpoints. -/
structure FiniteDistinctEligiblePair
    (before innerRoof outerRoof : Set V) where
  source : V
  target : V
  ne : source ≠ target
  eligible : HammockEligible before innerRoof outerRoof source (.vertex target)

namespace FiniteDistinctEligiblePair

def toEligible
    {before innerRoof outerRoof : Set V}
    (q : FiniteDistinctEligiblePair before innerRoof outerRoof) :
    EligiblePair before innerRoof outerRoof :=
  ⟨(q.source, .vertex q.target), q.eligible⟩

theorem toEligible_injective
    {before innerRoof outerRoof : Set V} :
    Function.Injective
      (toEligible : FiniteDistinctEligiblePair before innerRoof outerRoof →
        EligiblePair before innerRoof outerRoof) := by
  rintro ⟨u, v, huv, helig⟩ ⟨u', v', huv', helig'⟩ h
  simp only [toEligible] at h
  cases h
  rfl

theorem ext
    {before innerRoof outerRoof : Set V}
    {q r : FiniteDistinctEligiblePair before innerRoof outerRoof}
    (hsource : q.source = r.source) (htarget : q.target = r.target) : q = r := by
  cases q
  cases r
  simp_all

end FiniteDistinctEligiblePair

/-- A currently active finite pair, together with the fact that both
endpoints already lie in the global reservoir. -/
structure ActiveGlobalFiniteDistinctPair
    (globalZ innerRoof outerRoof X : Set V) where
  current : FiniteDistinctEligiblePair X innerRoof outerRoof
  source_global : current.source ∈ globalZ
  target_global : current.target ∈ globalZ

namespace ActiveGlobalFiniteDistinctPair

def toCurrent
    {globalZ innerRoof outerRoof X : Set V}
    (q : ActiveGlobalFiniteDistinctPair globalZ innerRoof outerRoof X) :
    FiniteDistinctEligiblePair X innerRoof outerRoof := q.current

theorem toCurrent_injective
    {globalZ innerRoof outerRoof X : Set V} :
    Function.Injective
      (toCurrent : ActiveGlobalFiniteDistinctPair globalZ innerRoof outerRoof X →
        FiniteDistinctEligiblePair X innerRoof outerRoof) := by
  rintro ⟨q, hqsource, hqtarget⟩ ⟨r, hrsource, hrtarget⟩ h
  simp only [toCurrent] at h
  cases h
  rfl

def toGlobal
    {globalZ innerRoof outerRoof X : Set V}
    (q : ActiveGlobalFiniteDistinctPair globalZ innerRoof outerRoof X) :
    FiniteDistinctEligiblePair globalZ innerRoof outerRoof where
  source := q.current.source
  target := q.current.target
  ne := q.current.ne
  eligible :=
    ⟨⟨q.source_global, q.current.eligible.1.2⟩,
      ⟨q.target_global, q.current.eligible.2.2⟩⟩

end ActiveGlobalFiniteDistinctPair

/-- A small carrier dynamically closed under ordinary hammocks, finite
roof-filtered nondegenerate hammocks, and full reference paths. -/
structure JointFilteredDynamicHammockClosure
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (globalZ X0 innerRoof roof : Set V)
    (P : AltPath Gamma.graph → Prop) where
  closedSet : Set V
  seed_subset : X0 ⊆ closedSet
  subset_global : closedSet ⊆ globalZ
  card_le : #closedSet ≤ kappa
  hammock_closed : HammockClosedUpTo Gamma Y closedSet closedSet
    innerRoof roof kappa
  finite_filtered_closed : FiniteFilteredHammockClosedUpTo Gamma Y closedSet
    closedSet innerRoof roof P kappa
  reference_closed : ClosedUnderPaths Gamma Y closedSet

namespace JointFilteredDynamicHammockClosure

/-- Extract the joint small closure from a reservoir which already contains
the corresponding actual ordinary and finite filtered closures. -/
theorem exists_of_globalClosures
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (globalZ X0 innerRoof roof : Set V)
    (P : AltPath Gamma.graph → Prop)
    (hkappa : aleph0 ≤ kappa)
    (hY : Gamma.IsWarp Y)
    (hGlobalHammocks : HammockClosedUpTo Gamma Y globalZ globalZ
      innerRoof roof kappa)
    (hGlobalFiltered : FiniteFilteredHammockClosedUpTo Gamma Y
      globalZ globalZ innerRoof roof P kappa)
    (hGlobalReferenceClosed : ClosedUnderPaths Gamma Y globalZ)
    (hX0global : X0 ⊆ globalZ)
    (hX0card : #X0 ≤ kappa) :
    Nonempty (JointFilteredDynamicHammockClosure Gamma Y kappa globalZ X0
      innerRoof roof P) := by
  let ordinarySelected : EligiblePair globalZ innerRoof roof →
      Set (AltPath Gamma.graph) := fun q ↦
    Classical.choose (hGlobalHammocks q.1.1 q.1.2 q.2)
  have ordinarySelected_spec (q : EligiblePair globalZ innerRoof roof) :
      HammockMaximalUpTo Gamma Y q.1.1 q.1.2 kappa
          (ordinarySelected q) ∧
        HammockContained (ordinarySelected q) globalZ :=
    Classical.choose_spec (hGlobalHammocks q.1.1 q.1.2 q.2)
  let filteredSelected : FiniteDistinctEligiblePair globalZ innerRoof roof →
      Set (AltPath Gamma.graph) := fun q ↦
    Classical.choose (hGlobalFiltered q.source q.target q.ne q.eligible)
  have filteredSelected_spec
      (q : FiniteDistinctEligiblePair globalZ innerRoof roof) :
      FilteredNondegenerateHammockMaximalUpTo Gamma Y q.source
          (.vertex q.target) P kappa (filteredSelected q) ∧
        HammockContained (filteredSelected q) globalZ :=
    Classical.choose_spec
      (hGlobalFiltered q.source q.target q.ne q.eligible)
  let ordinaryVertices : Set V → Set V := fun X ↦
    ⋃ q : ActiveGlobalHammockPair globalZ innerRoof roof X,
      hammockVertexSet (ordinarySelected q.toGlobal)
  let filteredVertices : Set V → Set V := fun X ↦
    ⋃ q : ActiveGlobalFiniteDistinctPair globalZ innerRoof roof X,
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
    apply jointFiltered_mk_iUnion_le_of_le hkappa
    · exact (ordinarySelected_spec q).1.card_le
    · intro Q
      exact (altPath_vertexSet_countable Q.1).le_aleph0.trans hkappa
  have hFilteredOne (q : FiniteDistinctEligiblePair globalZ innerRoof roof) :
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
    apply jointFiltered_mk_iUnion_le_of_le hkappa
    · exact (filteredSelected_spec q).1.card_le
    · intro Q
      exact (altPath_vertexSet_countable Q.1).le_aleph0.trans hkappa
  have hOrdinaryCard (S : Set V) (hScard : #S ≤ kappa) :
      #(ordinaryVertices S) ≤ kappa := by
    apply jointFiltered_mk_iUnion_le_of_le hkappa
    · exact (Cardinal.mk_le_of_injective
          ActiveGlobalHammockPair.toCurrent_injective).trans
        (mk_eligiblePair_le hkappa hScard)
    · intro q
      exact hOrdinaryOne q.toGlobal
  have hFilteredCard (S : Set V) (hScard : #S ≤ kappa) :
      #(filteredVertices S) ≤ kappa := by
    apply jointFiltered_mk_iUnion_le_of_le hkappa
    · exact (Cardinal.mk_le_of_injective
          ActiveGlobalFiniteDistinctPair.toCurrent_injective).trans
        ((Cardinal.mk_le_of_injective
          FiniteDistinctEligiblePair.toEligible_injective).trans
            (mk_eligiblePair_le hkappa hScard))
    · intro q
      exact hFilteredOne q.toGlobal
  have hSelectedCard (S : Set V) (hScard : #S ≤ kappa) :
      #(selectedVertices S) ≤ kappa :=
    jointFiltered_mk_union_le_of_le hkappa (hOrdinaryCard S hScard)
      (hFilteredCard S hScard)
  have hstepCard (S : Set V) (hScard : #S ≤ kappa) :
      #(step S) ≤ kappa := by
    apply jointFiltered_mk_union_le_of_le hkappa
    · exact jointFiltered_mk_union_le_of_le hkappa hScard
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
    apply jointFiltered_mk_iUnion_le_of_le hkappa
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
  have hFilteredClosed : FiniteFilteredHammockClosedUpTo Gamma Y X X
      innerRoof roof P kappa := by
    intro u v hne helig
    obtain ⟨nu, hun⟩ := Set.mem_iUnion.1 helig.1.1
    obtain ⟨nv, hvn⟩ := Set.mem_iUnion.1 helig.2.1
    let n := max nu nv
    have hun' := hstageMono (Nat.le_max_left nu nv) hun
    have hvn' := hstageMono (Nat.le_max_right nu nv) hvn
    let qCurrent : FiniteDistinctEligiblePair X innerRoof roof :=
      ⟨u, v, hne, helig⟩
    let q : ActiveGlobalFiniteDistinctPair globalZ innerRoof roof X :=
      ⟨qCurrent, hXglobal helig.1.1, hXglobal helig.2.1⟩
    have heligStage : HammockEligible (closureStage step X0 n)
        innerRoof roof u (.vertex v) :=
      ⟨⟨hun', helig.1.2⟩, ⟨hvn', helig.2.2⟩⟩
    let qStageCurrent : FiniteDistinctEligiblePair
        (closureStage step X0 n) innerRoof roof :=
      ⟨u, v, hne, heligStage⟩
    let qStage : ActiveGlobalFiniteDistinctPair globalZ innerRoof roof
        (closureStage step X0 n) :=
      ⟨qStageCurrent, hXglobal helig.1.1, hXglobal helig.2.1⟩
    have hq : q.toGlobal = qStage.toGlobal :=
      FiniteDistinctEligiblePair.ext rfl rfl
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
    finite_filtered_closed := hFilteredClosed
    reference_closed := hXclosed
  }⟩

end JointFilteredDynamicHammockClosure

#print axioms JointFilteredDynamicHammockClosure.exists_of_globalClosures

end Erdos599.Blueprint.LinkageBlueprint
