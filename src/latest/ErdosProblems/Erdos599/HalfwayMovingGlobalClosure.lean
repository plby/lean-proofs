/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMovingGlobalClosureCapture
import ErdosProblems.Erdos599.HalfwayClause

/-!
# Closing under the limiting warp before choosing the later stage

Assertion 9.31 first closes a small set under the *global* limiting warp and
only then chooses the later club stage which roofs the completed set.  This
file packages that source-order construction.  In particular, the limiting
warp is not replaced by a finite selected stage reference.

The closure theorem used below applies to arbitrary directed paths.  Rays in
the limiting warp therefore require no finite-character hypothesis: a path
which meets the growing set is inserted through its (countable) support by
the same omega closure as a finite path.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

private theorem moving_mk_iUnion_le_of_le {I X : Type u}
    {f : I → Set X} {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hI : #I ≤ kappa)
    (hf : ∀ i, #(f i) ≤ kappa) :
    #(⋃ i, f i) ≤ kappa := by
  refine (Cardinal.mk_iUnion_le f).trans ?_
  exact Cardinal.mul_le_of_le hkappa hI (ciSup_le' hf)

private theorem moving_mk_union_le_of_le {A B : Set V}
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hA : #A ≤ kappa) (hB : #B ≤ kappa) :
    #(A ∪ B : Set V) ≤ kappa :=
  (Cardinal.mk_union_le A B).trans
    (Cardinal.add_le_of_le hkappa hA hB)

/-- Source-faithful Assertions 9.22--9.25 closure from a global set which
already contains a maximal-up-to-`rho` hammock for every eligible endpoint
pair.

The source proof invokes its preceding maximal-hammock assertion inside the
global set `Z`; it does *not* assert that every safe alternating path stays
in `Z`.  This theorem therefore selects the supplied roof-contained
hammocks, closes under their vertices, target paths, and reference paths,
and never uses the false uniform safe-path containment premise. -/
theorem exists_assertions_9_22_to_9_25_of_roof_hammocks
    (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho kappa : Cardinal.{u})
    (ZBefore innerRoof roof T B X0 : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (hY : Gamma.IsWarp Y)
    (hYroof : ∀ p ∈ Y, p.support ⊆ roof)
    (hRoofHammocks :
      HammockClosedUpTo Gamma Y roof ZBefore innerRoof roof rho)
    (hkappa : aleph0 ≤ kappa) (hrho : rho ≤ kappa)
    (hZBefore : #ZBefore ≤ kappa)
    (hX0card : #X0 ≤ kappa) (hX0roof : X0 ⊆ roof) :
    ∃ Z : Set V,
      X0 ⊆ Z ∧ #Z ≤ kappa ∧
      HammockClosedUpTo Gamma Y Z ZBefore innerRoof roof rho ∧
      HasPreservingTargetPaths Gamma T Z B Preserves ∧
      ClosedUnderPaths Gamma Y Z ∧ ContainedInRoof Z roof := by
  let selected : EligiblePair ZBefore innerRoof roof →
      Set (AltPath Gamma.graph) := fun q ↦
    Classical.choose (hRoofHammocks q.1.1 q.1.2 q.2)
  have selected_spec (q : EligiblePair ZBefore innerRoof roof) :
      HammockMaximalUpTo Gamma Y q.1.1 q.1.2 rho (selected q) ∧
        HammockContained (selected q) roof :=
    Classical.choose_spec (hRoofHammocks q.1.1 q.1.2 q.2)
  let selectedVertices : Set V :=
    ⋃ q : EligiblePair ZBefore innerRoof roof, hammockVertexSet (selected q)
  let step : Set V → Set V := fun X ↦
    ((X ∪ selectedVertices) ∪
      targetVertices Gamma T roof B Preserves hTarget X) ∪
        meetingVertices Gamma Y X
  let Z : Set V := omegaClosure step X0
  have hSelectedOne (q : EligiblePair ZBefore innerRoof roof) :
      #(hammockVertexSet (selected q)) ≤ kappa := by
    have heq : hammockVertexSet (selected q) =
        ⋃ Q : selected q, Q.1.vertexSet := by
      ext x
      simp only [hammockVertexSet, Set.mem_iUnion]
      constructor
      · rintro ⟨Q, hQ, hxQ⟩
        exact ⟨⟨Q, hQ⟩, hxQ⟩
      · rintro ⟨Q, hxQ⟩
        exact ⟨Q.1, Q.2, hxQ⟩
    rw [heq]
    apply moving_mk_iUnion_le_of_le hkappa
    · exact (selected_spec q).1.card_le.trans hrho
    · intro Q
      exact (altPath_vertexSet_countable Q.1).le_aleph0.trans hkappa
  have hSelectedCard : #selectedVertices ≤ kappa := by
    apply moving_mk_iUnion_le_of_le hkappa
    · exact mk_eligiblePair_le hkappa hZBefore
    · exact hSelectedOne
  have hSelectedRoof : selectedVertices ⊆ roof := by
    intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.1 hx
    exact (selected_spec q).2 hxq
  have hstepCard : ∀ X : Set V, #X ≤ kappa → #(step X) ≤ kappa := by
    intro X hX
    apply moving_mk_union_le_of_le hkappa
    · apply moving_mk_union_le_of_le hkappa
      · exact moving_mk_union_le_of_le hkappa hX hSelectedCard
      · exact mk_targetVertices_le Gamma T roof B Preserves hTarget X
          hkappa hX
    · exact mk_meetingVertices_le Gamma Y X hY hkappa hX
  have hstepRoof : ∀ X : Set V, X ⊆ roof → step X ⊆ roof := by
    intro X hX x hx
    rcases hx with (hx | hx) | hx
    · rcases hx with hx | hx
      · exact hX hx
      · exact hSelectedRoof hx
    · exact targetVertices_subset_roof Gamma T roof B Preserves hTarget X hx
    · exact meetingVertices_subset_roof Gamma Y X roof hYroof hx
  have hstageCard : ∀ n, #(closureStage step X0 n) ≤ kappa :=
    mk_closureStage_le hX0card hstepCard
  have hstageRoof : ∀ n, closureStage step X0 n ⊆ roof :=
    closureStage_subset_roof hX0roof hstepRoof
  have hZroof : Z ⊆ roof := by
    intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
    exact hstageRoof n hxn
  refine ⟨Z, closureStage_subset_omegaClosure step X0 0, ?_, ?_, ?_, ?_, hZroof⟩
  · change #(⋃ n, closureStage step X0 n) ≤ kappa
    let stages : ULift.{u} ℕ → Set V :=
      fun n ↦ closureStage step X0 n.down
    have heq : (⋃ n, closureStage step X0 n) = ⋃ i, stages i := by
      ext x
      simp [stages]
    rw [heq]
    apply moving_mk_iUnion_le_of_le hkappa
    · simpa [Cardinal.mk_nat] using hkappa
    · intro i
      exact hstageCard i.down
  · intro u e helig
    let q : EligiblePair ZBefore innerRoof roof := ⟨(u, e), helig⟩
    refine ⟨selected q, (selected_spec q).1, ?_⟩
    intro x hx
    apply closureStage_subset_omegaClosure step X0 1
    exact Or.inl (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨q, hx⟩)))
  · intro v hv
    have hvRoof : v ∈ roof := hZroof hv.2
    let tv : TargetVertex T roof := ⟨v, hv.1, hvRoof⟩
    let p := targetChoice Gamma T roof B Preserves hTarget tv
    obtain ⟨n, hvn⟩ := Set.mem_iUnion.1 hv.2
    have hpSupport : p.support ⊆ Z := by
      intro x hx
      apply closureStage_subset_omegaClosure step X0 (n + 1)
      exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨⟨tv, hvn⟩, hx⟩))
    exact ⟨p, (targetChoice_spec Gamma T roof B Preserves hTarget tv).1,
      (targetChoice_spec Gamma T roof B Preserves hTarget tv).2.1,
      hpSupport,
      (targetChoice_spec Gamma T roof B Preserves hTarget tv).2.2.2⟩
  · intro p hpY hpMeet
    obtain ⟨x, hxp, hxZ⟩ := hpMeet
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hxZ
    intro y hyp
    apply closureStage_subset_omegaClosure step X0 (n + 1)
    exact Or.inr (Set.mem_iUnion.2
      ⟨⟨p, hpY, ⟨x, hxp, hxn⟩⟩, hyp⟩)

/-- The completed global-reference closure together with the club stage
chosen after it.  Every field preceding `later` is an Assertion 9.22--9.25
conclusion for the actual limiting warp. -/
structure MovingGlobalClosure
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (ZBefore T B X0 : Set V)
    (Preserves : FinitePath Gamma.graph → Prop) where
  closedSet : Set V
  seed_subset : X0 ⊆ closedSet
  card_le : #closedSet ≤ kappa
  hammock_closed : HammockClosedUpTo Gamma C.ladder.limitWarp closedSet
    ZBefore C.innerRoof C.ladder.limitRoof kappa
  preserving_target_paths :
    HasPreservingTargetPaths Gamma T closedSet B Preserves
  reference_closed : ClosedUnderPaths Gamma C.ladder.limitWarp closedSet
  subset_limitRoof : closedSet ⊆ C.ladder.limitRoof
  later : LaterClubRoofCapture C closedSet

/-- The actual Assertion 9.31 closing output.  Its scheduled safe path has
already been inserted into `X0`, exactly as `V(P)` is inserted into `X_0`
in Claim 9.31.  Consequently no universal target-path choice is part of this
record. -/
structure Moving931GlobalClosure
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (ZBefore X0 : Set V) where
  closedSet : Set V
  seed_subset : X0 ⊆ closedSet
  card_le : #closedSet ≤ kappa
  hammock_closed : HammockClosedUpTo Gamma C.ladder.limitWarp closedSet
    ZBefore C.innerRoof C.ladder.limitRoof kappa
  reference_closed : ClosedUnderPaths Gamma C.ladder.limitWarp closedSet
  subset_limitRoof : closedSet ⊆ C.ladder.limitRoof
  later : LaterClubRoofCapture C closedSet

namespace Moving931GlobalClosure

/-- Close the already-scheduled 9.31 seed under roof-contained maximal
hammocks and the global limiting warp, then choose the later stage. -/
theorem exists_of_scheduledSeed
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (ZBefore X0 : Set V)
    (hReferenceRoof : ∀ p ∈ C.ladder.limitWarp,
      p.support ⊆ C.ladder.limitRoof)
    (hRoofHammocks : HammockClosedUpTo Gamma C.ladder.limitWarp
      C.ladder.limitRoof ZBefore C.innerRoof C.ladder.limitRoof kappa)
    (hZBefore : #ZBefore ≤ kappa)
    (hX0card : #X0 ≤ kappa)
    (hX0roof : X0 ⊆ C.ladder.limitRoof) :
    Nonempty (Moving931GlobalClosure C ZBefore X0) := by
  have hLimitWarp : Gamma.IsWarp C.ladder.limitWarp :=
    C.legal.warpStages (Ladder.finalStage (succ kappa))
  have hNoTarget : ∀ v ∈ (∅ : Set V) ∩ C.ladder.limitRoof,
      ∃ p : FinitePath Gamma.graph,
        p.start = v ∧ p.finish ∈ (∅ : Set V) ∧
          p.support ⊆ C.ladder.limitRoof ∧ True := by
    intro v hv
    exact False.elim hv.1
  obtain ⟨X, hX0X, hXcard, hHammock, _hTarget, hClosed, hXroof⟩ :=
    exists_assertions_9_22_to_9_25_of_roof_hammocks
      Gamma C.ladder.limitWarp kappa kappa ZBefore C.innerRoof
      C.ladder.limitRoof ∅ ∅ X0 (fun _ ↦ True) hNoTarget hLimitWarp
      hReferenceRoof hRoofHammocks C.capacity_infinite le_rfl
      hZBefore hX0card hX0roof
  obtain ⟨later⟩ :=
    LaterClubRoofCapture.exists_of_subset_limitRoof C X hXcard hXroof
  exact ⟨{
    closedSet := X
    seed_subset := hX0X
    card_le := hXcard
    hammock_closed := hHammock
    reference_closed := hClosed
    subset_limitRoof := hXroof
    later := later
  }⟩

theorem laterStage_isUnhindered
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {ZBefore X0 : Set V} (R : Moving931GlobalClosure C ZBefore X0) :
    (C.ladder.stageWeb R.later.stage).IsUnhindered :=
  R.later.stageWeb_isUnhindered

end Moving931GlobalClosure

/-! ## The dynamically indexed Claim 9.31 closure -/

/-- Eligible endpoint pairs from a current small set whose exposed
endpoints already belong to the global closing set.  The extra fields are
automatic when the current set is a subset of the global set, but recording
them here makes the one-step operator total on arbitrary sets. -/
abbrev ActiveGlobalHammockPair
    (globalZ innerRoof roof X : Set V) :=
  {q : EligiblePair X innerRoof roof //
    q.1.1 ∈ globalZ ∧
      match q.1.2 with
      | .vertex v => v ∈ globalZ
      | .infinity => True}

namespace ActiveGlobalHammockPair

def toCurrent
    {globalZ innerRoof roof X : Set V}
    (q : ActiveGlobalHammockPair globalZ innerRoof roof X) :
    EligiblePair X innerRoof roof := q.1

theorem toCurrent_injective
    {globalZ innerRoof roof X : Set V} :
    Function.Injective
      (toCurrent : ActiveGlobalHammockPair globalZ innerRoof roof X →
        EligiblePair X innerRoof roof) := by
  intro q r h
  exact Subtype.ext h

def toGlobal
    {globalZ innerRoof roof X : Set V}
    (q : ActiveGlobalHammockPair globalZ innerRoof roof X) :
    EligiblePair globalZ innerRoof roof := by
  refine ⟨q.1.1, ?_⟩
  constructor
  · exact ⟨q.2.1, q.1.2.1.2⟩
  · cases h : q.1.1.2 with
    | infinity => trivial
    | vertex v =>
        change v ∈ globalZ ∩ roof
        have hglobal : v ∈ globalZ := by
          simpa only [h] using q.2.2
        have hroof : v ∈ roof := by
          have hv : v ∈ X ∩ roof := by
            simpa only [HammockEligible, h] using q.1.2.2
          exact hv.2
        exact ⟨hglobal, hroof⟩

end ActiveGlobalHammockPair

/-- The exact dynamic closure in Claim 9.31.  Unlike a closure over one
fixed `ZBefore`, newly inserted endpoints participate at the next omega
stage.  The global set is used only as the already-constructed reservoir of
roofed maximal hammocks and global-reference paths. -/
structure DynamicMoving931GlobalClosure
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ X0 : Set V) where
  closedSet : Set V
  seed_subset : X0 ⊆ closedSet
  subset_global : closedSet ⊆ globalZ
  card_le : #closedSet ≤ kappa
  hammock_closed : HammockClosedUpTo Gamma C.ladder.limitWarp closedSet
    closedSet C.ladder.limitStrictRoof C.ladder.limitRoof kappa
  reference_closed : ClosedUnderPaths Gamma C.ladder.limitWarp closedSet
  subset_limitRoof : closedSet ⊆ C.ladder.limitRoof
  later : LaterClubRoofCapture C closedSet

namespace DynamicMoving931GlobalClosure

/-- Extract the small, dynamically indexed Claim 9.31 closure from the
global ladder closing set `globalZ`, and only afterwards capture it below a
later club frontier.

This is the formal dependency order of the paper: `globalZ` was constructed
alongside the ladder and already contains the required maximal hammocks;
`X` is the small omega subclosure used for this one transaction. -/
theorem exists_of_globalClosedSet
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ X0 : Set V)
    (hGlobalRoof : globalZ ⊆ C.ladder.limitRoof)
    (hGlobalHammocks : HammockClosedUpTo Gamma C.ladder.limitWarp
      globalZ globalZ C.ladder.limitStrictRoof C.ladder.limitRoof kappa)
    (hGlobalReferenceClosed :
      ClosedUnderPaths Gamma C.ladder.limitWarp globalZ)
    (hX0global : X0 ⊆ globalZ)
    (hX0card : #X0 ≤ kappa) :
    Nonempty (DynamicMoving931GlobalClosure C globalZ X0) := by
  let globalSelected : EligiblePair globalZ C.ladder.limitStrictRoof
      C.ladder.limitRoof →
      Set (AltPath Gamma.graph) := fun q ↦
    Classical.choose (hGlobalHammocks q.1.1 q.1.2 q.2)
  have globalSelected_spec
      (q : EligiblePair globalZ C.ladder.limitStrictRoof
        C.ladder.limitRoof) :
      HammockMaximalUpTo Gamma C.ladder.limitWarp q.1.1 q.1.2 kappa
          (globalSelected q) ∧
        HammockContained (globalSelected q) globalZ :=
    Classical.choose_spec (hGlobalHammocks q.1.1 q.1.2 q.2)
  let selectedVertices : Set V → Set V := fun X ↦
    ⋃ q : ActiveGlobalHammockPair globalZ C.ladder.limitStrictRoof
      C.ladder.limitRoof X,
        hammockVertexSet (globalSelected q.toGlobal)
  let step : Set V → Set V := fun X ↦
    (X ∪ selectedVertices X) ∪
      meetingVertices Gamma C.ladder.limitWarp X
  let X : Set V := omegaClosure step X0
  have hSelectedOne
      (q : EligiblePair globalZ C.ladder.limitStrictRoof
        C.ladder.limitRoof) :
      #(hammockVertexSet (globalSelected q)) ≤ kappa := by
    have heq : hammockVertexSet (globalSelected q) =
        ⋃ Q : globalSelected q, Q.1.vertexSet := by
      ext x
      simp only [hammockVertexSet, Set.mem_iUnion]
      constructor
      · rintro ⟨Q, hQ, hxQ⟩
        exact ⟨⟨Q, hQ⟩, hxQ⟩
      · rintro ⟨Q, hxQ⟩
        exact ⟨Q.1, Q.2, hxQ⟩
    rw [heq]
    apply moving_mk_iUnion_le_of_le C.capacity_infinite
    · exact (globalSelected_spec q).1.card_le
    · intro Q
      exact (altPath_vertexSet_countable Q.1).le_aleph0.trans
        C.capacity_infinite
  have hSelectedCard (S : Set V) (hScard : #S ≤ kappa) :
      #(selectedVertices S) ≤ kappa := by
    apply moving_mk_iUnion_le_of_le C.capacity_infinite
    · exact (Cardinal.mk_le_of_injective
          ActiveGlobalHammockPair.toCurrent_injective).trans
        (mk_eligiblePair_le C.capacity_infinite hScard)
    · intro q
      exact hSelectedOne q.toGlobal
  have hstepCard (S : Set V) (hScard : #S ≤ kappa) :
      #(step S) ≤ kappa := by
    apply moving_mk_union_le_of_le C.capacity_infinite
    · exact moving_mk_union_le_of_le C.capacity_infinite hScard
        (hSelectedCard S hScard)
    · exact mk_meetingVertices_le Gamma C.ladder.limitWarp S
        (C.legal.warpStages (Ladder.finalStage (succ kappa)))
        C.capacity_infinite hScard
  have hSelectedGlobal (S : Set V) : selectedVertices S ⊆ globalZ := by
    intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.1 hx
    exact (globalSelected_spec q.toGlobal).2 hxq
  have hMeetingGlobal (S : Set V) (hSglobal : S ⊆ globalZ) :
      meetingVertices Gamma C.ladder.limitWarp S ⊆ globalZ := by
    intro x hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.1 hx
    apply hGlobalReferenceClosed p.1 p.2.1
    obtain ⟨z, hzp, hzS⟩ := p.2.2
    exact ⟨z, hzp, hSglobal hzS⟩
    exact hxp
  have hstepGlobal (S : Set V) (hSglobal : S ⊆ globalZ) :
      step S ⊆ globalZ := by
    intro x hx
    rcases hx with (hx | hx) | hx
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
    apply moving_mk_iUnion_le_of_le C.capacity_infinite
    · simpa [Cardinal.mk_nat] using C.capacity_infinite
    · intro i
      exact hstageCard i.down
  have hXclosed : ClosedUnderPaths Gamma C.ladder.limitWarp X := by
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
  have hXhammock : HammockClosedUpTo Gamma C.ladder.limitWarp X X
      C.ladder.limitStrictRoof C.ladder.limitRoof kappa := by
    intro u e helig
    cases e with
    | infinity =>
        obtain ⟨n, hun⟩ := Set.mem_iUnion.1 helig.1.1
        let qCurrent : EligiblePair X C.ladder.limitStrictRoof
            C.ladder.limitRoof :=
          ⟨(u, .infinity), helig⟩
        let q : ActiveGlobalHammockPair globalZ C.ladder.limitStrictRoof
            C.ladder.limitRoof X :=
          ⟨qCurrent, hXglobal helig.1.1, trivial⟩
        have heligStage : HammockEligible (closureStage step X0 n)
            C.ladder.limitStrictRoof C.ladder.limitRoof u .infinity :=
          ⟨⟨hun, helig.1.2⟩, trivial⟩
        let qStageCurrent : EligiblePair (closureStage step X0 n)
            C.ladder.limitStrictRoof C.ladder.limitRoof :=
          ⟨(u, .infinity), heligStage⟩
        let qStage : ActiveGlobalHammockPair globalZ C.ladder.limitStrictRoof
            C.ladder.limitRoof (closureStage step X0 n) :=
          ⟨qStageCurrent, hXglobal helig.1.1, trivial⟩
        have hq : q.toGlobal = qStage.toGlobal := by
          apply Subtype.ext
          rfl
        refine ⟨globalSelected q.toGlobal,
          (globalSelected_spec q.toGlobal).1, ?_⟩
        intro x hx
        apply closureStage_subset_omegaClosure step X0 (n + 1)
        apply Or.inl
        apply Or.inr
        apply Set.mem_iUnion.2
        refine ⟨qStage, ?_⟩
        rw [← hq]
        exact hx
    | vertex v =>
        have hvX : v ∈ X := helig.2.1
        obtain ⟨nu, hun⟩ := Set.mem_iUnion.1 helig.1.1
        obtain ⟨nv, hvn⟩ := Set.mem_iUnion.1 hvX
        let n := max nu nv
        have hun' : u ∈ closureStage step X0 n :=
          hstageMono (Nat.le_max_left nu nv) hun
        have hvn' : v ∈ closureStage step X0 n :=
          hstageMono (Nat.le_max_right nu nv) hvn
        let qCurrent : EligiblePair X C.ladder.limitStrictRoof
            C.ladder.limitRoof :=
          ⟨(u, .vertex v), helig⟩
        let q : ActiveGlobalHammockPair globalZ C.ladder.limitStrictRoof
            C.ladder.limitRoof X :=
          ⟨qCurrent, hXglobal helig.1.1, hXglobal hvX⟩
        have heligStage : HammockEligible (closureStage step X0 n)
            C.ladder.limitStrictRoof C.ladder.limitRoof u (.vertex v) :=
          ⟨⟨hun', helig.1.2⟩, ⟨hvn', helig.2.2⟩⟩
        let qStageCurrent : EligiblePair (closureStage step X0 n)
            C.ladder.limitStrictRoof C.ladder.limitRoof :=
          ⟨(u, .vertex v), heligStage⟩
        let qStage : ActiveGlobalHammockPair globalZ C.ladder.limitStrictRoof
            C.ladder.limitRoof (closureStage step X0 n) :=
          ⟨qStageCurrent, hXglobal helig.1.1, hXglobal hvX⟩
        have hq : q.toGlobal = qStage.toGlobal := by
          apply Subtype.ext
          rfl
        refine ⟨globalSelected q.toGlobal,
          (globalSelected_spec q.toGlobal).1, ?_⟩
        intro x hx
        apply closureStage_subset_omegaClosure step X0 (n + 1)
        apply Or.inl
        apply Or.inr
        apply Set.mem_iUnion.2
        refine ⟨qStage, ?_⟩
        rw [← hq]
        exact hx
  have hXroof : X ⊆ C.ladder.limitRoof := hXglobal.trans hGlobalRoof
  obtain ⟨later⟩ :=
    LaterClubRoofCapture.exists_of_subset_limitRoof C X hXcard hXroof
  exact ⟨{
    closedSet := X
    seed_subset := closureStage_subset_omegaClosure step X0 0
    subset_global := hXglobal
    card_le := hXcard
    hammock_closed := hXhammock
    reference_closed := hXclosed
    subset_limitRoof := hXroof
    later := later
  }⟩

end DynamicMoving931GlobalClosure

namespace MovingGlobalClosure

/-- Run Assertions 9.22--9.25 with the full limiting warp and the limiting
roof, then choose a strictly later club stage containing the result.

The reference paths and chosen target paths stay in the global ladder roof.
For hammocks, the input is the source-faithful preceding assertion that the
global roof itself already contains a maximal-up-to-`kappa` hammock for each
eligible endpoint pair.  No claim is made that every safe alternating path
is roof-contained.  The conclusion is unconditional in the choice of a
later stage and has no finite-character premise on `C.ladder.limitWarp`. -/
theorem exists_of_limitRoof_geometry
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (ZBefore T B X0 : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ C.ladder.limitRoof,
      ∃ p : FinitePath Gamma.graph,
        p.start = v ∧ p.finish ∈ B ∧
          p.support ⊆ C.ladder.limitRoof ∧ Preserves p)
    (hReferenceRoof : ∀ p ∈ C.ladder.limitWarp,
      p.support ⊆ C.ladder.limitRoof)
    (hRoofHammocks : HammockClosedUpTo Gamma C.ladder.limitWarp
      C.ladder.limitRoof ZBefore C.innerRoof C.ladder.limitRoof kappa)
    (hZBefore : #ZBefore ≤ kappa)
    (hX0card : #X0 ≤ kappa)
    (hX0roof : X0 ⊆ C.ladder.limitRoof) :
    Nonempty (MovingGlobalClosure C ZBefore T B X0 Preserves) := by
  have hLimitWarp : Gamma.IsWarp C.ladder.limitWarp :=
    C.legal.warpStages (Ladder.finalStage (succ kappa))
  obtain ⟨X, hX0X, hXcard, hHammock, hTargetX, hClosed, hXroof⟩ :=
    exists_assertions_9_22_to_9_25_of_roof_hammocks
      Gamma C.ladder.limitWarp kappa kappa ZBefore C.innerRoof
      C.ladder.limitRoof T B X0 Preserves hTarget hLimitWarp
      hReferenceRoof hRoofHammocks C.capacity_infinite le_rfl
      hZBefore hX0card hX0roof
  obtain ⟨later⟩ :=
    LaterClubRoofCapture.exists_of_subset_limitRoof C X hXcard hXroof
  exact ⟨{
    closedSet := X
    seed_subset := hX0X
    card_le := hXcard
    hammock_closed := hHammock
    preserving_target_paths := hTargetX
    reference_closed := hClosed
    subset_limitRoof := hXroof
    later := later
  }⟩

/-- The post-closure stage selected by the construction is an unhindered
stage web. -/
theorem laterStage_isUnhindered
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {ZBefore T B X0 : Set V}
    {Preserves : FinitePath Gamma.graph → Prop}
    (R : MovingGlobalClosure C ZBefore T B X0 Preserves) :
    (C.ladder.stageWeb R.later.stage).IsUnhindered :=
  R.later.stageWeb_isUnhindered

end MovingGlobalClosure

#print axioms MovingGlobalClosure.exists_of_limitRoof_geometry
#print axioms MovingGlobalClosure.laterStage_isUnhindered
#print axioms exists_assertions_9_22_to_9_25_of_roof_hammocks
#print axioms Moving931GlobalClosure.exists_of_scheduledSeed
#print axioms Moving931GlobalClosure.laterStage_isUnhindered
#print axioms DynamicMoving931GlobalClosure.exists_of_globalClosedSet

end Erdos599.Blueprint.LinkageBlueprint
