/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayStageGeometryCore
import ErdosProblems.Erdos599.LadderExistence
import ErdosProblems.Erdos599.RegularCardinal

/-!
# Concrete club-stage geometry for the half-way construction

This file constructs the `ClubStageGeometry` retained by the Section 9
blueprint transaction.  The ladder is the canonical legal ladder of length
`kappa^+`.  Theorem 7.30 (passed in its exact grounding form) makes the
ladder obstruction nonstationary in an unhindered web, and hence supplies a
club disjoint from `phi`.  Two successive points of that club are the old
and new transaction stages.

The only data belonging to the closing-up recursion itself are its increasing
stage family and the stagewise cardinal bound.  These imply the apparently
stronger bound on `Z_{< beta}` immediately: monotonicity puts every earlier
closed set inside `Z_beta`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating Ladder

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry

/-! ## The causal closing-up recursion -/

/-- Local data for the source recursion `Z_alpha`.

The safety field is intentionally causal: it is required only for a
`kappa`-bounded preceding set already contained in the current roof.  This
is the exact local geometry needed to run Assertions 9.22--9.25 at the
current stage; it does not assume a final closed set. -/
structure CausalClosureSystem
    (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (kappa theta : Cardinal.{u}) where
  seed : Ladder.Stage theta -> Set V
  innerRoof : Ladder.Stage theta -> Set V
  outerRoof : Ladder.Stage theta -> Set V
  targetSlice : Ladder.Stage theta -> Set V
  targetSide : Ladder.Stage theta -> Set V
  Preserves : Ladder.Stage theta -> FinitePath Gamma.graph -> Prop
  reference_isWarp : Gamma.IsWarp Y
  seed_card : forall a, #(seed a) <= kappa
  seed_in_roof : forall a, seed a ⊆ outerRoof a
  outerRoof_mono : forall {a b}, a <= b -> outerRoof a ⊆ outerRoof b
  reference_in_roof : forall a p, p ∈ Y -> p.support ⊆ outerRoof a
  target_paths : forall a v, v ∈ targetSlice a ∩ outerRoof a ->
    exists p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ targetSide a ∧
        p.support ⊆ outerRoof a ∧ Preserves a p
  safe_in_roof : forall a (before : Set V),
    #before <= kappa -> before ⊆ outerRoof a ->
      EligibleHammocksContainedInRoof Gamma Y before
        (innerRoof a) (outerRoof a)
  capacity_infinite : aleph0 <= kappa

namespace CausalClosureSystem

variable {theta : Cardinal.{u}}

/-- The union of all recursively constructed stages strictly preceding
`a`.  The dependent argument prevents a consumer from reading a future
stage while constructing the current one. -/
def priorUnion (a : Ladder.Stage theta)
    (previous : forall b : Ladder.Stage theta, b < a -> Set V) : Set V :=
  ⋃ b : Set.Iio a, previous b.1 b.2

theorem previous_subset_priorUnion
    (a : Ladder.Stage theta)
    (previous : forall b : Ladder.Stage theta, b < a -> Set V)
    {b : Ladder.Stage theta} (hba : b < a) :
    previous b hba ⊆ priorUnion a previous := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨⟨b, hba⟩, hx⟩

/-- The current one-step operator from Assertions 9.22--9.25. -/
def stageStep (S : CausalClosureSystem Gamma Y kappa theta)
    (a : Ladder.Stage theta) (before : Set V) : Set V -> Set V :=
  closingStep Gamma Y kappa before (S.innerRoof a) (S.outerRoof a)
    (S.targetSlice a) (S.targetSide a) (S.Preserves a)
    (S.target_paths a)

/-- One transfinite stage: collect every earlier closure, adjoin the
stage seed, and run the explicit omega hammock closure. -/
def build (S : CausalClosureSystem Gamma Y kappa theta)
    (a : Ladder.Stage theta)
    (previous : forall b : Ladder.Stage theta, b < a -> Set V) : Set V :=
  let before := priorUnion a previous
  omegaClosure (S.stageStep a before) (before ∪ S.seed a)

/-- The canonical source-faithful closing-up family. -/
noncomputable def closedStage
    (S : CausalClosureSystem Gamma Y kappa theta)
    (a : Ladder.Stage theta) : Set V :=
  WellFounded.fix wellFounded_lt (fun a previous => S.build a previous) a

theorem closedStage_eq
    (S : CausalClosureSystem Gamma Y kappa theta)
    (a : Ladder.Stage theta) :
    S.closedStage a =
      S.build a (fun b _hba => S.closedStage b) := by
  exact WellFounded.fix_eq wellFounded_lt
    (fun a previous => S.build a previous) a

/-- Every earlier closed stage is inserted into the current causal seed. -/
theorem closedStage_subset_of_lt
    (S : CausalClosureSystem Gamma Y kappa theta)
    {a b : Ladder.Stage theta} (hab : a < b) :
    S.closedStage a ⊆ S.closedStage b := by
  rw [S.closedStage_eq b]
  intro x hx
  apply closureStage_subset_omegaClosure
    (S.stageStep b
      (priorUnion b (fun c _hcb => S.closedStage c)))
    (priorUnion b (fun c _hcb => S.closedStage c) ∪ S.seed b) 0
  exact Or.inl
    (previous_subset_priorUnion b
      (fun c _hcb => S.closedStage c) hab hx)

/-- The canonical causal closure family is increasing. -/
theorem closedStage_mono
    (S : CausalClosureSystem Gamma Y kappa theta) :
    Monotone S.closedStage := by
  intro a b hab
  rcases hab.eq_or_lt with rfl | hab
  · exact Set.Subset.rfl
  · exact S.closedStage_subset_of_lt hab

/-- The type of stages preceding one stage of a `kappa^+` recursion has
cardinality at most `kappa` (in the lifted universe of the stage order). -/
theorem mk_stageIio_le_lift (a : Ladder.Stage (succ kappa)) :
    #(Set.Iio a) <= Cardinal.lift.{u + 1, u} kappa := by
  let f : Set.Iio a -> Set.Iio a.1 := fun b => ⟨b.1.1, b.2⟩
  have hf : Function.Injective f := by
    intro b c hbc
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Set.Iio a.1 => z.1) hbc
  calc
    #(Set.Iio a) <= #(Set.Iio a.1) := Cardinal.mk_le_of_injective hf
    _ = Cardinal.lift.{u + 1, u} a.1.card := by
      rw [Cardinal.mk_Iio_ordinal]
    _ <= Cardinal.lift.{u + 1, u} kappa :=
      Cardinal.lift_le.mpr (CardinalInduction.card_le_of_lt_succ_ord a.2)

/-- A union of the already constructed stages below `a` remains
`kappa`-bounded. -/
theorem mk_priorUnion_le
    (hkappa : aleph0 <= kappa) (a : Ladder.Stage (succ kappa))
    (previous : forall b : Ladder.Stage (succ kappa), b < a -> Set V)
    (hprevious : forall b hba, #(previous b hba) <= kappa) :
    #(priorUnion a previous) <= kappa := by
  let f : Set.Iio a -> Set V := fun b => previous b.1 b.2
  have hfamily := Cardinal.mk_iUnion_le_lift f
  have hindex : Cardinal.lift.{u, u + 1} #(Set.Iio a) <=
      Cardinal.lift.{u + 1, u} kappa := by
    rw [Cardinal.lift_id'.{u, u + 1}]
    exact mk_stageIio_le_lift (kappa := kappa) a
  have hsets : (⨆ b, Cardinal.lift.{u + 1, u} #(f b)) <=
      Cardinal.lift.{u + 1, u} kappa := by
    exact ciSup_le' fun b => Cardinal.lift_le.mpr (hprevious b.1 b.2)
  have hinfinite : aleph0 <= Cardinal.lift.{u + 1, u} kappa := by
    exact Cardinal.aleph0_le_lift.mpr hkappa
  have hbound := hfamily.trans
    (Cardinal.mul_le_of_le hinfinite hindex hsets)
  exact Cardinal.lift_le.mp (by simpa only [f, priorUnion] using hbound)

/-- The explicit omega closure at one causal stage remains
`kappa`-bounded. -/
theorem mk_stageClosure_le
    (S : CausalClosureSystem Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) (before : Set V)
    (hbefore : #before <= kappa) :
    #(omegaClosure (S.stageStep a before) (before ∪ S.seed a)) <= kappa := by
  have hinitial : #(before ∪ S.seed a : Set V) <= kappa :=
    (Cardinal.mk_union_le before (S.seed a)).trans
      (Cardinal.add_le_of_le S.capacity_infinite hbefore (S.seed_card a))
  have hstage : forall n,
      #(closureStage (S.stageStep a before) (before ∪ S.seed a) n) <=
        kappa := by
    apply mk_closureStage_le hinitial
    intro X hX
    exact mk_closingStep_le Gamma Y before (S.innerRoof a) (S.outerRoof a)
      (S.targetSlice a) (S.targetSide a) (S.Preserves a)
      (S.target_paths a) S.reference_isWarp S.capacity_infinite
      (le_refl kappa) hbefore X hX
  change #(⋃ n, closureStage (S.stageStep a before)
    (before ∪ S.seed a) n) <= kappa
  let stages : ULift.{u} Nat -> Set V := fun n =>
    closureStage (S.stageStep a before) (before ∪ S.seed a) n.down
  have heq : (⋃ n, closureStage (S.stageStep a before)
      (before ∪ S.seed a) n) = ⋃ i, stages i := by
    ext x
    simp [stages]
  rw [heq]
  apply CardinalInduction.mk_iUnion_le_of_le S.capacity_infinite
  · simpa [Cardinal.mk_nat] using S.capacity_infinite
  · intro i
    exact hstage i.down

/-- Roof containment of the explicit omega closure at one causal stage. -/
theorem stageClosure_subset_outerRoof
    (S : CausalClosureSystem Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) (before : Set V)
    (hbeforeCard : #before <= kappa)
    (hbeforeRoof : before ⊆ S.outerRoof a) :
    omegaClosure (S.stageStep a before) (before ∪ S.seed a) ⊆
      S.outerRoof a := by
  have hinitial : before ∪ S.seed a ⊆ S.outerRoof a :=
    Set.union_subset hbeforeRoof (S.seed_in_roof a)
  have hstage : forall n,
      closureStage (S.stageStep a before) (before ∪ S.seed a) n ⊆
        S.outerRoof a := by
    apply closureStage_subset_roof hinitial
    intro X hX
    exact closingStep_subset_roof Gamma Y kappa before
      (S.innerRoof a) (S.outerRoof a) (S.targetSlice a) (S.targetSide a)
      (S.Preserves a) (S.target_paths a)
      (S.safe_in_roof a before hbeforeCard hbeforeRoof)
      (S.reference_in_roof a) X hX
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
  exact hstage n hxn

/-- Cardinality and roof containment are maintained simultaneously by the
causal transfinite recursion. -/
theorem closedStage_card_and_subset_outerRoof
    (S : CausalClosureSystem Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) :
    #(S.closedStage a) <= kappa ∧ S.closedStage a ⊆ S.outerRoof a := by
  let wf : WellFounded (fun b a : Ladder.Stage (succ kappa) => b < a) :=
    wellFounded_lt
  induction a using wf.induction with
  | h a ih =>
      rw [S.closedStage_eq a]
      let previous : forall b : Ladder.Stage (succ kappa), b < a -> Set V :=
        fun b _hba => S.closedStage b
      let before : Set V := priorUnion a previous
      have hpreviousCard : forall b hba, #(previous b hba) <= kappa := by
        intro b hba
        exact (ih b hba).1
      have hbeforeCard : #before <= kappa := by
        exact mk_priorUnion_le S.capacity_infinite a previous hpreviousCard
      have hbeforeRoof : before ⊆ S.outerRoof a := by
        intro x hx
        obtain ⟨b, hxb⟩ := Set.mem_iUnion.1 hx
        have hxbRoof : x ∈ S.outerRoof b.1 := (ih b.1 b.2).2 hxb
        exact S.outerRoof_mono b.2.le hxbRoof
      change #(omegaClosure (S.stageStep a before)
          (before ∪ S.seed a)) <= kappa ∧
        omegaClosure (S.stageStep a before) (before ∪ S.seed a) ⊆
          S.outerRoof a
      exact ⟨S.mk_stageClosure_le a before hbeforeCard,
        S.stageClosure_subset_outerRoof a before hbeforeCard hbeforeRoof⟩

theorem closedStage_card
    (S : CausalClosureSystem Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) :
    #(S.closedStage a) <= kappa :=
  (S.closedStage_card_and_subset_outerRoof a).1

theorem closedStage_subset_outerRoof
    (S : CausalClosureSystem Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) :
    S.closedStage a ⊆ S.outerRoof a :=
  (S.closedStage_card_and_subset_outerRoof a).2

end CausalClosureSystem

/-- Source-fixed version of the causal data: the inner and outer roofs are
definitionally the strict and ordinary roofs of one legal ladder's
frontiers.  Thus the consumer cannot accidentally close at a roof unrelated
to the ladder used to select the club stages. -/
structure LadderCausalClosureData
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (L : Gamma.KappaLadder (succ kappa)) where
  seed : Ladder.Stage (succ kappa) -> Set V
  targetSlice : Ladder.Stage (succ kappa) -> Set V
  targetSide : Ladder.Stage (succ kappa) -> Set V
  Preserves : Ladder.Stage (succ kappa) -> FinitePath Gamma.graph -> Prop
  reference_isWarp : Gamma.IsWarp Y
  seed_card : forall a, #(seed a) <= kappa
  seed_in_roof : forall a, seed a ⊆ Gamma.roof (L.frontier a)
  reference_in_roof : forall a p, p ∈ Y ->
    p.support ⊆ Gamma.roof (L.frontier a)
  target_paths : forall a v,
    v ∈ targetSlice a ∩ Gamma.roof (L.frontier a) ->
      exists p : FinitePath Gamma.graph,
        p.start = v ∧ p.finish ∈ targetSide a ∧
          p.support ⊆ Gamma.roof (L.frontier a) ∧ Preserves a p
  safe_in_roof : forall a (before : Set V),
    #before <= kappa -> before ⊆ Gamma.roof (L.frontier a) ->
      EligibleHammocksContainedInRoof Gamma Y before
        (Gamma.strictRoof (L.frontier a)) (Gamma.roof (L.frontier a))
  capacity_infinite : aleph0 <= kappa

namespace LadderCausalClosureData

/-- Forget only the definitional ladder tie.  Ordinary roof monotonicity is
derived from legal-ladder frontier chronology. -/
def toCausalClosureSystem
    {L : Gamma.KappaLadder (succ kappa)}
    (D : LadderCausalClosureData Gamma Y kappa L)
    (hL : DWeb.KappaLadder.Deferred.IsDeferredLegal L) :
    CausalClosureSystem Gamma Y kappa (succ kappa) where
  seed := D.seed
  innerRoof := fun a => Gamma.strictRoof (L.frontier a)
  outerRoof := fun a => Gamma.roof (L.frontier a)
  targetSlice := D.targetSlice
  targetSide := D.targetSide
  Preserves := D.Preserves
  reference_isWarp := D.reference_isWarp
  seed_card := D.seed_card
  seed_in_roof := D.seed_in_roof
  outerRoof_mono := by
    intro a b hab
    rcases hab.lt_or_eq with hab | rfl
    · exact Gamma.roof_cut (hL.frontierChronology hab)
    · exact Set.Subset.rfl
  reference_in_roof := D.reference_in_roof
  target_paths := D.target_paths
  safe_in_roof := D.safe_in_roof
  capacity_infinite := D.capacity_infinite

end LadderCausalClosureData

/-- An increasing, stagewise `kappa`-bounded closing-up family has a
`kappa`-bounded strict initial union at every stage.  The proof uses the
strong form of the source recursion: every earlier stage has already been
absorbed into the current stage. -/
theorem mk_closedBefore_le
    {theta : Cardinal.{u}}
    (closedStage : Ladder.Stage theta -> Set V)
    (hmono : forall {a b}, a <= b -> closedStage a ⊆ closedStage b)
    (hcard : forall a, #(closedStage a) <= kappa)
    (beta : Ladder.Stage theta) :
    #(closedBefore closedStage beta) <= kappa := by
  apply (Cardinal.mk_subtype_mono ?_).trans (hcard beta)
  rintro x ⟨a, ha, hxa⟩
  exact hmono ha.le hxa

/-- A legal ladder, an avoiding club, and a bounded monotone closing-up
family determine a concrete pair of club stages. -/
theorem exists_of_legal_of_avoidingClub
    {theta : Cardinal.{u}}
    (hkappa : aleph0 <= kappa)
    (hGamma : Gamma.IsNormalized)
    (L : Gamma.KappaLadder theta)
    (hL : DWeb.KappaLadder.Deferred.IsDeferredLegal L)
    (hRungs : ∀ a, ¬ (L.stageWeb a).IsUnhindered →
      (L.stageWeb a).IsHindrance (L.rung a))
    (hindranceObstruction : L.phiHindrance ⊆
      DWeb.KappaLadder.Deferred.phi L)
    (Sigma : Set (Ladder.Stage theta))
    (hSigma : Stationary.IsClubBelow theta Sigma)
    (havoid : Disjoint Sigma (DWeb.KappaLadder.Deferred.phi L))
    (closedStage : Ladder.Stage theta -> Set V)
    (hmono : forall {a b}, a <= b -> closedStage a ⊆ closedStage b)
    (hcard : forall a, #(closedStage a) <= kappa) :
    Nonempty (ClubStageGeometry Gamma Y kappa theta) := by
  let zero : Ladder.Stage theta := ⟨0, hL.regular.ord_pos⟩
  let oldStage := RegularCardinal.nextInClub hL.regular Sigma hSigma zero
  let newStage := RegularCardinal.nextInClub hL.regular Sigma hSigma oldStage
  exact ⟨{
    ladder := L
    legal := hL
    hindranceRungs := hRungs
    hindranceObstruction := hindranceObstruction
    normalized := hGamma
    club := Sigma
    club_isClub := hSigma
    club_avoids_phi := havoid
    oldStage := oldStage
    newStage := newStage
    old_mem_club := RegularCardinal.nextInClub_mem
      hL.regular Sigma hSigma zero
    new_mem_club := RegularCardinal.nextInClub_mem
      hL.regular Sigma hSigma oldStage
    old_lt_new := RegularCardinal.lt_nextInClub
      hL.regular Sigma hSigma oldStage
    closedStage := closedStage
    closedStage_mono := hmono
    before_card := mk_closedBefore_le closedStage hmono hcard newStage
    capacity_infinite := hkappa }⟩

/-- Source-faithful construction of the club-stage geometry for the
`kappa^+` ladder used by the half-way argument.

The grounding premise is precisely the reusable implication supplied by
Theorem 7.30: a stationary obstruction set for this legal canonical ladder
produces an ordinary hindrance in the ambient web. -/
theorem exists_for_canonicalLadder
    (hkappa : aleph0 <= kappa)
    (hGamma : Gamma.IsNormalized) (hUnhindered : Gamma.IsUnhindered)
    (preferred : Ladder.Stage (succ kappa) -> Option V)
    (closedStage : Ladder.Stage (succ kappa) -> Set V)
    (hmono : forall {a b}, a <= b -> closedStage a ⊆ closedStage b)
    (hcard : forall a, #(closedStage a) <= kappa)
    (hground :
      let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma (succ kappa) preferred
      DWeb.KappaLadder.Deferred.IsKappaHindrance L →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (ClubStageGeometry Gamma Y kappa (succ kappa)) := by
  let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
    Gamma (succ kappa) preferred
  have hsuccRegular : (succ kappa).IsRegular := Cardinal.isRegular_succ hkappa
  have hsuccUncountable : aleph0 < succ kappa :=
    hkappa.trans_lt (lt_succ kappa)
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  have hL : DWeb.KappaLadder.Deferred.IsDeferredLegal L :=
    DWeb.KappaLadder.Deferred.canonicalDeferredLadder_isDeferredLegal
      preferred hsuccRegular hsuccUncountable hNoEnter
  have hRungs : ∀ a, ¬ (L.stageWeb a).IsUnhindered →
      (L.stageWeb a).IsHindrance (L.rung a) := by
    intro a hstage
    exact DWeb.KappaLadder.canonicalLadderCore_rung_isHindrance
      (G := Gamma) (succ kappa) preferred a hstage
  have hindranceObstruction : L.phiHindrance ⊆
      DWeb.KappaLadder.Deferred.phi L :=
    DWeb.KappaLadder.Deferred.canonicalDeferredLadder_phiHindrance_subset_phi
      preferred hsuccRegular hsuccUncountable hGamma hNoEnter
  have hnonstationary :
      ¬ Stationary.IsStationaryBelow (succ kappa)
        (DWeb.KappaLadder.Deferred.phi L) := by
    intro hstationary
    obtain ⟨W, hW⟩ := hground ⟨hL, hstationary⟩
    exact hUnhindered ⟨W, hW⟩
  obtain ⟨Sigma, hSigma, hdisjoint⟩ :=
    not_isStationary_iff.mp hnonstationary
  have havoid : Disjoint Sigma
      (DWeb.KappaLadder.Deferred.phi L) := hdisjoint.symm
  exact exists_of_legal_of_avoidingClub hkappa hGamma L hL hRungs
    hindranceObstruction
    Sigma hSigma havoid closedStage hmono hcard

/-- Fully concrete form of the preceding theorem.  The closing-up family is
not an input: it is the canonical transfinite family generated by the
source-local hammock data in `S`. -/
theorem exists_for_canonicalLadder_of_causalClosure
    (hGamma : Gamma.IsNormalized) (hUnhindered : Gamma.IsUnhindered)
    (preferred : Ladder.Stage (succ kappa) -> Option V)
    (S : CausalClosureSystem Gamma Y kappa (succ kappa))
    (hground :
      let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma (succ kappa) preferred
      DWeb.KappaLadder.Deferred.IsKappaHindrance L →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (ClubStageGeometry Gamma Y kappa (succ kappa)) := by
  exact exists_for_canonicalLadder S.capacity_infinite hGamma hUnhindered
    preferred S.closedStage (fun {_ _} h => S.closedStage_mono h)
    S.closedStage_card hground

/-- Canonical-ladder specialization in which the closure roofs are fixed to
the same ladder used by the grounding and club arguments. -/
theorem exists_for_canonicalLadder_of_ladderClosureData
    (hGamma : Gamma.IsNormalized) (hUnhindered : Gamma.IsUnhindered)
    (preferred : Ladder.Stage (succ kappa) -> Option V)
    (D : LadderCausalClosureData Gamma Y kappa
      (DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma (succ kappa) preferred))
    (hground :
      let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma (succ kappa) preferred
      DWeb.KappaLadder.Deferred.IsKappaHindrance L →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (ClubStageGeometry Gamma Y kappa (succ kappa)) := by
  let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
    Gamma (succ kappa) preferred
  have hregular : (succ kappa).IsRegular :=
    Cardinal.isRegular_succ D.capacity_infinite
  have huncountable : aleph0 < succ kappa :=
    D.capacity_infinite.trans_lt (lt_succ kappa)
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  have hL : DWeb.KappaLadder.Deferred.IsDeferredLegal L :=
    DWeb.KappaLadder.Deferred.canonicalDeferredLadder_isDeferredLegal
      preferred hregular huncountable hNoEnter
  let S : CausalClosureSystem Gamma Y kappa (succ kappa) :=
    D.toCausalClosureSystem hL
  exact exists_for_canonicalLadder_of_causalClosure hGamma hUnhindered
    preferred S hground

end ClubStageGeometry
end LinkageBlueprint
end Blueprint
end Erdos599
