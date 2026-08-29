/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCardinal
import ErdosProblems.Erdos599.Ladder
import ErdosProblems.Erdos599.LadderBookkeepingChoice
import ErdosProblems.Erdos599.LadderLemma76
import ErdosProblems.Erdos599.LadderRoofRecursion
import ErdosProblems.Erdos599.RegularRows
import ErdosProblems.Erdos599.HalfwayClause
import ErdosProblems.Erdos599.SingularCardinal
import ErdosProblems.Erdos599.RegularClosureAssembly
import ErdosProblems.Erdos599.HindranceGrounding
import ErdosProblems.Erdos599.ControlledSlices
import ErdosProblems.Erdos599.SliceSplice
import ErdosProblems.Erdos599.SliceSpliceConstructor
import ErdosProblems.Erdos599.RegularSuccessorStage
import ErdosProblems.Erdos599.RegularLimitStage
import ErdosProblems.Erdos599.RegularNormalization

/-!
# The regular-cardinal extension step

This file contains the concrete closing-up operation used in the regular
branch of Aharoni--Berger, Section 9.  If `F` is the already available
linkage on the complementary source set, `linkageClosure F S` is the least
omega-closed superset of `S` with the following property: as soon as a
member of `F` meets the set, every vertex of that member is inserted.

The operation is deliberately stronger than closure merely under competing
initial vertices.  It is the exact closure required in the last line of the
regular proof: a member of `F` whose initial vertex is outside the closed
set is then disjoint from every path constructed inside the closed set.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

open DirectedPath

universe u

variable {V : Type u}

namespace RegularExtension

variable (G : DWeb V)

/-! ## Concrete form of the slice data -/

open Ladder RegularCardinal
open SliceSpliceConstructor.LocalConstruction

/-- A path is non-maverick when it is a fragment of the limiting ladder
warp. -/
abbrev IsLadderFragment (Y : Set G.DPath) (p : G.DPath) : Prop :=
  ControlledSlices.IsLadderFragment G Y p

/-- Members of a slice linkage which are not fragments of the ladder. -/
abbrev sliceMavericks (Y T : Set G.DPath) : Set G.DPath :=
  ControlledSlices.sliceMavericks G Y T

/-- The graph-theoretic part of source Assertion 9.15. -/
abbrev SliceGood {κ : Cardinal.{u}} (L : G.KappaLadder κ)
    (T : Set G.DPath) (α β : Ladder.Stage κ) (U : Set V) : Prop :=
  ControlledSlices.SliceGood G L T α β U

/-- Source-faithful specialization of the parameterized controlled-slice
predicate from `RegularCardinal`. -/
def HasRegularControlledSlices {κ : Cardinal.{u}}
    (L : G.KappaLadder κ) (Sigma : Set (Ladder.Stage κ)) (Z : Set V) : Prop :=
  HasControlledSlices Sigma L.frontier Z (SliceGood G L)
    (sliceMavericks G L.limitWarp) (fun p : G.DPath => p.support)

/-- Usable maximal-rung data.  The first conjunct is the roof-order
consequence of maximality; the second says that a hindered stage was given
a hindrance rung. -/
def HasMaximalRungs {κ : Cardinal.{u}} (L : G.KappaLadder κ) : Prop :=
  (∀ a (W : Set (L.stageWeb a).DPath),
      (L.stageWeb a).IsWave W →
        (L.stageWeb a).RoofLE W (L.rung a)) ∧
    ∀ a, ¬ (L.stageWeb a).IsUnhindered →
      (L.stageWeb a).IsHindrance (L.rung a)

/-- The canonical ladder geometry uses a roof-maximal wave at every rung,
and that rung is a hindrance whenever its stage web is hindered. -/
theorem canonicalLadderCore_hasMaximalRungs
    (κ : Cardinal.{u}) (preferred : Ladder.Stage κ → Option V) :
    HasMaximalRungs G (G.canonicalLadderCore κ preferred) := by
  constructor
  · intro a W hW
    exact DWeb.KappaLadder.canonicalLadderCore_roofLE_rung
      κ preferred a W hW
  · intro a hstage
    exact DWeb.KappaLadder.canonicalLadderCore_rung_isHindrance
      κ preferred a hstage

/-- Installing the independent ray-preferring bookkeeping does not alter
the canonical rung geometry, so maximality survives unchanged. -/
theorem canonicalLadderWithBookkeeping_hasMaximalRungs
    (κ : Cardinal.{u}) (preferred : Ladder.Stage κ → Option V) :
    HasMaximalRungs G
      ((G.canonicalLadderCore κ preferred).withValidBookkeeping) := by
  constructor
  · intro a W hW
    exact DWeb.KappaLadder.canonicalLadderCore_roofLE_rung
      κ preferred a W hW
  · intro a hstage
    exact DWeb.KappaLadder.canonicalLadderCore_rung_isHindrance
      κ preferred a hstage

/-- Deferred bookkeeping also leaves the canonical rung geometry unchanged. -/
theorem canonicalDeferredLadder_hasMaximalRungs
    (κ : Cardinal.{u}) (preferred : Ladder.Stage κ → Option V) :
    HasMaximalRungs G
      (DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        G κ preferred) := by
  constructor
  · intro a W hW
    exact DWeb.KappaLadder.canonicalLadderCore_roofLE_rung
      κ preferred a W hW
  · intro a hstage
    exact DWeb.KappaLadder.canonicalLadderCore_rung_isHindrance
      κ preferred a hstage

/-- Every causal prefix of the canonical ladder is already a warp.  This
fact is available before the full legality package: normalization supplies
the no-edge-enters-source premise of the structural ladder recursion.  It is
the warp input used to bound the ladder-path contribution to one closing-up
row. -/
theorem canonicalLadderCore_warpAt_isWarp_of_normalized
    (hG : G.IsNormalized) (κ : Cardinal.{u})
    (preferred : Ladder.Stage κ → Option V) (a : Ladder.Stage κ) :
    G.IsWarp ((G.canonicalLadderCore κ preferred).warpAt a) := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hG hxy).1 hy
  have hgeometry := DWeb.KappaLadder.canonicalLadder_geometry
    (G := G) preferred hNoEnter
  exact hgeometry.warpStages (Ladder.Stage.toExtended a)

/-- Two vertices on one limiting-ladder component already occur together
on one ordinary-stage prefix of that component.  This is the converse
support direction needed by the causal closing-up rows: after a limiting
path meets an earlier row, every one of its vertices is eventually visible
to a later row through some `warpAt` prefix. -/
theorem exists_warpAt_member_containing_two_of_limitWarp
    {κ : Cardinal.{u}} {L : G.KappaLadder κ}
    (hL : SliceSpliceConstructor.SpliceLadderGeometry G L)
    {p : G.DPath} (hp : p ∈ L.limitWarp) {x y : V}
    (hxp : x ∈ p.support) (hyp : y ∈ p.support) :
    ∃ a : Ladder.Stage κ, ∃ q ∈ L.warpAt a,
      q.initial = p.initial ∧ x ∈ q.support ∧ y ∈ q.support := by
  have hsucc : Order.IsSuccLimit κ.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨C, hstage, hlimit⟩ :=
    hL.limitStages (Ladder.finalStage κ) hsucc
  have hpLimit : p ∈ C.limitPaths G := by
    rw [← hlimit]
    exact hp
  obtain ⟨s, rfl⟩ := hpLimit
  obtain ⟨i, qi, hqi, hqiInitial, hxqi⟩ :=
    (C.mem_support_threadLimit_iff G s x).1 hxp
  obtain ⟨j, qj, hqj, hqjInitial, hyqj⟩ :=
    (C.mem_support_threadLimit_iff G s y).1 hyp
  let k : Set.Iio κ.ord := max i j
  obtain ⟨ri, hri, hqiri⟩ :=
    C.grows (show i ≤ k from le_max_left _ _) qi hqi
  obtain ⟨rj, hrj, hqjrj⟩ :=
    C.grows (show j ≤ k from le_max_right _ _) qj hqj
  have hriInitial : ri.initial = s.1 :=
    (G.extends_initial hqiri).symm.trans hqiInitial
  have hrjInitial : rj.initial = s.1 :=
    (G.extends_initial hqjrj).symm.trans hqjInitial
  have hrirj : ri = rj :=
    DWeb.IsWarp.eq_of_initial_eq G (C.isWarp k) hri hrj
      (hriInitial.trans hrjInitial.symm)
  refine ⟨k, ri, ?_, ?_, ?_, ?_⟩
  · have hri' := hri
    rw [hstage k] at hri'
    exact hri'
  · exact hriInitial.trans (C.threadLimit_initial G s).symm
  · exact G.support_mono_of_extends hqiri hxqi
  · rw [hrirj]
    exact G.support_mono_of_extends hqjrj hyqj

/-- Members of `F` which meet a vertex set `S`.  This definition precedes
the row-closure lemmas that use it; keeping it here also makes the module
dependency on `RegularRows` acyclic. -/
def pathsMeeting (F : Set G.DPath) (S : Set V) : Set G.DPath :=
  {p | p ∈ F ∧ (p.support ∩ S).Nonempty}

@[simp]
theorem mem_pathsMeeting {F : Set G.DPath} {S : Set V} {p : G.DPath} :
    p ∈ pathsMeeting G F S ↔ p ∈ F ∧ (p.support ∩ S).Nonempty :=
  Iff.rfl

/-- Stagewise path registrations make the final row union closed under the
limiting ladder warp.  A limiting component and two of its vertices are
simultaneously visible on one finite-stage prefix; registering every such
prefix that meets an earlier row therefore registers the second vertex. -/
theorem isLimitWarpClosed_of_rowRegistrations
    {κ : Cardinal.{u}} {L : G.KappaLadder κ}
    (hL : SliceSpliceConstructor.SpliceLadderGeometry G L)
    (R : RegularRows.RowSystem κ V)
    (hregister : ∀ i a,
      G.vertexSet (pathsMeeting G (L.warpAt a) (R.row i)) ⊆ R.carrier) :
    SliceSplice.IsLimitWarpClosed G L R.carrier := by
  intro p hp hmeet y hyp
  obtain ⟨x, hxp, hxcarrier⟩ := hmeet
  obtain ⟨i, hxi⟩ := RegularRows.RowSystem.mem_carrier.mp hxcarrier
  obtain ⟨a, q, hqa, _hqinitial, hxq, hyq⟩ :=
    exists_warpAt_member_containing_two_of_limitWarp G hL hp hxp hyp
  apply hregister i a
  exact ⟨q, ⟨hqa, ⟨x, hxq, hxi⟩⟩, hyq⟩

/-- The analogous row-registration criterion for the old complementary
linkage.  This is the exact closure fact used by the final untouched-path
union, stated in terms of the causal rows rather than assumed directly. -/
theorem support_subset_carrier_of_rowRegistrations
    {κ : Cardinal.{u}} (R : RegularRows.RowSystem κ V)
    (F : Set G.DPath)
    (hregister : ∀ i,
      G.vertexSet (pathsMeeting G F (R.row i)) ⊆ R.carrier)
    {p : G.DPath} (hpF : p ∈ F)
    (hmeet : (p.support ∩ R.carrier).Nonempty) :
    p.support ⊆ R.carrier := by
  obtain ⟨x, hxp, hxcarrier⟩ := hmeet
  obtain ⟨i, hxi⟩ := RegularRows.RowSystem.mem_carrier.mp hxcarrier
  intro y hyp
  exact hregister i ⟨p, ⟨hpF, ⟨x, hxp, hxi⟩⟩, hyp⟩

/-! ## Registrations supplied by the causal rows

The graph-specific row rule lives in `RegularRows`, upstream from this
module.  The following lemmas discharge the two static registration
hypotheses above from the actual causal recursion.  They are deliberately
proved here: `RegularRows` cannot mention `pathsMeeting` without introducing
an import cycle.
-/

private theorem pathsMeeting_eq_rowPathsMeeting
    (F : Set G.DPath) (S : Set V) :
    pathsMeeting G F S = RegularRows.CausalRegular.rowPathsMeeting G F S := by
  ext p
  constructor
  · rintro ⟨hpF, x, hxp, hxS⟩
    exact ⟨hpF, Set.not_disjoint_iff.2 ⟨x, hxp, hxS⟩⟩
  · rintro ⟨hpF, hpS⟩
    obtain ⟨x, hxp, hxS⟩ := Set.not_disjoint_iff.1 hpS
    exact ⟨hpF, x, hxp, hxS⟩

/-- The seed is present in the carrier of the actual causal row system. -/
theorem rowRule_base_subset_carrier
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
      hG hlower F hF base hbase
    base ⊆ (Q.rowSystem hregular.aleph0_le).carrier := by
  dsimp only
  let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
    hG hlower F hF base hbase
  intro x hx
  let a : Ladder.Stage kappa := ⟨0, hregular.ord_pos⟩
  apply RegularRows.RowSystem.mem_carrier.2
  refine ⟨a, ?_⟩
  change x ∈ (Q.state hregular.aleph0_le a).row
  rw [Q.state_row_eq]
  change x ∈
    ((base ∪ RegularRows.pairRegistrations a
      (RegularRows.CausalRegular.pairEntry G hlower huncountable F a
        (fun b _hba ↦ Q.state hregular.aleph0_le b))) ∪
      RegularRows.tripleRegistrations a
        (RegularRows.CausalRegular.tripleEntry G hregular.aleph0_le a
          (fun b _hba ↦ Q.state hregular.aleph0_le b)))
  exact Or.inl (Or.inl hx)

/-- Every row of the source-shaped causal rule is closed, in the final row
union, under all old-linkage paths meeting that row.  The relevant pair
registration is put into the immediately following row. -/
theorem rowRule_registers_oldLinkage
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
      hG hlower F hF base hbase
    let R := Q.rowSystem hregular.aleph0_le
    ∀ i, G.vertexSet (pathsMeeting G F (R.row i)) ⊆ R.carrier := by
  dsimp only
  let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
    hG hlower F hF base hbase
  let R := Q.rowSystem hregular.aleph0_le
  intro i x hx
  let a : Ladder.Stage kappa :=
    ⟨i.1 + 1, (Cardinal.isSuccLimit_ord hregular.aleph0_le).succ_lt i.2⟩
  have hia : i < a := by
    change i.1 < i.1 + 1
    exact lt_add_one i.1
  have hx' : x ∈ G.vertexSet
      (pathsMeeting G F (Q.state hregular.aleph0_le i).row) := by
    exact hx
  apply RegularRows.RowSystem.mem_carrier.2
  refine ⟨a, ?_⟩
  change x ∈ (Q.state hregular.aleph0_le a).row
  rw [Q.state_row_eq]
  change x ∈
    ((base ∪ RegularRows.pairRegistrations a
      (RegularRows.CausalRegular.pairEntry G hlower huncountable F a
        (fun b _hba ↦ Q.state hregular.aleph0_le b))) ∪
      RegularRows.tripleRegistrations a
        (RegularRows.CausalRegular.tripleEntry G hregular.aleph0_le a
          (fun b _hba ↦ Q.state hregular.aleph0_le b)))
  apply Or.inl
  apply Or.inr
  apply RegularRows.pair_entry_subset_registrations a _
      (⟨i, hia⟩ : Set.Iio a) (⟨i, hia⟩ : Set.Iio a)
  unfold RegularRows.CausalRegular.pairEntry
  apply Or.inl
  change x ∈ RegularRows.CausalRegular.twoWarpRowRegistration G F _
    (Q.state hregular.aleph0_le i).row
  unfold RegularRows.CausalRegular.twoWarpRowRegistration
  apply Or.inl
  rw [← pathsMeeting_eq_rowPathsMeeting G]
  exact hx'

/-- The same causal pair-registration clause closes the final carrier under
every ordinary prefix of the final canonical ladder.  A path visible at
stage `a` is first extended to a common later stage `c`; prefix invariance
identifies the temporary ladder used when row `c` was born with the final
ladder at that stage. -/
theorem rowRule_registers_ladderPrefixes
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
      hG hlower F hF base hbase
    let R := Q.rowSystem hregular.aleph0_le
    let L := G.canonicalLadderCore kappa
      (Q.preferred hregular.aleph0_le)
    ∀ i a,
      G.vertexSet (pathsMeeting G (L.warpAt a) (R.row i)) ⊆ R.carrier := by
  dsimp only
  let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
    hG hlower F hF base hbase
  let R := Q.rowSystem hregular.aleph0_le
  let L := G.canonicalLadderCore kappa
    (Q.preferred hregular.aleph0_le)
  intro i a x hx
  let c : Ladder.Stage kappa :=
    ⟨max i.1 a.1 + 1,
      (Cardinal.isSuccLimit_ord hregular.aleph0_le).succ_lt
        (max_lt i.2 a.2)⟩
  have hic : i < c := by
    change i.1 < max i.1 a.1 + 1
    exact (le_max_left _ _).trans_lt (lt_add_one _)
  have hac : a < c := by
    change a.1 < max i.1 a.1 + 1
    exact (le_max_right _ _).trans_lt (lt_add_one _)
  let prior := fun b (_hbc : b < c) ↦ Q.state hregular.aleph0_le b
  have hpref : ∀ b, b < a →
      RegularRows.CausalRegular.preferredOfPrior c prior b =
        Q.preferred hregular.aleph0_le b := by
    intro b hb
    simp only [RegularRows.CausalRegular.preferredOfPrior, prior,
      dif_pos (hb.trans hac), RegularRows.CausalRowRule.preferred]
  have hprefix :
      (RegularRows.CausalRegular.priorLadder G c
        prior).warpAt a = L.warpAt a := by
    exact RegularRows.LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
      G _ _ a hpref
  apply RegularRows.RowSystem.mem_carrier.2
  refine ⟨c, ?_⟩
  change x ∈ (Q.state hregular.aleph0_le c).row
  rw [Q.state_row_eq]
  change x ∈
    ((base ∪ RegularRows.pairRegistrations c
      (RegularRows.CausalRegular.pairEntry G hlower huncountable F c
        (fun b _hbc ↦ Q.state hregular.aleph0_le b))) ∪
      RegularRows.tripleRegistrations c
        (RegularRows.CausalRegular.tripleEntry G hregular.aleph0_le c
          (fun b _hbc ↦ Q.state hregular.aleph0_le b)))
  apply Or.inl
  apply Or.inr
  apply RegularRows.pair_entry_subset_registrations c _
      (⟨i, hic⟩ : Set.Iio c) (⟨a, hac⟩ : Set.Iio c)
  unfold RegularRows.CausalRegular.pairEntry
  apply Or.inl
  unfold RegularRows.CausalRegular.twoWarpRowRegistration
  apply Or.inr
  rw [hprefix, ← pathsMeeting_eq_rowPathsMeeting G]
  exact hx

/-- Consequently the carrier of the actual causal row rule has both closure
properties required by the regular splice and the final untouched-path
assembly. -/
theorem rowRule_carrier_closure
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (hgeometry : SliceSpliceConstructor.SpliceLadderGeometry G
      (G.canonicalLadderCore kappa
        ((RegularRows.CausalRegular.rowRule G hregular huncountable
          hG hlower F hF base hbase).preferred hregular.aleph0_le))) :
    let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
      hG hlower F hF base hbase
    let R := Q.rowSystem hregular.aleph0_le
    let L := G.canonicalLadderCore kappa
      (Q.preferred hregular.aleph0_le)
    SliceSplice.IsLimitWarpClosed G L R.carrier ∧
      (∀ p ∈ F, (p.support ∩ R.carrier).Nonempty →
        p.support ⊆ R.carrier) := by
  dsimp only
  let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
    hG hlower F hF base hbase
  let R := Q.rowSystem hregular.aleph0_le
  let L := G.canonicalLadderCore kappa
    (Q.preferred hregular.aleph0_le)
  constructor
  · exact isLimitWarpClosed_of_rowRegistrations G hgeometry R
      (rowRule_registers_ladderPrefixes G hregular huncountable hG
        hlower F hF base hbase)
  · intro p hpF hpMeet
    exact support_subset_carrier_of_rowRegistrations G R F
      (rowRule_registers_oldLinkage G hregular huncountable hG
        hlower F hF base hbase) hpF hpMeet

/-- The request table computed from a strict causal prefix agrees at every
coordinate already visible in that prefix with the final request table.
This is the request-level counterpart of canonical-ladder prefix
invariance. -/
theorem priorRequest_eq_finalRequest_of_lt
    {kappa : Cardinal.{u}} (Q : RegularRows.CausalRowRule kappa V)
    (hkappa : ℵ₀ ≤ kappa)
    {c delta gamma : Ladder.Stage kappa}
    (hdelta : delta < c) (hgamma : gamma < c) :
    RegularRows.CausalRegular.priorRequest G hkappa c
        (fun b _hbc ↦ Q.state hkappa b) delta gamma =
      RegularRows.CausalRegular.finalRequest G Q hkappa delta gamma := by
  have hfrontier :
      (RegularRows.CausalRegular.priorLadder G c
        (fun b _hbc ↦ Q.state hkappa b)).frontier delta =
      (G.canonicalLadderCore kappa
        (Q.preferred hkappa)).frontier delta := by
    apply RegularRows.LadderPrefix.canonicalLadderCore_frontier_eq_of_forall_lt
    intro b hb
    exact Q.priorPreferred_eq_preferred_of_lt hkappa (hb.trans hdelta)
  ext x
  simp only [RegularRows.CausalRegular.priorRequest,
    RegularRows.CausalRegular.finalRequest,
    ControlledSlices.diagonalRequest, Set.mem_inter_iff, hfrontier]
  constructor
  · rintro ⟨hxfrontier, theta, eta, htheta, heta, hx⟩
    refine ⟨hxfrontier, theta, eta, htheta, heta, ?_⟩
    rw [RegularRows.CausalRegular.priorEnumeration_eq_actual_of_lt
      Q hkappa (htheta.trans hgamma)] at hx
    exact hx
  · rintro ⟨hxfrontier, theta, eta, htheta, heta, hx⟩
    refine ⟨hxfrontier, theta, eta, htheta, heta, ?_⟩
    rw [RegularRows.CausalRegular.priorEnumeration_eq_actual_of_lt
      Q hkappa (htheta.trans hgamma)]
    exact hx

/-- The stable enumeration stored by the causal states enumerates every
member of every final row. -/
theorem actualEnumeration_enumerates
    {kappa : Cardinal.{u}} (Q : RegularRows.CausalRowRule kappa V)
    (hkappa : ℵ₀ ≤ kappa) :
    RegularCardinal.EnumeratesRows (Q.rowSystem hkappa).row
      (RegularRows.CausalRegular.actualEnumeration Q hkappa) := by
  intro theta x hx
  let xs : (Q.state hkappa theta).row := ⟨x, hx⟩
  exact ⟨(Q.state hkappa theta).rowEmbedding hkappa xs,
    RegularCardinal.enumerateAlong_apply
      ((Q.state hkappa theta).rowEmbedding hkappa) xs⟩

/-- Assertion (9.13) for the final causal request table: every small subset
of one frontier inside the completed carrier is captured by a diagonal
request. -/
theorem finalRequest_captures_small
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (Q : RegularRows.CausalRowRule kappa V)
    {delta : Ladder.Stage kappa} {U : Set V}
    (hU : U ⊆
      (G.canonicalLadderCore kappa
        (Q.preferred hregular.aleph0_le)).frontier delta ∩
        (Q.rowSystem hregular.aleph0_le).carrier)
    (hUcard : #U < kappa) :
    ∃ gamma, U ⊆ RegularRows.CausalRegular.finalRequest G Q
      hregular.aleph0_le delta gamma := by
  let R := Q.rowSystem hregular.aleph0_le
  obtain ⟨gamma, hdiagonal⟩ :=
    RegularCardinal.exists_diagonalSlice_superset hregular
      (actualEnumeration_enumerates Q hregular.aleph0_le)
      (U := U) (fun x hx ↦ hU hx |>.2) hUcard
  refine ⟨gamma, ?_⟩
  intro x hx
  exact ⟨(hU hx).1, hdiagonal hx⟩

/-- Every coordinate of the final annular candidate table is registered in
the causal carrier.  The coordinate is installed at a stage strictly above
all three of its indices; prefix invariance then identifies the causal
candidate with the final one. -/
theorem rowRule_registers_candidateVertices
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
      hG hlower F hF base hbase
    let R := Q.rowSystem hregular.aleph0_le
    let L := G.canonicalLadderCore kappa
      (Q.preferred hregular.aleph0_le)
    let request := RegularRows.CausalRegular.finalRequest G Q
      hregular.aleph0_le
    ∀ delta beta gamma,
      SliceCandidate.candidateVerticesAt G L request delta beta gamma ⊆
        R.carrier := by
  dsimp only
  let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
    hG hlower F hF base hbase
  let R := Q.rowSystem hregular.aleph0_le
  let L := G.canonicalLadderCore kappa
    (Q.preferred hregular.aleph0_le)
  let request := RegularRows.CausalRegular.finalRequest G Q
    hregular.aleph0_le
  intro delta beta gamma x hx
  let c : Ladder.Stage kappa :=
    ⟨max (max delta.1 beta.1) gamma.1 + 1,
      (Cardinal.isSuccLimit_ord hregular.aleph0_le).succ_lt
        (max_lt (max_lt delta.2 beta.2) gamma.2)⟩
  have hdelta : delta < c := by
    change delta.1 < max (max delta.1 beta.1) gamma.1 + 1
    exact (le_max_left delta.1 beta.1).trans
      (le_max_left (max delta.1 beta.1) gamma.1) |>.trans_lt (lt_add_one _)
  have hbeta : beta < c := by
    change beta.1 < max (max delta.1 beta.1) gamma.1 + 1
    exact (le_max_right delta.1 beta.1).trans
      (le_max_left (max delta.1 beta.1) gamma.1) |>.trans_lt (lt_add_one _)
  have hgamma : gamma < c := by
    change gamma.1 < max (max delta.1 beta.1) gamma.1 + 1
    exact (le_max_right (max delta.1 beta.1) gamma.1).trans_lt
      (lt_add_one _)
  let prior := fun b (_hbc : b < c) ↦ Q.state hregular.aleph0_le b
  let Lc := RegularRows.CausalRegular.priorLadder G c prior
  let requestc := RegularRows.CausalRegular.priorRequest G
    hregular.aleph0_le c prior
  have hwarpDelta : Lc.warpAt delta = L.warpAt delta := by
    apply RegularRows.LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
    intro b hb
    exact Q.priorPreferred_eq_preferred_of_lt hregular.aleph0_le
      (hb.trans hdelta)
  have hwarpBeta : Lc.warpAt beta = L.warpAt beta := by
    apply RegularRows.LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
    intro b hb
    exact Q.priorPreferred_eq_preferred_of_lt hregular.aleph0_le
      (hb.trans hbeta)
  have hfrontierDelta : Lc.frontier delta = L.frontier delta := by
    apply RegularRows.LadderPrefix.canonicalLadderCore_frontier_eq_of_forall_lt
    intro b hb
    exact Q.priorPreferred_eq_preferred_of_lt hregular.aleph0_le
      (hb.trans hdelta)
  have hfrontierBeta : Lc.frontier beta = L.frontier beta := by
    apply RegularRows.LadderPrefix.canonicalLadderCore_frontier_eq_of_forall_lt
    intro b hb
    exact Q.priorPreferred_eq_preferred_of_lt hregular.aleph0_le
      (hb.trans hbeta)
  have hrequest : requestc delta gamma = request delta gamma := by
    exact priorRequest_eq_finalRequest_of_lt G Q hregular.aleph0_le
      hdelta hgamma
  have hcandidate :
      SliceCandidate.candidateVerticesAt G Lc requestc delta beta gamma =
        SliceCandidate.candidateVerticesAt G L request delta beta gamma :=
    SliceCandidate.candidateVerticesAt_congr_stageData hwarpDelta hwarpBeta
      hfrontierDelta hfrontierBeta hrequest
  rw [← hcandidate] at hx
  apply RegularRows.RowSystem.mem_carrier.2
  refine ⟨c, ?_⟩
  change x ∈ (Q.state hregular.aleph0_le c).row
  rw [Q.state_row_eq]
  change x ∈
    ((base ∪ RegularRows.pairRegistrations c
      (RegularRows.CausalRegular.pairEntry G hlower huncountable F c
        (fun b _hbc ↦ Q.state hregular.aleph0_le b))) ∪
      RegularRows.tripleRegistrations c
        (RegularRows.CausalRegular.tripleEntry G hregular.aleph0_le c
          (fun b _hbc ↦ Q.state hregular.aleph0_le b)))
  apply Or.inr
  apply RegularRows.triple_entry_subset_registrations c _
      (⟨delta, hdelta⟩ : Set.Iio c) (⟨beta, hbeta⟩ : Set.Iio c)
      (⟨gamma, hgamma⟩ : Set.Iio c)
  exact hx

/-- Union form of the preceding coordinatewise registration theorem. -/
theorem rowRule_registers_allCandidateMavericks
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
      hG hlower F hF base hbase
    let R := Q.rowSystem hregular.aleph0_le
    let L := G.canonicalLadderCore kappa
      (Q.preferred hregular.aleph0_le)
    let request := RegularRows.CausalRegular.finalRequest G Q
      hregular.aleph0_le
    SliceCandidate.chosenAnnularMaverickVertices G L request ⊆ R.carrier := by
  dsimp only
  intro x hx
  obtain ⟨delta, hx⟩ := Set.mem_iUnion.1 hx
  obtain ⟨beta, hx⟩ := Set.mem_iUnion.1 hx
  obtain ⟨gamma, hx⟩ := Set.mem_iUnion.1 hx
  exact rowRule_registers_candidateVertices G hregular huncountable hG
    hlower F hF base hbase delta beta gamma hx

/-- A club avoiding the ladder obstruction consists of unhindered stages,
provided source Lemma 7.6 has been established for the constructed ladder. -/
theorem stageWeb_isUnhindered_of_mem_avoiding
    {κ : Cardinal.{u}} {L : G.KappaLadder κ}
    (hmax : HasMaximalRungs G L) (hhindrance : L.phiHindrance ⊆ L.phi)
    {Sigma : Set (Ladder.Stage κ)} (havoid : Disjoint Sigma L.phi)
    {a : Ladder.Stage κ} (ha : a ∈ Sigma) :
    (L.stageWeb a).IsUnhindered := by
  intro h
  obtain ⟨W, hW⟩ := h
  have hrung : (L.stageWeb a).IsHindrance (L.rung a) :=
    hmax.2 a (fun hstage => hstage ⟨W, hW⟩)
  exact Set.disjoint_left.1 havoid ha (hhindrance hrung)

/-- Normalized legal-ladder specialization of the club-stage
unhinderedness argument.  Source Lemma 7.6 supplies the obstruction
inclusion, so no separate rung-bookkeeping hypothesis remains. -/
theorem stageWeb_isUnhindered_of_mem_avoiding_of_normalized
    {κ : Cardinal.{u}} {L : G.KappaLadder κ}
    (hG : G.IsNormalized) (hlegal : L.IsLegal)
    (hmax : HasMaximalRungs G L)
    {Sigma : Set (Ladder.Stage κ)} (havoid : Disjoint Sigma L.phi)
    {a : Ladder.Stage κ} (ha : a ∈ Sigma) :
    (L.stageWeb a).IsUnhindered :=
  stageWeb_isUnhindered_of_mem_avoiding G hmax
    (L.phiHindrance_subset_phi hG hlegal) havoid ha

/-- Deferred-bookkeeping specialization of the club-stage argument.  The
obstruction set here is `Deferred.phi`, not the legacy projection on the
ladder structure. -/
theorem stageWeb_isUnhindered_of_mem_avoiding_of_deferred
    {kappa : Cardinal.{u}} {L : G.KappaLadder kappa}
    (hmax : HasMaximalRungs G L)
    (hhindrance : L.phiHindrance ⊆ DWeb.KappaLadder.Deferred.phi L)
    {Sigma : Set (Ladder.Stage kappa)}
    (havoid : Disjoint Sigma (DWeb.KappaLadder.Deferred.phi L))
    {a : Ladder.Stage kappa} (ha : a ∈ Sigma) :
    (L.stageWeb a).IsUnhindered := by
  intro h
  obtain ⟨W, hW⟩ := h
  have hrung : (L.stageWeb a).IsHindrance (L.rung a) :=
    hmax.2 a (fun hstage ↦ hstage ⟨W, hW⟩)
  exact Set.disjoint_left.1 havoid ha (hhindrance hrung)

/-- Club avoidance from the exact implication asserted by Theorem 7.30:
every stationary legal ladder obstruction grounds to an ordinary
hindrance.  This formulation keeps the Section 8 theorem as a reusable
input and performs the short unhinderedness contradiction locally. -/
theorem exists_club_avoiding_phi_of_grounding
    {κ : Cardinal.{u}} {L : G.KappaLadder κ}
    (hG : G.IsUnhindered) (hlegal : L.IsLegal)
    (hground : L.IsKappaHindrance →
      ∃ W : Set G.DPath, G.IsHindrance W) :
    ∃ Sigma : Set (Ladder.Stage κ),
      Stationary.IsClubBelow κ Sigma ∧ Disjoint Sigma L.phi := by
  have hnonstationary :
      ¬ Stationary.IsStationaryBelow κ L.phi := by
    intro hstationary
    obtain ⟨W, hW⟩ := hground ⟨hlegal, hstationary⟩
    exact hG ⟨W, hW⟩
  obtain ⟨Sigma, hSigma, hdisjoint⟩ :=
    not_isStationary_iff.mp hnonstationary
  exact ⟨Sigma, hSigma, hdisjoint.symm⟩

/-- Club avoidance for the repaired deferred obstruction set.  This is the
nonstationarity conversion needed by the canonical deferred limit compiler. -/
theorem exists_club_avoiding_deferred_phi_of_grounding
    {κ : Cardinal.{u}} {L : G.KappaLadder κ}
    (hG : G.IsUnhindered)
    (hlegal : DWeb.KappaLadder.Deferred.IsDeferredLegal L)
    (hground : DWeb.KappaLadder.Deferred.IsKappaHindrance L →
      ∃ W : Set G.DPath, G.IsHindrance W) :
    ∃ Sigma : Set (Ladder.Stage κ),
      Stationary.IsClubBelow κ Sigma ∧
        Disjoint Sigma (DWeb.KappaLadder.Deferred.phi L) := by
  have hnonstationary : ¬ Stationary.IsStationaryBelow κ
      (DWeb.KappaLadder.Deferred.phi L) := by
    intro hstationary
    obtain ⟨W, hW⟩ := hground ⟨hlegal, hstationary⟩
    exact hG ⟨W, hW⟩
  obtain ⟨Sigma, hSigma, hdisjoint⟩ :=
    not_isStationary_iff.mp hnonstationary
  exact ⟨Sigma, hSigma, hdisjoint.symm⟩

/-- The exact remaining Section 8 input for the canonical deferred ladder:
stationarity of its obstruction set produces an ordinary hindrance.  Keeping
this interface independent of the causal-row construction makes explicit
that grounding depends only on the preferred-vertex bookkeeping. -/
def HasCanonicalDeferredGrounding
    (kappa : Cardinal.{u})
    (preferred : Ladder.Stage kappa → Option V) : Prop :=
  let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
    G kappa preferred
  DWeb.KappaLadder.Deferred.IsKappaHindrance L →
    ∃ W : Set G.DPath, G.IsHindrance W

/-- Canonical deferred club avoidance together with the stage-web
unhinderedness needed to construct annular slices. -/
theorem exists_canonicalDeferredLadder_club_unhindered_of_grounding
    (kappa : Cardinal.{u}) (preferred : Ladder.Stage kappa → Option V)
    (hregular : kappa.IsRegular) (huncountable : ℵ₀ < kappa)
    (hGNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hground : HasCanonicalDeferredGrounding G kappa preferred) :
    let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
      G kappa preferred
    ∃ Sigma : Set (Ladder.Stage kappa),
      Stationary.IsClubBelow kappa Sigma ∧
        Disjoint Sigma (DWeb.KappaLadder.Deferred.phi L) ∧
        ∀ a ∈ Sigma, (L.stageWeb a).IsUnhindered := by
  dsimp only at hground ⊢
  let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
    G kappa preferred
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hGNorm hxy).1 hy
  have hlegal : DWeb.KappaLadder.Deferred.IsDeferredLegal L :=
    DWeb.KappaLadder.Deferred.canonicalDeferredLadder_isDeferredLegal
      preferred hregular huncountable hNoEnter
  have hmax : HasMaximalRungs G L :=
    canonicalDeferredLadder_hasMaximalRungs G kappa preferred
  have hhindrance : L.phiHindrance ⊆
      DWeb.KappaLadder.Deferred.phi L :=
    DWeb.KappaLadder.Deferred.canonicalDeferredLadder_phiHindrance_subset_phi
      preferred hregular huncountable hGNorm hNoEnter
  obtain ⟨Sigma, hSigma, havoid⟩ :=
    exists_club_avoiding_deferred_phi_of_grounding
      G hG hlegal hground
  refine ⟨Sigma, hSigma, havoid, ?_⟩
  intro a ha
  exact stageWeb_isUnhindered_of_mem_avoiding_of_deferred
    G hmax hhindrance havoid ha

/-- One path-closing step. -/
def linkageClosureStep (F : Set G.DPath) (S : Set V) : Set V :=
  S ∪ G.vertexSet (pathsMeeting G F S)

/-- The finite iterations of `linkageClosureStep`. -/
def linkageClosureIterate (F : Set G.DPath) (S : Set V) : ℕ → Set V
  | 0 => S
  | n + 1 =>
      linkageClosureStep G F (linkageClosureIterate F S n)

/-- The omega closure of `S` under paths of `F` which meet it. -/
def linkageClosure (F : Set G.DPath) (S : Set V) : Set V :=
  ⋃ n, linkageClosureIterate (G := G) F S n

theorem linkageClosureIterate_subset_succ (F : Set G.DPath) (S : Set V)
    (n : ℕ) :
    linkageClosureIterate (G := G) F S n ⊆
      linkageClosureIterate (G := G) F S (n + 1) := by
  intro x hx
  exact Or.inl hx

theorem linkageClosureIterate_mono_nat (F : Set G.DPath) (S : Set V) :
    Monotone (linkageClosureIterate (G := G) F S) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact Subset.rfl
  | succ n _ ih =>
      exact ih.trans (linkageClosureIterate_subset_succ G F S n)

theorem subset_linkageClosure (F : Set G.DPath) (S : Set V) :
    S ⊆ linkageClosure G F S := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨0, hx⟩

/-- A path which already meets `S` is inserted in the very next closing
step, together with all of its vertices. -/
theorem support_subset_linkageClosureStep_of_meets
    (F : Set G.DPath) (S : Set V) {p : G.DPath}
    (hpF : p ∈ F) (hp : (p.support ∩ S).Nonempty) :
    p.support ⊆ linkageClosureStep G F S := by
  intro x hxp
  exact Or.inr ⟨p, ⟨hpF, hp⟩, hxp⟩

/-- The omega union is closed under every whole `F`-path that meets it. -/
theorem support_subset_linkageClosure_of_meets
    (F : Set G.DPath) (S : Set V) {p : G.DPath}
    (hpF : p ∈ F) (hp : (p.support ∩ linkageClosure G F S).Nonempty) :
    p.support ⊆ linkageClosure G F S := by
  obtain ⟨x, hxp, hx⟩ := hp
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
  intro y hyp
  apply Set.mem_iUnion.2
  refine ⟨n + 1, Or.inr ?_⟩
  exact ⟨p, ⟨hpF, ⟨x, hxp, hxn⟩⟩, hyp⟩

/-- In particular, every old path meeting the closure starts in it. -/
theorem initial_mem_linkageClosure_of_meets
    (F : Set G.DPath) (S : Set V) {p : G.DPath}
    (hpF : p ∈ F) (hp : (p.support ∩ linkageClosure G F S).Nonempty) :
    p.initial ∈ linkageClosure G F S :=
  support_subset_linkageClosure_of_meets G F S hpF hp
    p.initial_mem_support

private theorem pathsMeeting_eq_singular_pathsMeeting
    (F : Set G.DPath) (S : Set V) :
    pathsMeeting G F S =
      {p | p ∈ F ∧ ¬ Disjoint p.support S} := by
  ext p
  constructor
  · rintro ⟨hpF, x, hxp, hxS⟩
    exact ⟨hpF, Set.not_disjoint_iff.2 ⟨x, hxp, hxS⟩⟩
  · rintro ⟨hpF, hpS⟩
    obtain ⟨x, hxp, hxS⟩ := Set.not_disjoint_iff.1 hpS
    exact ⟨hpF, x, hxp, hxS⟩

/-- A single path-closing step through an arbitrary warp preserves a
`≤ κ` cardinal bound.  Rays cause no difficulty because every directed
path in this development has countable support. -/
theorem mk_linkageClosureStep_le_of_warp {F : Set G.DPath} {S : Set V}
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hFwarp : G.IsWarp F)
    (hS : #S ≤ κ) :
    #(linkageClosureStep G F S) ≤ κ := by
  have hpaths : #(pathsMeeting G F S) ≤ κ := by
    rw [pathsMeeting_eq_singular_pathsMeeting G F S]
    exact (G.mk_pathsMeeting_le F S hFwarp).trans hS
  have hvertices : #(G.vertexSet (pathsMeeting G F S)) ≤ κ := by
    by_cases hnonempty : (pathsMeeting G F S).Nonempty
    · letI : Nonempty (pathsMeeting G F S) := hnonempty.to_subtype
      have heq : G.vertexSet (pathsMeeting G F S) =
          ⋃ p : pathsMeeting G F S, p.1.support := by
        ext x
        simp only [DWeb.vertexSet, Set.mem_ofPred_eq, Set.mem_iUnion]
        constructor
        · rintro ⟨p, hp, hxp⟩
          exact ⟨⟨p, hp⟩, hxp⟩
        · rintro ⟨p, hxp⟩
          exact ⟨p.1, p.2, hxp⟩
      rw [heq]
      refine (Cardinal.mk_iUnion_le
        (fun p : pathsMeeting G F S => p.1.support)).trans ?_
      apply Cardinal.mul_le_of_le hκ hpaths
      apply ciSup_le
      intro p
      exact p.1.support_countable.le_aleph0.trans hκ
    · have hempty : pathsMeeting G F S = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hnonempty
      rw [hempty, DWeb.vertexSet]
      simp
  exact (Cardinal.mk_union_le S (G.vertexSet (pathsMeeting G F S))).trans
    (Cardinal.add_le_of_le hκ hS hvertices)

/-- The new vertices contributed by all members of a warp meeting one
bounded row are still bounded by the same infinite cardinal.  This is the
stagewise form used by the causal `(9.13a)` row rule: it exposes only the
new registration term, rather than the row together with that term. -/
theorem mk_vertexSet_pathsMeeting_le_of_warp
    {F : Set G.DPath} {S : Set V} {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hFwarp : G.IsWarp F) (hS : #S ≤ κ) :
    #(G.vertexSet (pathsMeeting G F S)) ≤ κ := by
  apply (Cardinal.mk_subtype_mono (show
    G.vertexSet (pathsMeeting G F S) ⊆ linkageClosureStep G F S by
      intro x hx
      exact Or.inr hx)).trans
  exact mk_linkageClosureStep_le_of_warp G hκ hFwarp hS

/-- The two ambient path-closure contributions made from one earlier row:
whole old-linkage paths and whole current ladder-warp paths which meet it. -/
def twoWarpRowRegistration (F Y : Set G.DPath) (S : Set V) : Set V :=
  G.vertexSet (pathsMeeting G F S) ∪
    G.vertexSet (pathsMeeting G Y S)

theorem mk_twoWarpRowRegistration_le
    {F Y : Set G.DPath} {S : Set V} {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hF : G.IsWarp F) (hY : G.IsWarp Y)
    (hS : #S ≤ κ) :
    #(twoWarpRowRegistration G F Y S) ≤ κ := by
  apply (Cardinal.mk_union_le _ _).trans
  exact Cardinal.add_le_of_le hκ
    (mk_vertexSet_pathsMeeting_le_of_warp G hκ hF hS)
    (mk_vertexSet_pathsMeeting_le_of_warp G hκ hY hS)

theorem vertexSet_pathsMeeting_left_subset_twoWarpRowRegistration
    (F Y : Set G.DPath) (S : Set V) :
    G.vertexSet (pathsMeeting G F S) ⊆
      twoWarpRowRegistration G F Y S :=
  Set.subset_union_left

theorem vertexSet_pathsMeeting_right_subset_twoWarpRowRegistration
    (F Y : Set G.DPath) (S : Set V) :
    G.vertexSet (pathsMeeting G Y S) ⊆
      twoWarpRowRegistration G F Y S :=
  Set.subset_union_right

/-- Finite-character specialization retained for callers which already
carry linkage data. -/
theorem mk_linkageClosureStep_le {F : Set G.DPath} {S : Set V}
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hFwarp : G.IsWarp F)
    (_hFfinite : G.HasFiniteCharacter F) (hS : #S ≤ κ) :
    #(linkageClosureStep G F S) ≤ κ :=
  mk_linkageClosureStep_le_of_warp G hκ hFwarp hS

/-- Every finite closing stage has cardinality at most `κ`. -/
theorem mk_linkageClosureIterate_le {F : Set G.DPath} {S : Set V}
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hFwarp : G.IsWarp F)
    (hFfinite : G.HasFiniteCharacter F) (hS : #S ≤ κ) :
    ∀ n, #(linkageClosureIterate (G := G) F S n) ≤ κ := by
  intro n
  induction n with
  | zero => exact hS
  | succ n ih =>
      exact mk_linkageClosureStep_le G hκ hFwarp hFfinite ih

/-- The finite stages are bounded for an arbitrary (possibly ray-valued)
warp. -/
theorem mk_linkageClosureIterate_le_of_warp
    {F : Set G.DPath} {S : Set V} {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hFwarp : G.IsWarp F) (hS : #S ≤ κ) :
    ∀ n, #(linkageClosureIterate (G := G) F S n) ≤ κ := by
  intro n
  induction n with
  | zero => exact hS
  | succ n ih => exact mk_linkageClosureStep_le_of_warp G hκ hFwarp ih

/-- Countably many closing stages preserve the same infinite bound. -/
theorem mk_linkageClosure_le {F : Set G.DPath} {S : Set V}
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hFwarp : G.IsWarp F)
    (hFfinite : G.HasFiniteCharacter F) (hS : #S ≤ κ) :
    #(linkageClosure G F S) ≤ κ := by
  exact DWeb.mk_iUnion_nat_le hκ
    (mk_linkageClosureIterate_le G hκ hFwarp hFfinite hS)

theorem mk_linkageClosure_le_of_warp {F : Set G.DPath} {S : Set V}
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hFwarp : G.IsWarp F)
    (hS : #S ≤ κ) :
    #(linkageClosure G F S) ≤ κ := by
  exact DWeb.mk_iUnion_nat_le hκ
    (mk_linkageClosureIterate_le_of_warp G hκ hFwarp hS)

/-- Starting from exactly `κ` points, closing under a finite-character warp
still has cardinality exactly `κ`. -/
theorem mk_linkageClosure_eq {F : Set G.DPath} {S : Set V}
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hFwarp : G.IsWarp F)
    (hFfinite : G.HasFiniteCharacter F) (hS : #S = κ) :
    #(linkageClosure G F S) = κ := by
  apply le_antisymm
  · exact mk_linkageClosure_le G hκ hFwarp hFfinite hS.le
  · rw [← hS]
    exact Cardinal.mk_subtype_mono (subset_linkageClosure G F S)

/-! ## Simultaneous closure under the old linkage and the ladder warp -/

/-- One row first closes under `F` and then under `Y`. -/
def twoWarpClosureStep (F Y : Set G.DPath) (S : Set V) : Set V :=
  linkageClosureStep G Y (linkageClosureStep G F S)

def twoWarpClosureIterate (F Y : Set G.DPath) (S : Set V) : ℕ → Set V
  | 0 => S
  | n + 1 => twoWarpClosureStep G F Y
      (twoWarpClosureIterate F Y S n)

/-- The omega closing-up set used in the regular construction for the two
ambient warps `F` and `Y`. -/
def twoWarpClosure (F Y : Set G.DPath) (S : Set V) : Set V :=
  ⋃ n, twoWarpClosureIterate (G := G) F Y S n

theorem subset_twoWarpClosure (F Y : Set G.DPath) (S : Set V) :
    S ⊆ twoWarpClosure G F Y S := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨0, hx⟩

theorem twoWarpClosureIterate_subset_succ
    (F Y : Set G.DPath) (S : Set V) (n : ℕ) :
    twoWarpClosureIterate (G := G) F Y S n ⊆
      twoWarpClosureIterate (G := G) F Y S (n + 1) := by
  intro x hx
  exact Or.inl (Or.inl hx)

/-- The joint omega closure contains every whole `F`-path which meets it. -/
theorem support_subset_twoWarpClosure_of_mem_left
    (F Y : Set G.DPath) (S : Set V) {p : G.DPath}
    (hpF : p ∈ F) (hp : (p.support ∩ twoWarpClosure G F Y S).Nonempty) :
    p.support ⊆ twoWarpClosure G F Y S := by
  obtain ⟨x, hxp, hx⟩ := hp
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
  intro y hyp
  apply Set.mem_iUnion.2
  refine ⟨n + 1, Or.inl ?_⟩
  exact support_subset_linkageClosureStep_of_meets G F _ hpF
    ⟨x, hxp, hxn⟩ hyp

/-- The joint omega closure also contains every whole `Y`-path which meets
it. -/
theorem support_subset_twoWarpClosure_of_mem_right
    (F Y : Set G.DPath) (S : Set V) {p : G.DPath}
    (hpY : p ∈ Y) (hp : (p.support ∩ twoWarpClosure G F Y S).Nonempty) :
    p.support ⊆ twoWarpClosure G F Y S := by
  obtain ⟨x, hxp, hx⟩ := hp
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
  intro y hyp
  apply Set.mem_iUnion.2
  refine ⟨n + 1, ?_⟩
  exact support_subset_linkageClosureStep_of_meets G Y _ hpY
    ⟨x, hxp, Or.inl hxn⟩ hyp

/-- The joint closure is closed under every member of its right-hand warp.
This is the exact closure premise used when ordinary controlled-slice
components are fragments of the limiting ladder warp. -/
theorem twoWarpClosure_isLimitWarpClosed
    {kappa : Cardinal.{u}} (L : G.KappaLadder kappa)
    (F : Set G.DPath) (S : Set V) :
    SliceSplice.IsLimitWarpClosed G L
      (twoWarpClosure G F L.limitWarp S) := by
  intro p hpY hpmeet
  exact support_subset_twoWarpClosure_of_mem_right
    G F L.limitWarp S hpY hpmeet

theorem mk_twoWarpClosureIterate_le
    {F Y : Set G.DPath} {S : Set V} {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hF : G.IsWarp F) (hY : G.IsWarp Y)
    (hS : #S ≤ κ) :
    ∀ n, #(twoWarpClosureIterate (G := G) F Y S n) ≤ κ := by
  intro n
  induction n with
  | zero => exact hS
  | succ n ih =>
      exact mk_linkageClosureStep_le_of_warp G hκ hY
        (mk_linkageClosureStep_le_of_warp G hκ hF ih)

theorem mk_twoWarpClosure_le
    {F Y : Set G.DPath} {S : Set V} {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hF : G.IsWarp F) (hY : G.IsWarp Y)
    (hS : #S ≤ κ) :
    #(twoWarpClosure G F Y S) ≤ κ := by
  exact DWeb.mk_iUnion_nat_le hκ
    (mk_twoWarpClosureIterate_le G hκ hF hY hS)

theorem mk_twoWarpClosure_eq
    {F Y : Set G.DPath} {S : Set V} {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hF : G.IsWarp F) (hY : G.IsWarp Y)
    (hS : #S = κ) :
    #(twoWarpClosure G F Y S) = κ := by
  apply le_antisymm (mk_twoWarpClosure_le G hκ hF hY hS.le)
  rw [← hS]
  exact Cardinal.mk_subtype_mono (subset_twoWarpClosure G F Y S)

/-! ## Final closed-set assembly -/

/-- General closed-carrier form of the final untouched-path assembly.  It
is useful for the causal rows, whose carrier is not definitionally an omega
closure but has the required old-linkage closure theorem. -/
theorem isLinkable_of_internal_linkage_on_closedCarrier
    (A₀ Z : Set V) (F P : Set G.DPath)
    (hA₀Z : A₀ ⊆ Z)
    (hP : IsLinkageBetween G (G.source ∩ Z) G.target P)
    (hPclosed : G.vertexSet P ⊆ Z)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hFclosed : ∀ p ∈ F, (p.support ∩ Z).Nonempty →
      p.support ⊆ Z) :
    IsLinkable G := by
  have houtside :
      ∀ p ∈ RegularClosureAssembly.outsidePaths G F Z,
        Disjoint p.support (G.vertexSet P) := by
    intro p hp
    rw [Set.disjoint_left]
    intro x hxp hxP
    apply hp.2
    exact hFclosed p hp.1 ⟨x, hxp, hPclosed hxP⟩
      p.initial_mem_support
  refine ⟨P ∪ RegularClosureAssembly.outsidePaths G F Z, ?_⟩
  exact RegularClosureAssembly.linkageBetween_union_outside_of_disjoint
    G A₀ Z P F hA₀Z hP hPclosed hF houtside

/-- Once the regular ladder/slice recursion has constructed a linkage on
the sources in the canonical `F`-closure of a base set containing `A₀`, the
untouched members of `F` complete it to a linkage of every source.  The
closure and disjointness needed in this final step are consequences, not
hypotheses. -/
theorem isLinkable_of_internal_linkage_on_linkageClosure_of_subset
    (A₀ S : Set V) (F P : Set G.DPath) (hA₀S : A₀ ⊆ S)
    (hP : IsLinkageBetween G
      (G.source ∩ linkageClosure G F S) G.target P)
    (hPclosed : G.vertexSet P ⊆ linkageClosure G F S)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F) :
    IsLinkable G := by
  let Z := linkageClosure G F S
  have hA₀Z : A₀ ⊆ Z := hA₀S.trans (subset_linkageClosure G F S)
  have houtside :
      ∀ p ∈ RegularClosureAssembly.outsidePaths G F Z,
        Disjoint p.support (G.vertexSet P) := by
    intro p hp
    rw [Set.disjoint_left]
    intro x hxp hxP
    apply hp.2
    apply initial_mem_linkageClosure_of_meets G F S hp.1
    exact ⟨x, hxp, hPclosed hxP⟩
  refine ⟨P ∪ RegularClosureAssembly.outsidePaths G F Z, ?_⟩
  exact RegularClosureAssembly.linkageBetween_union_outside_of_disjoint
    G A₀ Z P F hA₀Z hP hPclosed hF houtside

/-- The common specialization in which the closing-up recursion starts at
the designated source set itself. -/
theorem isLinkable_of_internal_linkage_on_linkageClosure
    (A₀ : Set V) (F P : Set G.DPath)
    (hP : IsLinkageBetween G
      (G.source ∩ linkageClosure G F A₀) G.target P)
    (hPclosed : G.vertexSet P ⊆ linkageClosure G F A₀)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F) :
    IsLinkable G :=
  isLinkable_of_internal_linkage_on_linkageClosure_of_subset
    G A₀ A₀ F P Subset.rfl hP hPclosed hF

/-- Source-faithful two-warp specialization of the final regular assembly.
The set closed during (9.13a) contains whole paths of both the old
complementary linkage `F` and the limiting ladder warp `Y`.  Only the
`F`-closure is needed for the last disjointness argument, while retaining
the `Y`-closure in the statement makes this theorem apply directly to the
set constructed by the regular recursion. -/
theorem isLinkable_of_internal_linkage_on_twoWarpClosure_of_subset
    (A₀ S : Set V) (F Y P : Set G.DPath) (hA₀S : A₀ ⊆ S)
    (hP : IsLinkageBetween G
      (G.source ∩ twoWarpClosure G F Y S) G.target P)
    (hPclosed : G.vertexSet P ⊆ twoWarpClosure G F Y S)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F) :
    IsLinkable G := by
  let Z := twoWarpClosure G F Y S
  have hA₀Z : A₀ ⊆ Z := hA₀S.trans (subset_twoWarpClosure G F Y S)
  have houtside :
      ∀ p ∈ RegularClosureAssembly.outsidePaths G F Z,
        Disjoint p.support (G.vertexSet P) := by
    intro p hp
    rw [Set.disjoint_left]
    intro x hxp hxP
    apply hp.2
    have hpSupport : p.support ⊆ Z :=
      support_subset_twoWarpClosure_of_mem_left G F Y S hp.1
        ⟨x, hxp, hPclosed hxP⟩
    exact hpSupport p.initial_mem_support
  refine ⟨P ∪ RegularClosureAssembly.outsidePaths G F Z, ?_⟩
  exact RegularClosureAssembly.linkageBetween_union_outside_of_disjoint
    G A₀ Z P F hA₀Z hP hPclosed hF houtside

/-- Common two-warp specialization in which (9.13a) starts at `A₀`. -/
theorem isLinkable_of_internal_linkage_on_twoWarpClosure
    (A₀ : Set V) (F Y P : Set G.DPath)
    (hP : IsLinkageBetween G
      (G.source ∩ twoWarpClosure G F Y A₀) G.target P)
    (hPclosed : G.vertexSet P ⊆ twoWarpClosure G F Y A₀)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F) :
    IsLinkable G :=
  isLinkable_of_internal_linkage_on_twoWarpClosure_of_subset
    G A₀ A₀ F Y P Subset.rfl hP hPclosed hF

/-! ## Closing a verified regular splice

The transfinite recursion itself is isolated in `SliceSplice`.  Once that
recursion has been verified locally, its direct limit is an internal
linkage in the joint `F`/ladder closure.  The following theorem performs the
remaining, completely canonical, regular-cardinal assembly.  In
particular, no additional disjointness premise is exposed here: closure
under whole `F`-paths proves it.
-/

/-- Any set of at most `kappa` vertices has a partial enumeration by the
canonical stage order which hits every vertex.  This is the scheduler used
by the controlled-splice recursion. -/
theorem exists_coveringStageRequest
    {kappa : Cardinal.{u}} {A : Set V} (hA : #A ≤ kappa) :
    ∃ request : Ladder.Stage kappa → Option ↑A,
      ∀ a : ↑A, ∃ i, request i = some a := by
  let e : A ↪ Ladder.Stage kappa :=
    Classical.choice
      (RegularCardinal.nonempty_embedding_stage_of_mk_le hA)
  let request : Ladder.Stage kappa → Option A := fun i ↦ by
    classical
    exact if h : ∃ a : A, e a = i then some (Classical.choose h) else none
  refine ⟨request, ?_⟩
  intro a
  refine ⟨e a, ?_⟩
  dsimp only [request]
  split
  next h =>
    exact congrArg some (e.injective (Classical.choose_spec h))
  next h =>
    exact (h ⟨a, rfl⟩).elim

/-- The canonical joint closure of a `κ`-sized seed admits a covering
stage request whenever both ambient families are warps. -/
theorem exists_coveringStageRequest_twoWarpClosure
    {kappa : Cardinal.{u}} (hkappa : ℵ₀ ≤ kappa)
    {L : G.KappaLadder kappa} {F : Set G.DPath} {S : Set V}
    (hF : G.IsWarp F) (hY : G.IsWarp L.limitWarp)
    (hS : #S ≤ kappa) :
    ∃ request : Ladder.Stage kappa →
        Option ↑(G.source ∩ twoWarpClosure G F L.limitWarp S),
      ∀ a : ↑(G.source ∩ twoWarpClosure G F L.limitWarp S),
        ∃ i, request i = some a := by
  apply exists_coveringStageRequest
  exact (Cardinal.mk_subtype_mono Set.inter_subset_right).trans
    (mk_twoWarpClosure_le G hkappa hF hY hS)

/-- A verified local controlled-slice recursion over the canonical
two-warp closure proves the extension conclusion.  This is the precise
consumer of the local-splice constructor in the regular branch. -/
theorem isLinkable_of_localSpliceOperation
    {kappa : Cardinal.{u}} (hkappa : kappa.IsRegular)
    {L : G.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (A₀ S : Set V) (F : Set G.DPath) (hA₀S : A₀ ⊆ S)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hY : G.IsWarp L.limitWarp)
    {request : Ladder.Stage kappa →
      Option ↑(G.source ∩ twoWarpClosure G F L.limitWarp S)}
    (R : SliceSplice.LocalSpliceOperation G L Sigma
      (twoWarpClosure G F L.limitWarp S)
      (G.source ∩ twoWarpClosure G F L.limitWarp S) request)
    (hrequest : ∀ a : ↑(G.source ∩
      twoWarpClosure G F L.limitWarp S), ∃ i, request i = some a) :
    IsLinkable G := by
  obtain ⟨P, hP, hPclosed⟩ :=
    R.exists_internal_linkage_of_localSpliceOperation
      hkappa hSigma hrequest
  exact isLinkable_of_internal_linkage_on_twoWarpClosure_of_subset
    G A₀ S F L.limitWarp P hA₀S hP hPclosed hF

/-- Final consumer specialized to the actual causal `(9.13a)` carrier.
Unlike the older two-warp-closure wrapper, this theorem uses the row
registration proofs above, so its closed set is exactly the set enumerated
by the source construction. -/
theorem isLinkable_of_causalRowLocalSpliceOperation
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (A₀ : Set V) (hA₀card : #A₀ = kappa)
    (F : Set G.DPath)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (Sigma : Set (Ladder.Stage kappa))
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    {request :
      let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
        hG hlower F hF.isWarp A₀ hA₀card.le
      Ladder.Stage kappa → Option
        ↑(G.source ∩ (Q.rowSystem hregular.aleph0_le).carrier)}
    (Rsplice :
      let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
        hG hlower F hF.isWarp A₀ hA₀card.le
      let rows := Q.rowSystem hregular.aleph0_le
      let L := G.canonicalLadderCore kappa
        (Q.preferred hregular.aleph0_le)
      SliceSplice.LocalSpliceOperation G L Sigma rows.carrier
        (G.source ∩ rows.carrier) request)
    (hrequest :
      let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
        hG hlower F hF.isWarp A₀ hA₀card.le
      let rows := Q.rowSystem hregular.aleph0_le
      ∀ a : ↑(G.source ∩ rows.carrier),
        ∃ i, request i = some a) :
    IsLinkable G := by
  dsimp only at request Rsplice hrequest ⊢
  let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
    hG hlower F hF.isWarp A₀ hA₀card.le
  let rows := Q.rowSystem hregular.aleph0_le
  let L := G.canonicalLadderCore kappa
    (Q.preferred hregular.aleph0_le)
  obtain ⟨P, hP, hPclosed⟩ :=
    Rsplice.exists_internal_linkage_of_localSpliceOperation
      hregular hSigma hrequest
  apply isLinkable_of_internal_linkage_on_closedCarrier
    G A₀ rows.carrier F P
  · exact rowRule_base_subset_carrier G hregular huncountable hG
      hlower F hF.isWarp A₀ hA₀card.le
  · exact hP
  · exact hPclosed
  · exact hF
  · intro p hp hpMeet
    exact support_subset_carrier_of_rowRegistrations G rows F
      (rowRule_registers_oldLinkage G hregular huncountable hG
        hlower F hF.isWarp A₀ hA₀card.le) hp hpMeet

/-- Final causal-row consumer in the local-data form.  All transfinite
splice recursion is discharged by `SliceSpliceConstructor`; the remaining
input is the genuinely local assertion that every valid history admits one
sound tight stage. -/
theorem isLinkable_of_causalRowTightStageData
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (A₀ : Set V) (hA₀card : #A₀ = kappa)
    (F : Set G.DPath)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (Sigma : Set (Ladder.Stage kappa))
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (L : G.KappaLadder kappa)
    {request :
      let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
        hG hlower F hF.isWarp A₀ hA₀card.le
      Ladder.Stage kappa → Option
        ↑(G.source ∩ (Q.rowSystem hregular.aleph0_le).carrier)}
    (hstage :
      let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
        hG hlower F hF.isWarp A₀ hA₀card.le
      let rows := Q.rowSystem hregular.aleph0_le
      SliceSpliceConstructor.LocalConstruction.HasTightStageData
        G L Sigma rows.carrier (G.source ∩ rows.carrier) request
          hG Set.inter_subset_left)
    (hrequest :
      let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
        hG hlower F hF.isWarp A₀ hA₀card.le
      let rows := Q.rowSystem hregular.aleph0_le
      ∀ a : ↑(G.source ∩ rows.carrier),
        ∃ i, request i = some a) :
    IsLinkable G := by
  dsimp only at request hstage hrequest ⊢
  let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
    hG hlower F hF.isWarp A₀ hA₀card.le
  let rows := Q.rowSystem hregular.aleph0_le
  obtain ⟨P, hP, hPclosed⟩ :=
    SliceSpliceConstructor.LocalConstruction.exists_internal_linkage_of_tightStageData
      hG Set.inter_subset_left hstage hregular hSigma hrequest
  apply isLinkable_of_internal_linkage_on_closedCarrier
    G A₀ rows.carrier F P
  · exact rowRule_base_subset_carrier G hregular huncountable hG
      hlower F hF.isWarp A₀ hA₀card.le
  · exact hP
  · exact hPclosed
  · exact hF
  · intro p hp hpMeet
    exact support_subset_carrier_of_rowRegistrations G rows F
      (rowRule_registers_oldLinkage G hregular huncountable hG
        hlower F hF.isWarp A₀ hA₀card.le) hp hpMeet

/-- Causal-row endpoint with the recursive certificate fully eliminated.
Tracked controlled slices supply dummy data on invalid histories; hence the
only splice-specific premise is the positive base/successor/limit theorem
which constructs a sound tight stage from a valid earlier history. -/
theorem isLinkable_of_causalRowSoundStageConstruction
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (A₀ : Set V) (hA₀card : #A₀ = kappa)
    (F : Set G.DPath)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (Sigma : Set (Ladder.Stage kappa))
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    {request :
      let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
        hG hlower F hF.isWarp A₀ hA₀card.le
      Ladder.Stage kappa → Option
        ↑(G.source ∩ (Q.rowSystem hregular.aleph0_le).carrier)}
    (hslices :
      let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
        hG hlower F hF.isWarp A₀ hA₀card.le
      let rows := Q.rowSystem hregular.aleph0_le
      let L := G.canonicalLadderCore kappa
        (Q.preferred hregular.aleph0_le)
      SliceCandidate.HasTrackedTightAnnularControlledSlices
        G L Sigma rows.carrier)
    (hsound :
      let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
        hG hlower F hF.isWarp A₀ hA₀card.le
      let rows := Q.rowSystem hregular.aleph0_le
      let L := G.canonicalLadderCore kappa
        (Q.preferred hregular.aleph0_le)
      ∀ (i : Ladder.Stage kappa)
        (previous : ∀ j : Ladder.Stage kappa, j < i →
          SliceSplice.StagePayload G L Sigma rows.carrier),
        (∀ j (hji : j < i),
          SliceSplice.IsValidStage request j
            (fun l hlj ↦ previous l (lt_trans hlj hji))
            (previous j hji)) →
        ∃ D : SliceSpliceConstructor.LocalConstruction.TightStageData
            G L Sigma rows.carrier,
          D.IsSound (A := G.source ∩ rows.carrier)
            (request := request) hG Set.inter_subset_left i previous)
    (hrequest :
      let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
        hG hlower F hF.isWarp A₀ hA₀card.le
      let rows := Q.rowSystem hregular.aleph0_le
      ∀ a : ↑(G.source ∩ rows.carrier),
        ∃ i, request i = some a) :
    IsLinkable G := by
  dsimp only at request hslices hsound hrequest ⊢
  let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
    hG hlower F hF.isWarp A₀ hA₀card.le
  let rows := Q.rowSystem hregular.aleph0_le
  let L := G.canonicalLadderCore kappa
    (Q.preferred hregular.aleph0_le)
  have hstage :
      SliceSpliceConstructor.LocalConstruction.HasTightStageData
        G L Sigma rows.carrier (G.source ∩ rows.carrier) request
          hG Set.inter_subset_left :=
    SliceSpliceConstructor.LocalConstruction.hasTightStageData_of_sound_exists
      hG Set.inter_subset_left hregular hSigma hslices hsound
  exact isLinkable_of_causalRowTightStageData G hregular huncountable hG
    hlower A₀ hA₀card F hF Sigma hSigma L hstage hrequest

/-- The strengthened zero/successor/limit assembly for the actual causal
rows and the canonical deferred ladder.  Successor stages are completely
discharged by the tracked annular table, and the canonical limit compiler
discharges marker freshness and limit-miss geometry.  Thus the only local
slice inputs left here are the tracked table itself and its genuine
zero-to-club first slice. -/
theorem causalRow_hasTightStageData_of_deferredSlices
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) (hG : G.IsNormalized)
    (hUnhindered : G.IsUnhindered)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (A₀ : Set V) (hA₀card : #A₀ = kappa)
    (F : Set G.DPath)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (Sigma : Set (Ladder.Stage kappa))
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid :
      let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
        hG hlower F hF.isWarp A₀ hA₀card.le
      let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder G kappa
        (Q.preferred hregular.aleph0_le)
      Disjoint Sigma (DWeb.KappaLadder.Deferred.phi L))
    (hslices :
      let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
        hG hlower F hF.isWarp A₀ hA₀card.le
      let rows := Q.rowSystem hregular.aleph0_le
      let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder G kappa
        (Q.preferred hregular.aleph0_le)
      SliceCandidate.HasTrackedTightAnnularControlledSlices
        G L Sigma rows.carrier)
    (hfirst :
      let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
        hG hlower F hF.isWarp A₀ hA₀card.le
      let rows := Q.rowSystem hregular.aleph0_le
      let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder G kappa
        (Q.preferred hregular.aleph0_le)
      SliceSpliceConstructor.LocalConstruction.HasFirstTrackedSlice
        G L Sigma rows.carrier hregular) :
    let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
      hG hlower F hF.isWarp A₀ hA₀card.le
    let rows := Q.rowSystem hregular.aleph0_le
    let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder G kappa
      (Q.preferred hregular.aleph0_le)
    ∀ request : Ladder.Stage kappa →
        Option ↑(G.source ∩ rows.carrier),
      SliceSpliceConstructor.LocalConstruction.HasTightStageData
        G L Sigma rows.carrier (G.source ∩ rows.carrier) request
          hG Set.inter_subset_left := by
  dsimp only at havoid hslices hfirst ⊢
  let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
    hG hlower F hF.isWarp A₀ hA₀card.le
  let rows := Q.rowSystem hregular.aleph0_le
  let preferred := Q.preferred hregular.aleph0_le
  let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
    G kappa preferred
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hG hxy).1 hy
  have hlegal : DWeb.KappaLadder.Deferred.IsDeferredLegal L :=
    DWeb.KappaLadder.Deferred.canonicalDeferredLadder_isDeferredLegal
      preferred hregular huncountable hNoEnter
  have hgeometry :
      SliceSpliceConstructor.SpliceLadderGeometry G L :=
    ⟨hlegal.regular, hlegal.initialStage, hlegal.limitStages,
      hlegal.warpStages, hlegal.frontiersEssential,
      hlegal.frontierChronology, hlegal.strictFrontierChronology⟩
  have hclosed : SliceSplice.IsLimitWarpClosed G L rows.carrier :=
    isLimitWarpClosed_of_rowRegistrations G hgeometry rows
      (rowRule_registers_ladderPrefixes G hregular huncountable hG
        hlower F hF.isWarp A₀ hA₀card.le)
  intro request
  apply hasTightStageData_of_firstTrackedSlice_and_limitCompiler
      hG hUnhindered hgeometry rfl hclosed hSigma hslices hfirst
  exact canonicalDeferredLadder_limitStageCompiler
      preferred hG hregular huncountable Set.inter_subset_left
        hclosed hSigma hslices havoid

/-- Exact late reduction of the regular extension clause to the remaining
normalized construction.  The premise does not contain a completed linkage
or recursive splice operation: for the actual causal carrier it supplies a
club, a request enumerating every closed source, and the local sound-stage
theorem consumed by `SliceSpliceConstructor`. -/
theorem regularExtensionClauseStep_of_normalizedTightStageData
    (kappa : Cardinal.{u})
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : ℵ₀ < kappa)
    (Gamma : DWeb V)
    (hconstruction :
      ∀ (A₀ : Set V), A₀ ⊆ Gamma.normalized.source →
        (hA₀card : #A₀ = kappa) →
      ∀ (F : Set Gamma.normalized.DPath),
        (hF : IsLinkageBetween Gamma.normalized
          (Gamma.normalized.source \ A₀) Gamma.normalized.target F) →
      let Q := RegularRows.CausalRegular.rowRule Gamma.normalized
        hregular huncountable Gamma.normalized_isNormalized hlower
        F hF.isWarp A₀ hA₀card.le
      let rows := Q.rowSystem hregular.aleph0_le
      let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma.normalized kappa
        (Q.preferred hregular.aleph0_le)
      ∃ Sigma : Set (Ladder.Stage kappa),
        Stationary.IsClubBelow kappa Sigma ∧
        ∃ request : Ladder.Stage kappa →
            Option ↑(Gamma.normalized.source ∩ rows.carrier),
          (∀ a : ↑(Gamma.normalized.source ∩ rows.carrier),
            ∃ i, request i = some a) ∧
          SliceSpliceConstructor.LocalConstruction.HasTightStageData
            Gamma.normalized L Sigma rows.carrier
              (Gamma.normalized.source ∩ rows.carrier) request
              Gamma.normalized_isNormalized Set.inter_subset_left) :
    ExtensionClauseAt Gamma kappa := by
  apply RegularNormalization.extensionClauseAt_of_normalized
    kappa hregular.aleph0_le
  intro A₀ hA₀ hA₀card hcomplement
  obtain ⟨F, hF⟩ := hcomplement
  obtain ⟨Sigma, hSigma, request, hrequest, hstage⟩ :=
    hconstruction A₀ hA₀ hA₀card F hF
  let Q := RegularRows.CausalRegular.rowRule Gamma.normalized
    hregular huncountable Gamma.normalized_isNormalized hlower
    F hF.isWarp A₀ hA₀card.le
  let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
    Gamma.normalized kappa (Q.preferred hregular.aleph0_le)
  exact isLinkable_of_causalRowTightStageData Gamma.normalized
    hregular huncountable Gamma.normalized_isNormalized hlower
    A₀ hA₀card F hF Sigma hSigma L hstage hrequest

end RegularExtension

end CardinalInduction
end Erdos599
