/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction
import ErdosProblems.Erdos599.Ladder
import ErdosProblems.Erdos599.RegularCardinal
import ErdosProblems.Erdos599.RegularSplitLegality

/-!
# Controlled slices in the regular-cardinal construction

This file gives the concrete path-theoretic vocabulary used in Assertion
9.15 of Aharoni--Berger.  A path of a slice is *ordinary* when it is a
fragment of a path of the limiting ladder warp; the other paths are the
mavericks of the slice.  The lemmas below turn the source proof's
``all but fewer than `κ` paths are ordinary'' conclusion into the two
cardinal-and-support clauses of `RegularCardinal.IsControlledSlice`.

The graph-theoretic existence of the slice linkage is intentionally kept
separate from these elementary consequences.  In particular, none of the
definitions below contains an existence field for a controlled slice.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace ControlledSlices

open DirectedPath

universe u

variable {V : Type u}

/-- Source Lemma 7.26 in its direct bookkeeping form.  At a stage outside
the obstruction set every inessential successor component has already
been recorded at a strictly earlier stage.  Since the bookkeeping records
at most one path per stage, there are fewer than `κ` such components. -/
theorem mk_inessentialSuccessor_lt_of_not_mem_phi
    {κ : Cardinal.{u}} (Γ : DWeb V) (L : Γ.KappaLadder κ)
    (hL : L.IsSplitLegal) (α : RegularCardinal.Stage κ)
    (hα : α ∉ L.phi) :
    #(Γ.inessentialPaths (L.successorWarp α)) < κ := by
  classical
  have hrecorded : Γ.inessentialPaths (L.successorWarp α) ⊆
      L.bookkeeping.recordedBefore α := by
    intro p hp
    by_contra hpRecorded
    apply hα
    exact ⟨p, hp, hpRecorded⟩
  let stageWitness : ∀ p : L.bookkeeping.recordedBefore α,
      ∃ β : RegularCardinal.Stage κ,
        β < α ∧ L.chosen β = some p.1 :=
    fun p ↦ p.2
  let recordStage : L.bookkeeping.recordedBefore α →
      RegularCardinal.Stage κ :=
    fun p ↦ Classical.choose (stageWitness p)
  have hrecordStage : Function.Injective recordStage := by
    intro p q hpq
    apply Subtype.ext
    have hp := (Classical.choose_spec (stageWitness p)).2
    have hq := (Classical.choose_spec (stageWitness q)).2
    rw [show Classical.choose (stageWitness p) =
      Classical.choose (stageWitness q) by exact hpq] at hp
    exact Option.some.inj (hp.symm.trans hq)
  have hrecordedCard : #(L.bookkeeping.recordedBefore α) < κ := by
    exact RegularCardinal.mk_lt_of_injective_bounded_stage
      α recordStage hrecordStage
        (fun p ↦ (Classical.choose_spec (stageWitness p)).1)
  exact (Cardinal.mk_subtype_mono hrecorded).trans_lt hrecordedCard

/-- Current-stage form of the same estimate.  Legality says that an
inessential component persists through the next arrow step, where the
preceding bookkeeping estimate applies. -/
theorem mk_inessentialWarpAt_lt_of_not_mem_phi
    {κ : Cardinal.{u}} (Γ : DWeb V) (L : Γ.KappaLadder κ)
    (hL : L.IsSplitLegal) (α : RegularCardinal.Stage κ)
    (hα : α ∉ L.phi) :
    #(Γ.inessentialPaths (L.warpAt α)) < κ := by
  exact (Cardinal.mk_subtype_mono (hL.currentInessentialPersists α)).trans_lt
    (mk_inessentialSuccessor_lt_of_not_mem_phi Γ L hL α hα)

/-- A diagonal row slice below one stage of a regular cardinal has size
strictly below the cardinal.  This is the cardinal input which permits the
lower half-way clause to be applied to
`T_δ ∩ Z^{<γ}_{<γ}`. -/
theorem mk_diagonalSlice_lt {κ : Cardinal.{u}} {X : Type u}
    (hκ : κ.IsRegular)
    (row : RegularCardinal.Stage κ → RegularCardinal.Stage κ → Option X)
    (α : RegularCardinal.Stage κ) :
    #(RegularCardinal.diagonalSlice row α) < κ := by
  classical
  have hwitness : ∀ x : RegularCardinal.diagonalSlice row α,
      ∃ c : Set.Iio α.1 × Set.Iio α.1,
        row ⟨c.1.1, show c.1.1 < κ.ord from lt_trans c.1.2 α.2⟩
          ⟨c.2.1, show c.2.1 < κ.ord from lt_trans c.2.2 α.2⟩ =
            some x.1 := by
    intro x
    obtain ⟨θ, γ, hθα, hγα, hx⟩ := x.2
    exact ⟨⟨⟨θ.1, hθα⟩, ⟨γ.1, hγα⟩⟩, hx⟩
  choose coord hcoord using hwitness
  have hcoordInjective : Function.Injective coord := by
    intro x y hxy
    apply Subtype.ext
    have hx := hcoord x
    have hy := hcoord y
    rw [hxy] at hx
    exact Option.some.inj (hx.symm.trans hy)
  have hleLift :=
    Cardinal.lift_mk_le_lift_mk_of_injective hcoordInjective
  have hle : #(RegularCardinal.diagonalSlice row α) ≤
      α.1.card * α.1.card := by
    apply Cardinal.lift_le.mp
    simpa only [Cardinal.mk_prod, Cardinal.mk_Iio_ordinal,
      Cardinal.lift_lift, Cardinal.lift_mul] using hleLift
  apply hle.trans_lt
  exact Cardinal.mul_lt_of_lt hκ.aleph0_le
    (Cardinal.lt_ord.mp α.2) (Cardinal.lt_ord.mp α.2)

/-- The actual request used in the table at `(δ,γ)`. -/
def diagonalRequest {κ : Cardinal.{u}}
    (frontier : RegularCardinal.Stage κ → Set V)
    (row : RegularCardinal.Stage κ → RegularCardinal.Stage κ → Option V)
    (δ γ : RegularCardinal.Stage κ) : Set V :=
  frontier δ ∩ RegularCardinal.diagonalSlice row γ

theorem mk_diagonalRequest_lt {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (frontier : RegularCardinal.Stage κ → Set V)
    (row : RegularCardinal.Stage κ → RegularCardinal.Stage κ → Option V)
    (δ γ : RegularCardinal.Stage κ) :
    #(diagonalRequest frontier row δ γ) < κ :=
  (Cardinal.mk_subtype_mono Set.inter_subset_right).trans_lt
    (mk_diagonalSlice_lt hκ row γ)

/-- A path is an ordinary ladder fragment when it is a subpath of one
member of the limiting ladder warp.  This is the source phrase
``contained in a path of `Y`''. -/
def IsLadderFragment (Γ : DWeb V) (Y : Set Γ.DPath) (p : Γ.DPath) : Prop :=
  ∃ q ∈ Y, p.IsSubpathOf q

/-- The mavericks of a slice are exactly its members which are not ladder
fragments. -/
def sliceMavericks (Γ : DWeb V) (Y T : Set Γ.DPath) : Set Γ.DPath :=
  {p | p ∈ T ∧ ¬ IsLadderFragment Γ Y p}

@[simp]
theorem mem_sliceMavericks {Γ : DWeb V} {Y T : Set Γ.DPath}
    {p : Γ.DPath} :
    p ∈ sliceMavericks Γ Y T ↔
      p ∈ T ∧ ¬ IsLadderFragment Γ Y p :=
  Iff.rfl

theorem sliceMavericks_subset (Γ : DWeb V) (Y T : Set Γ.DPath) :
    sliceMavericks Γ Y T ⊆ T :=
  fun _ hp ↦ hp.1

/-- Enlarging the slice can only enlarge its maverick subfamily. -/
theorem sliceMavericks_mono_slice
    (Γ : DWeb V) (Y : Set Γ.DPath) {T T' : Set Γ.DPath}
    (hTT' : T ⊆ T') :
    sliceMavericks Γ Y T ⊆ sliceMavericks Γ Y T' := by
  intro p hp
  exact ⟨hTT' hp.1, hp.2⟩

/-- Enlarging the ladder warp can only turn mavericks into ordinary
fragments. -/
theorem sliceMavericks_antitone_ladder
    (Γ : DWeb V) {Y Y' T : Set Γ.DPath} (hYY' : Y ⊆ Y') :
    sliceMavericks Γ Y' T ⊆ sliceMavericks Γ Y T := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  rintro ⟨q, hqY, hpq⟩
  exact hp.2 ⟨q, hYY' hqY, hpq⟩

/-- Cardinal control can also be supplied directly as containment in a
small exceptional family. -/
theorem mk_sliceMavericks_lt_of_subset
    (Γ : DWeb V) {κ : Cardinal.{u}} {Y T E : Set Γ.DPath}
    (hsub : sliceMavericks Γ Y T ⊆ E) (hE : #E < κ) :
    #(sliceMavericks Γ Y T) < κ :=
  (Cardinal.mk_subtype_mono hsub).trans_lt hE

/-- Source Assertion 9.15's graph-theoretic conclusion before the
cardinality and closing-up clauses are appended: `T` links one ladder
frontier to a later frontier and links every requested vertex all the way
to the original target. -/
def SliceGood {κ : Cardinal.{u}} (Γ : DWeb V)
    (L : Γ.KappaLadder κ) (T : Set Γ.DPath)
    (α β : RegularCardinal.Stage κ) (U : Set V) : Prop :=
  IsLinkageBetween Γ (L.frontier α) (L.frontier β) T ∧
    LinksToTarget Γ T U

/-- Linking a larger request set to the target also links each of its
subsets.  The source's suffix condition is preserved because the selected
path met the larger request in the singleton `{a}`. -/
theorem linksToTarget_mono
    (Γ : DWeb V) (T : Set Γ.DPath) {U U' : Set V}
    (hUU' : U ⊆ U') (hlinks : LinksToTarget Γ T U') :
    LinksToTarget Γ T U := by
  intro a haU
  obtain ⟨p, hpT, q, rfl, hqU', hsuffix⟩ := hlinks a (hUU' haU)
  refine ⟨.inl q, hpT, q, rfl, ?_, hsuffix⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxq, hxU⟩
    have hx : x ∈ ({a} : Set V) := by
      rw [← hqU']
      exact ⟨hxq, hUU' hxU⟩
    exact hx
  · intro x hx
    have hxa : x = a := Set.mem_singleton_iff.mp hx
    subst x
    have haSupport : a ∈ q.support := by
      have : a ∈ q.support ∩ U' := by
        rw [hqU']
        exact Set.mem_singleton a
      exact this.1
    exact ⟨haSupport, haU⟩

/-- An exceptional family certifies the source statement that all other
paths of `T` are contained in paths of `Y`. -/
def OrdinaryOutside (Γ : DWeb V) (Y T E : Set Γ.DPath) : Prop :=
  E ⊆ T ∧ ∀ p ∈ T, p ∉ E → IsLadderFragment Γ Y p

theorem sliceMavericks_subset_exceptional
    (Γ : DWeb V) {Y T E : Set Γ.DPath}
    (hordinary : OrdinaryOutside Γ Y T E) :
    sliceMavericks Γ Y T ⊆ E := by
  intro p hp
  by_contra hpE
  exact hp.2 (hordinary.2 p hp.1 hpE)

/-- The phrase ``all but fewer than `κ`'' has its literal cardinal
consequence for the maverick subfamily. -/
theorem mk_sliceMavericks_lt_of_ordinaryOutside
    (Γ : DWeb V) {κ : Cardinal.{u}} {Y T E : Set Γ.DPath}
    (hordinary : OrdinaryOutside Γ Y T E) (hE : #E < κ) :
    #(sliceMavericks Γ Y T) < κ :=
  mk_sliceMavericks_lt_of_subset Γ
    (sliceMavericks_subset_exceptional Γ hordinary) hE

/-- Every maverick of a finite-character slice is a finite path. -/
theorem sliceMavericks_finiteCharacter
    (Γ : DWeb V) {Y T : Set Γ.DPath}
    (hfinite : Γ.HasFiniteCharacter T) :
    Γ.HasFiniteCharacter (sliceMavericks Γ Y T) := by
  intro p hp
  exact hfinite hp.1

/-- The union of the vertices on all mavericks is the concrete
`maverickVertexSet` appearing in the generic regular-cardinal interface. -/
theorem maverickVertexSet_eq_vertexSet
    (Γ : DWeb V) (Y T : Set Γ.DPath) :
    RegularCardinal.maverickVertexSet
        (sliceMavericks Γ Y) (fun p : Γ.DPath ↦ p.support) T =
      Γ.vertexSet (sliceMavericks Γ Y T) := by
  ext x
  simp only [RegularCardinal.maverickVertexSet, DWeb.vertexSet,
    Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨p, hpM, hxp⟩
    exact ⟨p, hpM, hxp⟩
  · rintro ⟨p, hpM, hxp⟩
    exact ⟨p, hpM, hxp⟩

/-- Registering the exceptional paths in a closing-up set registers every
maverick vertex.  This is the precise use of the last union in (9.13a). -/
theorem maverickVertexSet_subset_of_exceptional_registered
    (Γ : DWeb V) {Y T E : Set Γ.DPath} {Z : Set V}
    (hordinary : OrdinaryOutside Γ Y T E)
    (hregistered : Γ.vertexSet E ⊆ Z) :
    RegularCardinal.maverickVertexSet
        (sliceMavericks Γ Y) (fun p : Γ.DPath ↦ p.support) T ⊆ Z := by
  rw [maverickVertexSet_eq_vertexSet]
  intro x hx
  obtain ⟨p, hpM, hxp⟩ := hx
  exact hregistered ⟨p,
    sliceMavericks_subset_exceptional Γ hordinary hpM, hxp⟩

/-- Fewer than `κ` exceptional finite paths have fewer than `κ` vertices
altogether.  This is the regularity calculation used when those vertices
are inserted into a row of (9.13a). -/
theorem mk_vertexSet_exceptional_lt
    (Γ : DWeb V) {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {T E : Set Γ.DPath} (hEsub : E ⊆ T) (hE : #E < κ)
    (hfinite : Γ.HasFiniteCharacter T) :
    #(Γ.vertexSet E) < κ := by
  have heq : Γ.vertexSet E = ⋃ p ∈ E, p.support := by
    ext x
    simp only [DWeb.vertexSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨p, hpE, hxp⟩
      exact Set.mem_iUnion.2 ⟨p,
        Set.mem_iUnion.2 ⟨hpE, hxp⟩⟩
    · intro hx
      obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hx
      obtain ⟨hpE, hxp⟩ := Set.mem_iUnion.1 hp
      exact ⟨p, hpE, hxp⟩
  rw [heq]
  apply RegularCardinal.mk_maverickVertexSet_lt hκ hE
  intro p hpE
  obtain ⟨q, hpq⟩ := hfinite (hEsub hpE)
  subst p
  exact q.support_finite

/-- The complete controlled-slice payload follows from the two concrete
outputs of the source replacement argument: a small exceptional family
outside which paths are ladder fragments, and registration of that family
in `Z`. -/
theorem isControlledSlice_of_ordinaryOutside
    (Γ : DWeb V) {κ : Cardinal.{u}} {Y T E : Set Γ.DPath}
    {Z U : Set V} {α β : RegularCardinal.Stage κ}
    (L : Γ.KappaLadder κ)
    (hgood : SliceGood Γ L T α β U)
    (hordinary : OrdinaryOutside Γ Y T E)
    (hE : #E < κ) (hregistered : Γ.vertexSet E ⊆ Z) :
    RegularCardinal.IsControlledSlice
      (SliceGood Γ L) (sliceMavericks Γ Y)
      (fun p : Γ.DPath ↦ p.support) Z α β U T := by
  refine ⟨hgood,
    mk_sliceMavericks_lt_of_ordinaryOutside Γ hordinary hE, ?_⟩
  exact maverickVertexSet_subset_of_exceptional_registered Γ
    hordinary hregistered

/-- Specialization to the limiting warp of a ladder, which is the `Y`
used throughout the regular-cardinal proof. -/
theorem isControlledSlice_of_limitWarp_exceptions
    (Γ : DWeb V) {κ : Cardinal.{u}} {T E : Set Γ.DPath}
    {Z U : Set V} {α β : RegularCardinal.Stage κ}
    (L : Γ.KappaLadder κ)
    (hgood : SliceGood Γ L T α β U)
    (hordinary : OrdinaryOutside Γ L.limitWarp T E)
    (hE : #E < κ) (hregistered : Γ.vertexSet E ⊆ Z) :
    RegularCardinal.IsControlledSlice
      (SliceGood Γ L) (sliceMavericks Γ L.limitWarp)
      (fun p : Γ.DPath ↦ p.support) Z α β U T :=
  isControlledSlice_of_ordinaryOutside Γ L hgood hordinary hE hregistered

/-! ## The source's pre-recorded candidate table

In (9.13a) a candidate `U_{β,γ,δ}` is chosen for every triple of indices
for which one exists, and all vertices on its mavericks are inserted into
the corresponding closing-up row.  Later, the proof of 9.15 first proves
that a candidate exists and then uses the already chosen, already
registered member of this table.  The following definitions formalize that
order of quantifiers; no candidate-existence proposition is stored as
data. -/

/-- The property used when filling one entry of the table in (9.13a).
The request at `(δ,γ)` is linked across the slice and the maverick family
is already known to have size `< κ`. -/
def IsSliceCandidate {κ : Cardinal.{u}} (Γ : DWeb V)
    (L : Γ.KappaLadder κ)
    (request : RegularCardinal.Stage κ → RegularCardinal.Stage κ → Set V)
    (δ β γ : RegularCardinal.Stage κ) (T : Set Γ.DPath) : Prop :=
  SliceGood Γ L T δ β (request δ γ) ∧
    #(sliceMavericks Γ (L.warpAt β) T) < κ

/-- Every stage path is contained in a path of the limiting ladder warp.
For a legal ladder this is supplied by the direct path-thread limit
construction. -/
def StagesEmbedInLimit {κ : Cardinal.{u}} (Γ : DWeb V)
    (L : Γ.KappaLadder κ) : Prop :=
  ∀ β q, q ∈ L.warpAt β →
    ∃ r ∈ L.limitWarp, q.IsSubpathOf r

/-- The geometric fields actually used by the stage-to-limit argument.
The final ladder stage is a genuine limit, and every path in an earlier
accumulated warp grows along its unique thread to that direct limit.  This
form deliberately does not mention hanging-record provenance. -/
theorem stagesEmbedInLimit_of_limitStages
    {κ : Cardinal.{u}} (Γ : DWeb V) (L : Γ.KappaLadder κ)
    (hregular : κ.IsRegular) (hlimitStages : L.HasLimitStages) :
    StagesEmbedInLimit Γ L := by
  intro β q hq
  have hlimit : Order.IsSuccLimit κ.ord :=
    Cardinal.isSuccLimit_ord hregular.aleph0_le
  obtain ⟨r, hr, hqr⟩ := hlimitStages.grows_to_limit
    (Ladder.finalStage κ) hlimit ⟨β.1, β.2⟩ q hq
  exact ⟨r, hr,
    Γ.support_mono_of_extends hqr,
    DirectedPath.Path.edgeSet_mono_of_extends hqr⟩

/-- Legacy legality is one supplier of the provenance-free geometric
stage-to-limit interface. -/
theorem stagesEmbedInLimit_of_legal
    {κ : Cardinal.{u}} (Γ : DWeb V) (L : Γ.KappaLadder κ)
    (hL : L.IsSplitLegal) :
    StagesEmbedInLimit Γ L :=
  stagesEmbedInLimit_of_limitStages Γ L hL.regular hL.limitStages

/-- Every legal ladder frontier is carried by the limiting warp.  A
frontier point is the terminal of an essential accumulated component, and
the direct-limit extension of that component still contains the point. -/
theorem frontier_subset_vertexSet_limitWarp_of_legal
    {κ : Cardinal.{u}} (Γ : DWeb V) (L : Γ.KappaLadder κ)
    (hL : L.IsSplitLegal) (α : RegularCardinal.Stage κ) :
    L.frontier α ⊆ Γ.vertexSet L.limitWarp := by
  intro x hx
  obtain ⟨q, hq, hqx⟩ :=
    Γ.exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
      (hL.roofsSourceAtStages (Ladder.Stage.toExtended α)) hx
  obtain ⟨r, hr, hqr⟩ :=
    stagesEmbedInLimit_of_legal Γ L hL α q hq.1
  exact ⟨r, hr, hqr.1 (Γ.terminal_mem_support hqx)⟩

/-- A fragment of a stage path remains a fragment of the corresponding
limiting path. -/
theorem isLadderFragment_limit_of_stage
    {κ : Cardinal.{u}} (Γ : DWeb V) (L : Γ.KappaLadder κ)
    (hstageLimit : StagesEmbedInLimit Γ L)
    {β : RegularCardinal.Stage κ} {p : Γ.DPath}
    (hp : IsLadderFragment Γ (L.warpAt β) p) :
    IsLadderFragment Γ L.limitWarp p := by
  obtain ⟨q, hqβ, hpq⟩ := hp
  obtain ⟨r, hrLimit, hqr⟩ := hstageLimit β q hqβ
  exact ⟨r, hrLimit, hpq.1.trans hqr.1, hpq.2.trans hqr.2⟩

/-- Consequently every maverick relative to the final warp was already a
maverick relative to the stage warp. -/
theorem sliceMavericks_limit_subset_stage
    {κ : Cardinal.{u}} (Γ : DWeb V) (L : Γ.KappaLadder κ)
    (hstageLimit : StagesEmbedInLimit Γ L)
    (β : RegularCardinal.Stage κ) (T : Set Γ.DPath) :
    sliceMavericks Γ L.limitWarp T ⊆
      sliceMavericks Γ (L.warpAt β) T := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  intro hpStage
  exact hp.2 (isLadderFragment_limit_of_stage Γ L hstageLimit hpStage)

/-- The source's chosen `U_{β,γ,δ}`.  If no candidate exists, the entry
is empty, exactly as in the two cases immediately preceding (9.13a). -/
def chosenSlice {κ : Cardinal.{u}} (Γ : DWeb V)
    (L : Γ.KappaLadder κ)
    (request : RegularCardinal.Stage κ → RegularCardinal.Stage κ → Set V)
    (δ β γ : RegularCardinal.Stage κ) : Set Γ.DPath := by
  classical
  exact if h : ∃ T, IsSliceCandidate Γ L request δ β γ T then
    Classical.choose h
  else ∅

theorem chosenSlice_spec_of_exists {κ : Cardinal.{u}} (Γ : DWeb V)
    (L : Γ.KappaLadder κ)
    (request : RegularCardinal.Stage κ → RegularCardinal.Stage κ → Set V)
    {δ β γ : RegularCardinal.Stage κ}
    (h : ∃ T, IsSliceCandidate Γ L request δ β γ T) :
    IsSliceCandidate Γ L request δ β γ
      (chosenSlice Γ L request δ β γ) := by
  classical
  rw [chosenSlice, dif_pos h]
  exact Classical.choose_spec h

/-- All maverick vertices inserted by the candidate-table clause of
(9.13a), before the entries are distributed among bounded rows. -/
def chosenMaverickVertices {κ : Cardinal.{u}} (Γ : DWeb V)
    (L : Γ.KappaLadder κ)
    (request : RegularCardinal.Stage κ → RegularCardinal.Stage κ → Set V) :
    Set V :=
  ⋃ δ, ⋃ β, ⋃ γ, Γ.vertexSet
    (sliceMavericks Γ (L.warpAt β) (chosenSlice Γ L request δ β γ))

theorem vertexSet_sliceMavericks_chosen_subset
    {κ : Cardinal.{u}} (Γ : DWeb V) (L : Γ.KappaLadder κ)
    (request : RegularCardinal.Stage κ → RegularCardinal.Stage κ → Set V)
    (δ β γ : RegularCardinal.Stage κ) :
    Γ.vertexSet
        (sliceMavericks Γ (L.warpAt β)
          (chosenSlice Γ L request δ β γ)) ⊆
      chosenMaverickVertices Γ L request := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨δ, Set.mem_iUnion.2 ⟨β,
    Set.mem_iUnion.2 ⟨γ, hx⟩⟩⟩

/-- Once existence at a table entry has been proved, the source's
pre-recorded choice is a controlled slice for every subrequest, provided
the closing-up set contains the candidate-table vertex union. -/
theorem chosenSlice_isControlled_of_exists
    {κ : Cardinal.{u}} (Γ : DWeb V) (L : Γ.KappaLadder κ)
    (request : RegularCardinal.Stage κ → RegularCardinal.Stage κ → Set V)
    {Z U : Set V} {δ β γ : RegularCardinal.Stage κ}
    (hstageLimit : StagesEmbedInLimit Γ L)
    (hcandidate : ∃ T, IsSliceCandidate Γ L request δ β γ T)
    (hU : U ⊆ request δ γ)
    (hregistered : chosenMaverickVertices Γ L request ⊆ Z) :
    RegularCardinal.IsControlledSlice
      (SliceGood Γ L) (sliceMavericks Γ L.limitWarp)
      (fun p : Γ.DPath ↦ p.support) Z δ β U
      (chosenSlice Γ L request δ β γ) := by
  have hchosen := chosenSlice_spec_of_exists Γ L request hcandidate
  have hmaverickSub :
      sliceMavericks Γ L.limitWarp (chosenSlice Γ L request δ β γ) ⊆
        sliceMavericks Γ (L.warpAt β)
          (chosenSlice Γ L request δ β γ) :=
    sliceMavericks_limit_subset_stage Γ L hstageLimit β _
  refine ⟨⟨hchosen.1.1,
    linksToTarget_mono Γ _ hU hchosen.1.2⟩,
    mk_sliceMavericks_lt_of_subset Γ hmaverickSub hchosen.2, ?_⟩
  rw [maverickVertexSet_eq_vertexSet]
  intro x hx
  obtain ⟨p, hpM, hxp⟩ := hx
  apply hregistered
  apply vertexSet_sliceMavericks_chosen_subset Γ L request δ β γ
  exact ⟨p, hmaverickSub hpM, hxp⟩

/-- Source-faithful table-selection form of Assertion 9.15.  The first
hypothesis is 9.13 (capture the small request by a diagonal request); the
second is the 9.10-style graph construction proving that some later table
entry exists; the third is exactly the maverick-registration clause of
(9.13a).  The conclusion is the concrete controlled-slice interface used
by the regular recursion. -/
theorem hasControlledSlices_of_chosenTable
    {κ : Cardinal.{u}} (Γ : DWeb V) (L : Γ.KappaLadder κ)
    (C : Set (RegularCardinal.Stage κ)) (Z : Set V)
    (request : RegularCardinal.Stage κ → RegularCardinal.Stage κ → Set V)
    (hstageLimit : StagesEmbedInLimit Γ L)
    (hcapture : ∀ δ ∈ C, ∀ U : Set V,
      U ⊆ L.frontier δ ∩ Z → #U < κ →
        ∃ γ, U ⊆ request δ γ)
    (hexists : ∀ δ ∈ C, ∀ γ,
      ∃ β ∈ C, δ < β ∧
        ∃ T, IsSliceCandidate Γ L request δ β γ T)
    (hregistered : chosenMaverickVertices Γ L request ⊆ Z) :
    RegularCardinal.HasControlledSlices C L.frontier Z
      (SliceGood Γ L) (sliceMavericks Γ L.limitWarp)
      (fun p : Γ.DPath ↦ p.support) := by
  intro δ hδ U hU hcard
  obtain ⟨γ, hUrequest⟩ := hcapture δ hδ U hU hcard
  obtain ⟨β, hβC, hδβ, hcandidate⟩ := hexists δ hδ γ
  refine ⟨β, hβC, hδβ, chosenSlice Γ L request δ β γ, ?_⟩
  exact chosenSlice_isControlled_of_exists Γ L request
    hstageLimit hcandidate hUrequest hregistered

/-- Legal-ladder specialization of the table-selection theorem.  This
removes the formerly external stage-to-limit compatibility hypothesis:
that compatibility is already a consequence of the direct-limit clause
in `KappaLadder.IsLegal`. -/
theorem hasControlledSlices_of_legal_chosenTable
    {κ : Cardinal.{u}} (Γ : DWeb V) (L : Γ.KappaLadder κ)
    (hL : L.IsSplitLegal)
    (C : Set (RegularCardinal.Stage κ)) (Z : Set V)
    (request : RegularCardinal.Stage κ → RegularCardinal.Stage κ → Set V)
    (hcapture : ∀ δ ∈ C, ∀ U : Set V,
      U ⊆ L.frontier δ ∩ Z → #U < κ →
        ∃ γ, U ⊆ request δ γ)
    (hexists : ∀ δ ∈ C, ∀ γ,
      ∃ β ∈ C, δ < β ∧
        ∃ T, IsSliceCandidate Γ L request δ β γ T)
    (hregistered : chosenMaverickVertices Γ L request ⊆ Z) :
    RegularCardinal.HasControlledSlices C L.frontier Z
      (SliceGood Γ L) (sliceMavericks Γ L.limitWarp)
      (fun p : Γ.DPath ↦ p.support) := by
  exact hasControlledSlices_of_chosenTable Γ L C Z request
    (stagesEmbedInLimit_of_legal Γ L hL)
    hcapture hexists hregistered

end ControlledSlices
end CardinalInduction
end Erdos599
