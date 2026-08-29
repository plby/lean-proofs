/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ControlledSlices

/-!
# The graph core of the regular-cardinal slice argument

This file isolates the two elementary graph operations used in Assertions
9.8--9.10 of Aharoni--Berger.

* Nested roofs turn a stop-over set `C` into a separator between two ladder
  frontiers.
* Choosing, on distinct components of the limiting ladder warp, finite
  frontier-to-frontier segments produces a genuine linkage.
* Adjoining a small family of unreplaced components preserves both linkage
  and the assertion that every nonexceptional member is a limiting-warp
  fragment.

The data below are witnesses for individual path segments and exceptional
components.  They do not contain the controlled-slice conclusion or an
existence field for it.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceSegmentCore

open DirectedPath
open ControlledSlices

universe u

variable {V : Type u}

/-! ## Nested roofs separate ladder frontiers -/

/-- Generic form of the nested-roof step: an essential later boundary, a
stop-over separating `A` from the target, and roofing of that stop-over by
the later boundary imply separation between `A` and the boundary.  This
form can be applied inside a ladder stage web or one of its quotients. -/
theorem separates_between_of_roofed
    (Gamma : DWeb V) {A C T : Set V}
    (hessential : Gamma.essential T = T)
    (hsep : IsSeparatorFrom Gamma A C)
    (hroof : C ⊆ Gamma.roof T) :
    RelationalRoof.Separates Gamma.graph.Adj A T C := by
  apply RelationalRoof.nested_roofs_separate
      (R := Gamma.graph.Adj) (B := Gamma.target)
  · exact hessential.symm
  · exact Gamma.roof_cut hsep
  · exact Gamma.roof_cut hroof

/-- If a wave is below a comparison family in roof order, and the latter's
terminal frontier is roofed by `T`, then so is the wave's terminal
frontier.  This is the roof-calculus content of the passage from maximal
rungs (9.7) to every later frontier (9.8); the ladder construction supplies
the two displayed hypotheses. -/
theorem terminalFrontier_subset_roof_of_roofLE
    (Gamma : DWeb V) {W R : Set Gamma.DPath} {T : Set V}
    (hWR : Gamma.RoofLE W R)
    (hRT : Gamma.terminalFrontier R ⊆ Gamma.roof T) :
    Gamma.terminalFrontier W ⊆ Gamma.roof T := by
  exact (Gamma.subset_roof (Gamma.terminalFrontier W)).trans
    (hWR.trans (Gamma.roof_cut hRT))

/-- A stop-over separator for `T_alpha` which is itself roofed by
`T_beta` separates `T_alpha` from `T_beta`.

This is the concrete nested-roof inference used after Assertions 9.8 and
9.9.  Essentiality of the later frontier is supplied by ladder legality;
the two applications of `roof_cut` turn the pointwise hypotheses into the
roof inclusions required by Aharoni--Berger Lemma 2.19. -/
theorem frontier_separates_of_roofed
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (hL : L.IsLegal)
    {alpha beta : RegularCardinal.Stage kappa} {C : Set V}
    (hsep : IsSeparatorFrom Gamma (L.frontier alpha) C)
    (hroof : C ⊆ Gamma.roof (L.frontier beta)) :
    RelationalRoof.Separates Gamma.graph.Adj
      (L.frontier alpha) (L.frontier beta) C := by
  exact separates_between_of_roofed Gamma
    (hL.frontiersEssential beta) hsep hroof

/-! ## Exceptional partial linkages -/

/-- A family which is a linkage on only part of `A`, but whose members are
already endpoint-pure relative to all of `A`.  These are exactly the facts
about the unreplaced components used in the union proof below. -/
structure IsExceptionalRemainder (Gamma : DWeb V) (A C : Set V)
    (E : Set Gamma.DPath) : Prop where
  isWarp : Gamma.IsWarp E
  finiteCharacter : Gamma.HasFiniteCharacter E
  initialSet_subset : Gamma.initialSet E ⊆ A
  terminalFrontier_subset : Gamma.terminalFrontier E ⊆ C
  endpointPure : ∀ p ∈ E, IsPathBetween Gamma A C p

/-! ## Lifting exceptional components out of a ladder stage -/

/-- The finite-path version of `KappaLadder.liftStagePath`.  It is useful
when transporting the endpoint-purity and target-linking witnesses carried
by a finite stage path. -/
def liftStageFinitePath
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    (p : DirectedPath.FinitePath (L.stageWeb alpha).graph) :
    DirectedPath.FinitePath Gamma.graph :=
  let Q := Gamma.quotient
    (Gamma.terminalFrontier (L.warpAt alpha))
  (p.lift (fun {_ _} h ↦ Q.essentialPart_adj_imp h)).lift
    (fun {_ _} h ↦ Gamma.quotient_adj_imp h)

@[simp]
theorem liftStagePath_finite
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    (p : DirectedPath.FinitePath (L.stageWeb alpha).graph) :
    L.liftStagePath alpha (Sum.inl p) =
      Sum.inl (liftStageFinitePath L alpha p) :=
  rfl

@[simp]
theorem liftStageFinitePath_start
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    (p : DirectedPath.FinitePath (L.stageWeb alpha).graph) :
    (liftStageFinitePath L alpha p).start = p.start :=
  rfl

@[simp]
theorem liftStageFinitePath_finish
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    (p : DirectedPath.FinitePath (L.stageWeb alpha).graph) :
    (liftStageFinitePath L alpha p).finish = p.finish :=
  rfl

@[simp]
theorem liftStageFinitePath_support
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    (p : DirectedPath.FinitePath (L.stageWeb alpha).graph) :
    (liftStageFinitePath L alpha p).support = p.support := by
  let Q := Gamma.quotient
    (Gamma.terminalFrontier (L.warpAt alpha))
  let hEss : ∀ {x y : V}, (L.stageWeb alpha).graph.Adj x y →
      Q.graph.Adj x y := fun {_ _} h ↦ Q.essentialPart_adj_imp h
  let hQuot : ∀ {x y : V}, Q.graph.Adj x y →
      Gamma.graph.Adj x y := fun {_ _} h ↦ Gamma.quotient_adj_imp h
  change ((p.lift hEss).lift hQuot).support = p.support
  calc
    ((p.lift hEss).lift hQuot).support = (p.lift hEss).support :=
      DirectedPath.FinitePath.support_lift hQuot (p.lift hEss)
    _ = p.support := DirectedPath.FinitePath.support_lift hEss p

@[simp]
theorem liftStageFinitePath_walk_support
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    (p : DirectedPath.FinitePath (L.stageWeb alpha).graph) :
    (liftStageFinitePath L alpha p).walk.support = p.walk.support := by
  let Q := Gamma.quotient
    (Gamma.terminalFrontier (L.warpAt alpha))
  let hEss : ∀ {x y : V}, (L.stageWeb alpha).graph.Adj x y →
      Q.graph.Adj x y := fun {_ _} h ↦ Q.essentialPart_adj_imp h
  let hQuot : ∀ {x y : V}, Q.graph.Adj x y →
      Gamma.graph.Adj x y := fun {_ _} h ↦ Gamma.quotient_adj_imp h
  change (((p.walk.lift hEss).lift hQuot).support) = p.walk.support
  calc
    ((p.walk.lift hEss).lift hQuot).support =
        (p.walk.lift hEss).support :=
      DirectedPath.Walk.support_lift hQuot (p.walk.lift hEss)
    _ = p.walk.support := DirectedPath.Walk.support_lift hEss p.walk

@[simp]
theorem liftStagePath_support
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    (p : (L.stageWeb alpha).DPath) :
    (L.liftStagePath alpha p).support = p.support := by
  unfold DWeb.KappaLadder.liftStagePath
  rw [Gamma.support_liftQuotientPath]
  exact (Gamma.quotient
    (Gamma.terminalFrontier (L.warpAt alpha))).support_liftEssentialPartPath p

@[simp]
theorem liftStagePath_initial
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    (p : (L.stageWeb alpha).DPath) :
    (L.liftStagePath alpha p).initial = p.initial := by
  rcases p with p | r <;> rfl

@[simp]
theorem liftStagePath_terminal
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    (p : (L.stageWeb alpha).DPath) :
    Gamma.terminal? (L.liftStagePath alpha p) =
      (L.stageWeb alpha).terminal? p := by
  rcases p with p | r <;> rfl

/-- Lift a family of paths from the essential quotient stage back to the
ambient web. -/
def liftStageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    (W : Set (L.stageWeb alpha).DPath) : Set Gamma.DPath :=
  L.liftStagePath alpha '' W

@[simp]
theorem mem_liftStageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {alpha : RegularCardinal.Stage kappa}
    {W : Set (L.stageWeb alpha).DPath} {p : Gamma.DPath} :
    p ∈ liftStageFamily L alpha W ↔
      ∃ q ∈ W, L.liftStagePath alpha q = p :=
  Iff.rfl

theorem liftStageFamily_isWarp
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    {W : Set (L.stageWeb alpha).DPath}
    (hW : (L.stageWeb alpha).IsWarp W) :
    Gamma.IsWarp (liftStageFamily L alpha W) := by
  intro p hp q hq hpq
  obtain ⟨p₀, hp₀, rfl⟩ := hp
  obtain ⟨q₀, hq₀, rfl⟩ := hq
  change Disjoint
    (L.liftStagePath alpha p₀).support
    (L.liftStagePath alpha q₀).support
  rw [liftStagePath_support, liftStagePath_support]
  apply hW hp₀ hq₀
  intro hpq₀
  subst q₀
  exact hpq rfl

theorem liftStageFamily_finiteCharacter
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    {W : Set (L.stageWeb alpha).DPath}
    (hW : (L.stageWeb alpha).HasFiniteCharacter W) :
    Gamma.HasFiniteCharacter (liftStageFamily L alpha W) := by
  rintro p ⟨q, hqW, rfl⟩
  obtain ⟨f, rfl⟩ := hW hqW
  exact ⟨liftStageFinitePath L alpha f, liftStagePath_finite L alpha f⟩

@[simp]
theorem initialSet_liftStageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    (W : Set (L.stageWeb alpha).DPath) :
    Gamma.initialSet (liftStageFamily L alpha W) =
      (L.stageWeb alpha).initialSet W := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hqW, rfl⟩, hpx⟩
    exact ⟨q, hqW, liftStagePath_initial L alpha q ▸ hpx⟩
  · rintro ⟨q, hqW, hqx⟩
    refine ⟨L.liftStagePath alpha q, ⟨q, hqW, rfl⟩, ?_⟩
    exact (liftStagePath_initial L alpha q).trans hqx

@[simp]
theorem terminalFrontier_liftStageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    (W : Set (L.stageWeb alpha).DPath) :
    Gamma.terminalFrontier (liftStageFamily L alpha W) =
      (L.stageWeb alpha).terminalFrontier W := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hqW, rfl⟩, hpx⟩
    exact ⟨q, hqW, liftStagePath_terminal L alpha q ▸ hpx⟩
  · rintro ⟨q, hqW, hqx⟩
    refine ⟨L.liftStagePath alpha q, ⟨q, hqW, rfl⟩, ?_⟩
    exact (liftStagePath_terminal L alpha q).trans hqx

/-- Any subfamily of a stage linkage lifts to an ambient exceptional
remainder.  This is the exact bridge needed after the component replacement
has identified the small set of half-way components which must be kept. -/
theorem liftStageSubfamily_isExceptionalRemainder
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    {A C : Set V} {W K : Set (L.stageWeb alpha).DPath}
    (hW : IsLinkageBetween (L.stageWeb alpha) A C W)
    (hKW : K ⊆ W) :
    IsExceptionalRemainder Gamma A C (liftStageFamily L alpha K) := by
  refine ⟨liftStageFamily_isWarp L alpha (hW.isWarp.subset hKW),
    liftStageFamily_finiteCharacter L alpha
      (fun {_} hp ↦ hW.finiteCharacter (hKW hp)), ?_, ?_, ?_⟩
  · rw [initialSet_liftStageFamily]
    intro x hx
    obtain ⟨p, hpK, rfl⟩ := hx
    rw [← hW.initialSet_eq]
    exact ⟨p, hKW hpK, rfl⟩
  · rw [terminalFrontier_liftStageFamily]
    rintro x ⟨p, hpK, hpx⟩
    exact hW.terminalFrontier_subset ⟨p, hKW hpK, hpx⟩
  · rintro p ⟨q, hqK, rfl⟩
    obtain ⟨f, rfl, hends, hsource⟩ := hW.endpointPure q (hKW hqK)
    refine ⟨liftStageFinitePath L alpha f, liftStagePath_finite L alpha f,
      ?_, ?_⟩
    · simpa only [liftStageFinitePath_support, liftStageFinitePath_start,
        liftStageFinitePath_finish] using hends
    · simpa only [liftStageFinitePath_support, liftStageFinitePath_start]
        using hsource

/-- The target-linking witness on a stage subfamily is unchanged by the
ambient lift: ordered support lists and the target set are preserved. -/
theorem linksToTarget_liftStageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    {K : Set (L.stageWeb alpha).DPath} {U : Set V}
    (hK : LinksToTarget (L.stageWeb alpha) K U) :
    LinksToTarget Gamma (liftStageFamily L alpha K) U := by
  intro u hu
  obtain ⟨p, hpK, f, rfl, hinter, before, after, hsupport,
      b, hb, hbafter⟩ := hK u hu
  refine ⟨L.liftStagePath alpha (Sum.inl f),
    ⟨Sum.inl f, hpK, rfl⟩, liftStageFinitePath L alpha f,
    liftStagePath_finite L alpha f, ?_, ?_⟩
  · simpa only [liftStageFinitePath_support] using hinter
  · refine ⟨before, after, ?_, b, ?_, hbafter⟩
    · simpa only [liftStageFinitePath_walk_support] using hsupport
    · exact hb

theorem mk_liftStageFamily_le
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : RegularCardinal.Stage kappa)
    (K : Set (L.stageWeb alpha).DPath) :
    #(liftStageFamily L alpha K) ≤ #K :=
  Cardinal.mk_image_le

/-! ## Finite segments of a warp -/

/-- Source-indexed finite segments lying on pairwise distinct members of a
reference warp.  Endpoint purity is stated relative to the *ambient* source
set `A`, rather than merely the indexed subset `S`; this is what permits the
segments to be combined with exceptional components without retruncation. -/
structure SegmentRealization (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (A C S : Set V) where
  source_subset : S ⊆ A
  carrier : S → Gamma.DPath
  carrier_mem : ∀ x, carrier x ∈ Y
  carrier_injective : Function.Injective carrier
  segment : S → DirectedPath.FinitePath Gamma.graph
  segment_start : ∀ x, (segment x).start = x.1
  segment_finish_mem : ∀ x, (segment x).finish ∈ C
  segment_subpath : ∀ x, (segment x).IsSubpathOf (carrier x)
  segment_endpoints : ∀ x,
    (segment x).support ∩ (A ∪ C) =
      {(segment x).start, (segment x).finish}
  segment_source : ∀ x,
    (segment x).support ∩ A = {(segment x).start}

/-- The path family selected by a segment realization. -/
def segmentFamily {Gamma : DWeb V} {Y : Set Gamma.DPath}
    {A C S : Set V} (R : SegmentRealization Gamma Y A C S) :
    Set Gamma.DPath :=
  Set.range fun x : S ↦ (Sum.inl (R.segment x) : Gamma.DPath)

@[simp]
theorem mem_segmentFamily {Gamma : DWeb V} {Y : Set Gamma.DPath}
    {A C S : Set V} {R : SegmentRealization Gamma Y A C S}
    {p : Gamma.DPath} :
    p ∈ segmentFamily R ↔
      ∃ x : S, p = (Sum.inl (R.segment x) : Gamma.DPath) :=
  by
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩

theorem segmentFamily_isWarp
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (hY : Gamma.IsWarp Y) (R : SegmentRealization Gamma Y A C S) :
    Gamma.IsWarp (segmentFamily R) := by
  intro p hp q hq hpq
  obtain ⟨x, rfl⟩ := hp
  obtain ⟨y, rfl⟩ := hq
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hpq rfl
  have hcarrier : R.carrier x ≠ R.carrier y :=
    R.carrier_injective.ne hxy
  exact (hY (R.carrier_mem x) (R.carrier_mem y) hcarrier).mono
    (R.segment_subpath x).1 (R.segment_subpath y).1

theorem segmentFamily_finiteCharacter
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (R : SegmentRealization Gamma Y A C S) :
    Gamma.HasFiniteCharacter (segmentFamily R) := by
  rintro p ⟨x, rfl⟩
  exact ⟨R.segment x, rfl⟩

@[simp]
theorem initialSet_segmentFamily
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (R : SegmentRealization Gamma Y A C S) :
    Gamma.initialSet (segmentFamily R) = S := by
  ext v
  constructor
  · rintro ⟨p, ⟨x, rfl⟩, hp⟩
    change (R.segment x).start = v at hp
    have : x.1 = v := (R.segment_start x).symm.trans hp
    exact this ▸ x.2
  · intro hv
    let x : S := ⟨v, hv⟩
    refine ⟨(Sum.inl (R.segment x) : Gamma.DPath), ⟨x, rfl⟩, ?_⟩
    change (R.segment x).start = v
    exact R.segment_start x

theorem terminalFrontier_segmentFamily_subset
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (R : SegmentRealization Gamma Y A C S) :
    Gamma.terminalFrontier (segmentFamily R) ⊆ C := by
  rintro v ⟨p, ⟨x, rfl⟩, hp⟩
  change some (R.segment x).finish = some v at hp
  exact Option.some.inj hp ▸ R.segment_finish_mem x

/-- Distinct components of a warp yield a linkage of their selected finite
segments. -/
theorem segmentFamily_isLinkageBetween
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (hY : Gamma.IsWarp Y) (R : SegmentRealization Gamma Y A C S) :
    IsLinkageBetween Gamma S C (segmentFamily R) := by
  refine ⟨segmentFamily_isWarp hY R,
    segmentFamily_finiteCharacter R, initialSet_segmentFamily R,
    terminalFrontier_segmentFamily_subset R, ?_⟩
  rintro p ⟨x, rfl⟩
  refine ⟨R.segment x, rfl, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨hvSupport, hv⟩
      have hv' : v ∈ (R.segment x).support ∩ (A ∪ C) :=
        ⟨hvSupport, hv.elim (fun h ↦ Or.inl (R.source_subset h)) Or.inr⟩
      rw [R.segment_endpoints x] at hv'
      exact hv'
    · intro hv
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact ⟨(R.segment x).start_mem_support,
          Or.inl (R.segment_start x ▸ x.2)⟩
      · exact ⟨(R.segment x).finish_mem_support,
          Or.inr (R.segment_finish_mem x)⟩
  · ext v
    constructor
    · rintro ⟨hvSupport, hvS⟩
      have hv' : v ∈ (R.segment x).support ∩ A :=
        ⟨hvSupport, R.source_subset hvS⟩
      rw [R.segment_source x] at hv'
      exact hv'
    · intro hv
      have hvstart : v = (R.segment x).start := by
        simpa only [Set.mem_singleton_iff] using hv
      subst v
      exact ⟨(R.segment x).start_mem_support,
        R.segment_start x ▸ x.2⟩

/-- Every selected segment is an ordinary fragment of the reference warp. -/
theorem segmentFamily_isLadderFragment
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (R : SegmentRealization Gamma Y A C S) :
    ∀ p ∈ segmentFamily R, IsLadderFragment Gamma Y p := by
  rintro p ⟨x, rfl⟩
  exact ⟨R.carrier x, R.carrier_mem x, R.segment_subpath x⟩

/-! ## Replacement of all nonexceptional components -/

/-- A source-indexed realization of the finitely joined exceptional
components.  In the slice proof these paths are obtained by appending the
small residual `C`--`T_beta` linkage to the corresponding lifted half-way
components.  Keeping the realization at path level makes the union theorem
independent of the particular append construction. -/
structure ExceptionalRealization (Gamma : DWeb V) (A C S : Set V) where
  path : S → DirectedPath.FinitePath Gamma.graph
  path_start : ∀ x, (path x).start = x.1
  path_finish_mem : ∀ x, (path x).finish ∈ C
  endpointPure : ∀ x,
    (path x).support ∩ (A ∪ C) = {(path x).start, (path x).finish}
  sourcePure : ∀ x, (path x).support ∩ A = {(path x).start}
  pairwise_disjoint : ∀ x y, x ≠ y →
    Disjoint (path x).support (path y).support

def exceptionalFamily
    {Gamma : DWeb V} {A C S : Set V}
    (R : ExceptionalRealization Gamma A C S) : Set Gamma.DPath :=
  Set.range fun x : S ↦ (Sum.inl (R.path x) : Gamma.DPath)

@[simp]
theorem initialSet_exceptionalFamily
    {Gamma : DWeb V} {A C S : Set V}
    (R : ExceptionalRealization Gamma A C S) :
    Gamma.initialSet (exceptionalFamily R) = S := by
  ext v
  constructor
  · rintro ⟨p, ⟨x, rfl⟩, hpx⟩
    change (R.path x).start = v at hpx
    exact (R.path_start x).symm.trans hpx ▸ x.2
  · intro hv
    let x : S := ⟨v, hv⟩
    refine ⟨(Sum.inl (R.path x) : Gamma.DPath), ⟨x, rfl⟩, ?_⟩
    exact R.path_start x

/-- A realized exceptional family is an ambient partial linkage. -/
theorem exceptionalFamily_isExceptionalRemainder
    {Gamma : DWeb V} {A C S : Set V}
    (hS : S ⊆ A) (R : ExceptionalRealization Gamma A C S) :
    IsExceptionalRemainder Gamma A C (exceptionalFamily R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq
    apply R.pairwise_disjoint
    intro hxy
    subst y
    exact hpq rfl
  · rintro p ⟨x, rfl⟩
    exact ⟨R.path x, rfl⟩
  · rw [initialSet_exceptionalFamily]
    exact hS
  · rintro v ⟨p, ⟨x, rfl⟩, hpv⟩
    change some (R.path x).finish = some v at hpv
    exact Option.some.inj hpv ▸ R.path_finish_mem x
  · rintro p ⟨x, rfl⟩
    exact ⟨R.path x, rfl, R.endpointPure x, R.sourcePure x⟩

theorem mk_exceptionalFamily_le
    {Gamma : DWeb V} {A C S : Set V}
    (R : ExceptionalRealization Gamma A C S) :
    #(exceptionalFamily R) ≤ #S :=
  Cardinal.mk_range_le

/-- The vertex-disjoint union of ordinary segments and an exceptional
remainder is a linkage, provided their initial vertices cover the ambient
source frontier. -/
theorem linkageBetween_segmentFamily_union_exceptional
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (hY : Gamma.IsWarp Y) (R : SegmentRealization Gamma Y A C S)
    {E : Set Gamma.DPath} (hE : IsExceptionalRemainder Gamma A C E)
    (hcover : A = S ∪ Gamma.initialSet E)
    (hdisjoint : Disjoint (Gamma.vertexSet (segmentFamily R))
      (Gamma.vertexSet E)) :
    IsLinkageBetween Gamma A C (segmentFamily R ∪ E) := by
  have hO := segmentFamily_isLinkageBetween hY R
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hpO | hpE
    · rcases hq with hqO | hqE
      · exact hO.isWarp hpO hqO hpq
      · change Disjoint p.support q.support
        rw [Set.disjoint_left]
        intro x hxp hxq
        exact Set.disjoint_left.1 hdisjoint
          ⟨p, hpO, hxp⟩ ⟨q, hqE, hxq⟩
    · rcases hq with hqO | hqE
      · change Disjoint p.support q.support
        rw [Set.disjoint_left]
        intro x hxp hxq
        exact Set.disjoint_left.1 hdisjoint
          ⟨q, hqO, hxq⟩ ⟨p, hpE, hxp⟩
      · exact hE.isWarp hpE hqE hpq
  · intro p hp
    rcases hp with hpO | hpE
    · exact hO.finiteCharacter hpO
    · exact hE.finiteCharacter hpE
  · rw [DWeb.initialSet_union, initialSet_segmentFamily, hcover]
  · rw [DWeb.terminalFrontier_union]
    exact Set.union_subset
      (terminalFrontier_segmentFamily_subset R)
      hE.terminalFrontier_subset
  · intro p hp
    rcases hp with hpO | hpE
    · obtain ⟨x, rfl⟩ := hpO
      exact ⟨R.segment x, rfl, R.segment_endpoints x, R.segment_source x⟩
    · exact hE.endpointPure p hpE

/-- Linking a designated set to the final target is monotone in the path
family. -/
theorem linksToTarget_mono_family
    {Gamma : DWeb V} {W T : Set Gamma.DPath} {U : Set V}
    (hWT : W ⊆ T) (hW : LinksToTarget Gamma W U) :
    LinksToTarget Gamma T U := by
  intro u hu
  obtain ⟨p, hpW, hp⟩ := hW u hu
  exact ⟨p, hWT hpW, hp⟩

/-- Replacing every nonexceptional component by its segment on the limiting
ladder warp gives the raw output required by the controlled-slice layer.

The exceptional paths themselves retain the requested target links.  This
is the form used in 9.10: paths associated with the small scheduled set are
kept among the exceptions, while all remaining components are replaced by
limiting-warp segments. -/
theorem exists_sliceGood_of_limitWarp_componentReplacement
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa)
    {alpha beta : RegularCardinal.Stage kappa} {S U : Set V}
    (hY : Gamma.IsWarp L.limitWarp)
    (R : SegmentRealization Gamma L.limitWarp
      (L.frontier alpha) (L.frontier beta) S)
    {E : Set Gamma.DPath}
    (hE : IsExceptionalRemainder Gamma
      (L.frontier alpha) (L.frontier beta) E)
    (hcover : L.frontier alpha = S ∪ Gamma.initialSet E)
    (hdisjoint : Disjoint (Gamma.vertexSet (segmentFamily R))
      (Gamma.vertexSet E))
    (hlinks : LinksToTarget Gamma E U) (hEcard : #E < kappa) :
    ∃ T : Set Gamma.DPath,
      SliceGood Gamma L T alpha beta U ∧
      OrdinaryOutside Gamma L.limitWarp T E ∧ #E < kappa := by
  let O := segmentFamily R
  let T := O ∪ E
  have hlinkage : IsLinkageBetween Gamma
      (L.frontier alpha) (L.frontier beta) T := by
    exact linkageBetween_segmentFamily_union_exceptional hY R hE hcover
      hdisjoint
  have htarget : LinksToTarget Gamma T U :=
    linksToTarget_mono_family Set.subset_union_right hlinks
  refine ⟨T, ⟨hlinkage, htarget⟩, ?_, hEcard⟩
  refine ⟨Set.subset_union_right, ?_⟩
  intro p hpT hpE
  have hpO : p ∈ O := hpT.resolve_right hpE
  exact segmentFamily_isLadderFragment R p hpO

/-- Fully path-realized component replacement.  The ordinary and
exceptional source sets partition the old frontier, the two realized
families are disjoint, and fewer than `kappa` exceptional sources are used.
The conclusion supplies both the final slice and its concrete exceptional
subfamily. -/
theorem exists_sliceGood_of_realizedComponentReplacement
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa)
    {alpha beta : RegularCardinal.Stage kappa}
    {Sordinary Sexceptional U : Set V}
    (hY : Gamma.IsWarp L.limitWarp)
    (Rordinary : SegmentRealization Gamma L.limitWarp
      (L.frontier alpha) (L.frontier beta) Sordinary)
    (Rexceptional : ExceptionalRealization Gamma
      (L.frontier alpha) (L.frontier beta) Sexceptional)
    (hExceptionalSource : Sexceptional ⊆ L.frontier alpha)
    (hcover : L.frontier alpha = Sordinary ∪ Sexceptional)
    (hdisjoint : Disjoint (Gamma.vertexSet (segmentFamily Rordinary))
      (Gamma.vertexSet (exceptionalFamily Rexceptional)))
    (hlinks : LinksToTarget Gamma
      (exceptionalFamily Rexceptional) U)
    (hsmall : #Sexceptional < kappa) :
    ∃ (T E : Set Gamma.DPath),
      SliceGood Gamma L T alpha beta U ∧
      OrdinaryOutside Gamma L.limitWarp T E ∧ #E < kappa := by
  let E := exceptionalFamily Rexceptional
  have hE : IsExceptionalRemainder Gamma
      (L.frontier alpha) (L.frontier beta) E :=
    exceptionalFamily_isExceptionalRemainder hExceptionalSource Rexceptional
  have hEcard : #E < kappa :=
    (mk_exceptionalFamily_le Rexceptional).trans_lt hsmall
  have hcover' : L.frontier alpha =
      Sordinary ∪ Gamma.initialSet E := by
    rw [initialSet_exceptionalFamily]
    exact hcover
  obtain ⟨T, hgood, hordinary, hcard⟩ :=
    exists_sliceGood_of_limitWarp_componentReplacement L hY Rordinary
      hE hcover' hdisjoint hlinks hEcard
  exact ⟨T, E, hgood, hordinary, hcard⟩

end SliceSegmentCore
end CardinalInduction
end Erdos599
