/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOutsideMacroAssignment
import ErdosProblems.Erdos599.FracturedWarpOfWarp
import ErdosProblems.Erdos599.HalfwayInsideCutSplice

/-!
# The honest outside-row survivor rank

If the reference warp is literally a subwarp of the later row, a source
uncovered by the reference belongs to a unique row member disjoint from the
entire reference.  Consequently the macro-owned simultaneous assignment
cannot use a backward reference link: its selected route stays on that one
row member and, when finite, has the same terminal.

This observation supplies the missing global rank for Assertion 9.31.  The
canonical predecessor depth of the honest later-row relation increases both
on every inside edge and on every nontrivial compressed assignment edge.
Thus the inside-plus-assignment relation has neither a directed cycle nor a
reverse directed ray; neither fact is accepted as a callback.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating
open Alternating.RelationDecomposition

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y W : Set Gamma.DPath}
variable {X : Set V} {kappa : Cardinal.{u}}

namespace OutsideMacroFullAssignment

/-- Every vertex of a selected full-reference route lies on the unique
outside later-row member beginning at its source. -/
theorem assigned_vertexSet_subset_initialPath
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    (s : {z // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet Y}) :
    (A.assignment.assigned s).vertexSet ⊆
      (initialPath (outsideReference W X)
        ⟨s.1, s.property.1⟩).1.support := by
  intro x hx
  let t := SimultaneousAssignment.toOutsideSource (X := X) s
  let p : outsideReference W X :=
    initialPath (outsideReference W X) ⟨t.1, t.property.1⟩
  have hx' : x ∈ (A.provenance.assigned t).vertexSet := by
    change x ∈ (A.full.assigned s).vertexSet at hx
    rw [A.full_assigned s] at hx
    exact hx
  obtain ⟨q, hqOwner, hxq⟩ := A.provenance.vertex_owner t x hx'
  change q ∈ macroOrbit (outsideReference W X)
      (outsideReference Y X) p ∨
    q ∈ macroReference (outsideReference W X)
      (outsideReference Y X) p at hqOwner
  have hZ : Gamma.IsWarp (outsideReference W X) :=
    outsideReference_isWarp hW
  have hpOutside : p.1 ∉ outsideReference Y X := by
    intro hp
    exact t.property.2 ⟨p.1, hp, initialPath_initial _ _⟩
  have hstepRoot : ¬ ∃ r : outsideReference W X,
      AssignmentMacroStep (outsideReference W X)
        (outsideReference Y X) p r := by
    rintro ⟨r, qY, v, hpterm, hqterm, _hqr⟩
    let qZ : outsideReference W X := ⟨qY.1, hsub qY.2⟩
    have hpq : p = qZ := by
      apply Subtype.ext
      exact DWeb.IsWarp.eq_of_mem_support hZ p.2 qZ.2
        (Gamma.terminal_mem_support hpterm)
        (Gamma.terminal_mem_support hqterm)
    exact hpOutside (hpq ▸ qY.2)
  have horbit : macroOrbit (outsideReference W X)
      (outsideReference Y X) p = {p.1} := by
    ext r
    constructor
    · rintro ⟨hrZ, hpr⟩
      rcases Relation.ReflTransGen.cases_head hpr with h | ⟨q, hpq, _⟩
      · simpa only [Set.mem_singleton_iff] using
          (congrArg Subtype.val h).symm
      · exact False.elim (hstepRoot ⟨q, hpq⟩)
    · intro hr
      have hrp : r = p.1 := Set.mem_singleton_iff.mp hr
      subst r
      exact mem_macroOrbit_root _ _ p
  have hreference : macroReference (outsideReference W X)
      (outsideReference Y X) p = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    rcases hr.2 with ⟨q, hqOrbit, hqr⟩
    have hqp : q = p.1 := by simpa [horbit] using hqOrbit
    have hrZ : r ∈ outsideReference W X := hsub hr.1
    have hrp : r = p.1 := by
      apply DWeb.IsWarp.eq_of_mem_support hZ hrZ p.2
        r.initial_mem_support
      rw [← hqr]
      simpa [hqp] using q.initial_mem_support
    exact hpOutside (hrp ▸ hr.1)
  rcases hqOwner with hqOrbit | hqReference
  · have hqp : q = p.1 := by simpa [horbit] using hqOrbit
    simpa [p, t, hqp] using hxq
  · rw [hreference] at hqReference
    exact False.elim hqReference

/-- No selected route can traverse a reference link backwards: the route
is confined to a later-row member whose initial is uncovered by `Y`, while
every backward link lies on a member of the subwarp `Y ⊆ W`. -/
theorem no_backward_link
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hYclosed : ClosedUnderPaths Gamma Y X)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    (s : {z // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet Y})
    (l : Link Gamma.graph) (hl : l ∈ (A.assignment.assigned s).links) :
    l.direction ≠ .backward := by
  intro hbackward
  obtain ⟨q, hqY, hlq⟩ :=
    (A.assignment.safe s).1.2.1 l hl hbackward
  let p : outsideReference W X :=
    initialPath (outsideReference W X) ⟨s.1, s.property.1⟩
  have hxQ : l.path.start ∈ (A.assignment.assigned s).vertexSet :=
    (A.assignment.assigned s).link_support_subset_vertexSet hl
      l.path.start_mem_support
  have hxp : l.path.start ∈ p.1.support :=
    A.assigned_vertexSet_subset_initialPath hW hsub s hxQ
  have hxq : l.path.start ∈ q.support :=
    hlq.1 l.path.start_mem_support
  have hxnot : l.path.start ∉ X := by
    exact Set.disjoint_left.1 (A.full_avoids s) hxQ
  have hqdisjoint : Disjoint q.support X := by
    rw [Set.disjoint_left]
    intro z hzq hzX
    have hqX : q.support ⊆ X := hYclosed q hqY ⟨z, hzq, hzX⟩
    exact hxnot (hqX hxq)
  have hqW : q ∈ W := (hsub ⟨hqY, hqdisjoint⟩).1
  have hpq : p.1 = q :=
    DWeb.IsWarp.eq_of_mem_support hW p.2.1 hqW hxp hxq
  apply s.property.2
  exact ⟨q, hqY, (congrArg Path.initial hpq).symm.trans
    (initialPath_initial _ _)⟩

/-- Since directions alternate, a route with no backward link cannot be an
infinite alternating trace. -/
theorem assigned_not_infinite
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hYclosed : ClosedUnderPaths Gamma Y X)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    (s : {z // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet Y}) :
    ¬ (A.assignment.assigned s).IsInfinite := by
  intro hinfinite
  cases hQ : A.assignment.assigned s with
  | trivial v =>
      rw [hQ] at hinfinite
      exact hinfinite
  | finite Q =>
      rw [hQ] at hinfinite
      exact hinfinite
  | infinite Q =>
      have hl0 : Q.link 0 ∈ (A.assignment.assigned s).links := by
        rw [hQ]
        exact ⟨0, rfl⟩
      have hl1 : Q.link 1 ∈ (A.assignment.assigned s).links := by
        rw [hQ]
        exact ⟨1, rfl⟩
      have h0 : (Q.link 0).direction ≠ .backward := by
        exact A.no_backward_link hW hYclosed hsub s (Q.link 0) hl0
      have h1 : (Q.link 1).direction ≠ .backward := by
        exact A.no_backward_link hW hYclosed hsub s (Q.link 1) hl1
      have hd0 : (Q.link 0).direction = .forward := by
        cases hd : (Q.link 0).direction with
        | forward => rfl
        | backward => exact False.elim (h0 hd)
      have hd1 : (Q.link 1).direction = .forward := by
        cases hd : (Q.link 1).direction with
        | forward => rfl
        | backward => exact False.elim (h1 hd)
      exact Q.alternates 0 (hd0.trans hd1.symm)

/-- Every compressed assignment edge is the initial-to-terminal shortcut
of the unique honest later-row path at its source. -/
theorem assigned_terminal_initialPath
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    (s : {z // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet Y}) {v : V}
    (hterminal : (A.assignment.assigned s).terminal? = some v) :
    Gamma.terminal?
      (initialPath (outsideReference W X) ⟨s.1, s.property.1⟩).1 =
        some v := by
  let p : outsideReference W X :=
    initialPath (outsideReference W X) ⟨s.1, s.property.1⟩
  obtain ⟨q, hqZ, hqterminal⟩ :=
    (A.assignment.finite_terminal_mem s hterminal).1
  have hvQ : v ∈ (A.assignment.assigned s).vertexSet :=
    (A.assignment.assigned s).mem_vertexSet_of_terminal_eq hterminal
  have hvp : v ∈ p.1.support :=
    A.assigned_vertexSet_subset_initialPath hW hsub s hvQ
  have hvq : v ∈ q.support := Gamma.terminal_mem_support hqterminal
  have hpq : p.1 = q :=
    DWeb.IsWarp.eq_of_mem_support hW p.2.1 hqZ.1 hvp hvq
  exact (congrArg Gamma.terminal? hpq).trans hqterminal

end OutsideMacroFullAssignment

/-! ## The canonical later-row rank -/

/-- The honest warp relation has well-founded predecessor order. -/
theorem familyEdges_predecessorWellFounded
    (hW : Gamma.IsWarp W) :
    WellFounded (fun x y : V ↦ (x, y) ∈ familyEdges W) :=
  ForwardOrientation.predecessor_wellFounded (familyEdges W)
    (PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsDirectedCycle hW)
    (PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay hW)

/-- Canonical natural-number depth in the honest later-row warp. -/
noncomputable def laterRowRank (W : Set Gamma.DPath)
    (hW : Gamma.IsWarp W) : V → Nat :=
  ForwardOrientation.wellFoundedDepth (familyEdges W)
    (familyEdges_predecessorWellFounded hW)

theorem laterRowRank_lt_of_mem_familyEdges
    (hW : Gamma.IsWarp W) {x y : V}
    (hxy : (x, y) ∈ familyEdges W) :
    laterRowRank W hW x < laterRowRank W hW y := by
  have hstep := ForwardOrientation.wellFoundedDepth_step
    (familyEdges W) (Alternating.IsWarp.familyEdges_biUnique hW)
    (familyEdges_predecessorWellFounded hW) hxy
  change ForwardOrientation.wellFoundedDepth (familyEdges W)
      (familyEdges_predecessorWellFounded hW) x <
    ForwardOrientation.wellFoundedDepth (familyEdges W)
      (familyEdges_predecessorWellFounded hW) y
  omega

private theorem walk_rank_le_end
    {D : Digraph V} {a b : V} (P : Walk D a b) (rank : V → Nat)
    (hstep : ∀ {x y}, (x, y) ∈ P.edgeSet → rank x < rank y) :
    rank a ≤ rank b := by
  induction P with
  | nil => exact le_rfl
  | @cons a c b h P ih =>
      have hac : rank a < rank c := hstep (by simp [Walk.edgeSet_cons])
      have htail : ∀ {x y}, (x, y) ∈ P.edgeSet → rank x < rank y := by
        intro x y hxy
        exact hstep (by simp [Walk.edgeSet_cons, hxy])
      exact hac.le.trans (ih htail)

private theorem walk_rank_lt_end_of_ne
    {D : Digraph V} {a b : V} (P : Walk D a b) (rank : V → Nat)
    (hstep : ∀ {x y}, (x, y) ∈ P.edgeSet → rank x < rank y)
    (hne : a ≠ b) : rank a < rank b := by
  cases P with
  | nil => exact False.elim (hne rfl)
  | @cons a c b h P =>
      have hac : rank a < rank c := hstep (by simp [Walk.edgeSet_cons])
      have htail : ∀ {x y}, (x, y) ∈ P.edgeSet → rank x < rank y := by
        intro x y hxy
        exact hstep (by simp [Walk.edgeSet_cons, hxy])
      exact hac.trans_le (walk_rank_le_end P rank htail)

/-- The later-row depth strictly separates the two endpoints of every
nontrivial finite row member. -/
theorem laterRowRank_initial_lt_terminal
    (hW : Gamma.IsWarp W) {p : Gamma.DPath} (hpW : p ∈ W)
    {q : FinitePath Gamma.graph} (hpq : p = .inl q)
    (hne : q.start ≠ q.finish) :
    laterRowRank W hW p.initial < laterRowRank W hW q.finish := by
  rw [hpq] at hpW ⊢
  apply walk_rank_lt_end_of_ne q.walk (laterRowRank W hW)
  · intro x y hxy
    apply laterRowRank_lt_of_mem_familyEdges hW
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨.inl q, hpW, hxy⟩
  · exact hne

/-! ## Rank consequences for the inside-plus-assignment relation -/

variable {before innerRoof outerRoof : Set V}

/-! ## Exact outside relation under row closure -/

/-- If the row is closed under `X`, deleting edges internal to `X` simply
keeps the complete members whose supports avoid `X`. -/
theorem outsideFamilyEdges_eq_familyEdges_outsideReference
    (hclosed : ClosedUnderPaths Gamma W X) :
    outsideFamilyEdges W X = familyEdges (outsideReference W X) := by
  apply Set.Subset.antisymm
  · intro e he
    have heW : e ∈ familyEdges W := he.1
    simp only [familyEdges, Set.mem_iUnion] at heW
    obtain ⟨p, hpW, hep⟩ := heW
    have hpdisjoint : Disjoint p.support X := by
      rw [Set.disjoint_left]
      intro x hxp hxX
      have hpX : p.support ⊆ X := hclosed p hpW ⟨x, hxp, hxX⟩
      have hend := p.edgeSet_subset_support_prod hep
      exact he.2 ⟨hpX hend.1, hpX hend.2⟩
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨p, ⟨hpW, hpdisjoint⟩, hep⟩
  · intro e he
    simp only [familyEdges, Set.mem_iUnion] at he
    obtain ⟨p, hp, hep⟩ := he
    refine ⟨Set.mem_iUnion.2 ⟨p,
      Set.mem_iUnion.2 ⟨hp.1, hep⟩⟩, ?_⟩
    have hend := p.edgeSet_subset_support_prod hep
    rintro ⟨hxX, hyX⟩
    exact Set.disjoint_left.1 hp.2 hend.1 hxX

/-- Under the same closure, the literal outside carrier is exactly the
vertex set of the honest outside subwarp. -/
theorem outsideCarrier_eq_vertexSet_outsideReference
    (hclosed : ClosedUnderPaths Gamma W X) :
    outsideCarrier W X = Gamma.vertexSet (outsideReference W X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxW : x ∈ Gamma.vertexSet W :=
      outsideCarrier_subset_vertexSet W X hx
    have hxnot : x ∉ X :=
      Set.disjoint_left.1
        (outsideCarrier_disjoint_of_closedUnderPaths W X hclosed) hx
    obtain ⟨p, hpW, hxp⟩ := hxW
    have hpdisjoint : Disjoint p.support X := by
      rw [Set.disjoint_left]
      intro y hyp hyX
      have hpX : p.support ⊆ X := hclosed p hpW ⟨y, hyp, hyX⟩
      exact hxnot (hpX hxp)
    exact ⟨p, ⟨hpW, hpdisjoint⟩, hxp⟩
  · rintro x ⟨p, hp, hxp⟩
    exact Or.inl ⟨⟨p, hp.1, hxp⟩,
      fun hxX ↦ Set.disjoint_left.1 hp.2 hxp hxX⟩

/-- Closed-row cut roots are exactly the initials of the honest outside
subwarp. -/
theorem cutInitial_eq_initialSet_outsideReference
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hclosed : ClosedUnderPaths Gamma W X) :
    CutSplit.initialVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X =
      Gamma.initialSet (outsideReference W X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hxcut | ⟨hxcarrier, _hxnot, hno⟩
    · obtain ⟨hxX, y, hxy⟩ := hxcut
      have hxcarrier := (outsideFamilyEdges_endpoints W X hxy).1
      exact False.elim <| Set.disjoint_left.1
        (outsideCarrier_disjoint_of_closedUnderPaths W X hclosed)
        hxcarrier hxX
    · rw [initialSet_eq_vertexSet_diff_hasIncoming
        (outsideReference_isWarp hW)
        (outsideReference_finiteCharacter hWfinite)]
      refine ⟨outsideCarrier_eq_vertexSet_outsideReference hclosed ▸
        hxcarrier, ?_⟩
      rintro ⟨y, hyx⟩
      apply hno ⟨y, ?_⟩
      rw [outsideFamilyEdges_eq_familyEdges_outsideReference hclosed]
      exact hyx
  · rintro x ⟨p, hp, rfl⟩
    have hxnot : p.initial ∉ X :=
      Set.disjoint_left.1 hp.2 p.initial_mem_support
    apply Or.inr
    refine ⟨Or.inl ⟨⟨p, hp.1, p.initial_mem_support⟩, hxnot⟩,
      hxnot, ?_⟩
    rintro ⟨y, hyx⟩
    have hpinitial : p.initial ∈ Gamma.initialSet W := ⟨p, hp.1, rfl⟩
    rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfinite] at hpinitial
    exact hpinitial.2 ⟨y, outsideFamilyEdges_subset W X hyx⟩

/-- Closed-row cut sinks are exactly the finite terminals of the honest
outside subwarp. -/
theorem cutTerminal_eq_terminalFrontier_outsideReference
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hclosed : ClosedUnderPaths Gamma W X) :
    CutSplit.terminalVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X =
      Gamma.terminalFrontier (outsideReference W X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hxcut | ⟨hxcarrier, _hxnot, hno⟩
    · obtain ⟨hxX, y, hyx⟩ := hxcut
      have hxcarrier := (outsideFamilyEdges_endpoints W X hyx).2
      exact False.elim <| Set.disjoint_left.1
        (outsideCarrier_disjoint_of_closedUnderPaths W X hclosed)
        hxcarrier hxX
    · rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing
        (outsideReference_isWarp hW)
        (outsideReference_finiteCharacter hWfinite)]
      refine ⟨outsideCarrier_eq_vertexSet_outsideReference hclosed ▸
        hxcarrier, ?_⟩
      rintro ⟨y, hxy⟩
      apply hno ⟨y, ?_⟩
      rw [outsideFamilyEdges_eq_familyEdges_outsideReference hclosed]
      exact hxy
  · rintro x ⟨p, hp, hterminal⟩
    have hxSupport : x ∈ p.support := Gamma.terminal_mem_support hterminal
    have hxnot : x ∉ X := Set.disjoint_left.1 hp.2 hxSupport
    apply Or.inr
    refine ⟨Or.inl ⟨⟨p, hp.1, hxSupport⟩, hxnot⟩, hxnot, ?_⟩
    rintro ⟨y, hxy⟩
    have hxterminal : x ∈ Gamma.terminalFrontier W :=
      ⟨p, hp.1, hterminal⟩
    rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfinite]
        at hxterminal
    exact hxterminal.2 ⟨y, outsideFamilyEdges_subset W X hxy⟩

namespace CanonicalInsideCut

variable {F : FracturedWarp Gamma}

/-! ### Honest outside-row attachment -/

/-- An initial of the honest outside subwarp is a literal initial vertex of
the cut relation.  Row closure is stronger than needed for the incidence
argument, but records the exact Section 9 situation and supplies disjointness
from the cut. -/
theorem outsideReference_initial_subset_cutInitial
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hclosed : ClosedUnderPaths Gamma W X) :
    Gamma.initialSet (outsideReference W X) ⊆
      CutSplit.initialVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X := by
  rintro x ⟨p, hp, rfl⟩
  have hxnot : p.initial ∉ X :=
    Set.disjoint_left.1 hp.2 p.initial_mem_support
  apply Or.inr
  refine ⟨Or.inl ⟨⟨p, hp.1, p.initial_mem_support⟩, hxnot⟩,
    hxnot, ?_⟩
  rintro ⟨y, hyx⟩
  have hpinitial : p.initial ∈ Gamma.initialSet W := ⟨p, hp.1, rfl⟩
  rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfinite] at hpinitial
  exact hpinitial.2 ⟨y, outsideFamilyEdges_subset W X hyx⟩

/-- A finite terminal of the honest outside subwarp is a literal terminal
vertex of the cut relation. -/
theorem outsideReference_terminal_subset_cutTerminal
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hclosed : ClosedUnderPaths Gamma W X) :
    Gamma.terminalFrontier (outsideReference W X) ⊆
      CutSplit.terminalVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X := by
  rintro x ⟨p, hp, hterminal⟩
  have hxSupport : x ∈ p.support := Gamma.terminal_mem_support hterminal
  have hxnot : x ∉ X := Set.disjoint_left.1 hp.2 hxSupport
  apply Or.inr
  refine ⟨Or.inl ⟨⟨p, hp.1, hxSupport⟩, hxnot⟩, hxnot, ?_⟩
  rintro ⟨y, hxy⟩
  have hxterminal : x ∈ Gamma.terminalFrontier W :=
    ⟨p, hp.1, hterminal⟩
  rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfinite]
      at hxterminal
  exact hxterminal.2 ⟨y, outsideFamilyEdges_subset W X hxy⟩

/-- A macro-assignment source is a terminal of the complementary inside
family. -/
theorem macroAssignmentSource_mem_terminalSet
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hclosed : ClosedUnderPaths Gamma W X)
    (s : {z // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet Y}) :
    s.1 ∈ I.insideFamily.terminalSet := by
  apply I.uncoveredCutInitial_subset_terminalSet hW
  exact ⟨outsideReference_initial_subset_cutInitial hW hWfinite
    hclosed s.property.1, s.property.2⟩

/-- A finite macro-assignment target is an initial of the complementary
inside family. -/
theorem macroAssignmentTarget_mem_initialSet
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hclosed : ClosedUnderPaths Gamma W X)
    (s : {z // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet Y}) {v : V}
    (hterminal : (A.assignment.assigned s).terminal? = some v) :
    v ∈ I.insideFamily.initialSet := by
  apply I.uncoveredCutTerminal_subset_initialSet hW
  exact ⟨outsideReference_terminal_subset_cutTerminal hW hWfinite
      hclosed (A.assignment.finite_terminal_mem s hterminal).1,
    (A.assignment.finite_terminal_mem s hterminal).2⟩

/-- The literal inside relation and the honest outside macro shortcuts have
the required global degree bound. -/
theorem macroFullRelation_biUnique
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hclosed : ClosedUnderPaths Gamma W X) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ I.insideFamily.edgeSet ∪
        assignedFiniteEdges
          (Zf := FracturedWarp.ofWarp (outsideReference W X)
            (outsideReference_isWarp hW)) A.assignment) := by
  apply biUnique_union_of_cross
  · change Relator.BiUnique (fun x y ↦
      (x, y) ∈ familyEdges (Γ := imaginaryWeb Gamma Y kappa)
        I.insideFamily.paths)
    exact Alternating.IsWarp.familyEdges_biUnique
      (Γ := imaginaryWeb Gamma Y kappa) I.insideFamily.isWarp
  · exact assignedFiniteEdges_biUnique
      (Zf := FracturedWarp.ofWarp (outsideReference W X)
        (outsideReference_isWarp hW)) A.assignment
  · intro x y z hxz hyz
    obtain ⟨s, hterm, _⟩ := hyz
    exact False.elim <| I.insideFamily.no_incoming_of_mem_initialSet
      (I.macroAssignmentTarget_mem_initialSet A hW hWfinite hclosed
        s hterm) ⟨x, hxz⟩
  · intro x y z hxy hxz
    obtain ⟨s, _hterm, hsx⟩ := hxz
    exact False.elim <| I.insideFamily.no_outgoing_of_mem_terminalSet
      (by simpa [hsx] using
        I.macroAssignmentSource_mem_terminalSet hW hWfinite hclosed s)
      ⟨y, hxy⟩

/-- Every complementary-inside terminal is either an honest macro source or
already a terminal of the later row.  The apparently covered cut-root case
cannot occur in the canonical carrier. -/
theorem macroTerminalBoundary
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hclosed : ClosedUnderPaths Gamma W X)
    {target : Set V} (hrowTerminal : Gamma.terminalFrontier W ⊆ target) :
    I.insideFamily.terminalSet ⊆
      {x | ∃ s : {z // z ∈ Gamma.initialSet (outsideReference W X) \
        Gamma.initialSet Y}, s.1 = x} ∪ target := by
  intro x hxTerminal
  rcases I.terminalSet_subset_cutInitial_union_terminalFrontier hxTerminal with
      hxCut | hxRowTerminal
  · have hxOutsideInitial :
        x ∈ Gamma.initialSet (outsideReference W X) := by
      rw [← cutInitial_eq_initialSet_outsideReference hW hWfinite hclosed]
      exact hxCut
    by_cases hxY : x ∈ Gamma.initialSet Y
    · have hxCarrier : x ∈ I.insideFamily.vertexSet := by
        rw [I.insideFamily.terminalSet_eq_no_outgoing] at hxTerminal
        exact hxTerminal.1
      rw [I.vertexSet_eq] at hxCarrier
      obtain ⟨p, hpOutside, hpInitial⟩ := hxOutsideInitial
      have hxNotX : x ∉ X := by
        intro hxX
        exact Set.disjoint_left.1 hpOutside.2
          (hpInitial ▸ p.initial_mem_support) hxX
      have hxYVertex : x ∈ Gamma.vertexSet Y := by
        obtain ⟨q, hqY, hqInitial⟩ := hxY
        exact ⟨q, hqY, hqInitial ▸ q.initial_mem_support⟩
      rcases hxCarrier with (hxBase | hxInitial) | hxFinal
      · exact False.elim (hxNotX hxBase.2)
      · exact False.elim (hxInitial.2 hxY)
      · exact False.elim (hxFinal.2 hxYVertex)
    · exact Or.inl ⟨⟨x, hxOutsideInitial, hxY⟩, rfl⟩
  · exact Or.inr (hrowTerminal hxRowTerminal)

/-- After adding the finite macro shortcuts, every sink of the local
relation lies on the later frontier.  Infinite selected routes cannot occur
because the reference is a subwarp of the later row. -/
theorem macroFullSinkBoundary
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hYclosed : ClosedUnderPaths Gamma Y X)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    (hclosed : ClosedUnderPaths Gamma W X)
    {target : Set V} (hrowTerminal : Gamma.terminalFrontier W ⊆ target) :
    {x | x ∈ I.insideFamily.vertexSet ∧
      ¬ ∃ y, (x, y) ∈ I.insideFamily.edgeSet ∪
        assignedFiniteEdges
          (Zf := FracturedWarp.ofWarp (outsideReference W X)
            (outsideReference_isWarp hW)) A.assignment} ⊆ target := by
  intro x hx
  have hxInsideTerminal : x ∈ I.insideFamily.terminalSet := by
    rw [I.insideFamily.terminalSet_eq_no_outgoing]
    exact ⟨hx.1, fun ⟨y, hxy⟩ ↦ hx.2 ⟨y, Or.inl hxy⟩⟩
  rcases I.macroTerminalBoundary hW hWfinite hclosed hrowTerminal
      hxInsideTerminal with hxSource | hxTarget
  · obtain ⟨s, hsx⟩ := hxSource
    subst x
    rcases A.assignment.maximal s with hinfinite | ⟨v, _hv, hterm⟩
    · exact False.elim
        (A.assigned_not_infinite hW hYclosed hsub s hinfinite)
    · exact False.elim <| hx.2 ⟨v, Or.inr ⟨s, hterm, rfl⟩⟩
  · exact hxTarget

/-- Every edge of the local macro relation has both endpoints on one member
of the honest later row.  For a compressed edge this is the unique outside
row member at its source. -/
theorem macroFullEdge_has_rowOwner
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    {x y : V}
    (hxy : (x, y) ∈ I.insideFamily.edgeSet ∪
      assignedFiniteEdges
        (Zf := FracturedWarp.ofWarp (outsideReference W X)
          (outsideReference_isWarp hW)) A.assignment) :
    ∃ p : Gamma.DPath, p ∈ W ∧ x ∈ p.support ∧ y ∈ p.support := by
  rcases hxy with hxyInside | hxyAssigned
  · rw [I.edgeSet_eq] at hxyInside
    have hxyW := hxyInside.1
    simp only [familyEdges, Set.mem_iUnion] at hxyW
    obtain ⟨p, hpW, hxyp⟩ := hxyW
    have hend := p.edgeSet_subset_support_prod hxyp
    exact ⟨p, hpW, hend.1, hend.2⟩
  · rcases hxyAssigned with ⟨s, hterminal, rfl⟩
    let p : outsideReference W X :=
      initialPath (outsideReference W X) ⟨s.1, s.property.1⟩
    have hpterminal := A.assigned_terminal_initialPath hW hsub s hterminal
    have hySupport : _ ∈ p.1.support :=
      Gamma.terminal_mem_support hpterminal
    refine ⟨p.1, p.2.1, ?_, hySupport⟩
    have hpInitial := p.1.initial_mem_support
    simpa only [p, initialPath_initial] using hpInitial

/-- Finite character of the honest later row excludes a forward ray even
after every outside member is compressed to one macro edge.  A hypothetical
ray would remain on a single finite row member. -/
theorem macroFullRelation_noDirectedRay
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference Y X ⊆ outsideReference W X) :
    ¬ ContainsDirectedRay
      (I.insideFamily.edgeSet ∪
        assignedFiniteEdges
          (Zf := FracturedWarp.ofWarp (outsideReference W X)
            (outsideReference_isWarp hW)) A.assignment) := by
  rintro ⟨R, hR⟩
  obtain ⟨p, hpW, hp0, _hp1⟩ :=
    I.macroFullEdge_has_rowOwner A hW hsub (hR ⟨0, rfl⟩)
  have hall : ∀ n : ℕ, R.vertex n ∈ p.support := by
    intro n
    induction n with
    | zero => exact hp0
    | succ n ih =>
        obtain ⟨q, hqW, hqn, hqnext⟩ :=
          I.macroFullEdge_has_rowOwner A hW hsub (hR ⟨n, rfl⟩)
        have hpq : p = q :=
          DWeb.IsWarp.eq_of_mem_support hW hpW hqW ih hqn
        exact hpq ▸ hqnext
  obtain ⟨pf, rfl⟩ := hWfinite hpW
  exact pf.support_finite.not_infinite
    (Set.infinite_of_injective_forall_mem R.injective hall)

/-- The strong-ray obligation of `ClubStageUnionData` is therefore
vacuous for the finite-character macro survivor relation. -/
theorem macroEveryRelationRayStrong
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference Y X ⊆ outsideReference W X) :
    ∀ r : Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆
          I.insideFamily.edgeSet ∪
            assignedFiniteEdges
              (Zf := FracturedWarp.ofWarp (outsideReference W X)
                (outsideReference_isWarp hW)) A.assignment →
        (strongEdgeIndices r).Infinite := by
  intro r hr
  exfalso
  apply I.macroFullRelation_noDirectedRay A hW hWfinite hsub
  let R : DirectedRay V := {
    vertex := r.toFun
    injective := r.injective }
  refine ⟨R, ?_⟩
  rintro e ⟨n, rfl⟩
  exact hr ⟨n, rfl⟩

/-- An outside reference component is disjoint from the canonical inside
carrier.  The only nontrivial case is an uncovered cut root; its honest row
owner meets the reference component and hence is the same path, contradicting
that the root was declared uncovered. -/
theorem outsideReference_vertexSet_disjoint_insideFamily
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hclosed : ClosedUnderPaths Gamma W X)
    (hsub : outsideReference Y X ⊆ outsideReference W X) :
    Disjoint (Gamma.vertexSet (outsideReference Y X))
      I.insideFamily.vertexSet := by
  rw [Set.disjoint_left]
  intro x hxReference hxInside
  rw [I.vertexSet_eq] at hxInside
  rcases hxInside with (hxBase | hxInitial) | hxTerminal
  · obtain ⟨p, hp, hxp⟩ := hxReference
    exact Set.disjoint_left.1 hp.2 hxp hxBase.2
  · have hxOutsideInitial :
        x ∈ Gamma.initialSet (outsideReference W X) := by
      rw [← cutInitial_eq_initialSet_outsideReference hW hWfinite hclosed]
      exact hxInitial.1
    obtain ⟨p, hpY, hxp⟩ := hxReference
    obtain ⟨q, hqW, hqinitial⟩ := hxOutsideInitial
    have hpq : p = q :=
      DWeb.IsWarp.eq_of_mem_support hW (hsub hpY).1 hqW.1
        hxp (hqinitial ▸ q.initial_mem_support)
    apply hxInitial.2
    refine ⟨p, hpY.1, ?_⟩
    exact (congrArg Path.initial hpq).trans hqinitial
  · exact hxTerminal.2 (vertexSet_outsideReference_subset hxReference)

/-- The honest later linkage and the untouched outside reference cover the
ambient source exactly in the one-sided form required by stage data. -/
theorem macroCoversSource
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hclosed : ClosedUnderPaths Gamma W X)
    (hYclosed : ClosedUnderPaths Gamma Y X)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    {source target : Set V}
    (hinitial : Gamma.initialSet W = source)
    (hterminal : Gamma.terminalFrontier W ⊆ target) :
    source ⊆ I.insideFamily.initialSet ∪
      Gamma.initialSet
        (referencePathsMeeting Y target \
          referencePathsMeeting Y I.insideFamily.vertexSet) := by
  intro x hxSource
  have hxInitialW : x ∈ Gamma.initialSet W := hinitial.symm ▸ hxSource
  obtain ⟨p, hpW, hpinitial⟩ := hxInitialW
  by_cases hpMeets : (p.support ∩ X).Nonempty
  · have hpX : p.support ⊆ X := hclosed p hpW hpMeets
    apply Or.inl
    rw [I.insideFamily.initialSet_eq_no_incoming, I.vertexSet_eq]
    refine ⟨Or.inl (Or.inl
      ⟨⟨p, hpW, hpinitial ▸ p.initial_mem_support⟩,
        hpX (hpinitial ▸ p.initial_mem_support)⟩), ?_⟩
    rintro ⟨y, hyx⟩
    rw [I.edgeSet_eq] at hyx
    have hxInitialW' : x ∈ Gamma.initialSet W := ⟨p, hpW, hpinitial⟩
    rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfinite]
        at hxInitialW'
    exact hxInitialW'.2 ⟨y, hyx.1⟩
  · have hpDisjoint : Disjoint p.support X := by
      rw [Set.disjoint_left]
      exact fun z hzp hzX ↦ hpMeets ⟨z, hzp, hzX⟩
    by_cases hxY : x ∈ Gamma.initialSet Y
    · obtain ⟨q, hqY, hqinitial⟩ := hxY
      have hxNotX : x ∉ X := by
        exact Set.disjoint_left.1 hpDisjoint
          (hpinitial ▸ p.initial_mem_support)
      have hqDisjoint : Disjoint q.support X := by
        rw [Set.disjoint_left]
        intro z hzq hzX
        have hqX : q.support ⊆ X := hYclosed q hqY ⟨z, hzq, hzX⟩
        exact hxNotX (hqX (hqinitial ▸ q.initial_mem_support))
      have hpq : p = q :=
        DWeb.IsWarp.eq_of_mem_support hW hpW
          (hsub ⟨hqY, hqDisjoint⟩).1
          (hpinitial ▸ p.initial_mem_support)
          (hqinitial ▸ q.initial_mem_support)
      subst q
      apply Or.inr
      refine ⟨p, ⟨⟨hqY, ?_⟩, ?_⟩, hpinitial⟩
      · obtain ⟨pf, rfl⟩ := hWfinite hpW
        exact ⟨pf.finish, pf.finish_mem_support,
          hterminal ⟨Sum.inl pf, hpW, rfl⟩⟩
      · intro hpMeetsInside
        obtain ⟨_, z, hzp, hzInside⟩ := hpMeetsInside
        exact Set.disjoint_left.1
          (I.outsideReference_vertexSet_disjoint_insideFamily hW hWfinite
            hclosed hsub)
          ⟨p, ⟨hqY, hpDisjoint⟩, hzp⟩ hzInside
    · apply Or.inl
      rw [I.insideFamily.initialSet_eq_no_incoming, I.vertexSet_eq]
      have hxOutsideInitial :
          x ∈ Gamma.initialSet (outsideReference W X) :=
        ⟨p, ⟨hpW, hpDisjoint⟩, hpinitial⟩
      have hxCut : x ∈ CutSplit.initialVertices (outsideCarrier W X)
          (outsideFamilyEdges W X) X := by
        rw [cutInitial_eq_initialSet_outsideReference hW hWfinite hclosed]
        exact hxOutsideInitial
      refine ⟨Or.inl (Or.inr ⟨hxCut, hxY⟩), ?_⟩
      rintro ⟨y, hyx⟩
      rw [I.edgeSet_eq] at hyx
      exact Set.disjoint_left.1 hpDisjoint
        (hpinitial ▸ p.initial_mem_support) hyx.2.2

/-- Every inside edge strictly advances the honest later-row rank. -/
theorem inside_rank_laterRowRank
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (hW : Gamma.IsWarp W) {x y : V}
    (hxy : (x, y) ∈ I.insideFamily.edgeSet) :
    laterRowRank W hW x < laterRowRank W hW y := by
  apply laterRowRank_lt_of_mem_familyEdges hW
  rw [I.edgeSet_eq] at hxy
  exact hxy.1

/-- A nontriviality certificate for the row member owned by every finite
assigned source.  This is supplied by an actual linkage between disjoint
endpoint sides (or directly by its endpoint-purity theorem). -/
def AssignedRowPathsNontrivial
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X)) : Prop :=
  ∀ s : {z // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet Y},
    ∀ v, (A.assignment.assigned s).terminal? = some v → s.1 ≠ v

/-- The endpoint geometry of an actual ladder stage supplies the required
nontriviality: an uncovered row source is in the strict roof of the later
frontier, whereas every finite row terminal lies on that frontier.  Since
ladder frontiers are essential, the two regions are disjoint. -/
theorem assignedRowPathsNontrivial_of_endpointLocations
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    {before target : Set V}
    (hsource : Gamma.initialSet W \ Gamma.initialSet Y ⊆
      before ∩ Gamma.strictRoof target)
    (hterminal : Gamma.terminalFrontier W ⊆ target)
    (hessential : Gamma.essential target = target) :
    AssignedRowPathsNontrivial A := by
  intro s v hterm heq
  have hsStrict : s.1 ∈ Gamma.strictRoof target :=
    (hsource ⟨initialSet_outsideReference_subset s.property.1,
      s.property.2⟩).2
  have hvTarget : v ∈ target :=
    hterminal (terminalFrontier_outsideReference_subset
      (A.assignment.finite_terminal_mem s hterm).1)
  have hvEssential : v ∈ Gamma.essential target :=
    hessential.symm ▸ hvTarget
  have hdisjoint := Set.disjoint_left.1
    (Gamma.disjoint_strictRoof_essential target)
  exact hdisjoint hsStrict (heq ▸ hvEssential)

/-- Club-stage specialization of
`assignedRowPathsNontrivial_of_endpointLocations`. -/
theorem assignedRowPathsNontrivial_of_clubStage
    {theta : Cardinal.{u}} (C : ClubStageGeometry Gamma Y kappa theta)
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hsource : Gamma.initialSet W \ Gamma.initialSet Y ⊆
      C.before ∩ C.innerRoof)
    (hterminal : Gamma.terminalFrontier W ⊆ C.newSlice) :
    AssignedRowPathsNontrivial A := by
  exact assignedRowPathsNontrivial_of_endpointLocations A hsource
    hterminal (C.legal.frontiersEssential C.newStage)

/-- A source vertex which is already an initial of the complementary inside
family cannot be the target of a compressed macro edge.  Indeed, its row
member and the outside row member owned by that macro edge meet at the
vertex, hence are equal by warp disjointness.  Their common initial would
then equal the macro target, contradicting row nontriviality. -/
theorem macroCoveredInitial_not_assignedTarget
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    {source : Set V} (hinitial : Gamma.initialSet W = source)
    (hnontrivial : AssignedRowPathsNontrivial A) :
    source ∩ I.insideFamily.initialSet ⊆
      {x | ¬ ∃ y, (y, x) ∈ assignedFiniteEdges
        (Zf := FracturedWarp.ofWarp (outsideReference W X)
          (outsideReference_isWarp hW)) A.assignment} := by
  rintro x ⟨hxSource, _hxInsideInitial⟩ ⟨y, hyx⟩
  obtain ⟨s, hterminal, _hsy⟩ := hyx
  obtain ⟨p, hpW, hpinitial⟩ : x ∈ Gamma.initialSet W :=
    hinitial.symm ▸ hxSource
  let q : outsideReference W X :=
    initialPath (outsideReference W X) ⟨s.1, s.property.1⟩
  have hqterminal : Gamma.terminal? q.1 = some x :=
    A.assigned_terminal_initialPath hW hsub s hterminal
  have hpq : p = q.1 :=
    DWeb.IsWarp.eq_of_mem_support hW hpW q.2.1
      (hpinitial ▸ p.initial_mem_support)
      (Gamma.terminal_mem_support hqterminal)
  apply hnontrivial s x hterminal
  calc
    s.1 = q.1.initial := by
      simpa only [q] using
        (initialPath_initial (outsideReference W X)
          ⟨s.1, s.property.1⟩).symm
    _ = p.initial := congrArg Path.initial hpq.symm
    _ = x := hpinitial

/-- Compressed finite assignment edges also strictly advance the same row
rank; this is the key global chronology fact. -/
theorem assigned_rank_laterRowRank
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    (hnontrivial : AssignedRowPathsNontrivial A)
    {x y : V}
    (hxy : (x, y) ∈ assignedFiniteEdges
      (Zf := FracturedWarp.ofWarp (outsideReference W X)
        (outsideReference_isWarp hW)) A.assignment) :
    laterRowRank W hW x < laterRowRank W hW y := by
  rcases hxy with ⟨s, hterminal, rfl⟩
  let p : outsideReference W X :=
    initialPath (outsideReference W X) ⟨s.1, s.property.1⟩
  obtain ⟨q, hpq⟩ := hWfinite p.2.1
  have hqterminal : q.finish = y := by
    have hpterminal := A.assigned_terminal_initialPath hW hsub s hterminal
    rw [hpq] at hpterminal
    exact Option.some.inj hpterminal
  have hpinitial : p.1.initial = s.1 := initialPath_initial _ _
  have hne : q.start ≠ q.finish := by
    intro h
    apply hnontrivial s y hterminal
    calc
      s.1 = p.1.initial := hpinitial.symm
      _ = q.start := congrArg Path.initial hpq
      _ = q.finish := h
      _ = y := hqterminal
  have hrank := laterRowRank_initial_lt_terminal hW p.2.1 hpq hne
  simpa only [hpinitial, hqterminal] using hrank

/-- Hence the actual inside-plus-compressed relation has no directed
cycle. -/
theorem insideAssigned_acyclic
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    (hnontrivial : AssignedRowPathsNontrivial A) :
    ¬ ContainsDirectedCycle
      (I.insideFamily.edgeSet ∪ assignedFiniteEdges
        (Zf := FracturedWarp.ofWarp (outsideReference W X)
          (outsideReference_isWarp hW)) A.assignment) := by
  apply not_containsDirectedCycle_of_rank _ (laterRowRank W hW)
  intro x y hxy
  rcases hxy with hxy | hxy
  · exact I.inside_rank_laterRowRank hW hxy
  · exact assigned_rank_laterRowRank A hW hWfinite hsub
      hnontrivial hxy

/-- The same chronology rules out a reverse directed ray. -/
theorem insideAssigned_no_reverse_ray
    (I : CanonicalInsideCut (Y := Y) (kappa := kappa) W X)
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    (hnontrivial : AssignedRowPathsNontrivial A) :
    ¬ ContainsReverseDirectedRay
      (I.insideFamily.edgeSet ∪ assignedFiniteEdges
        (Zf := FracturedWarp.ofWarp (outsideReference W X)
          (outsideReference_isWarp hW)) A.assignment) := by
  apply not_containsReverseDirectedRay_of_rank _ (laterRowRank W hW)
  intro x y hxy
  rcases hxy with hxy | hxy
  · exact I.inside_rank_laterRowRank hW hxy
  · exact assigned_rank_laterRowRank A hW hWfinite hsub
      hnontrivial hxy

end CanonicalInsideCut

end LinkageBlueprint
end Blueprint
end Erdos599
