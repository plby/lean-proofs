/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClause

/-!
# The honest replacement interface for Assertion 9.30

The published proof of Assertion 9.30 chooses a member `Q` of a large
hammock, forms the formal switch `Y △ Q`, and splices that switched family
into the current blueprint.  Literal source safeness of `Q` does not imply
that the formal switch is a warp: an unrecorded forward contact with a
reference path can create a branching vertex.  Consequently this file never
turns `IsSafe Y Q` into `IsSwitchingSafe Y Q`.

Instead, the two nontrivial branches below consume an explicit *coupled
family replacement*.  Its fields are the concrete output obligations of a
global replacement construction: the cut is correct, an actual real path
reaches a fresh terminal in the slice, other real terminals survive, and all
old vertices satisfy the exact real-extension accounting relation (9.32).
The hammock member remains an input to the branch compiler, so a later
construction can use its endpoint and avoidance data, but no switching
conclusion is inferred from its literal safeness.

The final theorem performs all sound work which is independent of that
global construction.  It bounds the current blueprint's vertex set, selects
an avoiding member of the appropriate large hammock, handles the identity
branch, and packages either coupled replacement as the exact
`Continuation930Compiler` used by the terminal scheduler.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u}

namespace LinkageBlueprint

variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- A blueprint with at most `kappa` paths has at most `kappa` vertices
when `kappa` is infinite.  Every finite path and every ray has countable
support. -/
theorem mk_vertexSet_le_of_mk_paths_le
    (W : LinkageBlueprint Gamma Y kappa)
    (hkappa : aleph0 <= kappa) (hpaths : #W.paths <= kappa) :
    #W.vertexSet <= kappa := by
  by_cases hnonempty : W.paths.Nonempty
  · let : Nonempty W.paths := hnonempty.to_subtype
    have heq : W.vertexSet = ⋃ p : W.paths, p.1.support := by
      ext x
      simp only [LinkageBlueprint.vertexSet, DWeb.vertexSet,
        Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨p, hp, hxp⟩
        exact ⟨⟨p, hp⟩, hxp⟩
      · rintro ⟨p, hxp⟩
        exact ⟨p.1, p.2, hxp⟩
    rw [heq]
    refine (Cardinal.mk_iUnion_le (fun p : W.paths => p.1.support)).trans ?_
    apply Cardinal.mul_le_of_le hkappa hpaths
    apply ciSup_le
    intro p
    exact p.1.support_countable.le_aleph0.trans hkappa
  · have hempty : W.paths = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
    have hvertices : W.vertexSet = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨p, hp, _hxp⟩
      rw [hempty] at hp
      exact hp
    rw [hvertices]
    simp

/-- The edge-producing alternative for a terminal of the real part, with
the represented blueprint edge retained.  The older convenience theorem
only returned its imaginary-edge predicate, which is not enough to build
the exact cut `W^u`. -/
theorem real_terminal_is_terminal_or_has_imaginary_edge_mem
    {W : LinkageBlueprint Gamma Y kappa} {u : V}
    (hu : u ∈ W.realPart.terminals) :
    u ∈ W.terminalSet ∨
      ∃ v, (u, v) ∈ W.edgeSet ∧ IsImaginaryEdge Gamma Y kappa u v := by
  by_cases hut : u ∈ W.terminalSet
  · exact Or.inl hut
  · right
    obtain ⟨v, huv⟩ :=
      W.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet hu.1 hut
    refine ⟨v, huv, ?_⟩
    have hadj : (imaginaryGraph Gamma Y kappa).Adj u v := by
      rcases Set.mem_iUnion.1 huv with ⟨p, huv⟩
      rcases Set.mem_iUnion.1 huv with ⟨hpW, hpedge⟩
      exact p.edgeSet_subset_adj hpedge
    rcases hadj with horiginal | himaginary
    · exact False.elim <| hu.2
        ⟨v, W.mem_realPart_of_mem_edgeSet_of_original huv horiginal⟩
    · exact himaginary

/-- Low-level output of one genuinely coupled hammock replacement.

Unlike `Continuation930`, the two reachability clauses are represented by
one concrete original-graph path.  The last two fields expose Definition
(9.32) rather than hiding it behind an alleged safe switch.  This is the
interface that a global family-replacement construction must produce. -/
structure CoupledHammockReplacement
    (W cut U : LinkageBlueprint Gamma Y kappa)
    (u z : V) (T : Set V) where
  isCutAt : W.IsCutAt cut u
  ordinaryExtends : cut.OrdinaryExtends U
  path : FinitePath Gamma.graph
  path_start : path.start = u
  path_finish : path.finish = z
  path_vertices : path.support ⊆ U.realPart.vertices
  path_edges : path.edgeSet ⊆ U.realPart.edges
  endpoint_mem_slice : z ∈ T
  endpoint_terminal : z ∈ U.terminalSet
  preserves_other_terminals :
    W.realPart.terminals \ {u} ⊆ U.realPart.terminals
  endpoint_fresh : z ∉ W.realPart.terminals \ {u}
  real_part_extends : W.realPart.Extends U.realPart
  old_vertices_accounted :
    W.vertexSet ⊆
      (U.terminalSet ∩ W.terminalSet) ∪
        {x | ∃ y, (x, y) ∈ W.familyGraph.edges ∩ U.familyGraph.edges} ∪
          U.completedRealVertices {z}

/-- A coupled family replacement gives the endpoint-explicit 9.30 object
consumed by the 9.34 composition theorem. -/
theorem CoupledHammockReplacement.continuation930
    {W cut U : LinkageBlueprint Gamma Y kappa}
    {u z : V} {T B : Set V}
    (R : CoupledHammockReplacement W cut U u z T) :
    Continuation930 W cut U u z T B := by
  have hlinksZ : U.RealLinksTo u {z} := by
    exact ⟨R.path, R.path_start, by simpa [R.path_finish],
      R.path_vertices, R.path_edges⟩
  have hlinksT : U.RealLinksTo u T := by
    exact ⟨R.path, R.path_start, R.path_finish.symm ▸ R.endpoint_mem_slice,
      R.path_vertices, R.path_edges⟩
  exact {
    conclusion := ⟨R.isCutAt, R.ordinaryExtends, hlinksT,
      R.preserves_other_terminals⟩
    links_to_endpoint := hlinksZ
    endpoint_mem_slice := R.endpoint_mem_slice
    endpoint_terminal := R.endpoint_terminal
    preserves_other_terminals := R.preserves_other_terminals
    endpoint_fresh := R.endpoint_fresh
    real_extends_to_endpoint :=
      ⟨R.real_part_extends, R.old_vertices_accounted⟩ }

/-- Constructible terminal-outside-slice branch.  The selected member of
the infinity hammock is supplied with its literal safeness and exact
avoidance certificate.  The conclusion is required to come from a coupled
family replacement; no switchability of `Q` is assumed or inferred. -/
def TerminalOutsideHammockReplacementCompiler
    (T Z persistent : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V)
      (Q : AltPath Gamma.graph),
    W.IsLinkageBlueprint T Z persistent →
      persistent ⊆ T →
      u ∈ W.realPart.terminals →
      u ∈ W.terminalSet → u ∉ T →
      IsSafe Y Q → Q.initial = u → Q.IsInfinite →
      Disjoint (Q.vertexSet \ {u}) W.vertexSet →
      ∃ (U : LinkageBlueprint Gamma Y kappa) (z : V),
        Nonempty (CoupledHammockReplacement W W U u z T)

/-- Constructible imaginary-successor branch.  A global replacement is
allowed to cut and replace a whole coupled family at once; in particular it
need not realize `Y △ Q` as an exact symmetric-difference warp. -/
def ImaginarySuccessorHammockReplacementCompiler
    (T Z persistent : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u v : V)
      (Q : AltPath Gamma.graph),
    W.IsLinkageBlueprint T Z persistent →
      persistent ⊆ T →
      u ∈ W.realPart.terminals →
      (u, v) ∈ W.edgeSet →
      IsImaginaryEdge Gamma Y kappa u v →
      IsSafe Y Q → Q.initial = u → HasEnd Q (.vertex v) →
      Disjoint (hammockInterior u (.vertex v) Q) W.vertexSet →
      ∃ (cut U : LinkageBlueprint Gamma Y kappa) (z : V),
        W.IsImaginaryEdgeDeletionAt cut u v ∧
          Nonempty (CoupledHammockReplacement W cut U u z T)

/-- Honest assembly of Assertion 9.30 from the two coupled replacement
branches.

All uses of the large hammocks below are legitimate cardinal selections of
literal safe paths.  The only place where those paths are converted into a
new blueprint is through the two explicit compiler hypotheses above. -/
theorem continuation930Compiler_of_coupledHammockReplacement
    {T Z persistent B : Set V}
    (hkappa : aleph0 <= kappa)
    (hterminal : TerminalOutsideHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (himaginary : ImaginarySuccessorHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent) :
    Continuation930Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B := by
  intro W u hW hpersistent hu _huScheduled
  have hWvertices : #W.vertexSet <= kappa :=
    W.mk_vertexSet_le_of_mk_paths_le hkappa hW.card_paths
  rcases real_terminal_is_terminal_or_has_imaginary_edge_mem hu with
      huterm | ⟨v, huv, himag⟩
  · by_cases huT : u ∈ T
    · exact ⟨W, W, u,
        continuation930_of_terminal_mem_slice hu huterm huT⟩
    · have hhammock :
          HasHammockCard Gamma Y u .infinity (succ kappa) :=
        terminal_outside_slice_has_infinite_hammock hW hpersistent huterm huT
      obtain ⟨Q, hQsafe, hQinitial, hQinfinite, hQdisjoint⟩ :=
        exists_safe_infinite_hammock_path_avoiding hhammock hWvertices
      obtain ⟨U, z, ⟨hreplacement⟩⟩ :=
        hterminal W u Q hW hpersistent hu huterm huT hQsafe hQinitial
          hQinfinite hQdisjoint
      exact ⟨W, U, z, hreplacement.continuation930⟩
  · obtain ⟨Q, hQsafe, hQinitial, hQend, hQdisjoint⟩ :=
      exists_hammock_path_disjoint_of_mk_le himag hWvertices
    obtain ⟨cut, U, z, hcut, ⟨hreplacement⟩⟩ :=
      himaginary W u v Q hW hpersistent hu huv himag hQsafe hQinitial
        hQend hQdisjoint
    exact ⟨cut, U, z, hreplacement.continuation930⟩

/-- The repaired 9.30 construction, together with any source-faithful 9.31
compiler, gives the stable successor required by Assertion 9.34.

This is the scheduler-facing form of the honest replacement interface.  The
extra hypotheses are exactly the data which the old high-level API lacked:
the current slice contains the persistent vertices (passed by
`Stable934Compiler` itself), and both non-identity branches construct a
coupled family replacement.  In particular, this theorem does not infer a
warp switch from literal safeness of a hammock member. -/
theorem stable934Compiler_of_coupledHammockReplacement
    {T Z persistent B : Set V}
    (hkappa : aleph0 <= kappa)
    (hterminal : TerminalOutsideHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (himaginary : ImaginarySuccessorHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (hadvance : Advance931Compiler
      (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent B) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B :=
  stable934Compiler_of_930_931
    (continuation930Compiler_of_coupledHammockReplacement
      hkappa hterminal himaginary)
    hadvance

end LinkageBlueprint
end Blueprint
end Erdos599
