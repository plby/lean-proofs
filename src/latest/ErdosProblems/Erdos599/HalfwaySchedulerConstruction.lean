/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RealExtensionRelationLimit
import ErdosProblems.Erdos599.GlobalAdvance931
import Mathlib.Data.Prod.Lex

/-!
# The terminal scheduler for the half-way clause

This file isolates the genuinely constructive part of the terminal recursion
after Assertions 9.30--9.31 have supplied a `Stable934Compiler`.

A scheduler state remembers the terminals already linked to the target.  A
9.34 successor adds one currently real terminal and transports every earlier
link through the inclusion of real parts.  The total step is the identity
when the requested vertex is not currently a terminal.  Consequently finite
request lists can be executed without any additional hypothesis.

The transfinite limit remains a separate record.  This separation is
essential: the current `LinkageBlueprint.limit` theorem assumes literal
monotonicity of whole path values, whereas 9.34 supplies only `RealExtends`.
`FairResolutionLimit` states exactly the sound 9.33/fairness output needed by
the already proved terminal finalization theorem, while retaining the
transfinite provenance that every stage absorbs the scheduler seed.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {T Z persistent B : Set V}

/-- A state of the terminal-resolution recursion.  `linked` contains the
requests already discharged, and `links` is deliberately phrased in the
current blueprint so it transports through every later real extension. -/
structure TerminalResolutionState
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (T Z persistent B : Set V) where
  blueprint : LinkageBlueprint Gamma Y kappa
  isBlueprint : blueprint.IsLinkageBlueprint T Z persistent
  stable : blueprint.Stable T persistent
  linked : Set V
  links : ∀ x ∈ linked, blueprint.RealLinksTo x B

namespace TerminalResolutionState

/-! ### Algebra of real extensions -/

/-- The accounting relation (9.32) is transitive.  The only non-formal case
is when an old common edge is compared with the edge retained by the second
extension: right-uniqueness in the intermediate blueprint identifies their
heads.  Completed real paths transport by monotonicity of the real parts. -/
@[trans] theorem realExtends_trans
    {W U R : LinkageBlueprint Gamma Y kappa}
    (hWU : W.RealExtends U B) (hUR : U.RealExtends R B) :
    W.RealExtends R B := by
  refine ⟨FamilyGraph.extends_trans hWU.1 hUR.1, ?_⟩
  intro x hxW
  rcases hWU.2 hxW with (hxterm | hxedge) | hxcompleted
  · rcases hUR.2 (hWU.vertices_mono hxW) with
      (hxterm' | hxedge') | hxcompleted'
    · exact Or.inl (Or.inl ⟨hxterm'.1, hxterm.2⟩)
    · rcases hxedge' with ⟨y, hxyU, _hxyR⟩
      exact False.elim <|
        (mem_familyGraph_terminals_of_mem_terminalSet hxterm.1).2 ⟨y, hxyU⟩
    · exact Or.inr hxcompleted'
  · rcases hxedge with ⟨y, hxyW, hxyU⟩
    rcases hUR.2 (hWU.vertices_mono hxW) with
      (hxterm | hxedge') | hxcompleted
    · exact False.elim <|
        (mem_familyGraph_terminals_of_mem_terminalSet hxterm.2).2 ⟨y, hxyU⟩
    · rcases hxedge' with ⟨z, hxzU, hxzR⟩
      have hyz : y = z :=
        Alternating.IsWarp.familyEdges_rightUnique U.isWarp hxyU hxzU
      exact Or.inl (Or.inr ⟨y, hxyW, hyz ▸ hxzR⟩)
    · exact Or.inr hxcompleted
  · exact Or.inr <| completedRealVertices_mono hUR.1 hxcompleted

/-! ### A canonical cofinal request enumeration -/

/-- Repeat a linearly ordered request type in countably many lexicographic
blocks.  The next block revisits every request after every given stage, so a
terminal which appears late in one block is not missed permanently. -/
abbrev RepeatedRequestIndex (X : Type u) [LinearOrder X] := ℕ ×ₗ X

/-- The request named at a repeated lexicographic index. -/
def repeatedRequest {X : Type u} [LinearOrder X] :
    RepeatedRequestIndex X → X :=
  fun i ↦ (ofLex i).2

/-- Every request is named again at or after every stage.  This is the pure
enumeration part of scheduler fairness; the successor/limit recursion only
has to prove that successful requests are represented in its state chain. -/
theorem exists_later_repeatedRequest {X : Type u} [LinearOrder X]
    (i : RepeatedRequestIndex X) (x : X) :
    ∃ j, i ≤ j ∧ repeatedRequest j = x := by
  let j : RepeatedRequestIndex X := toLex ((ofLex i).1 + 1, x)
  refine ⟨j, ?_, rfl⟩
  exact le_of_lt (Prod.Lex.left _ _ (Nat.lt_succ_self (ofLex i).1))

/-- Repeating a request type of cardinality at most `kappa` still uses at
most `kappa` stages when `kappa` is infinite. -/
theorem mk_repeatedRequestIndex_le {X : Type u} [LinearOrder X]
    (hkappa : aleph0 ≤ kappa) (hX : #X ≤ kappa) :
    #(RepeatedRequestIndex X) ≤ kappa := by
  change #(ℕ × X) ≤ kappa
  rw [Cardinal.mk_prod, Cardinal.mk_nat]
  simp only [Cardinal.lift_aleph0]
  simpa only [Cardinal.lift_id'] using
    Cardinal.mul_le_of_le hkappa hkappa hX

/-- Start tracking an already constructed stable blueprint. -/
def initial (W : LinkageBlueprint Gamma Y kappa)
    (hW : W.IsLinkageBlueprint T Z persistent)
    (hstable : W.Stable T persistent) :
    TerminalResolutionState Gamma Y kappa T Z persistent B where
  blueprint := W
  isBlueprint := hW
  stable := hstable
  linked := ∅
  links := by simp

/-- The blueprint chosen by 9.34 for one currently real terminal. -/
noncomputable def advanceBlueprint
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    LinkageBlueprint Gamma Y kappa :=
  Classical.choose
    (compiler S.blueprint u S.isBlueprint hpersistent hu huT)

theorem advanceBlueprint_spec
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    StableExtensionConclusion S.blueprint
      (advanceBlueprint compiler hpersistent S u hu huT)
      u T Z persistent B :=
  Classical.choose_spec
    (compiler S.blueprint u S.isBlueprint hpersistent hu huT)

/-- Execute one genuine terminal request. -/
noncomputable def advance
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    TerminalResolutionState Gamma Y kappa T Z persistent B where
  blueprint := advanceBlueprint compiler hpersistent S u hu huT
  isBlueprint :=
    (advanceBlueprint_spec compiler hpersistent S u hu huT).isLinkageBlueprint
  stable := (advanceBlueprint_spec compiler hpersistent S u hu huT).stable
  linked := insert u S.linked
  links := by
    intro x hx
    rcases hx with hx | hx
    · subst x
      exact (advanceBlueprint_spec compiler hpersistent S u hu huT).links
    · exact realLinksTo_mono
        (advanceBlueprint_spec compiler hpersistent S u hu huT).realExtends.1
        (S.links x hx)

@[simp] theorem linked_advance
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    (S.advance compiler hpersistent u hu huT).linked = insert u S.linked :=
  rfl

theorem realPart_extends_advance
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    S.blueprint.realPart.Extends
      (S.advance compiler hpersistent u hu huT).blueprint.realPart :=
  (advanceBlueprint_spec compiler hpersistent S u hu huT).realExtends.1

theorem links_advance_request
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    (S.advance compiler hpersistent u hu huT).blueprint.RealLinksTo u B :=
  (advanceBlueprint_spec compiler hpersistent S u hu huT).links

/-! ### Forward-only successors for transfinite relation limits -/

/-- The result selected from the predecessor-preserving form of Assertion
9.34. -/
noncomputable def predecessorAdvanceBlueprint
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    LinkageBlueprint Gamma Y kappa :=
  Classical.choose
    (compiler S.blueprint u S.isBlueprint hpersistent hu huT)

theorem predecessorAdvanceBlueprint_spec
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    PredecessorPreservingStable934 S.blueprint
      (predecessorAdvanceBlueprint compiler hpersistent S u hu huT)
      u T Z persistent B :=
  Classical.choose_spec
    (compiler S.blueprint u S.isBlueprint hpersistent hu huT)

/-- Execute one genuine terminal request while retaining the local invariant
needed by the relation limit. -/
noncomputable def predecessorAdvance
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    TerminalResolutionState Gamma Y kappa T Z persistent B where
  blueprint := predecessorAdvanceBlueprint compiler hpersistent S u hu huT
  isBlueprint :=
    (predecessorAdvanceBlueprint_spec compiler hpersistent S u hu huT)
      |>.conclusion.1
  stable :=
    (predecessorAdvanceBlueprint_spec compiler hpersistent S u hu huT)
      |>.conclusion.2.1
  linked := insert u S.linked
  links := by
    intro x hx
    rcases hx with hx | hx
    · subst x
      exact (predecessorAdvanceBlueprint_spec compiler hpersistent S u hu huT)
        |>.conclusion.links
    · exact realLinksTo_mono
        ((predecessorAdvanceBlueprint_spec compiler hpersistent S u hu huT)
          |>.conclusion.realExtends.1)
        (S.links x hx)

theorem noNewRealPredecessors_predecessorAdvance
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    S.blueprint.NoNewRealPredecessorsTo
      (S.predecessorAdvance compiler hpersistent u hu huT).blueprint :=
  (predecessorAdvanceBlueprint_spec compiler hpersistent S u hu huT)
    |>.no_new_real_predecessors

/-- Total forward-only scheduler step.  A nonterminal request is an identity
transition; a terminal request uses the strengthened 9.34 compiler. -/
noncomputable def predecessorStep
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) : TerminalResolutionState Gamma Y kappa T Z persistent B := by
  classical
  exact if hu : u ∈ S.blueprint.realPart.terminals ∧ u ∈ T then
      S.predecessorAdvance compiler hpersistent u hu.1 hu.2
    else S

theorem noNewRealPredecessors_predecessorStep
    (compiler : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) :
    S.blueprint.NoNewRealPredecessorsTo
      (S.predecessorStep compiler hpersistent u).blueprint := by
  by_cases hu : u ∈ S.blueprint.realPart.terminals ∧ u ∈ T
  · simpa [predecessorStep, hu] using
      S.noNewRealPredecessors_predecessorAdvance
        compiler hpersistent u hu.1 hu.2
  · simp only [predecessorStep, hu, ↓reduceDIte]
    exact fun _ hyx ↦ hyx

/-- Total scheduler step.  Requests which are not terminals in the active
slice `T` at their stage are harmless no-ops; genuine scheduled requests use
9.34. -/
noncomputable def step
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) : TerminalResolutionState Gamma Y kappa T Z persistent B := by
  classical
  exact if hu : u ∈ S.blueprint.realPart.terminals ∧ u ∈ T then
      S.advance compiler hpersistent u hu.1 hu.2
    else S

theorem linked_subset_step
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) : S.linked ⊆ (S.step compiler hpersistent u).linked := by
  by_cases hu : u ∈ S.blueprint.realPart.terminals ∧ u ∈ T
  · simpa [step, hu] using Set.subset_insert u S.linked
  · simp [step, hu]

theorem realPart_extends_step
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) :
    S.blueprint.realPart.Extends
      (S.step compiler hpersistent u).blueprint.realPart := by
  by_cases hu : u ∈ S.blueprint.realPart.terminals ∧ u ∈ T
  · simpa [step, hu] using
      S.realPart_extends_advance compiler hpersistent u hu.1 hu.2
  · simpa [step, hu] using FamilyGraph.extends_refl S.blueprint.realPart

theorem links_step_of_terminal
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (hu : u ∈ S.blueprint.realPart.terminals) (huT : u ∈ T) :
    (S.step compiler hpersistent u).blueprint.RealLinksTo u B := by
  simpa [step, hu, huT] using
    S.links_advance_request compiler hpersistent u hu huT

/-- Execute a finite list of scheduler requests. -/
noncomputable def run
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T) :
    List V → TerminalResolutionState Gamma Y kappa T Z persistent B →
      TerminalResolutionState Gamma Y kappa T Z persistent B
  | [], S => S
  | u :: requests, S =>
      run compiler hpersistent requests (S.step compiler hpersistent u)

@[simp] theorem run_nil
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) :
    run compiler hpersistent [] S = S :=
  rfl

@[simp] theorem run_cons
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B)
    (u : V) (requests : List V) :
    run compiler hpersistent (u :: requests) S =
      run compiler hpersistent requests (S.step compiler hpersistent u) :=
  rfl

theorem linked_subset_run
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (requests : List V)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) :
    S.linked ⊆ (run compiler hpersistent requests S).linked := by
  induction requests generalizing S with
  | nil => exact Set.Subset.rfl
  | cons u requests ih =>
      exact (S.linked_subset_step compiler hpersistent u).trans
        (ih (S.step compiler hpersistent u))

theorem realPart_extends_run
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (requests : List V)
    (S : TerminalResolutionState Gamma Y kappa T Z persistent B) :
    S.blueprint.realPart.Extends
      (run compiler hpersistent requests S).blueprint.realPart := by
  induction requests generalizing S with
  | nil => exact FamilyGraph.extends_refl _
  | cons u requests ih =>
      exact FamilyGraph.extends_trans
        (S.realPart_extends_step compiler hpersistent u)
        (ih (S.step compiler hpersistent u))

/-
## Work in progress: a relation-level limit for real-extension chains

The path-set `LinkageBlueprint.limit` is not the right representation for
9.33: a finite path may be properly extended at every stage, and therefore
no whole path value need occur eventually.  The observables which really are
monotone under `RealExtends` are the vertices and real edges.  We first form
their unions and then decompose that relation into root orbits.

Two genuinely global requirements are deliberately visible below.  A
directed union of finite paths can acquire a reverse ray, and the persistence
disjunction in 9.32 has to hold at the limit rather than merely at every
successor.  Neither fact follows from set inclusion alone. -/

/-

/-- A linearly ordered chain under the actual relation (9.32), rather than
literal inclusion of whole path records. -/
structure RealExtensionChain (I : Type v) [LinearOrder I]
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (T Z persistent B : Set V) where
  stage : I → LinkageBlueprint Gamma Y kappa
  isBlueprint : ∀ i, (stage i).IsLinkageBlueprint T Z persistent
  stable : ∀ i, (stage i).Stable T persistent
  realExtends : ∀ {i j}, i ≤ j → (stage i).RealExtends (stage j) B

namespace RealExtensionChain

variable {I : Type v} [LinearOrder I]

/-- Every real vertex which occurs at some stage. -/
def realVertexLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) : Set V :=
  ⋃ i, (C.stage i).realPart.vertices

/-- Every real edge which occurs at some stage.  These edge sets are
monotone by the first conjunct of `RealExtends`. -/
def realEdgeLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) : Set (V × V) :=
  ⋃ i, (C.stage i).realPart.edges

theorem stage_vertices_subset_realVertexLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) (i : I) :
    (C.stage i).realPart.vertices ⊆ C.realVertexLimit :=
  Set.subset_iUnion (fun j ↦ (C.stage j).realPart.vertices) i

theorem stage_edges_subset_realEdgeLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) (i : I) :
    (C.stage i).realPart.edges ⊆ C.realEdgeLimit :=
  Set.subset_iUnion (fun j ↦ (C.stage j).realPart.edges) i

theorem realVertexLimit_mono
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) {i j : I}
    (hij : i ≤ j) :
    (C.stage i).realPart.vertices ⊆ (C.stage j).realPart.vertices :=
  (C.realExtends hij).realPart_extends.1

theorem realEdgeLimit_mono
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) {i j : I}
    (hij : i ≤ j) :
    (C.stage i).realPart.edges ⊆ (C.stage j).realPart.edges :=
  (C.realExtends hij).realEdges_mono

/-- The union relation is still locally a disjoint union of directed
threads.  Only finite comparison is needed here: move two competing edges
to the later of their two stages and use the warp property there. -/
theorem realEdgeLimit_biUnique
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ C.realEdgeLimit) := by
  constructor
  · intro x y z hxz hyz
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxz
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.1 hyz
    rcases le_total i j with hij | hji
    · exact (Alternating.IsWarp.familyEdges_leftUnique (C.stage j).isWarp)
        (C.realEdgeLimit_mono hij hxi).1 hyj.1
    · exact (Alternating.IsWarp.familyEdges_leftUnique (C.stage i).isWarp)
        hxi.1 (C.realEdgeLimit_mono hji hyj).1
  · intro x y z hxy hxz
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.1 hxy
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.1 hxz
    rcases le_total i j with hij | hji
    · exact (Alternating.IsWarp.familyEdges_rightUnique (C.stage j).isWarp)
        (C.realEdgeLimit_mono hij hyi).1 hzj.1
    · exact (Alternating.IsWarp.familyEdges_rightUnique (C.stage i).isWarp)
        hyi.1 (C.realEdgeLimit_mono hji hzj).1

theorem realEdgeLimit_in_graph
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) :
    C.realEdgeLimit ⊆ {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  intro e he
  obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
  exact Or.inl hei.2

theorem realEdgeLimit_endpoints
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) :
    ∀ e ∈ C.realEdgeLimit,
      e.1 ∈ C.realVertexLimit ∧ e.2 ∈ C.realVertexLimit := by
  intro e he
  obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
  have hends :
      e.1 ∈ (C.stage i).vertexSet ∧ e.2 ∈ (C.stage i).vertexSet :=
    Alternating.familyEdges_subset_vertexSet_prod
      (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths hei.1
  exact ⟨Set.mem_iUnion.2 ⟨i, by simpa using hends.1⟩,
    Set.mem_iUnion.2 ⟨i, by simpa using hends.2⟩⟩

/-- The two global well-foundedness obligations needed to turn the union
relation into paths.  `no_reverse_ray` cannot be dropped: successively
prepending one edge to a finite path is a counterexample. -/
structure RelationLimitCore
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) : Prop where
  no_directed_cycle : ¬ Alternating.ContainsDirectedCycle C.realEdgeLimit
  no_reverse_ray : ¬ Alternating.ContainsReverseDirectedRay C.realEdgeLimit

/-- The canonical forward orientation of the union of real edges. -/
noncomputable def relationLimitOrientation
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) :
    Alternating.RelationDecomposition.ForwardOrientation
      (imaginaryGraph Gamma Y kappa) :=
  Classical.choose (exists_forwardOrientation_exact
    C.realEdgeLimit C.realVertexLimit C.realEdgeLimit_in_graph
      C.realEdgeLimit_endpoints C.realEdgeLimit_biUnique
      H.no_directed_cycle H.no_reverse_ray)

theorem relationLimitOrientation_spec
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) :
    (C.relationLimitOrientation H).edge = C.realEdgeLimit ∧
      (C.relationLimitOrientation H).carrier = C.realVertexLimit :=
  Classical.choose_spec (exists_forwardOrientation_exact
    C.realEdgeLimit C.realVertexLimit C.realEdgeLimit_in_graph
      C.realEdgeLimit_endpoints C.realEdgeLimit_biUnique
      H.no_directed_cycle H.no_reverse_ray)

/-- Root-orbit decomposition of the monotone real observables.  In
particular, every edge of this blueprint is real. -/
noncomputable def relationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) : LinkageBlueprint Gamma Y kappa :=
  orientationBlueprint (C.relationLimitOrientation H)

theorem relationLimit_vertexSet
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) :
    (C.relationLimit H).vertexSet = C.realVertexLimit := by
  rw [relationLimit, orientationBlueprint_vertexSet,
    (C.relationLimitOrientation_spec H).2]

theorem relationLimit_edgeSet
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) :
    (C.relationLimit H).edgeSet = C.realEdgeLimit := by
  rw [relationLimit, orientationBlueprint_edgeSet,
    (C.relationLimitOrientation_spec H).1]

theorem relationLimit_edge_real
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) :
    (C.relationLimit H).familyGraph.edges ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  change e ∈ (C.relationLimit H).edgeSet at he
  rw [C.relationLimit_edgeSet H] at he
  obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
  exact hei.2

theorem realPart_extends_relationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) (i : I) :
    (C.stage i).realPart.Extends (C.relationLimit H).realPart := by
  constructor
  · change (C.stage i).vertexSet ⊆ (C.relationLimit H).vertexSet
    rw [C.relationLimit_vertexSet H]
    exact C.stage_vertices_subset_realVertexLimit i
  · intro e he
    change e ∈ (C.relationLimit H).edgeSet ∩
      {e | Gamma.graph.Adj e.1 e.2}
    refine ⟨?_, he.2⟩
    rw [C.relationLimit_edgeSet H]
    exact C.stage_edges_subset_realEdgeLimit i he

/-- Everything not forced by monotone real observables is collected here.
The `accounted` field is exactly the second conjunct of (9.32), stated for
the constructed root-orbit limit. -/
structure StableRelationLimitData
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) : Prop where
  isBlueprint : (C.relationLimit H).IsLinkageBlueprint T Z persistent
  stable : (C.relationLimit H).Stable T persistent
  accounted : ∀ i, (C.stage i).vertexSet ⊆
    ((C.relationLimit H).terminalSet ∩ (C.stage i).terminalSet) ∪
      {x | ∃ y, (x, y) ∈
        (C.stage i).familyGraph.edges ∩
          (C.relationLimit H).familyGraph.edges} ∪
        (C.relationLimit H).completedRealVertices B

theorem realExtends_relationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) (D : C.StableRelationLimitData H) (i : I) :
    (C.stage i).RealExtends (C.relationLimit H) B :=
  ⟨C.realPart_extends_relationLimit H i, D.accounted i⟩

/-- Sound replacement for the path-set-liminf limit theorem: the chain is
phrased in `RealExtends`, the limit is built from its real observables, and
the non-local hypotheses are exposed exactly where they are used. -/
theorem stableLimitConclusion_relationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) (D : C.StableRelationLimitData H) :
    StableLimitConclusion C.stage (C.relationLimit H)
      T Z persistent B :=
  ⟨D.isBlueprint, D.stable, C.realExtends_relationLimit H D⟩

end RealExtensionChain

-/

/-- A fair 9.33 limit with explicit transfinite provenance.  The scheduler
compiler has to build this object from the source's transfinite recursion;
the seed is absorbed by every stage, including honest relation-limit stages. -/
structure FairResolutionLimit
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B) where
  index : Type u
  stage : index → TerminalResolutionState Gamma Y kappa T Z persistent B
  scheduled : index → V
  seed_absorbed : ∀ i,
    seed.blueprint.RealExtends (stage i).blueprint B
  scheduled_linked : ∀ i, scheduled i ∈ (stage i).linked
  limit : TerminalResolutionState Gamma Y kappa T Z persistent B
  absorbed : ∀ i, (stage i).blueprint.realPart.Extends limit.blueprint.realPart
  fair : ∀ x ∈ limit.blueprint.realPart.terminals, x ∉ B →
    ∃ i, scheduled i = x
  real_limit : limit.blueprint.familyGraph.edges ⊆
    {e | Gamma.graph.Adj e.1 e.2}

/-! ## The actual relation-limit implementation of 9.33 -/

/-- A linearly ordered chain of scheduler states.  Unlike
`FairResolutionLimit`, this record stores the actual `RealExtends` transition
relation and therefore has a canonical relation limit. -/
structure ResolutionChain (I : Type u) [LinearOrder I]
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B)
    (hpersistent : persistent ⊆ T) where
  stage : I → TerminalResolutionState Gamma Y kappa T Z persistent B
  realExtends : ∀ {i j}, i ≤ j →
    (stage i).blueprint.RealExtends (stage j).blueprint B

namespace ResolutionChain

variable {I : Type u} [LinearOrder I]
variable {compiler : Stable934Compiler
  (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent B}
variable {hpersistent : persistent ⊆ T}

/-- Forget scheduler-state data and retain the real-extension chain used by
the relation-limit construction. -/
def toRealExtensionChain
    (C : ResolutionChain I compiler hpersistent) :
    RealExtensionChain I Gamma Y kappa T Z persistent B where
  stage := fun i ↦ (C.stage i).blueprint
  isBlueprint := fun i ↦ (C.stage i).isBlueprint
  stable := fun i ↦ (C.stage i).stable
  realExtends := C.realExtends

/-- The canonical limit core.  Directed cycles are excluded by finite-stage
capture; reverse rays are excluded by the explicitly maintained invariant
that successors never insert a new predecessor before an old real vertex. -/
def relationLimitCore (C : ResolutionChain I compiler hpersistent)
    (H : C.toRealExtensionChain.NoNewRealPredecessors) :
    C.toRealExtensionChain.RelationLimitCore :=
  C.toRealExtensionChain.relationLimitCore_of_noNewRealPredecessors H

/-- The three genuinely residual boundary obligations for a scheduler
relation union.  Source coverage follows from the predecessor invariant and
stage source coverage; carrier cardinality follows from the size of the
index.  Thus neither is repeated here as scheduler input. -/
structure ResidualRelationBoundaryData
    (C : ResolutionChain I compiler hpersistent) : Prop where
  every_relation_ray_strong :
    ∀ r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ C.toRealExtensionChain.realEdgeLimit →
        (strongEdgeIndices r).Infinite
  terminal_boundary :
    {x | x ∈ C.toRealExtensionChain.realVertexLimit ∧
      ¬ ∃ y, (x, y) ∈ C.toRealExtensionChain.realEdgeLimit} ⊆
      {x | IsPopular Gamma Y persistent kappa x} ∪ T
  stable_boundary :
    {x | x ∈ C.toRealExtensionChain.realVertexLimit ∧
      ¬ ∃ y, (x, y) ∈ C.toRealExtensionChain.realEdgeLimit} ∩ T ⊆
      persistent

/-- After scheduler fairness is available, the sink fields of
`ResidualRelationBoundaryData` are consequences of eventual completion.
This leaves only the genuinely infinitary forward-ray condition as raw
relation-boundary input. -/
structure RayRelationBoundaryData
    (C : ResolutionChain I compiler hpersistent) : Prop where
  every_relation_ray_strong :
    ∀ r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ C.toRealExtensionChain.realEdgeLimit →
        (strongEdgeIndices r).Infinite

/-- Compile the residual ray/sink boundary conditions to the full raw
relation-boundary record.  The two omitted fields are consequences of the
ordinary chain invariants and cardinal bounds. -/
def ResidualRelationBoundaryData.toRelationLimitBoundaryData
    [Nonempty I] {C : ResolutionChain I compiler hpersistent}
    (D : ResidualRelationBoundaryData C)
    (H : C.toRealExtensionChain.NoNewRealPredecessors)
    (hYwarp : Gamma.IsWarp Y) (hkappa : aleph0 ≤ kappa)
    (hindex : #I ≤ kappa) :
    C.toRealExtensionChain.RelationLimitBoundaryData where
  covers_source :=
    C.toRealExtensionChain.relationLimit_covers_source H hYwarp
  card_vertices :=
    C.toRealExtensionChain.mk_realVertexLimit_le hkappa hindex
  every_relation_ray_strong := D.every_relation_ray_strong
  terminal_boundary := D.terminal_boundary
  stable_boundary := D.stable_boundary

/-- The scheduler state at an honest relation limit.  Previously linked
requests are unioned, and their real paths transport along inclusion of real
parts into the root-orbit limit. -/
noncomputable def limitState
    (C : ResolutionChain I compiler hpersistent)
    (H : C.toRealExtensionChain.NoNewRealPredecessors)
    (D : C.toRealExtensionChain.StableRelationLimitData
      (C.relationLimitCore H)) :
    TerminalResolutionState Gamma Y kappa T Z persistent B where
  blueprint := C.toRealExtensionChain.relationLimit (C.relationLimitCore H)
  isBlueprint := D.isBlueprint
  stable := D.stable
  linked := ⋃ i, (C.stage i).linked
  links := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact realLinksTo_mono
      (C.toRealExtensionChain.realPart_extends_relationLimit
        (C.relationLimitCore H) i)
      ((C.stage i).links x hxi)

/-- A fair transfinite scheduler with all genuinely non-local limit
obligations exposed as invariants of its real-extension chain.  In
particular, this does not postulate an unrelated terminal blueprint: its
limit is definitionally the root-orbit decomposition of the union of stage
real edges. -/
structure FairRelationSchedule
    (C : ResolutionChain I compiler hpersistent)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B) where
  noNewPredecessors : C.toRealExtensionChain.NoNewRealPredecessors
  boundaryData : C.toRealExtensionChain.RelationLimitBoundaryData
  eventuallyLinked : ∀ i x,
    x ∈ (C.stage i).blueprint.realPart.terminals →
      ∃ j, x ∈ (C.stage j).linked
  scheduled : I → V
  seed_absorbed : ∀ i,
    seed.blueprint.RealExtends (C.stage i).blueprint B
  scheduled_linked : ∀ i, scheduled i ∈ (C.stage i).linked
  fair : ∀ x ∈
      (C.toRealExtensionChain.relationLimit
        (C.relationLimitCore noNewPredecessors)).realPart.terminals,
    x ∉ B → ∃ i, scheduled i = x

/-- A terminal of the real relation union was already a real terminal at
some stage.  Its vertex occurs at a stage by definition of the union; an
outgoing real edge there would survive in the relation limit and contradict
terminality. -/
theorem exists_stage_realTerminal_of_relationLimit_terminal
    (C : ResolutionChain I compiler hpersistent)
    (H : C.toRealExtensionChain.NoNewRealPredecessors) {x : V}
    (hx : x ∈
      (C.toRealExtensionChain.relationLimit
        (C.relationLimitCore H)).realPart.terminals) :
    ∃ i, x ∈ (C.stage i).blueprint.realPart.terminals := by
  rcases hx with ⟨hxv, hxout⟩
  rw [realPart_vertices,
    C.toRealExtensionChain.relationLimit_vertexSet
      (C.relationLimitCore H)] at hxv
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxv
  change x ∈ (C.stage i).blueprint.realPart.vertices at hxi
  refine ⟨i, hxi, ?_⟩
  rintro ⟨y, hxy⟩
  apply hxout
  exact ⟨y, C.toRealExtensionChain.realPart_extends_relationLimit
    (C.relationLimitCore H) i |>.2 hxy⟩

/-- The scheduler-facing content of a fair terminal enumeration.  This is
strictly execution data: every named request has actually been linked in its
stage, every real terminal occurring at any stage is named somewhere, and
all stages absorb the seed.  It assumes neither a limit blueprint nor any
limit conclusion.

In particular, this is the sound transfinite replacement for the earlier
finite-list reachability field.  Limit stages need not be equal to a finite
run, and predecessor-preserving choices are never identified with the
independent choices made by the weaker `run`. -/
structure SuccessfulResolutionEnumeration
    (C : ResolutionChain I compiler hpersistent)
    (seed : TerminalResolutionState Gamma Y kappa T Z persistent B) where
  scheduled : I → V
  seed_absorbed : ∀ i,
    seed.blueprint.RealExtends (C.stage i).blueprint B
  scheduled_linked : ∀ i, scheduled i ∈ (C.stage i).linked
  covers_stage_realTerminals : ∀ i x,
    x ∈ (C.stage i).blueprint.realPart.terminals →
      ∃ j, scheduled j = x

/-- A successful enumeration gives the exact eventual-completion hypothesis
used by relation-limit accounting. -/
theorem SuccessfulResolutionEnumeration.eventuallyLinked
    {C : ResolutionChain I compiler hpersistent}
    {seed : TerminalResolutionState Gamma Y kappa T Z persistent B}
    (E : SuccessfulResolutionEnumeration C seed) :
    ∀ i x, x ∈ (C.stage i).blueprint.realPart.terminals →
      ∃ j, x ∈ (C.stage j).linked := by
  intro i x hx
  obtain ⟨j, hj⟩ := E.covers_stage_realTerminals i x hx
  exact ⟨j, hj ▸ E.scheduled_linked j⟩

/-- The state invariant upgrades eventual membership in `linked` to the
exact eventual-completion hypothesis used by the relation limit. -/
theorem SuccessfulResolutionEnumeration.eventuallyCompleted
    {C : ResolutionChain I compiler hpersistent}
    {seed : TerminalResolutionState Gamma Y kappa T Z persistent B}
    (E : SuccessfulResolutionEnumeration C seed) :
    ∀ i x, x ∈ (C.stage i).blueprint.realPart.terminals →
      ∃ j, x ∈ (C.stage j).blueprint.completedRealVertices B := by
  intro i x hx
  obtain ⟨j, hxlinked⟩ := E.eventuallyLinked i x hx
  exact ⟨j, ((C.stage j).links x hxlinked).start_mem_completedRealVertices⟩

/-- Raw relation-boundary data, the predecessor invariant, and a successful
terminal enumeration compile the complete fair schedule.  Blueprint and
stability at the limit are constructed from `RelationLimitBoundaryData`;
eventual accounting and terminal fairness are derived from the enumeration. -/
noncomputable def FairRelationSchedule.ofSuccessfulEnumeration
    {C : ResolutionChain I compiler hpersistent}
    {seed : TerminalResolutionState Gamma Y kappa T Z persistent B}
    (H : C.toRealExtensionChain.NoNewRealPredecessors)
    (D : C.toRealExtensionChain.RelationLimitBoundaryData)
    (E : SuccessfulResolutionEnumeration C seed) :
    FairRelationSchedule C seed where
  noNewPredecessors := H
  boundaryData := D
  eventuallyLinked := E.eventuallyLinked
  scheduled := E.scheduled
  seed_absorbed := E.seed_absorbed
  scheduled_linked := E.scheduled_linked
  fair := by
    intro x hx hxB
    obtain ⟨i, hxi⟩ :=
      C.exists_stage_realTerminal_of_relationLimit_terminal H hx
    exact E.covers_stage_realTerminals i x hxi

/-- A successful enumeration together with only the genuinely residual
ray/sink boundary obligations compiles the fair schedule.  Source coverage
and the cardinal bound of the relation union are derived, not assumed. -/
noncomputable def FairRelationSchedule.ofSuccessfulEnumeration_of_residualBoundary
    [Nonempty I]
    {C : ResolutionChain I compiler hpersistent}
    {seed : TerminalResolutionState Gamma Y kappa T Z persistent B}
    (H : C.toRealExtensionChain.NoNewRealPredecessors)
    (hYwarp : Gamma.IsWarp Y) (hkappa : aleph0 ≤ kappa)
    (hindex : #I ≤ kappa) (D : ResidualRelationBoundaryData C)
    (E : SuccessfulResolutionEnumeration C seed) :
    FairRelationSchedule C seed :=
  FairRelationSchedule.ofSuccessfulEnumeration H
    (D.toRelationLimitBoundaryData H hYwarp hkappa hindex)
      E

/-- Fairness constructs both union-sink boundary fields.  Consequently an
honest scheduler needs to supply only the forward-ray condition, together
with the fixed compatibility of completed endpoints with the slice and its
persistent part. -/
noncomputable def FairRelationSchedule.ofSuccessfulEnumeration_of_rayBoundary
    [Nonempty I]
    {C : ResolutionChain I compiler hpersistent}
    {seed : TerminalResolutionState Gamma Y kappa T Z persistent B}
    (H : C.toRealExtensionChain.NoNewRealPredecessors)
    (hYwarp : Gamma.IsWarp Y) (hkappa : aleph0 ≤ kappa)
    (hindex : #I ≤ kappa)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (D : RayRelationBoundaryData C)
    (E : SuccessfulResolutionEnumeration C seed) :
    FairRelationSchedule C seed := by
  apply FairRelationSchedule.ofSuccessfulEnumeration H ?_ E
  exact
    { covers_source :=
        C.toRealExtensionChain.relationLimit_covers_source H hYwarp
      card_vertices :=
        C.toRealExtensionChain.mk_realVertexLimit_le hkappa hindex
      every_relation_ray_strong := D.every_relation_ray_strong
      terminal_boundary :=
        C.toRealExtensionChain
          |>.relationLimit_terminal_boundary_of_eventuallyCompleted
            E.eventuallyCompleted hterminalB
      stable_boundary :=
        C.toRealExtensionChain
          |>.relationLimit_stable_boundary_of_eventuallyCompleted
            E.eventuallyCompleted hstableB }

/-- The exact (9.32) accounting field is derived from scheduler fairness,
rather than supplied as an independent limit assumption.  Once a stage real
terminal is inserted into a later state's `linked` set, that state's stored
real path completes it to `B`; `accounted_relationLimit` transports the path
to the relation union. -/
def FairRelationSchedule.limitData
    {C : ResolutionChain I compiler hpersistent}
    {seed : TerminalResolutionState Gamma Y kappa T Z persistent B}
    (S : FairRelationSchedule C seed) :
    C.toRealExtensionChain.StableRelationLimitData
      (C.relationLimitCore S.noNewPredecessors) :=
  C.toRealExtensionChain
    |>.stableRelationLimitData_of_boundary_eventuallyCompleted
    (C.relationLimitCore S.noNewPredecessors) S.boundaryData (fun i x hx ↦ by
      obtain ⟨j, hxlinked⟩ := S.eventuallyLinked i x hx
      exact ⟨j, ((C.stage j).links x hxlinked).start_mem_completedRealVertices⟩)

/-- Compile the genuine relation-limit schedule to the small interface used
by terminal finalization. -/
noncomputable def FairRelationSchedule.toFairResolutionLimit
    {C : ResolutionChain I compiler hpersistent}
    {seed : TerminalResolutionState Gamma Y kappa T Z persistent B}
    (S : FairRelationSchedule C seed) :
    FairResolutionLimit compiler hpersistent seed where
  index := I
  stage := C.stage
  scheduled := S.scheduled
  seed_absorbed := S.seed_absorbed
  scheduled_linked := S.scheduled_linked
  limit := C.limitState S.noNewPredecessors S.limitData
  absorbed := fun i ↦
    C.toRealExtensionChain.realPart_extends_relationLimit
      (C.relationLimitCore S.noNewPredecessors) i
  fair := by
    simpa only [limitState] using S.fair
  real_limit := C.toRealExtensionChain.relationLimit_edge_real
    (C.relationLimitCore S.noNewPredecessors)

/-- Assertion 9.33 for the scheduler's actual relation limit, including the
full real-extension accounting relation (9.32). -/
theorem FairRelationSchedule.stableLimitConclusion
    {C : ResolutionChain I compiler hpersistent}
    {seed : TerminalResolutionState Gamma Y kappa T Z persistent B}
    (S : FairRelationSchedule C seed) :
    StableLimitConclusion
      (fun i ↦ (C.stage i).blueprint)
      (C.limitState S.noNewPredecessors S.limitData).blueprint
        T Z persistent B :=
  C.toRealExtensionChain.stableLimitConclusion_relationLimit
    (C.relationLimitCore S.noNewPredecessors) S.limitData

end ResolutionChain

/-- Forget transition provenance and retain the terminal chain consumed by
the final blueprint theorem. -/
def FairResolutionLimit.toTerminalScheduledChain
    {compiler : Stable934Compiler
      (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent B}
    {hpersistent : persistent ⊆ T}
    {seed : TerminalResolutionState Gamma Y kappa T Z persistent B}
    (R : FairResolutionLimit compiler hpersistent seed) :
    TerminalScheduledChain R.index (fun i => (R.stage i).blueprint)
      R.limit.blueprint B where
  scheduled := R.scheduled
  absorbed := R.absorbed
  fair := R.fair
  resolved := fun i => (R.stage i).links _ (R.scheduled_linked i)
  real_limit := R.real_limit

/-- The structural data accompanying a fair resolution limit.  Unlike
`TerminalScheduledBlueprintCertificate`, this record remembers the concrete
9.34 compiler and the scheduler's transfinite seed-absorption invariant. -/
structure FairResolutionCertificate
    (compiler : Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent Gamma.target)
    (hpersistent : persistent ⊆ T) (A0 : Set V) where
  seed : TerminalResolutionState Gamma Y kappa T Z persistent Gamma.target
  resolution : FairResolutionLimit compiler hpersistent seed
  slice : Set V
  stopover : Set V
  heightDelete : Set V
  heightWave : Set (Gamma.quotient heightDelete).DPath
  reference_isWarp : Gamma.IsWarp Y
  designated_source : A0 ⊆ Gamma.source
  designated_initial : A0 ⊆ resolution.limit.blueprint.initialSet
  source_cover : resolution.limit.blueprint.initialSet ∪
    Gamma.initialSet
      (resolution.limit.blueprint.referenceRemainder slice) = Gamma.source
  terminal_frontier : resolution.limit.blueprint.terminalSet ∪
    Gamma.terminalFrontier
      (resolution.limit.blueprint.referenceRemainder slice) = stopover
  blueprint_endpointPure : ∀ p ∈ resolution.limit.blueprint.paths,
    resolution.limit.blueprint.IsPathBetween Gamma.source stopover p
  reference_endpointPure :
    ∀ p ∈ resolution.limit.blueprint.referenceRemainder slice,
      CardinalInduction.IsPathBetween Gamma Gamma.source stopover p
  stopover_separator :
    CardinalInduction.IsSeparatorFrom Gamma Gamma.source stopover
  stopover_trimmed : Gamma.essential stopover = stopover
  quotient_unhindered : (Gamma.quotient stopover).IsUnhindered
  heightDelete_nonSource : heightDelete ⊆ Gamma.sourceᶜ
  heightWave_isWave : (Gamma.quotient heightDelete).IsWave heightWave
  stopover_roofed : stopover ⊆ Gamma.roof
    ((Gamma.quotient heightDelete).terminalFrontier heightWave)
  heightDelete_card : #heightDelete ≤ kappa

def FairResolutionCertificate.toTerminalScheduledBlueprintCertificate
    {compiler : Stable934Compiler
      (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent Gamma.target}
    {hpersistent : persistent ⊆ T} {A0 : Set V}
    (C : FairResolutionCertificate compiler hpersistent A0) :
    CardinalInduction.TerminalScheduledBlueprintCertificate Gamma A0 kappa where
  reference := Y
  blueprint := C.resolution.limit.blueprint
  index := C.resolution.index
  stage := fun i => (C.resolution.stage i).blueprint
  schedule := C.resolution.toTerminalScheduledChain
  slice := C.slice
  stopover := C.stopover
  heightDelete := C.heightDelete
  heightWave := C.heightWave
  reference_isWarp := C.reference_isWarp
  designated_source := C.designated_source
  designated_initial := C.designated_initial
  source_cover := C.source_cover
  terminal_frontier := C.terminal_frontier
  blueprint_endpointPure := C.blueprint_endpointPure
  reference_endpointPure := C.reference_endpointPure
  stopover_trimmed := C.stopover_trimmed
  quotient_unhindered := C.quotient_unhindered
  heightDelete_nonSource := C.heightDelete_nonSource
  heightWave_isWave := C.heightWave_isWave
  stopover_roofed := C.stopover_roofed
  heightDelete_card := C.heightDelete_card

end TerminalResolutionState
end LinkageBlueprint
end Blueprint

namespace CardinalInduction

open Blueprint LinkageBlueprint

variable {V : Type u}

/-- Strengthened global terminal certificate retaining the source-separator
fact used by the later regular and singular constructions.  Separation is an
independent field; it is not inferred from trimmedness. -/
structure SeparatingGloballyResolvedBlueprintCertificate
    (Gamma : DWeb V) (A0 : Set V) (kappa : Cardinal.{u}) where
  certificate : GloballyResolvedBlueprintCertificate Gamma A0 kappa
  stopover_separator :
    IsSeparatorFrom Gamma Gamma.source certificate.stopover

/-- The strengthened certificate yields the same concrete half-way linkage,
but also retains the separator proof for its exact stop-over. -/
theorem SeparatingGloballyResolvedBlueprintCertificate.exists_separatingHalfwayLinkage
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    (S : SeparatingGloballyResolvedBlueprintCertificate Gamma A0 kappa) :
    ∃ W : Set Gamma.DPath,
      IsSeparatingHalfwayStopover Gamma W S.certificate.stopover ∧
      LinksToTarget Gamma W A0 ∧
      HeightAtMost Gamma S.certificate.stopover kappa ∧
      Gamma.terminalFrontier W = S.certificate.stopover := by
  let C := S.certificate
  have hgraph : C.blueprint.familyGraph = C.blueprint.realPart := by
    change FamilyGraph.mk C.blueprint.familyGraph.vertices
      C.blueprint.familyGraph.edges =
      FamilyGraph.mk C.blueprint.realPart.vertices C.blueprint.realPart.edges
    apply congrArg₂ (fun vertices edges ↦ FamilyGraph.mk vertices edges)
    · rfl
    · change C.blueprint.familyGraph.edges =
        C.blueprint.familyGraph.edges ∩ {e | Gamma.graph.Adj e.1 e.2}
      apply Set.Subset.antisymm
      · intro e he
        exact ⟨he, C.edge_real he⟩
      · exact Set.inter_subset_left
  have hterminal : C.blueprint.terminalSet ⊆ Gamma.target := by
    intro x hx
    have hxterm := C.blueprint.terminalSet_subset_familyGraph_terminals
      C.blueprint_endpointPure hx
    rw [hgraph] at hxterm
    exact C.real_terminals_target hxterm
  have hlinks : C.blueprint.BlueprintLinksToTarget A0 :=
    C.blueprint.blueprintLinksToTarget_of_initial_terminal
      C.designated_source C.designated_initial C.blueprint_endpointPure
      hterminal
  obtain ⟨W, hstop, htarget, hheight, hfrontier⟩ :=
    exists_halfwayStopover_of_terminalBlueprint_withReference
      C.blueprint C.edge_real
      (C.blueprint.referenceRemainder C.slice)
      (C.blueprint.isWarp_referenceRemainder C.slice C.reference_isWarp)
      (C.blueprint.disjoint_referenceRemainder C.slice)
      C.source_cover C.terminal_frontier C.blueprint_endpointPure
      C.reference_endpointPure C.stopover_trimmed C.quotient_unhindered
      hlinks C.heightDelete_nonSource C.heightWave C.heightWave_isWave
      C.stopover_roofed C.heightDelete_card
  exact ⟨W, ⟨hstop, S.stopover_separator⟩, htarget, hheight, hfrontier⟩

/-- Turn a provenance-carrying fair resolution into the strengthened global
certificate without dropping separation. -/
def TerminalResolutionState.FairResolutionCertificate.toSeparatingGloballyResolved
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
    {T Z persistent : Set V}
    {compiler : Stable934Compiler
      (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent Gamma.target}
    {hpersistent : persistent ⊆ T} {A0 : Set V}
    (C : TerminalResolutionState.FairResolutionCertificate
      compiler hpersistent A0) :
    SeparatingGloballyResolvedBlueprintCertificate Gamma A0 kappa where
  certificate := C.toTerminalScheduledBlueprintCertificate.toGloballyResolved
  stopover_separator := C.stopover_separator

/-- Construction interface with explicit transfinite provenance through the
9.34 successor compiler and its relation limits. -/
def FairResolutionCertificateCompiler (Gamma : DWeb V)
    (kappa : Cardinal.{u}) : Prop :=
  ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
    ∃ (Y : Set Gamma.DPath) (T Z persistent : Set V)
      (compiler : Stable934Compiler
        (Γ := Gamma) (Y := Y) (κ := kappa)
        T Z persistent Gamma.target)
      (hpersistent : persistent ⊆ T),
      Nonempty (TerminalResolutionState.FairResolutionCertificate
        compiler hpersistent A0)

/-- Strengthened compiler target used by any later induction step which
needs the source-separator invariant, rather than only the public half-way
linkage conclusion. -/
def SeparatingGloballyResolvedBlueprintCompiler (Gamma : DWeb V)
    (kappa : Cardinal.{u}) : Prop :=
  ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
    Nonempty (SeparatingGloballyResolvedBlueprintCertificate Gamma A0 kappa)

theorem separatingGloballyResolvedBlueprintCompiler_of_fairResolution
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcompile : FairResolutionCertificateCompiler Gamma kappa) :
    SeparatingGloballyResolvedBlueprintCompiler Gamma kappa := by
  intro A0 hA0 hcard
  obtain ⟨Y, T, Z, persistent, compiler, hpersistent, C⟩ :=
    hcompile A0 hA0 hcard
  exact C.map
    TerminalResolutionState.FairResolutionCertificate.toSeparatingGloballyResolved

/-- A fair resolution compiler produces the previously defined terminal
scheduled compiler by forgetting transition provenance. -/
theorem terminalScheduledBlueprintCompiler_of_fairResolution
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcompile : FairResolutionCertificateCompiler Gamma kappa) :
    TerminalScheduledBlueprintCompiler Gamma kappa := by
  intro A0 hA0 hcard
  obtain ⟨Y, T, Z, persistent, compiler, hpersistent, C⟩ :=
    hcompile A0 hA0 hcard
  exact C.map
    TerminalResolutionState.FairResolutionCertificate.toTerminalScheduledBlueprintCertificate

theorem globallyResolvedBlueprintCompiler_of_fairResolution
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcompile : FairResolutionCertificateCompiler Gamma kappa) :
    GloballyResolvedBlueprintCompiler Gamma kappa :=
  globallyResolvedBlueprintCompiler_of_terminalScheduled
    (terminalScheduledBlueprintCompiler_of_fairResolution hcompile)

/-- Source-facing version: Assertions 9.30 and 9.31 determine the exact
9.34 transition used at every successor stage of the transfinite recursion. -/
def Fair930931ResolutionCertificateCompiler (Gamma : DWeb V)
    (kappa : Cardinal.{u}) : Prop :=
  ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
    ∃ (Y : Set Gamma.DPath) (T Z persistent : Set V)
      (hpersistent : persistent ⊆ T)
      (h30 : Continuation930Compiler
        (Γ := Gamma) (Y := Y) (κ := kappa)
        T Z persistent Gamma.target)
      (h31 : Advance931Compiler
        (Γ := Gamma) (Y := Y) (κ := kappa)
        T Z persistent Gamma.target),
      Nonempty (TerminalResolutionState.FairResolutionCertificate
        (stable934Compiler_of_930_931 h30 h31) hpersistent A0)

theorem fairResolutionCertificateCompiler_of_930_931
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcompile : Fair930931ResolutionCertificateCompiler Gamma kappa) :
    FairResolutionCertificateCompiler Gamma kappa := by
  intro A0 hA0 hcard
  obtain ⟨Y, T, Z, persistent, hpersistent, h30, h31, C⟩ :=
    hcompile A0 hA0 hcard
  exact ⟨Y, T, Z, persistent, stable934Compiler_of_930_931 h30 h31,
    hpersistent, C⟩

theorem globallyResolvedBlueprintCompiler_of_930_931_fairResolution
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcompile : Fair930931ResolutionCertificateCompiler Gamma kappa) :
    GloballyResolvedBlueprintCompiler Gamma kappa :=
  globallyResolvedBlueprintCompiler_of_fairResolution
    (fairResolutionCertificateCompiler_of_930_931 hcompile)

end CardinalInduction
end Erdos599
