/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingGroundedRecordMarkerDisjoint
import ErdosProblems.Erdos599.GroundingErasedRouteCore
import ErdosProblems.Erdos599.GroundingRelaxedEscape
import ErdosProblems.Erdos599.TerminalContactSwitch

/-!
# The generic finite-source duplicate decoder need not cover forward contacts

The private reverse/escape splice in
`GroundingFiniteSourceDuplicateExchange` does not, for an arbitrary
`PopularAuxiliary.Input`, imply the switching-ready contact condition.  The
four-vertex example below has a one-edge ladder component `a -> c`, and the
duplicate route starts at its finite terminal `c`.  After traversing that
component backwards it escapes through a second ladder vertex `z` to a
target marker `y`.  The decoded route is

`c -(backward)-> a -(forward)-> z -(forward)-> y`.

Thus `z` is a nonterminal forward contact with the reference ladder, but it
does not lie on a backward link.  This is an actual `Lambda` path and its
decoded route, not merely an abstract alternating trace.  The example
isolates one marker/source-overlap obstruction.  The legal ladder invariant
proved at the end excludes that overlap, but does not by itself establish
contact coverage: loop erasure can still hide earlier backward contacts.  The
final part therefore records the needed normalization step concretely, by
stopping the decoded trace at its first uncovered ladder contact and treating
that isolated contact as the switching terminal.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFiniteSourceRelaxedCounterexample

open DirectedPath Alternating

inductive Vertex
  | a | c | z | y
  deriving DecidableEq

open Vertex

def graph : Digraph Vertex where
  Adj u v :=
    (u = a ∧ v = c) ∨ (u = a ∧ v = z) ∨ (u = z ∧ v = y)

@[simp] theorem graph_adj (u v : Vertex) :
    graph.Adj u v ↔
      (u = a ∧ v = c) ∨ (u = a ∧ v = z) ∨ (u = z ∧ v = y) :=
  Iff.rfl

def ac : FinitePath graph where
  start := a
  finish := c
  walk := .cons (by simp [graph]) .nil
  isPath := by
    change [a, c].Nodup
    simp

@[simp] theorem ac_start : ac.start = a := rfl
@[simp] theorem ac_finish : ac.finish = c := rfl

@[simp] theorem ac_support : ac.support = ({a, c} : Set Vertex) := by
  ext v
  change v ∈ [a, c] ↔ _
  simp

@[simp] theorem ac_edgeSet :
    ac.walk.edgeSet = ({(a, c)} : Set (Vertex × Vertex)) := by
  simp [ac, DirectedPath.Walk.edgeSet]

def web : DWeb Vertex where
  graph := graph
  source := {a, z}
  target := {c, z, y}

def zPath : web.DPath := web.trivialPath z
def yPath : web.DPath := web.trivialPath y

@[simp] theorem acD_support :
    DirectedPath.Path.support (Sum.inl ac : web.DPath) =
      ({a, c} : Set Vertex) :=
  ac_support

@[simp] theorem acD_terminal :
    DirectedPath.Path.terminal? (Sum.inl ac : web.DPath) = some c :=
  rfl

@[simp] theorem acD_initial :
    DirectedPath.Path.initial (Sum.inl ac : web.DPath) = a :=
  rfl

def ladderPaths : Set web.DPath :=
  {(Sum.inl ac : web.DPath), zPath, yPath}

theorem ladderPaths_isWarp : web.IsWarp ladderPaths := by
  intro p hp q hq hpq
  simp only [ladderPaths, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl
  all_goals simp [Function.onFun, zPath, yPath] at hpq ⊢

def ladder : web.Warp := ⟨ladderPaths, ladderPaths_isWarp⟩

def input : PopularAuxiliary.Input web Empty where
  ladder := ladder
  groundedRecords := {(Sum.inl ac : web.DPath)}
  finiteSource := {c, z}
  markerSet := {z, y}
  proxyPath i := nomatch i
  proxy_isRay i := nomatch i

abbrev LV := PopularAuxiliary.Input.LambdaVertex Vertex Empty

@[simp] theorem input_ladder_paths : input.ladder.paths = ladderPaths := rfl
@[simp] theorem input_finiteSource : input.finiteSource = {c, z} := rfl
@[simp] theorem input_markerSet : input.markerSet = {z, y} := rfl

@[simp] theorem terminalFrontier_ladderPaths :
    web.terminalFrontier ladderPaths = ({c, z, y} : Set Vertex) := by
  ext v
  simp [ladderPaths, zPath, yPath, eq_comm]

@[simp] theorem web_essential_terminalFrontier :
    web.essential ({c, z, y} : Set Vertex) = {c, z, y} := by
  apply Set.Subset.antisymm (web.essential_subset _)
  intro v hv
  refine ⟨hv, ?_⟩
  rw [web.not_mem_roof_iff]
  refine ⟨FinitePath.trivial graph v, ⟨rfl, ?_⟩, ?_⟩
  · simpa [web] using hv
  · change Disjoint (FinitePath.trivial graph v).support
      ({c, z, y} \ {v})
    rw [FinitePath.support_trivial]
    exact Set.disjoint_sdiff_right

@[simp] theorem input_essentialLadder :
    input.essentialLadder = ladderPaths := by
  ext p
  constructor
  · exact fun hp ↦ hp.1
  · intro hp
    simp only [ladderPaths, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · refine ⟨by simp [ladderPaths], c, rfl, ?_⟩
      simp
    · refine ⟨by simp [ladderPaths], z, by simp [zPath], ?_⟩
      simp
    · refine ⟨by simp [ladderPaths], y, by simp [yPath], ?_⟩
      simp

@[simp] theorem input_targetMarkers :
    input.targetMarkers = ({z, y} : Set Vertex) := by
  ext v
  constructor
  · exact fun hv ↦ hv.1
  · intro hv
    refine ⟨hv, ?_⟩
    rw [input_essentialLadder]
    rcases hv with rfl | rfl
    · exact ⟨zPath, by simp [ladderPaths], by simp [zPath]⟩
    · exact ⟨yPath, by simp [ladderPaths], by simp [yPath]⟩

def cut : Set LV := {PopularAuxiliary.Input.LambdaVertex.old c}

@[simp] theorem cut_CV : GroundingCut.CV input cut = {c} := by
  ext v
  simp [cut, GroundingCut.CV, PopularAuxiliary.Input.oldPart]

@[simp] theorem cut_CE : GroundingCut.CE input cut = ∅ := by
  ext e
  simp [cut, GroundingCut.CE, PopularAuxiliary.Input.edgePart]

def wholeFragment : input.Fragment where
  path := Sum.inl ac
  parent := Sum.inl ac
  parent_mem := by simp [ladderPaths]
  support_subset := Subset.rfl
  edges_subset := Subset.rfl

theorem wholeFragment_mem_fragments :
    wholeFragment ∈ GroundingCut.fragments input cut := by
  constructor
  · rw [cut_CE]
    exact Set.disjoint_empty _
  · ext v
    constructor
    · intro hv
      refine ⟨hv, ?_⟩
      have hv' : v = a ∨ v = c := by
        change v ∈ ac.support at hv
        simpa using hv
      rcases hv' with rfl | rfl
      · refine ⟨FinitePath.trivial graph a, Or.inl ⟨rfl, rfl⟩,
          ?_, ?_, ?_⟩
        · intro w hw
          have hwa : w = a := by
            change w ∈ (FinitePath.trivial web.graph a).support at hw
            rw [FinitePath.support_trivial] at hw
            simpa using hw
          subst w
          change a ∈ ac.support
          simp
        · intro e he
          change e ∈ (FinitePath.trivial web.graph a).walk.edgeSet at he
          rw [FinitePath.trivial_walk] at he
          simpa using he
        · rw [cut_CE]
          exact Set.disjoint_empty _
      · refine ⟨ac, Or.inl ⟨rfl, rfl⟩, Subset.rfl, Subset.rfl, ?_⟩
        rw [cut_CE]
        exact Set.disjoint_empty _
    · exact fun hv ↦ hv.1

def escapePath : FinitePath input.lambda.graph where
  start := .old z
  finish := .old y
  walk := .cons (by
    rw [input.lambda_adj_old_old]
    exact ⟨Or.inr (by simp), Or.inr (by simp), by simp [web, graph]⟩) .nil
  isPath := by
    change [(.old z : LV), .old y].Nodup
    simp

theorem a_mem_escapeRegion : a ∈ input.escapeRegion cut := by
  exact ⟨{
    route := escapePath
    start_eq := Or.inr ⟨Or.inr (by simp), by simp [web, graph]⟩
    target := (input.mem_lambda_target_old y).2 (by simp)
    avoids := by
      change Disjoint escapePath.support cut
      rw [Set.disjoint_left]
      intro w hw hwc
      have hw' : w = (.old z : LV) ∨ w = .old y := by
        change w ∈ [(.old z : LV), .old y] at hw
        simpa using hw
      rcases hw' with rfl | rfl <;> simp [cut] at hwc
    old_not_mem := by simp [cut] }⟩

theorem initial_beforeEq {p : web.DPath} {v : Vertex}
    (hv : v ∈ p.support) : GroundingCut.BeforeEq p p.initial v := by
  cases p with
  | inl p =>
      obtain ⟨n, hn⟩ :=
        (GroundingCut.mem_support_iff_exists_occursAt (.inl p) v).1 hv
      refine ⟨0, n, ?_, hn, Nat.zero_le _⟩
      exact ⟨p.support_length_pos, p.support_getElem_zero⟩
  | inr r =>
      obtain ⟨n, hn⟩ :=
        (GroundingCut.mem_support_iff_exists_occursAt (.inr r) v).1 hv
      exact ⟨0, n, rfl, hn, Nat.zero_le _⟩

theorem wholeFragment_blockingPoint_eq_a :
    GroundingCut.blockingPoint input cut wholeFragment = a := by
  have hescape : PopularAuxiliary.Input.Fragment.MeetsEscape
      input cut wholeFragment := by
    exact ⟨a, by change a ∈ ac.support; simp, a_mem_escapeRegion⟩
  rw [GroundingCut.blockingPoint_eq_first_of_meetsEscape
    input cut wholeFragment hescape]
  apply GroundingCutDecoder.beforeEq_antisymm
  · exact GroundingCut.firstVertex_beforeEq wholeFragment.path
      (input.escapeRegion cut) hescape
      ⟨wholeFragment.path.initial_mem_support, a_mem_escapeRegion⟩
  · have hfirst : GroundingCut.firstVertex wholeFragment.path
        (input.escapeRegion cut) hescape ∈ wholeFragment.path.support :=
      (GroundingCut.firstVertex_mem wholeFragment.path
        (input.escapeRegion cut) hescape).1
    change GroundingCut.BeforeEq wholeFragment.path wholeFragment.path.initial
      (GroundingCut.firstVertex wholeFragment.path
        (input.escapeRegion cut) hescape)
    exact initial_beforeEq hfirst

/-- All hypotheses of the generic finite-source duplicate decoder hold in
the concrete input. -/
theorem duplicate_hypotheses :
    wholeFragment ∈ GroundingCut.fragments input cut ∧
      wholeFragment.path.terminal? = some c ∧
      PopularAuxiliary.Input.Fragment.MeetsEscape input cut wholeFragment ∧
      c ∈ input.finiteSource ∧ c ∈ GroundingCut.CV input cut ∧
      GroundingCut.blockingPoint input cut wholeFragment ≠ c := by
  refine ⟨wholeFragment_mem_fragments, rfl, ?_, by simp, by simp, ?_⟩
  · exact ⟨a, by change a ∈ ac.support; simp, a_mem_escapeRegion⟩
  · rw [wholeFragment_blockingPoint_eq_a]
    simp

theorem ac_mem_familyEdges : (a, c) ∈ input.familyEdges := by
  refine ⟨(Sum.inl ac : web.DPath), by simp [ladderPaths], ?_⟩
  change (a, c) ∈ ac.walk.edgeSet
  rw [ac_edgeSet]
  simp

/-- The private auxiliary path compiled by the reverse/escape splice. -/
def exchangePath : FinitePath input.lambda.graph where
  start := .old c
  finish := .old y
  walk := .cons (by
      exact (input.lambda_adj_old_edge c a c).2
        ⟨ac_mem_familyEdges, Or.inl rfl⟩)
    (.cons (by
        exact (input.lambda_adj_edge_old a c z).2
          ⟨ac_mem_familyEdges,
            Or.inr ⟨Or.inr (by simp), by simp [web, graph]⟩⟩)
      (.cons (by
          exact (input.lambda_adj_old_old z y).2
            ⟨Or.inr (by simp), Or.inr (by simp),
              by simp [web, graph]⟩) .nil))
  isPath := by
    change [(.old c : LV), .edge a c, .old z, .old y].Nodup
    simp

theorem exchangePath_start_source :
    exchangePath.start ∈ input.lambda.source := by
  rw [show exchangePath.start = (.old c : LV) from rfl,
    input.mem_lambda_source_old]
  simp

theorem exchangePath_finish_target :
    exchangePath.finish ∈ input.lambda.target := by
  rw [show exchangePath.finish = (.old y : LV) from rfl,
    input.mem_lambda_target_old]
  simp

theorem exchangePath_private :
    exchangePath.support ∩ cut = {(.old c : LV)} := by
  ext w
  change (w ∈ [(.old c : LV), .edge a c, .old z, .old y] ∧
      w ∈ cut) ↔ w ∈ ({(.old c : LV)} : Set LV)
  constructor
  · rintro ⟨_hw, hwc⟩
    simpa [cut] using hwc
  · intro hw
    have hwc : w = (.old c : LV) := by simpa using hw
    subst w
    constructor
    · simp
    · simp [cut]

def az : FinitePath graph where
  start := a
  finish := z
  walk := .cons (by simp [graph]) .nil
  isPath := by
    change [a, z].Nodup
    simp

@[simp] theorem az_support : az.support = ({a, z} : Set Vertex) := by
  ext v
  change v ∈ [a, z] ↔ _
  simp

@[simp] theorem az_edgeSet :
    az.walk.edgeSet = ({(a, z)} : Set (Vertex × Vertex)) := by
  simp [az, DirectedPath.Walk.edgeSet]

/-- The full forward escape retained by the unnormalized decoded route. -/
def ay : FinitePath graph where
  start := a
  finish := y
  walk := .cons (v := z) (by simp [graph])
    (.cons (by simp [graph]) .nil)
  isPath := by
    change [a, z, y].Nodup
    simp

@[simp] theorem ay_support : ay.support = ({a, z, y} : Set Vertex) := by
  ext v
  change v ∈ [a, z, y] ↔ _
  simp

@[simp] theorem ay_edgeSet :
    ay.walk.edgeSet = ({(a, z), (z, y)} : Set (Vertex × Vertex)) := by
  ext e
  simp [ay, DirectedPath.Walk.edgeSet]
  tauto

def backwardAC : Link graph where
  path := ac
  direction := .backward
  nontrivial := by simp

def forwardAZ : Link graph where
  path := az
  direction := .forward
  nontrivial := by
    change a ≠ z
    simp

def forwardAY : Link graph where
  path := ay
  direction := .forward
  nontrivial := by
    change a ≠ y
    simp

private def rawLink (i : Fin 2) : Link graph :=
  if i.1 = 0 then backwardAC else forwardAY

@[simp] private theorem rawLink_zero : rawLink 0 = backwardAC := by
  simp [rawLink]

@[simp] private theorem rawLink_one : rawLink 1 = forwardAY := by
  simp [rawLink]

/-- The unnormalized maximal-run presentation of the decoded route
`c <- a -> z -> y`. -/
def rawTrace : FiniteTrace graph where
  lastIndex := 1
  link := rawLink
  joins := by
    intro i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    simp [rawLink, backwardAC, forwardAY, Link.exit, Link.entry, ay]
  alternates := by
    intro i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    simp [backwardAC, forwardAY]
  compatible := by
    intro i j hij
    have hibound : i.1 < 2 := by simpa using i.isLt
    have hjbound : j.1 < 2 := by simpa using j.isLt
    have hiVal : i.1 = 0 := by omega
    have hjVal : j.1 = 1 := by omega
    have hi : i = (0 : Fin 2) := Fin.ext hiVal
    have hj : j = (1 : Fin 2) := Fin.ext hjVal
    subst i
    subst j
    simp only [rawLink_zero, rawLink_one]
    simp [CompatibleInOrder, backwardAC, forwardAY, Link.entry, Link.exit,
      Link.interior, ac_support, ay_support]

@[simp] theorem rawTrace_initial : rawTrace.initial = c := rfl
@[simp] theorem rawTrace_terminal : rawTrace.terminal = y := rfl

private def normalizedLink (i : Fin 2) : Link graph :=
  if i.1 = 0 then backwardAC else forwardAZ

@[simp] private theorem normalizedLink_zero :
    normalizedLink 0 = backwardAC := by simp [normalizedLink]

@[simp] private theorem normalizedLink_one :
    normalizedLink 1 = forwardAZ := by simp [normalizedLink]

/-- First-contact normalization of the bad private trace: stop at `z`
instead of retaining the rest of the escaping forward run. -/
def normalizedTrace : FiniteTrace graph where
  lastIndex := 1
  link := normalizedLink
  joins := by
    intro i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    rfl
  alternates := by
    intro i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    simp [backwardAC, forwardAZ]
  compatible := by
    intro i j hij
    have hibound : i.1 < 2 := by simpa using i.isLt
    have hjbound : j.1 < 2 := by simpa using j.isLt
    have hiVal : i.1 = 0 := by omega
    have hjVal : j.1 = 1 := by omega
    have hi : i = (0 : Fin 2) := Fin.ext hiVal
    have hj : j = (1 : Fin 2) := Fin.ext hjVal
    subst i
    subst j
    simp only [normalizedLink_zero, normalizedLink_one]
    simp [CompatibleInOrder, backwardAC, forwardAZ, Link.entry, Link.exit,
      Link.interior, ac_support, az_support]

@[simp] theorem normalizedTrace_initial : normalizedTrace.initial = c := rfl
@[simp] theorem normalizedTrace_terminal : normalizedTrace.terminal = z := rfl

@[simp] theorem familyEdges_ladderPaths :
    familyEdges ladderPaths = ({(a, c)} : Set (Vertex × Vertex)) := by
  ext e
  simp only [familyEdges, Set.mem_iUnion, ladderPaths,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨p, hp, he⟩
    rcases hp with rfl | rfl | rfl
    · change e ∈ ac.walk.edgeSet at he
      rw [ac_edgeSet] at he
      simpa using he
    · change e ∈ (FinitePath.trivial web.graph z).walk.edgeSet at he
      rw [FinitePath.trivial_walk] at he
      simp at he
    · change e ∈ (FinitePath.trivial web.graph y).walk.edgeSet at he
      rw [FinitePath.trivial_walk] at he
      simp at he
  · intro he
    refine ⟨(Sum.inl ac : web.DPath), Or.inl rfl, ?_⟩
    change e ∈ ac.walk.edgeSet
    rw [ac_edgeSet]
    simpa using he

@[simp] theorem vertexSet_ladderPaths :
    web.vertexSet ladderPaths = ({a, c, z, y} : Set Vertex) := by
  ext v
  simp [ladderPaths, zPath, yPath]
  tauto

@[simp] theorem initialSet_ladderPaths :
    web.initialSet ladderPaths = ({a, z, y} : Set Vertex) := by
  ext v
  simp [ladderPaths, zPath, yPath, eq_comm]

/-- The raw decoded trace fails precisely the strengthened contact-coverage
condition: its internal forward vertex `z` lies on the ladder, but no
backward link visits it and the raw trace terminates later at `y`. -/
theorem rawTrace_not_contactsCoveredAtTerminal :
    ¬ PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal
      web ladderPaths (.finite rawTrace) := by
  intro hcovered
  have hzForward : z ∈
      (AltPath.finite rawTrace).directionVertices .forward := by
    simp only [AltPath.directionVertices, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
    refine ⟨forwardAY, ⟨1, rfl⟩, rfl, ?_⟩
    change z ∈ ay.support
    simp
  have hzLadder : z ∈ web.vertexSet ladderPaths := by
    rw [vertexSet_ladderPaths]
    simp
  rcases hcovered hzForward hzLadder with hzBackward | hzTerminal
  · simp only [AltPath.directionVertices, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range] at hzBackward
    rcases hzBackward with ⟨l, ⟨i, rfl⟩, hdir, hz⟩
    have hibound : i.1 < 2 := by simpa [rawTrace] using i.isLt
    have hi : i.1 = 0 ∨ i.1 = 1 := by omega
    rcases hi with hi | hi
    · have hieq : i = (0 : Fin 2) := Fin.ext hi
      subst i
      change z ∈ ac.support at hz
      simp at hz
    · have hieq : i = (1 : Fin 2) := Fin.ext hi
      subst i
      simp [rawTrace, rawLink, forwardAY] at hdir
  · change some y = some z at hzTerminal
    have : y = z := Option.some.inj hzTerminal
    cases this

theorem normalizedTrace_backwardLinksOn :
    BackwardLinksOn ladderPaths (.finite normalizedTrace) := by
  intro l hl hdir
  simp only [AltPath.links, FiniteTrace.links, Set.mem_range] at hl
  obtain ⟨i, rfl⟩ := hl
  have hibound : i.1 < 2 := by simpa [normalizedTrace] using i.isLt
  have hi : i.1 = 0 ∨ i.1 = 1 := by omega
  rcases hi with hi | hi
  · have hieq : i = (0 : Fin 2) := Fin.ext hi
    subst i
    refine ⟨(Sum.inl ac : web.DPath), by simp [ladderPaths], ?_⟩
    exact FinitePath.isSubpathOf_self ac
  · have hieq : i = (1 : Fin 2) := Fin.ext hi
    subst i
    simp [normalizedTrace, normalizedLink, forwardAZ] at hdir

theorem normalizedTrace_forwardLinksOff :
    ForwardLinksOff ladderPaths (.finite normalizedTrace) := by
  intro l hl hdir
  simp only [AltPath.links, FiniteTrace.links, Set.mem_range] at hl
  obtain ⟨i, rfl⟩ := hl
  have hibound : i.1 < 2 := by simpa [normalizedTrace] using i.isLt
  have hi : i.1 = 0 ∨ i.1 = 1 := by omega
  rcases hi with hi | hi
  · have hieq : i = (0 : Fin 2) := Fin.ext hi
    subst i
    simp [normalizedTrace, normalizedLink, backwardAC] at hdir
  · have hieq : i = (1 : Fin 2) := Fin.ext hi
    subst i
    rw [familyEdges_ladderPaths]
    change Disjoint az.edgeSet ({(a, c)} : Set (Vertex × Vertex))
    rw [Set.disjoint_left]
    intro e heAZ heAC
    have heAZ' : e = (a, z) := by
      change e ∈ az.walk.edgeSet at heAZ
      simpa using heAZ
    have heAC' : e = (a, c) := by simpa using heAC
    cases Prod.mk.inj (heAZ'.symm.trans heAC')
    contradiction

theorem normalizedTrace_contactsCoveredAtTerminal :
    PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal
      web ladderPaths (.finite normalizedTrace) := by
  intro v hvForward hvLadder
  have hvF : v = a ∨ v = z := by
    simp only [AltPath.directionVertices, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range] at hvForward
    rcases hvForward with ⟨l, ⟨i, rfl⟩, hdir, hvl⟩
    have hibound : i.1 < 2 := by simpa [normalizedTrace] using i.isLt
    have hi : i.1 = 0 ∨ i.1 = 1 := by omega
    rcases hi with hi | hi
    · have hieq : i = (0 : Fin 2) := Fin.ext hi
      subst i
      simp [normalizedTrace, normalizedLink, backwardAC] at hdir
    · have hieq : i = (1 : Fin 2) := Fin.ext hi
      subst i
      change v ∈ az.support at hvl
      simpa using hvl
  rcases hvF with rfl | rfl
  · left
    simp only [AltPath.directionVertices, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
    refine ⟨backwardAC, ⟨0, ?_⟩, rfl, ?_⟩
    · rfl
    · change a ∈ ac.support
      simp
  · right
    rfl

/-- The first-contact-normalized private trace has the exact strengthened
terminal-relaxed alternation certificate required by the switching layer. -/
theorem normalizedTrace_isTerminalRelaxedAlternating :
    PopularAuxiliary.Input.IsTerminalRelaxedAlternating
      web ladderPaths (.finite normalizedTrace) := by
  refine ⟨ladderPaths_isWarp, normalizedTrace_backwardLinksOn,
    normalizedTrace_forwardLinksOff,
    normalizedTrace_contactsCoveredAtTerminal, ?_⟩
  intro hfirst
  change some normalizedTrace.firstLink.direction = some .forward at hfirst
  have hdir : normalizedTrace.firstLink.direction = .forward :=
    Option.some.inj hfirst
  change Direction.backward = Direction.forward at hdir
  cases hdir

/-- The normalized trace is immediately consumable by the terminal-contact
switch: its new terminal `z` is an isolated initial component of the
reference warp. -/
theorem normalizedTrace_terminalContactSwitching :
    IsTerminalContactSwitching ladderPaths normalizedTrace z := by
  refine IsTerminalContactSwitching.of_terminalRelaxed_isolated
    (u := z) normalizedTrace_isTerminalRelaxedAlternating rfl ?_ ?_ ?_
  · rw [initialSet_ladderPaths]
    simp
  · change web.trivialPath z ∈ ladderPaths
    simp [ladderPaths, zPath]
  · intro hout
    obtain ⟨w, hzw⟩ := hout
    simp only [AltPath.directionEdges, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range] at hzw
    rcases hzw with ⟨l, ⟨i, rfl⟩, hdir, he⟩
    have hibound : i.1 < 2 := by simpa [normalizedTrace] using i.isLt
    have hi : i.1 = 0 ∨ i.1 = 1 := by omega
    rcases hi with hi | hi
    · have hieq : i = 0 := Fin.ext hi
      subst i
      simp [normalizedTrace, normalizedLink, backwardAC] at hdir
    · have hieq : i = 1 := Fin.ext hi
      subst i
      change (z, w) ∈ az.walk.edgeSet at he
      rw [az_edgeSet] at he
      have : (z, w) = (a, z) := by simpa using he
      exact Vertex.noConfusion (congrArg Prod.fst this)

end GroundingFiniteSourceRelaxedCounterexample

namespace DWeb.KappaLadder

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Legality excludes exactly the marker/source overlap used by the generic
counterexample above.  A finite auxiliary source is the terminal of a
grounded recorded path, whereas target markers avoid the support of every
such record. -/
theorem finiteSource_disjoint_targetMarkers
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :
    Disjoint (L.popularAuxiliaryInput hlegal).finiteSource
      (L.popularAuxiliaryInput hlegal).targetMarkers := by
  rw [Set.disjoint_left]
  intro x hxFinite hxMarker
  change x ∈ L.groundedFiniteTerminalSet at hxFinite
  obtain ⟨a, ha, q, hchosen, hterminal⟩ := hxFinite
  have hrecord : q ∈
      (L.popularAuxiliaryInput hlegal).groundedRecords :=
    ⟨a, ha.1, hchosen⟩
  have hsupport : x ∈ q.support :=
    Gamma.terminal_mem_support hterminal
  exact Set.disjoint_left.1
    (L.groundedRecord_support_disjoint_targetMarkers hlegal hrecord)
    hsupport hxMarker

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.GroundingFiniteSourceRelaxedCounterexample.normalizedTrace_isTerminalRelaxedAlternating
#print axioms Erdos599.GroundingFiniteSourceRelaxedCounterexample.normalizedTrace_terminalContactSwitching
