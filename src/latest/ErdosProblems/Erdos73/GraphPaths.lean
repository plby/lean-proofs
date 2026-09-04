/-
Adapted from the Apache-2.0-licensed polynomial-grid-minor-theorem development,
https://github.com/EdouardBonnet/polynomial-grid-minor-theorem,
commit fe2848173913a00d85c64d2a17af63f2cf0d4fbf,
proofs/Lax17Proofs/Source/Paths.lean.
Local changes: import paths and namespace; Lean 4.33 compatibility changes.
-/
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import ErdosProblems.Erdos73.Degree

namespace Erdos73Infrastructure

universe u v w

/-!
# Paths and linkages for the grid-minor proof

This file formalizes the path-family language used in Section 2 of
Chuzhoy--Tan's proof of the polynomial grid-minor theorem.  A `GraphPath` is a
mathlib walk with no repeated vertices, bundled with its endpoints.  A
`PathPacking` is a finite indexed family of such paths connecting two finite
vertex sets.
-/

namespace SimpleGraph

namespace Walk

variable {V : Type*} {G H G' : _root_.SimpleGraph V}
variable {u v : V}

@[simp] theorem getVert_transfer (p : G.Walk u v)
    (hp : ∀ e, e ∈ p.edges → e ∈ H.edgeSet) (n : ℕ) :
    (p.transfer H hp).getVert n = p.getVert n := by
  induction p generalizing n with
  | nil =>
      simp
  | cons _ p ih =>
      cases n with
      | zero => simp
      | succ n =>
          change (p.transfer H _).getVert n = p.getVert n
          exact ih _ n

@[simp] theorem penultimate_transfer (p : G.Walk u v)
    (hp : ∀ e, e ∈ p.edges → e ∈ H.edgeSet) :
    (p.transfer H hp).penultimate = p.penultimate := by
  simp [_root_.SimpleGraph.Walk.penultimate]

@[simp] theorem getVert_mapLe (hGG' : G ≤ G') (p : G.Walk u v)
    (n : ℕ) :
    (p.mapLe hGG').getVert n = p.getVert n := by
  simpa [_root_.SimpleGraph.Walk.mapLe] using
    (_root_.SimpleGraph.Walk.getVert_map
      (f := _root_.SimpleGraph.Hom.ofLE hGG') (p := p) n)

@[simp] theorem penultimate_mapLe (hGG' : G ≤ G') (p : G.Walk u v) :
    (p.mapLe hGG').penultimate = p.penultimate := by
  have hlen : (p.mapLe hGG').length = p.length := by
    simpa [_root_.SimpleGraph.Walk.mapLe] using
      (_root_.SimpleGraph.Walk.length_map
        (f := _root_.SimpleGraph.Hom.ofLE hGG') (p := p))
  change (p.mapLe hGG').getVert ((p.mapLe hGG').length - 1) =
    p.getVert (p.length - 1)
  rw [hlen]
  simp

/-- In a nontrivial simple walk, the final endpoint does not occur in the
half-open support obtained by dropping the last vertex. -/
theorem end_not_mem_support_dropLast_toFinset_of_isPath [DecidableEq V]
    (p : G.Walk u v) (hp : p.IsPath) :
    v ∉ p.support.dropLast.toFinset := by
  classical
  intro hv
  have hvList : v ∈ p.support.dropLast := by
    simpa using hv
  have hconcat : p.support.dropLast ++ [v] = p.support := by
    have hlast : p.support.getLast p.support_ne_nil = v :=
      _root_.SimpleGraph.Walk.getLast_support p
    have hreplace :
        p.support.dropLast ++ [v] =
          p.support.dropLast ++
            [p.support.getLast p.support_ne_nil] :=
      congrArg (fun a => p.support.dropLast ++ [a]) hlast.symm
    exact hreplace.trans
      (List.dropLast_append_getLast (l := p.support) p.support_ne_nil)
  have hnodup : (p.support.dropLast ++ [v]).Nodup := by
    simpa [hconcat] using hp.support_nodup
  have hdisj : List.Disjoint p.support.dropLast [v] :=
    List.disjoint_of_nodup_append hnodup
  rw [List.disjoint_iff_ne] at hdisj
  exact hdisj v hvList v (by simp) rfl

end Walk

/-- A graph-theoretic path in a simple graph, bundled with its endpoints. -/
structure GraphPath {V : Type*} (G : _root_.SimpleGraph V) where
  /-- The first endpoint of the path. -/
  source : V
  /-- The second endpoint of the path. -/
  target : V
  /-- The underlying walk from `source` to `target`. -/
  walk : G.Walk source target
  /-- The walk has no repeated vertices. -/
  isPath : walk.IsPath

namespace GraphPath

variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}

/-- The length-zero path at a vertex. -/
def refl (G : _root_.SimpleGraph V) (v : V) : GraphPath G where
  source := v
  target := v
  walk := _root_.SimpleGraph.Walk.nil
  isPath := _root_.SimpleGraph.Walk.IsPath.nil

/-- The finite set of vertices appearing on a graph path. -/
noncomputable def vertexSet (P : GraphPath G) : Finset V :=
  P.walk.support.toFinset

/-- The finite set of edges appearing on a graph path. -/
noncomputable def edgeSet (P : GraphPath G) : Finset (Sym2 V) :=
  P.walk.edges.toFinset

/-- The penultimate vertex of a graph path, using mathlib's convention that it
is the unique vertex for a length-zero path. -/
def penultimate (P : GraphPath G) : V :=
  P.walk.penultimate

/-- Every edge of a graph path is an edge of the ambient graph. -/
theorem edgeSet_subset_edgeSet (P : GraphPath G) :
    ↑P.edgeSet ⊆ G.edgeSet := by
  intro e he
  exact P.walk.edges_subset_edgeSet (by simpa [edgeSet] using he)

/-- A vertex is one of the two endpoints of a graph path. -/
def IsEndpoint (P : GraphPath G) (v : V) : Prop :=
  v = P.source ∨ v = P.target

/-- Reverse the orientation of a graph path. -/
def reverse (P : GraphPath G) : GraphPath G where
  source := P.target
  target := P.source
  walk := P.walk.reverse
  isPath := P.isPath.reverse

omit [DecidableEq V] in
@[simp] theorem reverse_source (P : GraphPath G) :
    P.reverse.source = P.target := rfl

omit [DecidableEq V] in
@[simp] theorem reverse_target (P : GraphPath G) :
    P.reverse.target = P.source := rfl

@[simp] theorem reverse_vertexSet (P : GraphPath G) :
    P.reverse.vertexSet = P.vertexSet := by
  classical
  simp [reverse, vertexSet]

@[simp] theorem reverse_edgeSet (P : GraphPath G) :
    P.reverse.edgeSet = P.edgeSet := by
  classical
  simp [reverse, edgeSet]

@[simp] theorem source_mem_vertexSet (P : GraphPath G) :
    P.source ∈ P.vertexSet := by
  classical
  simp [vertexSet]

@[simp] theorem target_mem_vertexSet (P : GraphPath G) :
    P.target ∈ P.vertexSet := by
  classical
  simp [vertexSet]

omit [DecidableEq V] in
/-- A graph path with distinct endpoints has nonempty edge sequence. -/
theorem walk_not_nil_of_source_ne_target (P : GraphPath G)
    (h : P.source ≠ P.target) : ¬ P.walk.Nil := by
  intro hnil
  exact h hnil.eq

/-- The penultimate vertex of a nontrivial graph path lies on the path. -/
theorem penultimate_mem_vertexSet (P : GraphPath G)
    (h : P.source ≠ P.target) :
    P.penultimate ∈ P.vertexSet := by
  classical
  have hmemDrop :
      P.penultimate ∈ P.walk.support.dropLast :=
    P.walk.penultimate_mem_dropLast_support
      (P.walk_not_nil_of_source_ne_target h)
  simp [penultimate, vertexSet]

omit [DecidableEq V] in
/-- The final edge of a nontrivial graph path joins its penultimate vertex to
the target. -/
theorem penultimate_adj_target (P : GraphPath G)
    (h : P.source ≠ P.target) :
    G.Adj P.penultimate P.target := by
  simpa [penultimate] using
    P.walk.adj_penultimate (P.walk_not_nil_of_source_ne_target h)

omit [DecidableEq V] in
/-- Remove the last edge of a graph path, ending at the penultimate vertex. -/
def dropLast (P : GraphPath G) : GraphPath G where
  source := P.source
  target := P.penultimate
  walk := P.walk.dropLast
  isPath := by
    exact _root_.SimpleGraph.Walk.isPath_of_isSubwalk
      ((_root_.SimpleGraph.Walk.isSubwalk_rfl P.walk).dropLast) P.isPath

omit [DecidableEq V] in
@[simp] theorem dropLast_source (P : GraphPath G) :
    P.dropLast.source = P.source := rfl

omit [DecidableEq V] in
@[simp] theorem dropLast_target (P : GraphPath G) :
    P.dropLast.target = P.penultimate := rfl

@[simp] theorem dropLast_vertexSet_of_not_nil (P : GraphPath G)
    (h : P.source ≠ P.target) :
    P.dropLast.vertexSet = P.walk.support.dropLast.toFinset := by
  classical
  exact congrArg List.toFinset
    (P.walk.support_dropLast (P.walk_not_nil_of_source_ne_target h))

/-- The target of a nontrivial simple path is not in the drop-last path. -/
theorem target_not_mem_dropLast_vertexSet (P : GraphPath G)
    (h : P.source ≠ P.target) :
    P.target ∉ P.dropLast.vertexSet := by
  classical
  rw [P.dropLast_vertexSet_of_not_nil h]
  intro hv
  have hvList : P.target ∈ P.walk.support.dropLast := by
    simpa using hv
  have hconcat : P.walk.support.dropLast ++ [P.target] = P.walk.support := by
    have hlast : P.walk.support.getLast P.walk.support_ne_nil = P.target :=
      _root_.SimpleGraph.Walk.getLast_support P.walk
    have hreplace :
        P.walk.support.dropLast ++ [P.target] =
          P.walk.support.dropLast ++
            [P.walk.support.getLast P.walk.support_ne_nil] :=
      congrArg (fun a => P.walk.support.dropLast ++ [a]) hlast.symm
    exact hreplace.trans
      (List.dropLast_append_getLast (l := P.walk.support) P.walk.support_ne_nil)
  have hnodup : (P.walk.support.dropLast ++ [P.target]).Nodup := by
    simpa [hconcat] using P.isPath.support_nodup
  have hdisj : List.Disjoint P.walk.support.dropLast [P.target] :=
    List.disjoint_of_nodup_append hnodup
  rw [List.disjoint_iff_ne] at hdisj
  exact hdisj P.target hvList P.target (by simp) rfl

/-- On a nontrivial path, the vertex set is the drop-last vertex set together
with the target endpoint. -/
theorem mem_vertexSet_iff_mem_dropLast_or_eq_target (P : GraphPath G)
    (h : P.source ≠ P.target) (v : V) :
    v ∈ P.vertexSet ↔ v ∈ P.dropLast.vertexSet ∨ v = P.target := by
  classical
  have hconcat : P.walk.support.dropLast ++ [P.target] = P.walk.support := by
    have hlast : P.walk.support.getLast P.walk.support_ne_nil = P.target :=
      _root_.SimpleGraph.Walk.getLast_support P.walk
    have hreplace :
        P.walk.support.dropLast ++ [P.target] =
          P.walk.support.dropLast ++
            [P.walk.support.getLast P.walk.support_ne_nil] :=
      congrArg (fun a => P.walk.support.dropLast ++ [a]) hlast.symm
    exact hreplace.trans
      (List.dropLast_append_getLast (l := P.walk.support) P.walk.support_ne_nil)
  rw [P.dropLast_vertexSet_of_not_nil h]
  constructor
  · intro hv
    have hvSupport : v ∈ P.walk.support := by
      simpa [vertexSet] using hv
    have hvAppend : v ∈ P.walk.support.dropLast ++ [P.target] := by
      simpa [hconcat] using hvSupport
    rcases List.mem_append.mp hvAppend with hvDrop | hvTarget
    · exact Or.inl (by simpa using hvDrop)
    · exact Or.inr (by simpa using hvTarget)
  · rintro (hv | rfl)
    · have hvSupportDrop : v ∈ P.walk.support.dropLast := by
        simpa using hv
      have hvAppend : v ∈ P.walk.support.dropLast ++ [P.target] :=
        List.mem_append_left _ hvSupportDrop
      have hvSupport : v ∈ P.walk.support := by
        simpa [hconcat] using hvAppend
      exact by
        simpa [vertexSet] using hvSupport
    · exact P.target_mem_vertexSet

/-- If a non-target vertex is excluded from a path's allocated drop-last part,
then it is also excluded from the allocated drop-last part of the reversed
path. -/
theorem not_mem_reverse_dropLast_of_not_mem_dropLast_of_ne_target
    (P : GraphPath G) (h : P.source ≠ P.target) {v : V}
    (hnot : v ∉ P.dropLast.vertexSet) (hne : v ≠ P.target) :
    v ∉ P.reverse.dropLast.vertexSet := by
  intro hv
  have hvPath : v ∈ P.vertexSet := by
    have hvSupport : v ∈ P.reverse.walk.dropLast.support := by
      exact List.mem_toFinset.mp hv
    have hsub :
        P.reverse.walk.dropLast.support ⊆ P.reverse.walk.support :=
      ((_root_.SimpleGraph.Walk.isSubwalk_rfl P.reverse.walk).dropLast).support_subset
    have hvRev : v ∈ P.reverse.vertexSet := by
      simpa [vertexSet] using hsub hvSupport
    simpa using hvRev
  rcases (P.mem_vertexSet_iff_mem_dropLast_or_eq_target h v).1 hvPath with
    hvDrop | hvTarget
  · exact hnot hvDrop
  · exact hne hvTarget

/-- The drop-last path uses only vertices of the original path. -/
theorem dropLast_vertexSet_subset (P : GraphPath G) :
    P.dropLast.vertexSet ⊆ P.vertexSet := by
  intro v hv
  have hvSupport : v ∈ P.walk.dropLast.support := by
    exact List.mem_toFinset.mp hv
  have hsub :
      P.walk.dropLast.support ⊆ P.walk.support :=
    ((_root_.SimpleGraph.Walk.isSubwalk_rfl P.walk).dropLast).support_subset
  exact by
    simpa [vertexSet] using hsub hvSupport

/-- The initial segment of a graph path ending at a specified vertex on the
path. -/
noncomputable def takeUntil (P : GraphPath G) {v : V} (hv : v ∈ P.vertexSet) :
    GraphPath G where
  source := P.source
  target := v
  walk := P.walk.takeUntil v (by simpa [vertexSet] using hv)
  isPath := by
    exact _root_.SimpleGraph.Walk.isPath_of_isSubwalk
      (P.walk.isSubwalk_takeUntil (by simpa [vertexSet] using hv)) P.isPath

/-- The terminal segment of a graph path starting at a specified vertex on the
path. -/
noncomputable def dropUntil (P : GraphPath G) {v : V} (hv : v ∈ P.vertexSet) :
    GraphPath G where
  source := v
  target := P.target
  walk := P.walk.dropUntil v (by simpa [vertexSet] using hv)
  isPath := by
    exact _root_.SimpleGraph.Walk.isPath_of_isSubwalk
      (P.walk.isSubwalk_dropUntil (by simpa [vertexSet] using hv)) P.isPath

@[simp] theorem takeUntil_source (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.takeUntil hv).source = P.source := rfl

@[simp] theorem takeUntil_target (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.takeUntil hv).target = v := rfl

@[simp] theorem dropUntil_source (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.dropUntil hv).source = v := rfl

@[simp] theorem dropUntil_target (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.dropUntil hv).target = P.target := rfl

/-- An initial segment uses only vertices from the original path. -/
theorem takeUntil_vertexSet_subset (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.takeUntil hv).vertexSet ⊆ P.vertexSet := by
  classical
  intro x hx
  have hv' : v ∈ P.walk.support := by simpa [vertexSet] using hv
  have hx' : x ∈ (P.walk.takeUntil v hv').support := by
    simpa [takeUntil, vertexSet] using hx
  exact by
    simpa [vertexSet] using P.walk.support_takeUntil_subset hv' hx'

/-- A terminal segment uses only vertices from the original path. -/
theorem dropUntil_vertexSet_subset (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.dropUntil hv).vertexSet ⊆ P.vertexSet := by
  classical
  intro x hx
  have hv' : v ∈ P.walk.support := by simpa [vertexSet] using hv
  have hx' : x ∈ (P.walk.dropUntil v hv').support := by
    simpa [dropUntil, vertexSet] using hx
  exact by
    simpa [vertexSet] using P.walk.support_dropUntil_subset hv' hx'

/-- A terminal segment uses only edges from the original path. -/
theorem dropUntil_edgeSet_subset (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.dropUntil hv).edgeSet ⊆ P.edgeSet := by
  classical
  intro e he
  have hv' : v ∈ P.walk.support := by simpa [vertexSet] using hv
  have he' : e ∈ (P.walk.dropUntil v hv').edges := by
    simpa [dropUntil, edgeSet] using he
  exact by
    simpa [edgeSet] using P.walk.edges_dropUntil_subset hv' he'

/-- An initial segment uses only edges from the original path. -/
theorem takeUntil_edgeSet_subset (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.takeUntil hv).edgeSet ⊆ P.edgeSet := by
  classical
  intro e he
  have hv' : v ∈ P.walk.support := by simpa [vertexSet] using hv
  have he' : e ∈ (P.walk.takeUntil v hv').edges := by
    simpa [takeUntil, edgeSet] using he
  exact by
    simpa [edgeSet] using P.walk.edges_takeUntil_subset hv' he'

/-- An internal vertex of a simple graph path is incident with two distinct
edges of the path. -/
theorem exists_two_edgeSet_incident_of_mem_vertexSet_of_not_endpoint
    (P : GraphPath G) {x : V}
    (hx : x ∈ P.vertexSet) (hx_source : x ≠ P.source)
    (hx_target : x ≠ P.target) :
    ∃ e₁ ∈ P.edgeSet, x ∈ e₁ ∧
      ∃ e₂ ∈ P.edgeSet, x ∈ e₂ ∧ e₁ ≠ e₂ := by
  classical
  let Q := P.takeUntil hx
  have hQne : Q.source ≠ Q.target := by
    intro h
    exact hx_source (by simpa [Q] using h.symm)
  let e₁ : Sym2 V := s(Q.penultimate, Q.target)
  have he₁Qwalk : e₁ ∈ Q.walk.edges := by
    exact Q.walk.mk_penultimate_end_mem_edges
      (Q.walk_not_nil_of_source_ne_target hQne)
  have he₁Q : e₁ ∈ Q.edgeSet := by
    exact List.mem_toFinset.mpr (by simpa [Q, e₁, GraphPath.edgeSet] using he₁Qwalk)
  have he₁P : e₁ ∈ P.edgeSet := P.takeUntil_edgeSet_subset hx he₁Q
  have hx_e₁ : x ∈ e₁ := by
    simp [e₁, Q]
  let R := P.dropUntil hx
  have hRne : R.source ≠ R.target := by
    intro h
    exact hx_target (by simpa [R] using h)
  let e₂ : Sym2 V := s(R.source, R.walk.snd)
  have he₂Rwalk : e₂ ∈ R.walk.edges := by
    exact R.walk.mk_start_snd_mem_edges
      (R.walk_not_nil_of_source_ne_target hRne)
  have he₂R : e₂ ∈ R.edgeSet := by
    exact List.mem_toFinset.mpr (by simpa [R, e₂, GraphPath.edgeSet] using he₂Rwalk)
  have he₂P : e₂ ∈ P.edgeSet := P.dropUntil_edgeSet_subset hx he₂R
  have hx_e₂ : x ∈ e₂ := by
    simp [e₂, R]
  have hne : e₁ ≠ e₂ := by
    intro heq
    have hxwalk : x ∈ P.walk.support := by simpa [GraphPath.vertexSet] using hx
    have hdisj := P.isPath.isTrail.disjoint_edges_takeUntil_dropUntil hxwalk
    have he₁List : e₁ ∈ (P.walk.takeUntil x hxwalk).edges := by
      simpa [Q, e₁, GraphPath.takeUntil] using he₁Qwalk
    have he₂List : e₂ ∈ (P.walk.dropUntil x hxwalk).edges := by
      simpa [R, e₂, GraphPath.dropUntil] using he₂Rwalk
    exact hdisj he₁List (by simpa [heq] using he₂List)
  exact ⟨e₁, he₁P, hx_e₁, e₂, he₂P, hx_e₂, hne⟩

/-- If a simple graph path has equal endpoints, then every vertex on it is that
endpoint. -/
theorem eq_source_of_source_eq_target_of_mem_vertexSet
    (P : GraphPath G) (hst : P.source = P.target) {v : V}
    (hv : v ∈ P.vertexSet) :
    v = P.source := by
  cases P with
  | mk source target walk isPath =>
      dsimp at hst hv ⊢
      subst target
      have hwalk : walk = _root_.SimpleGraph.Walk.nil :=
        _root_.SimpleGraph.Walk.isPath_iff_eq_nil.mp isPath
      simpa [GraphPath.vertexSet, hwalk] using hv

/-- Any vertex on a nontrivial graph path is incident with some edge of the
path. -/
theorem exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
    (P : GraphPath G) (hne : P.source ≠ P.target)
    {x : V} (hx : x ∈ P.vertexSet) :
    ∃ e ∈ P.edgeSet, x ∈ e := by
  classical
  by_cases hxt : x = P.target
  · refine ⟨s(P.penultimate, P.target), ?_, ?_⟩
    · have hewalk :
          s(P.penultimate, P.target) ∈ P.walk.edges :=
        P.walk.mk_penultimate_end_mem_edges
          (P.walk_not_nil_of_source_ne_target hne)
      exact List.mem_toFinset.mpr (by simpa [GraphPath.penultimate] using hewalk)
    · simp [hxt]
  · let Q := P.dropUntil hx
    have hneQ : Q.source ≠ Q.target := by
      simpa [Q] using hxt
    refine ⟨s(Q.source, Q.walk.snd), ?_, ?_⟩
    · have heQwalk : s(Q.source, Q.walk.snd) ∈ Q.walk.edges :=
        Q.walk.mk_start_snd_mem_edges
          (Q.walk_not_nil_of_source_ne_target hneQ)
      have heQ : s(Q.source, Q.walk.snd) ∈ Q.edgeSet :=
        List.mem_toFinset.mpr (by simpa [GraphPath.edgeSet] using heQwalk)
      exact P.dropUntil_edgeSet_subset hx heQ
    · simp [Q]

/-- A graph path with distinct endpoints has a nonempty edge set. -/
theorem edgeSet_nonempty_of_source_ne_target
    (P : GraphPath G) (hne : P.source ≠ P.target) :
    P.edgeSet.Nonempty := by
  rcases P.exists_edgeSet_incident_of_mem_vertexSet_of_source_ne_target
      hne (GraphPath.source_mem_vertexSet P) with ⟨e, he, _⟩
  exact ⟨e, he⟩

/-- Splitting a path at a vertex and appending the two resulting pieces
recovers the original walk. -/
theorem takeUntil_append_dropUntil_walk (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    (P.takeUntil hv).walk.append (P.dropUntil hv).walk = P.walk := by
  have hv' : v ∈ P.walk.support := by simpa [vertexSet] using hv
  simp [takeUntil, dropUntil, P.walk.take_spec hv']

/-- The segment of a path between two vertices, when the second lies on the
terminal segment beginning at the first.  This formulation keeps the order
witness explicit and avoids committing later proofs to a particular numerical
indexing of vertices along the walk. -/
noncomputable def between (P : GraphPath G) {a b : V}
    (ha : a ∈ P.vertexSet) (hb : b ∈ (P.dropUntil ha).vertexSet) :
    GraphPath G :=
  (P.dropUntil ha).takeUntil hb

@[simp] theorem between_source (P : GraphPath G) {a b : V}
    (ha : a ∈ P.vertexSet) (hb : b ∈ (P.dropUntil ha).vertexSet) :
    (P.between ha hb).source = a := rfl

@[simp] theorem between_target (P : GraphPath G) {a b : V}
    (ha : a ∈ P.vertexSet) (hb : b ∈ (P.dropUntil ha).vertexSet) :
    (P.between ha hb).target = b := rfl

/-- A segment between two vertices of a path uses only vertices from the
original path. -/
theorem between_vertexSet_subset (P : GraphPath G) {a b : V}
    (ha : a ∈ P.vertexSet) (hb : b ∈ (P.dropUntil ha).vertexSet) :
    (P.between ha hb).vertexSet ⊆ P.vertexSet := by
  exact subset_trans
    ((P.dropUntil ha).takeUntil_vertexSet_subset hb)
    (P.dropUntil_vertexSet_subset ha)

/-- A segment between two vertices of a path uses only edges from the
original path. -/
theorem between_edgeSet_subset (P : GraphPath G) {a b : V}
    (ha : a ∈ P.vertexSet) (hb : b ∈ (P.dropUntil ha).vertexSet) :
    (P.between ha hb).edgeSet ⊆ P.edgeSet := by
  exact subset_trans
    ((P.dropUntil ha).takeUntil_edgeSet_subset hb)
    (P.dropUntil_edgeSet_subset ha)

/-- Vertex `a` appears no later than vertex `b` along an oriented graph path. -/
def Before (P : GraphPath G) (a b : V) : Prop :=
  ∃ ha : a ∈ P.vertexSet, b ∈ (P.dropUntil ha).vertexSet

/-- Every path vertex appears before itself. -/
theorem before_refl (P : GraphPath G) {a : V} (ha : a ∈ P.vertexSet) :
    P.Before a a := by
  exact ⟨ha, GraphPath.source_mem_vertexSet (P.dropUntil ha)⟩

/-- The path segment certified by a `Before` witness. -/
noncomputable def segmentOfBefore (P : GraphPath G) {a b : V}
    (h : P.Before a b) : GraphPath G :=
  P.between h.choose h.choose_spec

@[simp] theorem segmentOfBefore_source (P : GraphPath G) {a b : V}
    (h : P.Before a b) :
    (P.segmentOfBefore h).source = a := rfl

@[simp] theorem segmentOfBefore_target (P : GraphPath G) {a b : V}
    (h : P.Before a b) :
    (P.segmentOfBefore h).target = b := rfl

theorem segmentOfBefore_vertexSet_subset (P : GraphPath G) {a b : V}
    (h : P.Before a b) :
    (P.segmentOfBefore h).vertexSet ⊆ P.vertexSet :=
  P.between_vertexSet_subset h.choose h.choose_spec

/-- The path segment certified by a `Before` witness uses only edges from the
original path. -/
theorem segmentOfBefore_edgeSet_subset (P : GraphPath G) {a b : V}
    (h : P.Before a b) :
    (P.segmentOfBefore h).edgeSet ⊆ P.edgeSet :=
  P.between_edgeSet_subset h.choose h.choose_spec

/-- The zero-based position of a vertex in the support list of an oriented
path.  Vertices outside the path get the list length, following `List.idxOf`;
order lemmas below use it only for vertices known to lie on the path. -/
noncomputable def vertexIndex (P : GraphPath G) (v : V) : ℕ :=
  P.walk.support.idxOf v

private theorem list_idxOf_le_succ_of_sym2_mem_zipWith_tail
    {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    {a b : α}
    (hmem : s(a, b) ∈ List.zipWith (s(·, ·)) l l.tail) :
    l.idxOf b ≤ l.idxOf a + 1 := by
  classical
  rcases (List.exists_mem_iff_getElem
      (l := List.zipWith (s(·, ·)) l l.tail)
      (p := fun e : Sym2 α => e = s(a, b))).1 ⟨s(a, b), hmem, rfl⟩ with
    ⟨n, hn, hget⟩
  have hn_len : n + 1 < l.length := by
    have hn' : n < min l.length l.tail.length := by
      simpa [List.length_zipWith] using hn
    have htail : l.tail.length = l.length - 1 := List.length_tail
    omega
  have hn0 : n < l.length := by omega
  have hn1 : n + 1 < l.length := hn_len
  have htail_get :
      l.tail[n]'(by simpa [List.length_tail] using hn) =
        l[n + 1]'hn1 := by
    simp
  have hedge :
      s(l[n]'hn0, l[n + 1]'hn1) = s(a, b) := by
    simpa [List.getElem_zipWith, htail_get] using hget
  have hidx_n : l.idxOf (l[n]'hn0) = n :=
    hl.idxOf_getElem n hn0
  have hidx_succ : l.idxOf (l[n + 1]'hn1) = n + 1 :=
    hl.idxOf_getElem (n + 1) hn1
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hia : l.idxOf a = n := by simpa [← ha] using hidx_n
    have hib : l.idxOf b = n + 1 := by simpa [← hb] using hidx_succ
    omega
  · have hia : l.idxOf a = n + 1 := by simpa [← hb] using hidx_succ
    have hib : l.idxOf b = n := by simpa [← ha] using hidx_n
    omega

/-- If an unordered edge occurs in a simple path, the two endpoint indices
along the path differ by at most one in either orientation. -/
theorem edge_vertexIndex_le_succ (P : GraphPath G) {u v : V}
    (he : s(u, v) ∈ P.edgeSet) :
    P.vertexIndex v ≤ P.vertexIndex u + 1 := by
  classical
  have heWalk : s(u, v) ∈ P.walk.edges := by
    exact List.mem_toFinset.mp (by simpa [edgeSet] using he)
  rw [_root_.SimpleGraph.Walk.edges_eq_zipWith_support] at heWalk
  simpa [vertexIndex] using
    list_idxOf_le_succ_of_sym2_mem_zipWith_tail
      P.isPath.support_nodup heWalk

/-- Both endpoints of an edge used by a graph path occur on that path. -/
theorem endpoints_mem_vertexSet_of_edgeSet
    (P : GraphPath G) {x y : V}
    (he : s(x, y) ∈ P.edgeSet) :
    x ∈ P.vertexSet ∧ y ∈ P.vertexSet := by
  classical
  have heWalk : s(x, y) ∈ P.walk.edges :=
    List.mem_toFinset.mp (by simpa [GraphPath.edgeSet] using he)
  constructor
  · simpa [GraphPath.vertexSet] using
      P.walk.fst_mem_support_of_mem_edges heWalk
  · simpa [GraphPath.vertexSet] using
      P.walk.snd_mem_support_of_mem_edges heWalk

@[simp] theorem source_vertexIndex (P : GraphPath G) :
    P.vertexIndex P.source = 0 := by
  classical
  rw [vertexIndex]
  exact (List.idxOf_eq_zero_iff_head_eq P.walk.support_ne_nil).2 (by simp)

@[simp] theorem target_vertexIndex (P : GraphPath G) :
    P.vertexIndex P.target = P.walk.length := by
  classical
  rw [vertexIndex]
  have hidx :=
    P.isPath.support_nodup.idxOf_getElem P.walk.length
      (by rw [_root_.SimpleGraph.Walk.length_support]; exact Nat.lt_succ_self _)
  simpa [_root_.SimpleGraph.Walk.support_getElem_length] using hidx

/-- A graph path has as many distinct unordered edges as its walk length. -/
@[simp] theorem edgeSet_card (P : GraphPath G) :
    P.edgeSet.card = P.walk.length := by
  classical
  rw [edgeSet]
  calc
    P.walk.edges.toFinset.card = P.walk.edges.length :=
      List.toFinset_card_of_nodup P.isPath.isTrail.edges_nodup
    _ = P.walk.length := _root_.SimpleGraph.Walk.length_edges P.walk

private theorem list_idxOf_le_of_mem_drop_nodup {α : Type*} [DecidableEq α]
    {l : List α} (hl : l.Nodup) {a b : α} (ha : a ∈ l)
    (hb : b ∈ l.drop (l.idxOf a)) :
    l.idxOf a ≤ l.idxOf b := by
  classical
  let n := l.idxOf a
  have hnlt : n < l.length := by
    simpa [n] using (List.idxOf_lt_length_iff.2 ha)
  have hsplit : l.take n ++ l.drop n = l := List.take_append_drop n l
  have hnodup : (l.take n ++ l.drop n).Nodup := by
    simpa [hsplit] using hl
  have hdisj : List.Disjoint (l.take n) (l.drop n) :=
    List.disjoint_of_nodup_append hnodup
  have hbnot : b ∉ l.take n := by
    intro hb'
    exact hdisj hb' (by simpa [n] using hb)
  have hidx :
      (l.take n ++ l.drop n).idxOf b =
        (l.take n).length + (l.drop n).idxOf b :=
    List.idxOf_append_of_notMem hbnot
  have hlen_take : (l.take n).length = n := by
    simp [n, Nat.min_eq_left hnlt.le]
  calc
    l.idxOf a = n := rfl
    _ ≤ (l.take n).length + (l.drop n).idxOf b := by
      rw [hlen_take]
      omega
    _ = l.idxOf b := by
      simpa [hsplit] using hidx.symm

private theorem list_mem_drop_idxOf_of_le {α : Type*} [DecidableEq α]
    {l : List α} {a b : α} (hb : b ∈ l)
    (hidx : l.idxOf a ≤ l.idxOf b) :
    b ∈ l.drop (l.idxOf a) := by
  classical
  let n := l.idxOf a
  let m := l.idxOf b - n
  have hblt : l.idxOf b < l.length := List.idxOf_lt_length_iff.2 hb
  have hmlt : m < (l.drop n).length := by
    simp [m, n]
    omega
  refine List.mem_iff_getElem.2 ⟨m, hmlt, ?_⟩
  rw [List.getElem_drop]
  have hadd : n + m = l.idxOf b := by
    simp [m, n]
    omega
  have hsumlt : n + m < l.length := by
    have : m < l.length - n := by
      simpa [List.length_drop] using hmlt
    omega
  exact (getElem_congr (c := l) (d := l) rfl hadd hsumlt).trans
    (List.getElem_idxOf hblt)

private theorem list_idxOf_eq_add_idxOf_drop_of_mem_drop_nodup
    {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l.drop (l.idxOf a)) :
    l.idxOf b = l.idxOf a + (l.drop (l.idxOf a)).idxOf b := by
  classical
  let n := l.idxOf a
  have hnlt : n < l.length := by
    simpa [n] using (List.idxOf_lt_length_iff.2 ha)
  have hsplit : l.take n ++ l.drop n = l := List.take_append_drop n l
  have hnodup : (l.take n ++ l.drop n).Nodup := by
    simpa [hsplit] using hl
  have hdisj : List.Disjoint (l.take n) (l.drop n) :=
    List.disjoint_of_nodup_append hnodup
  have hbnot : b ∉ l.take n := by
    intro hb'
    exact hdisj hb' (by simpa [n] using hb)
  have hidx :
      (l.take n ++ l.drop n).idxOf b =
        (l.take n).length + (l.drop n).idxOf b :=
    List.idxOf_append_of_notMem hbnot
  have hlen_take : (l.take n).length = n := by
    simp [n, Nat.min_eq_left hnlt.le]
  calc
    l.idxOf b = (l.take n ++ l.drop n).idxOf b := by simp [hsplit]
    _ = (l.take n).length + (l.drop n).idxOf b := hidx
    _ = l.idxOf a + (l.drop (l.idxOf a)).idxOf b := by
      simp [n, hlen_take]

private theorem list_idxOf_le_of_mem_take_idxOf_succ
    {α : Type*} [DecidableEq α] {l : List α} {a b : α}
    (ha : a ∈ l.take (l.idxOf b + 1)) :
    l.idxOf a ≤ l.idxOf b := by
  have haList : a ∈ l := List.mem_of_mem_take ha
  have hlt : l.idxOf a < l.idxOf b + 1 := by
    simpa using (List.mem_take_iff_idxOf_lt haList).1 ha
  omega

theorem before_iff_vertexIndex_le (P : GraphPath G) {a b : V} :
    P.Before a b ↔
      a ∈ P.vertexSet ∧ b ∈ P.vertexSet ∧
        P.vertexIndex a ≤ P.vertexIndex b := by
  classical
  constructor
  · rintro ⟨ha, hb⟩
    have haSupport : a ∈ P.walk.support := by simpa [vertexSet] using ha
    have hbDrop :
        b ∈ P.walk.support.drop (P.walk.support.idxOf a) := by
      have hidxle : P.walk.support.idxOf a ≤ P.walk.length := by
        have hlt : P.walk.support.idxOf a < P.walk.support.length :=
          List.idxOf_lt_length_iff.2 haSupport
        rw [P.walk.length_support] at hlt
        omega
      have hbSupport :
          b ∈ (P.walk.dropUntil a haSupport).support := by
        simpa [dropUntil, vertexSet] using hb
      simpa [_root_.SimpleGraph.Walk.dropUntil_eq_drop,
        _root_.SimpleGraph.Walk.drop_support_eq_support_drop_min,
        Nat.min_eq_left hidxle] using hbSupport
    have hbSupport : b ∈ P.walk.support :=
      List.mem_of_mem_drop hbDrop
    exact ⟨ha, by simpa [vertexSet] using hbSupport,
      by
        simpa [vertexIndex] using
          list_idxOf_le_of_mem_drop_nodup P.isPath.support_nodup
            haSupport hbDrop⟩
  · rintro ⟨ha, hb, hidx⟩
    refine ⟨ha, ?_⟩
    have hbSupport : b ∈ P.walk.support := by simpa [vertexSet] using hb
    have hbDrop :
        b ∈ P.walk.support.drop (P.walk.support.idxOf a) :=
      list_mem_drop_idxOf_of_le hbSupport (by simpa [vertexIndex] using hidx)
    have haSupport : a ∈ P.walk.support := by simpa [vertexSet] using ha
    have hbDropUntil :
        b ∈ (P.walk.dropUntil a haSupport).support := by
      have hidxle : P.walk.support.idxOf a ≤ P.walk.length := by
        have hlt : P.walk.support.idxOf a < P.walk.support.length :=
          List.idxOf_lt_length_iff.2 haSupport
        rw [P.walk.length_support] at hlt
        omega
      simpa [_root_.SimpleGraph.Walk.dropUntil_eq_drop,
        _root_.SimpleGraph.Walk.drop_support_eq_support_drop_min,
        Nat.min_eq_left hidxle] using hbDrop
    simpa [dropUntil, vertexSet] using hbDropUntil

/-- The source of an oriented path occurs before every vertex of the path. -/
theorem source_before_of_mem (P : GraphPath G) {v : V} (hv : v ∈ P.vertexSet) :
    P.Before P.source v := by
  classical
  have hsourceIndex : P.vertexIndex P.source = 0 := by
    rw [vertexIndex]
    exact (List.idxOf_eq_zero_iff_head_eq P.walk.support_ne_nil).2 (by
      simp)
  refine (P.before_iff_vertexIndex_le).2
    ⟨GraphPath.source_mem_vertexSet P, hv, ?_⟩
  rw [hsourceIndex]
  exact Nat.zero_le _

/-- Every path vertex occurs before the target in the path order. -/
theorem before_target_of_mem (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    P.Before v P.target := by
  exact ⟨hv, by simpa using GraphPath.target_mem_vertexSet (P.dropUntil hv)⟩

/-- Dropping a path at its source leaves every original path vertex available. -/
theorem mem_dropUntil_source_of_mem (P : GraphPath G) {v : V}
    (hv : v ∈ P.vertexSet) :
    v ∈ (P.dropUntil (GraphPath.source_mem_vertexSet P)).vertexSet := by
  simpa using (P.source_before_of_mem hv).choose_spec

/-- The path order is transitive. -/
theorem before_trans (P : GraphPath G) {a b c : V}
    (hab : P.Before a b) (hbc : P.Before b c) :
    P.Before a c := by
  classical
  have hab' := (P.before_iff_vertexIndex_le).1 hab
  have hbc' := (P.before_iff_vertexIndex_le).1 hbc
  exact (P.before_iff_vertexIndex_le).2
    ⟨hab'.1, hbc'.2.1, Nat.le_trans hab'.2.2 hbc'.2.2⟩

/-- On a simple path, two vertices that occur before each other are equal. -/
theorem before_antisymm (P : GraphPath G) {a b : V}
    (hab : P.Before a b) (hba : P.Before b a) :
    a = b := by
  classical
  have hab' := (P.before_iff_vertexIndex_le).1 hab
  have hba' := (P.before_iff_vertexIndex_le).1 hba
  have hidx : P.vertexIndex a = P.vertexIndex b :=
    Nat.le_antisymm hab'.2.2 hba'.2.2
  have halt : P.vertexIndex a < P.walk.support.length := by
    simpa [vertexIndex, vertexSet] using
      (List.idxOf_lt_length_iff.2 (by simpa [vertexSet] using hab'.1 :
        a ∈ P.walk.support))
  have hblt : P.vertexIndex b < P.walk.support.length := by
    simpa [vertexIndex, vertexSet] using
      (List.idxOf_lt_length_iff.2 (by simpa [vertexSet] using hba'.1 :
        b ∈ P.walk.support))
  have halt' : P.walk.support.idxOf a < P.walk.support.length := by
    simpa [vertexIndex] using halt
  have hblt' : P.walk.support.idxOf b < P.walk.support.length := by
    simpa [vertexIndex] using hblt
  have ha_get :
      P.walk.support[P.vertexIndex a]'halt = a := by
    simp [vertexIndex]
  have hb_get :
      P.walk.support[P.vertexIndex b]'hblt = b := by
    simp [vertexIndex]
  have ha_get' :
      P.walk.support[P.vertexIndex b]'hblt = a := by
    simpa [hidx] using ha_get
  exact ha_get'.symm.trans hb_get

/-- If `b` occurs strictly after `a` on a simple path, then the suffix from
`b` no longer contains `a`. -/
theorem not_mem_dropUntil_of_mem_dropUntil_ne
    (P : GraphPath G) {a b : V} (ha : a ∈ P.vertexSet)
    (hb : b ∈ (P.dropUntil ha).vertexSet) (hne : b ≠ a) :
    a ∉ (P.dropUntil (P.dropUntil_vertexSet_subset ha hb)).vertexSet := by
  intro haSuffix
  have hab : P.Before a b := ⟨ha, hb⟩
  have hba : P.Before b a :=
    ⟨P.dropUntil_vertexSet_subset ha hb, haSuffix⟩
  exact hne (P.before_antisymm hba hab)

/-- If `b` lies on the suffix of a path starting at `a`, then the suffix
starting at `b` is contained in the suffix starting at `a`. -/
theorem dropUntil_vertexSet_subset_dropUntil_of_mem_dropUntil
    (P : GraphPath G) {a b : V} (ha : a ∈ P.vertexSet)
    (hb : b ∈ (P.dropUntil ha).vertexSet) :
    (P.dropUntil (P.dropUntil_vertexSet_subset ha hb)).vertexSet ⊆
      (P.dropUntil ha).vertexSet := by
  intro v hv
  have hab : P.Before a b := ⟨ha, hb⟩
  have hbv : P.Before b v :=
    ⟨P.dropUntil_vertexSet_subset ha hb, hv⟩
  exact (P.before_trans hab hbv).choose_spec

/-- The index of a vertex on a terminal segment is its offset in the terminal
segment plus the index of the segment source. -/
theorem vertexIndex_eq_add_vertexIndex_dropUntil (P : GraphPath G)
    {a v : V} (ha : a ∈ P.vertexSet)
    (hv : v ∈ (P.dropUntil ha).vertexSet) :
    P.vertexIndex v = P.vertexIndex a + (P.dropUntil ha).vertexIndex v := by
  classical
  have haSupport : a ∈ P.walk.support := by simpa [vertexSet] using ha
  have hidxle : P.walk.support.idxOf a ≤ P.walk.length := by
    have hlt : P.walk.support.idxOf a < P.walk.support.length :=
      List.idxOf_lt_length_iff.2 haSupport
    rw [P.walk.length_support] at hlt
    omega
  have hsupport :
      (P.walk.dropUntil a haSupport).support =
        P.walk.support.drop (P.walk.support.idxOf a) := by
    simp [_root_.SimpleGraph.Walk.dropUntil_eq_drop,
      _root_.SimpleGraph.Walk.drop_support_eq_support_drop_min,
      Nat.min_eq_left hidxle]
  have hvDrop :
      v ∈ P.walk.support.drop (P.walk.support.idxOf a) := by
    have hvSupport :
        v ∈ (P.walk.dropUntil a haSupport).support := by
      simpa [dropUntil, vertexSet] using hv
    simpa [hsupport] using hvSupport
  have hidx :=
    list_idxOf_eq_add_idxOf_drop_of_mem_drop_nodup
      P.isPath.support_nodup haSupport hvDrop
  simpa [vertexIndex, dropUntil, hsupport] using hidx

/-- Every vertex of a certified segment occurs after the segment source in the
ambient path. -/
theorem before_of_mem_segmentOfBefore_left (P : GraphPath G) {a b v : V}
    (h : P.Before a b) (hv : v ∈ (P.segmentOfBefore h).vertexSet) :
    P.Before a v := by
  exact ⟨h.choose,
    (P.dropUntil h.choose).takeUntil_vertexSet_subset h.choose_spec hv⟩

/-- Every vertex of a certified segment occurs before the segment target in the
ambient path. -/
theorem before_of_mem_segmentOfBefore_right (P : GraphPath G) {a b v : V}
    (h : P.Before a b) (hv : v ∈ (P.segmentOfBefore h).vertexSet) :
    P.Before v b := by
  classical
  let Q : GraphPath G := P.dropUntil h.choose
  have hbQ : b ∈ Q.vertexSet := by
    simpa [Q] using h.choose_spec
  have hvTakeSupport :
      v ∈ (Q.walk.takeUntil b (by simpa [vertexSet] using hbQ)).support := by
    simpa [Q, segmentOfBefore, between, takeUntil, vertexSet] using hv
  have hvTakeList :
      v ∈ Q.walk.support.take (Q.walk.support.idxOf b + 1) := by
    simpa [_root_.SimpleGraph.Walk.takeUntil_eq_take,
      _root_.SimpleGraph.Walk.take_support_eq_support_take_succ] using
      hvTakeSupport
  have hvQ : v ∈ Q.vertexSet := by
    exact by
      simpa [Q, vertexSet] using List.mem_of_mem_take hvTakeList
  have hidxQ : Q.vertexIndex v ≤ Q.vertexIndex b := by
    simpa [vertexIndex] using
      list_idxOf_le_of_mem_take_idxOf_succ hvTakeList
  have hPv :
      P.vertexIndex v = P.vertexIndex a + Q.vertexIndex v := by
    simpa [Q] using P.vertexIndex_eq_add_vertexIndex_dropUntil h.choose hvQ
  have hPb :
      P.vertexIndex b = P.vertexIndex a + Q.vertexIndex b := by
    simpa [Q] using P.vertexIndex_eq_add_vertexIndex_dropUntil h.choose hbQ
  have hvP : v ∈ P.vertexSet := P.segmentOfBefore_vertexSet_subset h hv
  have hbP : b ∈ P.vertexSet := ((P.before_iff_vertexIndex_le).1 h).2.1
  refine (P.before_iff_vertexIndex_le).2 ⟨hvP, hbP, ?_⟩
  rw [hPv, hPb]
  exact Nat.add_le_add_left hidxQ (P.vertexIndex a)

/-- Every vertex of the prefix `takeUntil b` occurs before `b` in the ambient
path. -/
theorem before_of_mem_takeUntil (P : GraphPath G) {b v : V}
    (hb : b ∈ P.vertexSet) (hv : v ∈ (P.takeUntil hb).vertexSet) :
    P.Before v b := by
  classical
  have hvTakeSupport :
      v ∈ (P.walk.takeUntil b (by simpa [vertexSet] using hb)).support := by
    simpa [takeUntil, vertexSet] using hv
  have hvTakeList :
      v ∈ P.walk.support.take (P.walk.support.idxOf b + 1) := by
    simpa [_root_.SimpleGraph.Walk.takeUntil_eq_take,
      _root_.SimpleGraph.Walk.take_support_eq_support_take_succ] using
      hvTakeSupport
  have hvP : v ∈ P.vertexSet := by
    simpa [vertexSet] using List.mem_of_mem_take hvTakeList
  have hidx : P.vertexIndex v ≤ P.vertexIndex b := by
    simpa [vertexIndex] using
      list_idxOf_le_of_mem_take_idxOf_succ hvTakeList
  exact (P.before_iff_vertexIndex_le).2 ⟨hvP, hb, hidx⟩

/-- If a vertex occurs before the target of a prefix, then it lies in that
prefix. -/
theorem mem_takeUntil_of_before (P : GraphPath G) {b v : V}
    (hb : b ∈ P.vertexSet) (hv : P.Before v b) :
    v ∈ (P.takeUntil hb).vertexSet := by
  classical
  have hv' := (P.before_iff_vertexIndex_le).1 hv
  have hvSupport : v ∈ P.walk.support := by
    simpa [vertexSet] using hv'.1
  have hvTakeList :
      v ∈ P.walk.support.take (P.walk.support.idxOf b + 1) := by
    have hidx : P.walk.support.idxOf v < P.walk.support.idxOf b + 1 := by
      simpa [vertexIndex] using Nat.lt_succ_of_le hv'.2.2
    exact (List.mem_take_iff_idxOf_lt hvSupport).2 hidx
  have hvTakeSupport :
      v ∈ (P.walk.takeUntil b (by simpa [vertexSet] using hb)).support := by
    simpa [_root_.SimpleGraph.Walk.takeUntil_eq_take,
      _root_.SimpleGraph.Walk.take_support_eq_support_take_succ] using
      hvTakeList
  simpa [takeUntil, vertexSet] using hvTakeSupport

/-- A vertex between the endpoints of a certified segment lies in the segment.
-/
theorem mem_segmentOfBefore_of_before_of_before (P : GraphPath G) {a b v : V}
    (h : P.Before a b) (hav : P.Before a v) (hvb : P.Before v b) :
    v ∈ (P.segmentOfBefore h).vertexSet := by
  classical
  let Q : GraphPath G := P.dropUntil h.choose
  have hbQ : b ∈ Q.vertexSet := by
    simpa [Q] using h.choose_spec
  have hvQ : v ∈ Q.vertexSet := by
    simpa [Q] using hav.choose_spec
  have hvbP := (P.before_iff_vertexIndex_le).1 hvb
  have hvPidx :
      P.vertexIndex v = P.vertexIndex a + Q.vertexIndex v := by
    simpa [Q] using P.vertexIndex_eq_add_vertexIndex_dropUntil h.choose hvQ
  have hbPidx :
      P.vertexIndex b = P.vertexIndex a + Q.vertexIndex b := by
    simpa [Q] using P.vertexIndex_eq_add_vertexIndex_dropUntil h.choose hbQ
  have hidxQ : Q.vertexIndex v ≤ Q.vertexIndex b := by
    omega
  have hv_before_b_Q : Q.Before v b :=
    (Q.before_iff_vertexIndex_le).2 ⟨hvQ, hbQ, hidxQ⟩
  have hvTake : v ∈ (Q.takeUntil hbQ).vertexSet :=
    Q.mem_takeUntil_of_before hbQ hv_before_b_Q
  simpa [segmentOfBefore, between, Q] using hvTake

/-- The first vertex of `P`, in the path order, that lies in a finite set
`U`, assuming `P` meets `U`. -/
noncomputable def firstHitVertex (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) : V :=
  Classical.choose (Finset.exists_min_image (P.vertexSet ∩ U) P.vertexIndex hne)

theorem firstHitVertex_spec (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    P.firstHitVertex U hne ∈ P.vertexSet ∩ U ∧
      ∀ v ∈ P.vertexSet ∩ U,
        P.vertexIndex (P.firstHitVertex U hne) ≤ P.vertexIndex v :=
  Classical.choose_spec
    (Finset.exists_min_image (P.vertexSet ∩ U) P.vertexIndex hne)

theorem firstHitVertex_mem_vertexSet (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    P.firstHitVertex U hne ∈ P.vertexSet :=
  (Finset.mem_inter.1 (P.firstHitVertex_spec U hne).1).1

theorem firstHitVertex_mem_set (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    P.firstHitVertex U hne ∈ U :=
  (Finset.mem_inter.1 (P.firstHitVertex_spec U hne).1).2

/-- Every later hit of `U` occurs after the first hit in the path order. -/
theorem firstHitVertex_before_of_mem_set (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) {v : V}
    (hvP : v ∈ P.vertexSet) (hvU : v ∈ U) :
    P.Before (P.firstHitVertex U hne) v := by
  refine (P.before_iff_vertexIndex_le).2
    ⟨P.firstHitVertex_mem_vertexSet U hne, hvP, ?_⟩
  exact (P.firstHitVertex_spec U hne).2 v (Finset.mem_inter.2 ⟨hvP, hvU⟩)

/-- A vertex of `U` on the prefix ending at the first hit is the first hit
itself. -/
theorem eq_firstHitVertex_of_mem_takeUntil_of_mem_set
    (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) {v : V}
    (hvPrefix :
      v ∈ (P.takeUntil (P.firstHitVertex_mem_vertexSet U hne)).vertexSet)
    (hvU : v ∈ U) :
    v = P.firstHitVertex U hne := by
  have hvP : v ∈ P.vertexSet :=
    P.takeUntil_vertexSet_subset (P.firstHitVertex_mem_vertexSet U hne) hvPrefix
  have hv_first : P.Before v (P.firstHitVertex U hne) :=
    P.before_of_mem_takeUntil (P.firstHitVertex_mem_vertexSet U hne) hvPrefix
  have hfirst_v : P.Before (P.firstHitVertex U hne) v :=
    P.firstHitVertex_before_of_mem_set U hne hvP hvU
  exact P.before_antisymm hv_first hfirst_v

/-- The prefix of `P` ending at its first hit of `U`. -/
noncomputable def cleanPrefixToSet (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) : GraphPath G :=
  P.takeUntil (P.firstHitVertex_mem_vertexSet U hne)

@[simp] theorem cleanPrefixToSet_source (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanPrefixToSet U hne).source = P.source := rfl

@[simp] theorem cleanPrefixToSet_target (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanPrefixToSet U hne).target = P.firstHitVertex U hne := rfl

theorem cleanPrefixToSet_target_mem (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanPrefixToSet U hne).target ∈ U := by
  simpa using P.firstHitVertex_mem_set U hne

theorem cleanPrefixToSet_vertexSet_subset (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanPrefixToSet U hne).vertexSet ⊆ P.vertexSet :=
  P.takeUntil_vertexSet_subset (P.firstHitVertex_mem_vertexSet U hne)

/-- The last vertex of `P`, in the path order, that lies in a finite set
`U`, assuming `P` meets `U`. -/
noncomputable def lastHitVertex (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) : V :=
  Classical.choose (Finset.exists_max_image (P.vertexSet ∩ U) P.vertexIndex hne)

theorem lastHitVertex_spec (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    P.lastHitVertex U hne ∈ P.vertexSet ∩ U ∧
      ∀ v ∈ P.vertexSet ∩ U,
        P.vertexIndex v ≤ P.vertexIndex (P.lastHitVertex U hne) :=
  Classical.choose_spec
    (Finset.exists_max_image (P.vertexSet ∩ U) P.vertexIndex hne)

theorem lastHitVertex_mem_vertexSet (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    P.lastHitVertex U hne ∈ P.vertexSet :=
  (Finset.mem_inter.1 (P.lastHitVertex_spec U hne).1).1

theorem lastHitVertex_mem_set (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    P.lastHitVertex U hne ∈ U :=
  (Finset.mem_inter.1 (P.lastHitVertex_spec U hne).1).2

/-- Every hit of `U` occurs before the last hit in the path order. -/
theorem before_lastHitVertex_of_mem_set (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) {v : V}
    (hvP : v ∈ P.vertexSet) (hvU : v ∈ U) :
    P.Before v (P.lastHitVertex U hne) := by
  refine (P.before_iff_vertexIndex_le).2
    ⟨hvP, P.lastHitVertex_mem_vertexSet U hne, ?_⟩
  exact (P.lastHitVertex_spec U hne).2 v (Finset.mem_inter.2 ⟨hvP, hvU⟩)

/-- A vertex of `U` on the suffix starting at the last hit is the last hit
itself. -/
theorem eq_lastHitVertex_of_mem_dropUntil_of_mem_set
    (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) {v : V}
    (hvSuffix :
      v ∈ (P.dropUntil (P.lastHitVertex_mem_vertexSet U hne)).vertexSet)
    (hvU : v ∈ U) :
    v = P.lastHitVertex U hne := by
  have hvP : v ∈ P.vertexSet :=
    P.dropUntil_vertexSet_subset (P.lastHitVertex_mem_vertexSet U hne) hvSuffix
  have hlast_v : P.Before (P.lastHitVertex U hne) v :=
    ⟨P.lastHitVertex_mem_vertexSet U hne, hvSuffix⟩
  have hv_last : P.Before v (P.lastHitVertex U hne) :=
    P.before_lastHitVertex_of_mem_set U hne hvP hvU
  exact P.before_antisymm hv_last hlast_v

/-- The suffix of `P` starting at its last hit of `U`. -/
noncomputable def cleanSuffixFromSet (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) : GraphPath G :=
  P.dropUntil (P.lastHitVertex_mem_vertexSet U hne)

@[simp] theorem cleanSuffixFromSet_source (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanSuffixFromSet U hne).source = P.lastHitVertex U hne := rfl

@[simp] theorem cleanSuffixFromSet_target (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanSuffixFromSet U hne).target = P.target := rfl

theorem cleanSuffixFromSet_source_mem (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanSuffixFromSet U hne).source ∈ U := by
  simpa using P.lastHitVertex_mem_set U hne

theorem cleanSuffixFromSet_vertexSet_subset (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanSuffixFromSet U hne).vertexSet ⊆ P.vertexSet :=
  P.dropUntil_vertexSet_subset (P.lastHitVertex_mem_vertexSet U hne)

/-- The last-hit suffix uses only edges from the original path. -/
theorem cleanSuffixFromSet_edgeSet_subset (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanSuffixFromSet U hne).edgeSet ⊆ P.edgeSet :=
  P.dropUntil_edgeSet_subset (P.lastHitVertex_mem_vertexSet U hne)

/-- A vertex strictly before the source of a certified segment is not on that
segment. -/
theorem not_mem_segmentOfBefore_of_before_source (P : GraphPath G)
    {a b z : V} (h : P.Before a b) (hz : P.Before z a)
    (hne : z ≠ a) :
    z ∉ (P.segmentOfBefore h).vertexSet := by
  intro hzmem
  exact hne (P.before_antisymm hz (P.before_of_mem_segmentOfBefore_left h hzmem))

/-- A vertex strictly after the target of a certified segment is not on that
segment. -/
theorem not_mem_segmentOfBefore_of_target_before (P : GraphPath G)
    {a b z : V} (h : P.Before a b) (hz : P.Before b z)
    (hne : z ≠ b) :
    z ∉ (P.segmentOfBefore h).vertexSet := by
  intro hzmem
  exact hne ((P.before_antisymm
    (P.before_of_mem_segmentOfBefore_right h hzmem) hz))

/-- A vertex strictly before the source of a certified segment is not in the
drop-last part of that segment. -/
theorem not_mem_segmentOfBefore_dropLast_of_before_source (P : GraphPath G)
    {a b z : V} (h : P.Before a b) (hz : P.Before z a)
    (hne : z ≠ a) :
    z ∉ (P.segmentOfBefore h).dropLast.vertexSet := by
  intro hzmem
  exact P.not_mem_segmentOfBefore_of_before_source h hz hne
    ((P.segmentOfBefore h).dropLast_vertexSet_subset hzmem)

/-- A vertex strictly after the target of a certified segment is not in the
drop-last part of that segment. -/
theorem not_mem_segmentOfBefore_dropLast_of_target_before (P : GraphPath G)
    {a b z : V} (h : P.Before a b) (hz : P.Before b z)
    (hne : z ≠ b) :
    z ∉ (P.segmentOfBefore h).dropLast.vertexSet := by
  intro hzmem
  exact P.not_mem_segmentOfBefore_of_target_before h hz hne
    ((P.segmentOfBefore h).dropLast_vertexSet_subset hzmem)

/-- If two certified segments of a simple path are ordered with the target of
the first before the source of the second, then any common vertex forces the
two boundary vertices to coincide and the common vertex is that boundary. -/
theorem eq_boundary_of_mem_segments_of_target_before_source
    (P : GraphPath G) {a b c d v : V}
    (hab : P.Before a b) (hcd : P.Before c d) (hbc : P.Before b c)
    (hvab : v ∈ (P.segmentOfBefore hab).vertexSet)
    (hvcd : v ∈ (P.segmentOfBefore hcd).vertexSet) :
    v = b ∧ b = c := by
  have hvb : P.Before v b :=
    P.before_of_mem_segmentOfBefore_right hab hvab
  have hcv : P.Before c v :=
    P.before_of_mem_segmentOfBefore_left hcd hvcd
  have hcb : P.Before c b := P.before_trans hcv hvb
  have hbc_eq : b = c := P.before_antisymm hbc hcb
  have hbv : P.Before b v := by
    simpa [hbc_eq] using hcv
  exact ⟨P.before_antisymm hvb hbv, hbc_eq⟩

/-- Disjointness of ordered half-open path segments. -/
theorem segmentOfBefore_dropLast_disjoint_of_target_before_source
    (P : GraphPath G) {a b c d : V}
    (hab : P.Before a b) (hcd : P.Before c d) (hbc : P.Before b c)
    (hne : a ≠ b) :
    Disjoint (P.segmentOfBefore hab).dropLast.vertexSet
      (P.segmentOfBefore hcd).dropLast.vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvab hvcd
  have hvabSeg :
      v ∈ (P.segmentOfBefore hab).vertexSet :=
    (P.segmentOfBefore hab).dropLast_vertexSet_subset hvab
  have hvcdSeg :
      v ∈ (P.segmentOfBefore hcd).vertexSet :=
    (P.segmentOfBefore hcd).dropLast_vertexSet_subset hvcd
  rcases P.eq_boundary_of_mem_segments_of_target_before_source hab hcd hbc
      hvabSeg hvcdSeg with ⟨rfl, _⟩
  exact (P.segmentOfBefore hab).target_not_mem_dropLast_vertexSet (by
    simpa using hne) hvab

/-- If two certified segments are ordered with a strict gap between the first
target and the second source, then their full vertex sets are disjoint. -/
theorem segmentOfBefore_disjoint_of_strict_target_before_source
    (P : GraphPath G) {a b c d : V}
    (hab : P.Before a b) (hcd : P.Before c d) (hbc : P.Before b c)
    (hne : b ≠ c) :
    Disjoint (P.segmentOfBefore hab).vertexSet
      (P.segmentOfBefore hcd).vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvab hvcd
  exact hne
    (P.eq_boundary_of_mem_segments_of_target_before_source hab hcd hbc
      hvab hvcd).2

/-- A reversed first segment is disjoint from a later segment when the first
target is strictly before the later source. -/
theorem reverse_segmentOfBefore_dropLast_disjoint_of_strict_target_before_source
    (P : GraphPath G) {a b c d : V}
    (hab : P.Before a b) (hcd : P.Before c d) (hbc : P.Before b c)
    (hne : b ≠ c) :
    Disjoint (P.segmentOfBefore hab).reverse.dropLast.vertexSet
      (P.segmentOfBefore hcd).dropLast.vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvab hvcd
  have hvabSeg :
      v ∈ (P.segmentOfBefore hab).vertexSet := by
    have hvRev :
        v ∈ (P.segmentOfBefore hab).reverse.vertexSet :=
      (P.segmentOfBefore hab).reverse.dropLast_vertexSet_subset hvab
    simpa using hvRev
  have hvcdSeg :
      v ∈ (P.segmentOfBefore hcd).vertexSet :=
    (P.segmentOfBefore hcd).dropLast_vertexSet_subset hvcd
  exact Finset.disjoint_left.mp
    (P.segmentOfBefore_disjoint_of_strict_target_before_source hab hcd hbc hne)
    hvabSeg hvcdSeg

/-- A segment is disjoint from the reversed form of a later segment when the
first target is strictly before the later source. -/
theorem segmentOfBefore_dropLast_disjoint_reverse_of_strict_target_before_source
    (P : GraphPath G) {a b c d : V}
    (hab : P.Before a b) (hcd : P.Before c d) (hbc : P.Before b c)
    (hne : b ≠ c) :
    Disjoint (P.segmentOfBefore hab).dropLast.vertexSet
      (P.segmentOfBefore hcd).reverse.dropLast.vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvab hvcd
  have hvabSeg :
      v ∈ (P.segmentOfBefore hab).vertexSet :=
    (P.segmentOfBefore hab).dropLast_vertexSet_subset hvab
  have hvcdSeg :
      v ∈ (P.segmentOfBefore hcd).vertexSet := by
    have hvRev :
        v ∈ (P.segmentOfBefore hcd).reverse.vertexSet :=
      (P.segmentOfBefore hcd).reverse.dropLast_vertexSet_subset hvcd
    simpa using hvRev
  exact Finset.disjoint_left.mp
    (P.segmentOfBefore_disjoint_of_strict_target_before_source hab hcd hbc hne)
    hvabSeg hvcdSeg

/-- Reversed ordered segments are disjoint when their underlying full segments
have a strict gap. -/
theorem reverse_segmentOfBefore_dropLast_disjoint_reverse_of_strict_target_before_source
    (P : GraphPath G) {a b c d : V}
    (hab : P.Before a b) (hcd : P.Before c d) (hbc : P.Before b c)
    (hne : b ≠ c) :
    Disjoint (P.segmentOfBefore hab).reverse.dropLast.vertexSet
      (P.segmentOfBefore hcd).reverse.dropLast.vertexSet := by
  rw [Finset.disjoint_left]
  intro v hvab hvcd
  have hvabSeg :
      v ∈ (P.segmentOfBefore hab).vertexSet := by
    have hvRev :
        v ∈ (P.segmentOfBefore hab).reverse.vertexSet :=
      (P.segmentOfBefore hab).reverse.dropLast_vertexSet_subset hvab
    simpa using hvRev
  have hvcdSeg :
      v ∈ (P.segmentOfBefore hcd).vertexSet := by
    have hvRev :
        v ∈ (P.segmentOfBefore hcd).reverse.vertexSet :=
      (P.segmentOfBefore hcd).reverse.dropLast_vertexSet_subset hvcd
    simpa using hvRev
  exact Finset.disjoint_left.mp
    (P.segmentOfBefore_disjoint_of_strict_target_before_source hab hcd hbc hne)
    hvabSeg hvcdSeg

/-- A path has a path-shaped trace on a finite vertex set when the vertices it
uses inside that set are exactly the vertices of another graph path. -/
def TraceOn (P : GraphPath G) (U : Finset V) : Prop :=
  ∃ Q : GraphPath G, Q.vertexSet = P.vertexSet ∩ U

/-- The vertices of a graph path induce a connected subgraph. -/
theorem connected_induce_vertexSet (P : GraphPath G) :
    (G.induce {v : V | v ∈ P.vertexSet}).Connected := by
  have hset :
      (↑P.vertexSet : Set V) = {v : V | v ∈ P.walk.support} := by
    ext v
    simp [vertexSet]
  rw [show {v : V | v ∈ P.vertexSet} = (↑P.vertexSet : Set V) by rfl]
  rw [hset]
  exact P.walk.connected_induce_support

/-- Cycle-erasure for a walk, packaged as a `GraphPath`.

This is the graph-path version of mathlib's `Walk.toPath`: it keeps the same
endpoints and chooses a simple subwalk of the original walk. -/
noncomputable def ofWalk {s t : V} (W : G.Walk s t) : GraphPath G where
  source := s
  target := t
  walk := W.toPath
  isPath := _root_.SimpleGraph.Path.isPath W.toPath

@[simp] theorem ofWalk_source {s t : V} (W : G.Walk s t) :
    (ofWalk W).source = s := rfl

@[simp] theorem ofWalk_target {s t : V} (W : G.Walk s t) :
    (ofWalk W).target = t := rfl

/-- The cycle-erased path uses only vertices of the original walk. -/
theorem ofWalk_vertexSet_subset {s t : V} (W : G.Walk s t) :
    (ofWalk W).vertexSet ⊆ W.support.toFinset := by
  classical
  intro v hv
  have hv_support :
      v ∈ ((W.toPath : G.Walk s t).support) := by
    simpa [ofWalk, vertexSet] using hv
  have hsub :
      (W.toPath : G.Walk s t).support ⊆ W.support :=
    _root_.SimpleGraph.Walk.support_toPath_subset W
  exact by
    simpa using hsub hv_support

/-- The cycle-erased path uses only edges of the original walk. -/
theorem ofWalk_edgeSet_subset {s t : V} (W : G.Walk s t) :
    (ofWalk W).edgeSet ⊆ W.edges.toFinset := by
  classical
  intro e he
  have he_edges :
      e ∈ ((W.toPath : G.Walk s t).edges) := by
    simpa [ofWalk, edgeSet] using he
  have hsub :
      (W.toPath : G.Walk s t).edges ⊆ W.edges :=
    _root_.SimpleGraph.Walk.edges_toPath_subset W
  exact by
    simpa using hsub he_edges

/-- Concatenate two compatible paths and erase any cycle in the resulting walk.

This is the primitive needed for rerouting operations that are naturally
described as concatenated walks followed by deletion of closed subwalks. -/
noncomputable def appendWithEqToPath (P Q : GraphPath G)
    (h : P.target = Q.source) : GraphPath G :=
  ofWalk (P.walk.append (Q.walk.copy h.symm rfl))

@[simp] theorem appendWithEqToPath_source (P Q : GraphPath G)
    (h : P.target = Q.source) :
    (P.appendWithEqToPath Q h).source = P.source := rfl

@[simp] theorem appendWithEqToPath_target (P Q : GraphPath G)
    (h : P.target = Q.source) :
    (P.appendWithEqToPath Q h).target = Q.target := rfl

/-- The cycle-erased concatenation uses only vertices of the two pieces. -/
theorem appendWithEqToPath_vertexSet_subset (P Q : GraphPath G)
    (h : P.target = Q.source) :
    (P.appendWithEqToPath Q h).vertexSet ⊆ P.vertexSet ∪ Q.vertexSet := by
  classical
  intro v hv
  have hvW :
      v ∈ (P.walk.append (Q.walk.copy h.symm rfl)).support.toFinset :=
    ofWalk_vertexSet_subset (P.walk.append (Q.walk.copy h.symm rfl)) hv
  simpa [appendWithEqToPath, vertexSet,
    _root_.SimpleGraph.Walk.mem_support_append_iff] using hvW

/-- The cycle-erased concatenation uses only edges of the two pieces. -/
theorem appendWithEqToPath_edgeSet_subset (P Q : GraphPath G)
    (h : P.target = Q.source) :
    (P.appendWithEqToPath Q h).edgeSet ⊆ P.edgeSet ∪ Q.edgeSet := by
  classical
  intro e he
  have heW :
      e ∈ (P.walk.append (Q.walk.copy h.symm rfl)).edges.toFinset :=
    ofWalk_edgeSet_subset (P.walk.append (Q.walk.copy h.symm rfl)) he
  simpa [appendWithEqToPath, edgeSet,
    _root_.SimpleGraph.Walk.edges_append] using heW

/-- Concatenate three compatible paths and erase cycles after the
concatenation.  The definition is expressed by two binary concatenations so it
can reuse the endpoint and support API for `appendWithEqToPath`. -/
noncomputable def append3WithEqToPath (P Q R : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source) :
    GraphPath G :=
  (P.appendWithEqToPath Q hPQ).appendWithEqToPath R (by simpa using hQR)

@[simp] theorem append3WithEqToPath_source (P Q R : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source) :
    (P.append3WithEqToPath Q R hPQ hQR).source = P.source := rfl

@[simp] theorem append3WithEqToPath_target (P Q R : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source) :
    (P.append3WithEqToPath Q R hPQ hQR).target = R.target := rfl

/-- The cycle-erased three-piece concatenation uses only vertices from the
three input paths. -/
theorem append3WithEqToPath_vertexSet_subset (P Q R : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source) :
    (P.append3WithEqToPath Q R hPQ hQR).vertexSet ⊆
      P.vertexSet ∪ Q.vertexSet ∪ R.vertexSet := by
  classical
  intro v hv
  have hv₂ :
      v ∈ (P.appendWithEqToPath Q hPQ).vertexSet ∪ R.vertexSet :=
    (P.appendWithEqToPath Q hPQ).appendWithEqToPath_vertexSet_subset R
      (by simpa using hQR) hv
  rcases Finset.mem_union.1 hv₂ with hvPQ | hvR
  · have hv₁ : v ∈ P.vertexSet ∪ Q.vertexSet :=
      P.appendWithEqToPath_vertexSet_subset Q hPQ hvPQ
    exact Finset.mem_union.2 (Or.inl hv₁)
  · exact Finset.mem_union.2 (Or.inr hvR)

/-- The cycle-erased three-piece concatenation uses only edges from the three
input paths. -/
theorem append3WithEqToPath_edgeSet_subset (P Q R : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source) :
    (P.append3WithEqToPath Q R hPQ hQR).edgeSet ⊆
      P.edgeSet ∪ Q.edgeSet ∪ R.edgeSet := by
  classical
  intro e he
  have he₂ :
      e ∈ (P.appendWithEqToPath Q hPQ).edgeSet ∪ R.edgeSet :=
    (P.appendWithEqToPath Q hPQ).appendWithEqToPath_edgeSet_subset R
      (by simpa using hQR) he
  rcases Finset.mem_union.1 he₂ with hePQ | heR
  · have he₁ : e ∈ P.edgeSet ∪ Q.edgeSet :=
      P.appendWithEqToPath_edgeSet_subset Q hPQ hePQ
    exact Finset.mem_union.2 (Or.inl he₁)
  · exact Finset.mem_union.2 (Or.inr heR)

/-- Concatenate four compatible paths and erase cycles after the
concatenation.  This is the path-level operation used by the cross
replacement: retained row piece, transversal segment, retained row piece, and
then any later cleanup can again be treated as a graph path. -/
noncomputable def append4WithEqToPath (P Q R S : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source)
    (hRS : R.target = S.source) : GraphPath G :=
  (P.append3WithEqToPath Q R hPQ hQR).appendWithEqToPath S (by simpa using hRS)

@[simp] theorem append4WithEqToPath_source (P Q R S : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source)
    (hRS : R.target = S.source) :
    (P.append4WithEqToPath Q R S hPQ hQR hRS).source = P.source := rfl

@[simp] theorem append4WithEqToPath_target (P Q R S : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source)
    (hRS : R.target = S.source) :
    (P.append4WithEqToPath Q R S hPQ hQR hRS).target = S.target := rfl

/-- The cycle-erased four-piece concatenation uses only vertices from the
four input paths. -/
theorem append4WithEqToPath_vertexSet_subset (P Q R S : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source)
    (hRS : R.target = S.source) :
    (P.append4WithEqToPath Q R S hPQ hQR hRS).vertexSet ⊆
      P.vertexSet ∪ Q.vertexSet ∪ R.vertexSet ∪ S.vertexSet := by
  classical
  intro v hv
  have hv₂ :
      v ∈ (P.append3WithEqToPath Q R hPQ hQR).vertexSet ∪ S.vertexSet :=
    (P.append3WithEqToPath Q R hPQ hQR).appendWithEqToPath_vertexSet_subset S
      (by simpa using hRS) hv
  rcases Finset.mem_union.1 hv₂ with hvPQR | hvS
  · have hv₁ : v ∈ P.vertexSet ∪ Q.vertexSet ∪ R.vertexSet :=
      P.append3WithEqToPath_vertexSet_subset Q R hPQ hQR hvPQR
    exact Finset.mem_union.2 (Or.inl hv₁)
  · exact Finset.mem_union.2 (Or.inr hvS)

/-- The cycle-erased four-piece concatenation uses only edges from the four
input paths. -/
theorem append4WithEqToPath_edgeSet_subset (P Q R S : GraphPath G)
    (hPQ : P.target = Q.source) (hQR : Q.target = R.source)
    (hRS : R.target = S.source) :
    (P.append4WithEqToPath Q R S hPQ hQR hRS).edgeSet ⊆
      P.edgeSet ∪ Q.edgeSet ∪ R.edgeSet ∪ S.edgeSet := by
  classical
  intro e he
  have he₂ :
      e ∈ (P.append3WithEqToPath Q R hPQ hQR).edgeSet ∪ S.edgeSet :=
    (P.append3WithEqToPath Q R hPQ hQR).appendWithEqToPath_edgeSet_subset S
      (by simpa using hRS) he
  rcases Finset.mem_union.1 he₂ with hePQR | heS
  · have he₁ : e ∈ P.edgeSet ∪ Q.edgeSet ∪ R.edgeSet :=
      P.append3WithEqToPath_edgeSet_subset Q R hPQ hQR hePQR
    exact Finset.mem_union.2 (Or.inl he₁)
  · exact Finset.mem_union.2 (Or.inr heS)

/-- Choose a simple path between two vertices in a connected finite induced
subgraph. -/
noncomputable def ofConnectedInduce
    (U : Finset V)
    (hconn : (G.induce {v : V | v ∈ U}).Connected)
    (s t : V) (hs : s ∈ U) (ht : t ∈ U) : GraphPath G := by
  classical
  let Uset : Set V := {v : V | v ∈ U}
  let R :
      (G.induce Uset).Reachable
        (⟨s, by simpa [Uset] using hs⟩ : Uset)
        (⟨t, by simpa [Uset] using ht⟩ : Uset) :=
    hconn.preconnected _ _
  let W : (G.induce Uset).Walk
      (⟨s, by simpa [Uset] using hs⟩ : Uset)
      (⟨t, by simpa [Uset] using ht⟩ : Uset) :=
    Classical.choice R
  let Psub := W.toPath
  refine
    { source := s
      target := t
      walk := ?_
      isPath := ?_ }
  · exact (Psub : (G.induce Uset).Walk
      (⟨s, by simpa [Uset] using hs⟩ : Uset)
      (⟨t, by simpa [Uset] using ht⟩ : Uset)).map
        (_root_.SimpleGraph.Embedding.induce Uset).toHom
  · exact _root_.SimpleGraph.Walk.map_isPath_of_injective
      (f := (_root_.SimpleGraph.Embedding.induce Uset).toHom)
      (by
        intro a b h
        exact Subtype.ext h)
      Psub.property

/-- The path chosen in a connected induced subgraph stays inside the inducing
finite set. -/
theorem ofConnectedInduce_vertexSet_subset
    (U : Finset V)
    (hconn : (G.induce {v : V | v ∈ U}).Connected)
    (s t : V) (hs : s ∈ U) (ht : t ∈ U) :
    (ofConnectedInduce U hconn s t hs ht).vertexSet ⊆ U := by
  classical
  intro v hv
  let Uset : Set V := {v : V | v ∈ U}
  let R :
      (G.induce Uset).Reachable
        (⟨s, by simpa [Uset] using hs⟩ : Uset)
        (⟨t, by simpa [Uset] using ht⟩ : Uset) :=
    hconn.preconnected _ _
  let W : (G.induce Uset).Walk
      (⟨s, by simpa [Uset] using hs⟩ : Uset)
      (⟨t, by simpa [Uset] using ht⟩ : Uset) :=
    Classical.choice R
  let Psub := W.toPath
  let mapped :
      G.Walk s t :=
    (Psub : (G.induce Uset).Walk
      (⟨s, by simpa [Uset] using hs⟩ : Uset)
      (⟨t, by simpa [Uset] using ht⟩ : Uset)).map
        (_root_.SimpleGraph.Embedding.induce Uset).toHom
  have hvSupport : v ∈ mapped.support := by
    simpa [ofConnectedInduce, vertexSet, Uset, R, W, Psub, mapped] using hv
  have hvSupport' :
      v ∈ (((Psub : (G.induce Uset).Walk
        (⟨s, by simpa [Uset] using hs⟩ : Uset)
        (⟨t, by simpa [Uset] using ht⟩ : Uset)).map
          (_root_.SimpleGraph.Embedding.induce Uset).toHom).support) := by
    simpa [mapped] using hvSupport
  rw [_root_.SimpleGraph.Walk.support_map] at hvSupport'
  rcases List.mem_map.1 hvSupport' with ⟨w, _hw, hwv⟩
  subst hwv
  exact w.2

@[simp] theorem refl_vertexSet (v : V) :
    (GraphPath.refl G v).vertexSet = {v} := by
  classical
  simp [GraphPath.refl, vertexSet]

omit [DecidableEq V] in
@[simp] theorem refl_source (v : V) :
    (GraphPath.refl G v).source = v := rfl

omit [DecidableEq V] in
@[simp] theorem refl_target (v : V) :
    (GraphPath.refl G v).target = v := rfl

/-- Map a graph path to a supergraph on the same vertex type. -/
def mapLe (P : GraphPath G) {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    GraphPath H where
  source := P.source
  target := P.target
  walk := P.walk.mapLe hGH
  isPath := by
    rw [_root_.SimpleGraph.Walk.isPath_def]
    rw [_root_.SimpleGraph.Walk.support_mapLe_eq_support]
    exact P.isPath.support_nodup

@[simp] theorem mapLe_vertexSet (P : GraphPath G)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).vertexSet = P.vertexSet := by
  classical
  simp [mapLe, vertexSet, _root_.SimpleGraph.Walk.support_mapLe_eq_support]

@[simp] theorem mapLe_edgeSet (P : GraphPath G)
    {H : _root_.SimpleGraph V} (hGH : G ≤ H) :
    (P.mapLe hGH).edgeSet = P.edgeSet := by
  classical
  simp [mapLe, edgeSet, _root_.SimpleGraph.Walk.edges_mapLe_eq_edges]

/-- Transfer a graph path to another graph on the same vertex type, given that
the target graph contains all of the path's edges. -/
def transfer (P : GraphPath G) (H : _root_.SimpleGraph V)
    (h : ∀ e, e ∈ P.walk.edges → e ∈ H.edgeSet) : GraphPath H where
  source := P.source
  target := P.target
  walk := P.walk.transfer H h
  isPath := by
    rw [_root_.SimpleGraph.Walk.isPath_def]
    simpa using P.isPath.support_nodup

@[simp] theorem transfer_vertexSet (P : GraphPath G)
    (H : _root_.SimpleGraph V)
    (h : ∀ e, e ∈ P.walk.edges → e ∈ H.edgeSet) :
    (P.transfer H h).vertexSet = P.vertexSet := by
  classical
  simp [transfer, vertexSet]

@[simp] theorem transfer_edgeSet (P : GraphPath G)
    (H : _root_.SimpleGraph V)
    (h : ∀ e, e ∈ P.walk.edges → e ∈ H.edgeSet) :
    (P.transfer H h).edgeSet = P.edgeSet := by
  classical
  simp [transfer, edgeSet]

/-- Lift a graph path that stays in a finite vertex set to the graph induced
on that set. -/
noncomputable def induce (P : GraphPath G) (U : Finset V)
    (hU : P.vertexSet ⊆ U) : GraphPath (G.induce {v : V | v ∈ U}) where
  source := ⟨P.source, hU (GraphPath.source_mem_vertexSet P)⟩
  target := ⟨P.target, hU (GraphPath.target_mem_vertexSet P)⟩
  walk := P.walk.induce {v : V | v ∈ U} (by
    intro x hx
    exact hU (by simpa [GraphPath.vertexSet] using hx))
  isPath := by
    rw [_root_.SimpleGraph.Walk.isPath_def]
    rw [_root_.SimpleGraph.Walk.support_induce]
    have hmap :
        (List.map Subtype.val
          (P.walk.support.attachWith (Membership.mem {v : V | v ∈ U}) (by
            intro x hx
            exact hU (by simpa [GraphPath.vertexSet] using hx)))).Nodup := by
      simpa [List.map_attachWith] using P.isPath.support_nodup
    exact List.Nodup.of_map Subtype.val hmap

@[simp] theorem induce_source (P : GraphPath G) (U : Finset V)
    (hU : P.vertexSet ⊆ U) :
    (P.induce U hU).source =
      ⟨P.source, hU (GraphPath.source_mem_vertexSet P)⟩ := rfl

@[simp] theorem induce_target (P : GraphPath G) (U : Finset V)
    (hU : P.vertexSet ⊆ U) :
    (P.induce U hU).target =
      ⟨P.target, hU (GraphPath.target_mem_vertexSet P)⟩ := rfl

@[simp] theorem mem_induce_vertexSet (P : GraphPath G) (U : Finset V)
    (hU : P.vertexSet ⊆ U) (v : {x : V // x ∈ U}) :
    v ∈ (P.induce U hU).vertexSet ↔ v.1 ∈ P.vertexSet := by
  classical
  constructor
  · intro hv
    have hv_support :
        v ∈ (P.induce U hU).walk.support := by
      have hv' : v ∈ (P.induce U hU).walk.support.toFinset := by
        simpa [GraphPath.vertexSet] using hv
      exact List.mem_toFinset.mp hv'
    change v ∈ (_root_.SimpleGraph.Walk.induce (↑U : Set V) P.walk _).support
      at hv_support
    rw [_root_.SimpleGraph.Walk.support_induce] at hv_support
    simpa [GraphPath.vertexSet] using hv_support
  · intro hv
    have hv_support : v.1 ∈ P.walk.support := by
      simpa [GraphPath.vertexSet] using hv
    let hWalk : ∀ x ∈ P.walk.support, x ∈ (↑U : Set V) := by
      intro x hx
      exact hU (by simpa [GraphPath.vertexSet] using hx)
    have hv_induce :
        v ∈ (_root_.SimpleGraph.Walk.induce (↑U : Set V) P.walk hWalk).support := by
      rw [_root_.SimpleGraph.Walk.support_induce]
      simpa using hv_support
    have hv_induce' : v ∈ (P.induce U hU).walk.support := by
      change v ∈ (_root_.SimpleGraph.Walk.induce (↑U : Set V) P.walk _).support
      simpa using hv_induce
    have hv_fin : v ∈ (P.induce U hU).walk.support.toFinset :=
      List.mem_toFinset.mpr hv_induce'
    simpa [GraphPath.vertexSet] using hv_fin

@[simp] theorem mem_induce_edgeSet (P : GraphPath G) (U : Finset V)
    (hU : P.vertexSet ⊆ U) (e : Sym2 {x : V // x ∈ U}) :
    e ∈ (P.induce U hU).edgeSet ↔
      Sym2.map Subtype.val e ∈ P.edgeSet := by
  classical
  constructor
  · intro he
    have heWalk : e ∈ (P.induce U hU).walk.edges := by
      have heFin : e ∈ (P.induce U hU).walk.edges.toFinset := by
        simpa [GraphPath.edgeSet] using he
      exact (List.mem_toFinset.1 heFin)
    have hmap :
        Sym2.map Subtype.val e ∈
          ((P.induce U hU).walk.map
            (_root_.SimpleGraph.Embedding.induce (↑U : Set V)).toHom).edges := by
      rw [_root_.SimpleGraph.Walk.edges_map]
      exact List.mem_map.2 ⟨e, heWalk, rfl⟩
    have hmap' : Sym2.map Subtype.val e ∈ P.walk.edges := by
      change Sym2.map Subtype.val e ∈
        ((_root_.SimpleGraph.Walk.induce (↑U : Set V) P.walk _).map
          (_root_.SimpleGraph.Embedding.induce (↑U : Set V)).toHom).edges at hmap
      rwa [_root_.SimpleGraph.Walk.map_induce] at hmap
    simpa [GraphPath.edgeSet] using hmap'
  · intro he
    have heWalk : Sym2.map Subtype.val e ∈ P.walk.edges := by
      have heFin : Sym2.map Subtype.val e ∈ P.walk.edges.toFinset := by
        simpa [GraphPath.edgeSet] using he
      exact (List.mem_toFinset.1 heFin)
    have hmap :
        Sym2.map Subtype.val e ∈
          ((P.induce U hU).walk.map
            (_root_.SimpleGraph.Embedding.induce (↑U : Set V)).toHom).edges := by
      change Sym2.map Subtype.val e ∈
        ((_root_.SimpleGraph.Walk.induce (↑U : Set V) P.walk _).map
          (_root_.SimpleGraph.Embedding.induce (↑U : Set V)).toHom).edges
      rwa [_root_.SimpleGraph.Walk.map_induce]
    have hmapEdges :
        Sym2.map Subtype.val e ∈
          (P.induce U hU).walk.edges.map (Sym2.map Subtype.val) := by
      rw [_root_.SimpleGraph.Walk.edges_map] at hmap
      exact hmap
    rcases List.mem_map.1 hmapEdges with ⟨e', he', hproj⟩
    have heq : e' = e :=
      (Sym2.map.injective Subtype.val_injective) hproj
    have heFin : e ∈ (P.induce U hU).walk.edges := by
      simpa [heq] using he'
    exact List.mem_toFinset.mpr (by simpa [GraphPath.edgeSet] using heFin)

/-- A path is disjoint from a finite vertex set when none of its vertices lie in
the set. -/
def DisjointFromSet (P : GraphPath G) (U : Finset V) : Prop :=
  Disjoint P.vertexSet U

/-- A path is internally disjoint from `U` when every vertex it shares with `U`
is an endpoint of the path. -/
def InternallyDisjointFromSet (P : GraphPath G) (U : Finset V) : Prop :=
  ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ U → P.IsEndpoint v

/-- Cycle-erased concatenation preserves internal disjointness from `U` when
the glued vertex is outside `U`.

This variant does not require the two input paths to meet only at the glue
vertex: the cycle erasure uses only vertices from the concatenated walk, so
endpoint-cleanliness follows from endpoint-cleanliness of the two pieces and
the fact that the common glue cannot be a forbidden internal vertex. -/
theorem appendWithEqToPath_internallyDisjointFromSet
    (P Q : GraphPath G) (h : P.target = Q.source) {U : Finset V}
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.InternallyDisjointFromSet U)
    (hglue : P.target ∉ U) :
    (P.appendWithEqToPath Q h).InternallyDisjointFromSet U := by
  intro v hv hvU
  have hvUnion :
      v ∈ P.vertexSet ∪ Q.vertexSet :=
    P.appendWithEqToPath_vertexSet_subset Q h hv
  rcases Finset.mem_union.1 hvUnion with hvP | hvQ
  · rcases hP hvP hvU with hsource | htarget
    · exact Or.inl (by simpa [appendWithEqToPath] using hsource)
    · exact False.elim (hglue (by simpa [htarget] using hvU))
  · rcases hQ hvQ hvU with hsource | htarget
    · exact False.elim (hglue (by simpa [h, hsource] using hvU))
    · exact Or.inr (by simpa [appendWithEqToPath] using htarget)

/-- A prefix of an internally-disjoint path is internally disjoint from the
same finite set. -/
theorem takeUntil_internallyDisjointFromSet (P : GraphPath G)
    {b : V} (hb : b ∈ P.vertexSet) {U : Finset V}
    (hP : P.InternallyDisjointFromSet U) :
    (P.takeUntil hb).InternallyDisjointFromSet U := by
  intro v hvPrefix hvU
  have hvP : v ∈ P.vertexSet :=
    P.takeUntil_vertexSet_subset hb hvPrefix
  rcases hP hvP hvU with hsrc | htgt
  · exact Or.inl (by simp [hsrc])
  · have hbefore : P.Before P.target b := by
      simpa [htgt] using P.before_of_mem_takeUntil hb hvPrefix
    have htarget_before : P.Before b P.target :=
      P.before_target_of_mem hb
    have htarget_eq : P.target = b :=
      P.before_antisymm hbefore htarget_before
    exact Or.inr (by simp [htgt, htarget_eq])

/-- A suffix of an internally-disjoint path is internally disjoint from the
same finite set. -/
theorem dropUntil_internallyDisjointFromSet (P : GraphPath G)
    {b : V} (hb : b ∈ P.vertexSet) {U : Finset V}
    (hP : P.InternallyDisjointFromSet U) :
    (P.dropUntil hb).InternallyDisjointFromSet U := by
  intro v hvSuffix hvU
  have hvP : v ∈ P.vertexSet :=
    P.dropUntil_vertexSet_subset hb hvSuffix
  rcases hP hvP hvU with hsrc | htgt
  · have hbefore : P.Before b P.source := by
      exact ⟨hb, by simpa [hsrc] using hvSuffix⟩
    have hsource_before : P.Before P.source b :=
      P.source_before_of_mem hb
    have hsource_eq : P.source = b :=
      P.before_antisymm hsource_before hbefore
    exact Or.inl (by simp [hsrc, hsource_eq])
  · exact Or.inr (by simp [htgt])

/-- The first-hit prefix is internally disjoint from the set it first hits. -/
theorem cleanPrefixToSet_internallyDisjointFromSet
    (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanPrefixToSet U hne).InternallyDisjointFromSet U := by
  intro v hvPrefix hvU
  exact Or.inr (by
    dsimp [cleanPrefixToSet]
    exact P.eq_firstHitVertex_of_mem_takeUntil_of_mem_set U hne hvPrefix hvU)

/-- The first-hit prefix meets the set it enters in exactly its target
vertex. -/
theorem cleanPrefixToSet_inter_eq_singleton_target
    (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    U ∩ (P.cleanPrefixToSet U hne).vertexSet =
      {(P.cleanPrefixToSet U hne).target} := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.1 hv with ⟨hvU, hvPrefix⟩
    have hvfirst :
        v = P.firstHitVertex U hne :=
      P.eq_firstHitVertex_of_mem_takeUntil_of_mem_set U hne hvPrefix hvU
    simpa [cleanPrefixToSet] using hvfirst
  · intro hv
    have hvtarget : v = (P.cleanPrefixToSet U hne).target := by
      simpa using hv
    subst hvtarget
    exact Finset.mem_inter.2
      ⟨P.cleanPrefixToSet_target_mem U hne,
        GraphPath.target_mem_vertexSet (P.cleanPrefixToSet U hne)⟩

/-- The last-hit suffix is internally disjoint from the set it last leaves. -/
theorem cleanSuffixFromSet_internallyDisjointFromSet
    (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    (P.cleanSuffixFromSet U hne).InternallyDisjointFromSet U := by
  intro v hvSuffix hvU
  exact Or.inl (by
    dsimp [cleanSuffixFromSet]
    exact P.eq_lastHitVertex_of_mem_dropUntil_of_mem_set U hne hvSuffix hvU)

/-- The last-hit suffix meets the set it leaves in exactly its source vertex. -/
theorem cleanSuffixFromSet_inter_eq_singleton_source
    (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) :
    U ∩ (P.cleanSuffixFromSet U hne).vertexSet =
      {(P.cleanSuffixFromSet U hne).source} := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.1 hv with ⟨hvU, hvSuffix⟩
    have hvlast :
        v = P.lastHitVertex U hne :=
      P.eq_lastHitVertex_of_mem_dropUntil_of_mem_set U hne hvSuffix hvU
    simpa [cleanSuffixFromSet] using hvlast
  · intro hv
    have hvsource : v = (P.cleanSuffixFromSet U hne).source := by
      simpa using hv
    subst hvsource
    exact Finset.mem_inter.2
      ⟨P.cleanSuffixFromSet_source_mem U hne,
        GraphPath.source_mem_vertexSet (P.cleanSuffixFromSet U hne)⟩

/-- Reversing a path preserves internal disjointness from a vertex set. -/
theorem reverse_internallyDisjointFromSet (P : GraphPath G) (U : Finset V) :
    P.reverse.InternallyDisjointFromSet U ↔ P.InternallyDisjointFromSet U := by
  constructor
  · intro h v hv hU
    have hend := h (by simpa using hv) hU
    rcases hend with hvtarget | hvsource
    · exact Or.inr hvtarget
    · exact Or.inl hvsource
  · intro h v hv hU
    have hend := h (by simpa using hv) hU
    rcases hend with hvsource | hvtarget
    · exact Or.inr hvsource
    · exact Or.inl hvtarget

/-- If a path is internally disjoint from `U` and starts outside `U`, then
any intersection with a path contained in `U` is forced to occur at its target.
-/
theorem eq_target_of_internallyDisjointFromSet_of_subset_of_source_not_mem
    (P Q : GraphPath G) {U : Finset V}
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource : P.source ∉ U)
    {v : V} (hvP : v ∈ P.vertexSet) (hvQ : v ∈ Q.vertexSet) :
    v = P.target := by
  rcases hP hvP (hQ hvQ) with hsrc | htgt
  · exact False.elim (hsource (by simpa [hsrc] using hQ hvQ))
  · exact htgt

/-- A vertex of degree exactly one in the ambient graph can appear on a simple
path only as one of the two endpoints of that path. -/
theorem isEndpoint_of_mem_vertexSet_of_degreeEquals_one
    (P : GraphPath G) {v : V}
    (hdeg : DegreeEquals G v 1) (hv : v ∈ P.vertexSet) :
    P.IsEndpoint v := by
  classical
  by_cases hsource : v = P.source
  · exact Or.inl hsource
  by_cases htarget : v = P.target
  · exact Or.inr htarget
  exfalso
  have hvSupport : v ∈ P.walk.support := by
    simpa [vertexSet] using hv
  rcases _root_.SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvSupport with
    ⟨n, hn, hnle⟩
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    apply hsource
    simpa [hn0] using hn.symm
  have hn_lt_length : n < P.walk.length := by
    by_contra hnot
    have hnlen : n = P.walk.length := by omega
    apply htarget
    simpa [hnlen] using hn.symm
  have hprev_adj :
      G.Adj v (P.walk.getVert (n - 1)) := by
    have hsub :
        P.walk.toSubgraph.Adj (P.walk.getVert (n - 1))
          (P.walk.getVert ((n - 1) + 1)) :=
      P.walk.toSubgraph_adj_getVert (by omega)
    have hsub' :
        P.walk.toSubgraph.Adj (P.walk.getVert (n - 1)) v := by
      simpa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn_ne_zero), hn] using hsub
    exact (P.walk.toSubgraph.adj_sub hsub').symm
  have hnext_adj :
      G.Adj v (P.walk.getVert (n + 1)) := by
    have hsub :
        P.walk.toSubgraph.Adj (P.walk.getVert n)
          (P.walk.getVert (n + 1)) :=
      P.walk.toSubgraph_adj_getVert hn_lt_length
    have hsub' :
        P.walk.toSubgraph.Adj v (P.walk.getVert (n + 1)) := by
      simpa [hn] using hsub
    exact P.walk.toSubgraph.adj_sub hsub'
  have hprev_ne_next :
      P.walk.getVert (n - 1) ≠ P.walk.getVert (n + 1) := by
    intro hsame
    have hidx := P.isPath.getVert_injOn
      (by exact (show n - 1 ≤ P.walk.length by omega))
      (by exact (show n + 1 ≤ P.walk.length by omega))
      hsame
    omega
  exact hprev_ne_next (DegreeEquals.one_adj_eq hdeg hprev_adj hnext_adj)

/-- Two paths are node-disjoint when their vertex sets are disjoint. -/
def NodeDisjoint (P Q : GraphPath G) : Prop :=
  Disjoint P.vertexSet Q.vertexSet

theorem nodeDisjoint_symm {P Q : GraphPath G}
    (h : P.NodeDisjoint Q) : Q.NodeDisjoint P :=
  h.symm

/-- If a path is contained in the union of two paths, and both of those paths
are node-disjoint from a fourth path, then the contained path is also
node-disjoint from the fourth path. -/
theorem nodeDisjoint_of_vertexSet_subset_union_left
    {P Q R W : GraphPath G}
    (hsub : R.vertexSet ⊆ P.vertexSet ∪ Q.vertexSet)
    (hP : P.NodeDisjoint W) (hQ : Q.NodeDisjoint W) :
    R.NodeDisjoint W := by
  rw [NodeDisjoint, Finset.disjoint_left]
  intro v hvR hvW
  rcases Finset.mem_union.1 (hsub hvR) with hvP | hvQ
  · exact Finset.disjoint_left.mp hP hvP hvW
  · exact Finset.disjoint_left.mp hQ hvQ hvW

/-- If two paths are each contained in a union of two paths, and all four
cross-pairs are node-disjoint, then the contained paths are node-disjoint. -/
theorem nodeDisjoint_of_vertexSet_subset_union_union
    {A B C D R W : GraphPath G}
    (hR : R.vertexSet ⊆ A.vertexSet ∪ B.vertexSet)
    (hW : W.vertexSet ⊆ C.vertexSet ∪ D.vertexSet)
    (hAC : A.NodeDisjoint C) (hAD : A.NodeDisjoint D)
    (hBC : B.NodeDisjoint C) (hBD : B.NodeDisjoint D) :
    R.NodeDisjoint W := by
  rw [NodeDisjoint, Finset.disjoint_left]
  intro v hvR hvW
  rcases Finset.mem_union.1 (hR hvR) with hvA | hvB
  · rcases Finset.mem_union.1 (hW hvW) with hvC | hvD
    · exact Finset.disjoint_left.mp hAC hvA hvC
    · exact Finset.disjoint_left.mp hAD hvA hvD
  · rcases Finset.mem_union.1 (hW hvW) with hvC | hvD
    · exact Finset.disjoint_left.mp hBC hvB hvC
    · exact Finset.disjoint_left.mp hBD hvB hvD

/-- Two paths are edge-disjoint when their edge sets are disjoint. -/
def EdgeDisjoint (P Q : GraphPath G) : Prop :=
  Disjoint P.edgeSet Q.edgeSet

theorem edgeDisjoint_symm {P Q : GraphPath G}
    (h : P.EdgeDisjoint Q) : Q.EdgeDisjoint P :=
  h.symm

/-- Two paths are internally disjoint when every common vertex is an endpoint
of both paths. -/
def InternallyDisjoint (P Q : GraphPath G) : Prop :=
  ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet →
    P.IsEndpoint v ∧ Q.IsEndpoint v

theorem internallyDisjoint_symm {P Q : GraphPath G}
    (h : P.InternallyDisjoint Q) : Q.InternallyDisjoint P := by
  intro v hvQ hvP
  exact (h hvP hvQ).symm

/-- A path connects `S` to `T` when its two endpoints lie one in each set.  The
orientation is irrelevant; a single-vertex path in `S ∩ T` also satisfies this
predicate. -/
def Connects (P : GraphPath G) (S T : Finset V) : Prop :=
  (P.source ∈ S ∧ P.target ∈ T) ∨ (P.source ∈ T ∧ P.target ∈ S)

/-- Orient a path connecting `S` and `T` so that it starts in `S` and ends in
`T`.  If it already has that orientation it is left unchanged; otherwise it is
reversed. -/
def orient (P : GraphPath G) {S T : Finset V} (_h : P.Connects S T) :
    GraphPath G :=
  if P.source ∈ S ∧ P.target ∈ T then P else P.reverse

@[simp] theorem orient_vertexSet (P : GraphPath G) {S T : Finset V}
    (h : P.Connects S T) :
    (P.orient h).vertexSet = P.vertexSet := by
  classical
  by_cases hst : P.source ∈ S ∧ P.target ∈ T
  · simp [orient, hst]
  · simp [orient, hst]

@[simp] theorem orient_edgeSet (P : GraphPath G) {S T : Finset V}
    (h : P.Connects S T) :
    (P.orient h).edgeSet = P.edgeSet := by
  classical
  by_cases hst : P.source ∈ S ∧ P.target ∈ T
  · simp [orient, hst]
  · simp [orient, hst]

theorem orient_source_mem (P : GraphPath G) {S T : Finset V}
    (h : P.Connects S T) :
    (P.orient h).source ∈ S := by
  classical
  by_cases hst : P.source ∈ S ∧ P.target ∈ T
  · simp [orient, hst]
  · rcases h with h | h
    · exact False.elim (hst h)
    · simpa [orient, hst, reverse] using h.2

theorem orient_target_mem (P : GraphPath G) {S T : Finset V}
    (h : P.Connects S T) :
    (P.orient h).target ∈ T := by
  classical
  by_cases hst : P.source ∈ S ∧ P.target ∈ T
  · simp [orient, hst]
  · rcases h with h | h
    · exact False.elim (hst h)
    · simpa [orient, hst, reverse] using h.1

/-- If a path connects `S` to some terminal set and, after that orientation, its
right endpoint lies in `T`, then the original unoriented path connects `S` to
`T`. -/
theorem connects_of_orient_target_mem (P : GraphPath G) {S U T : Finset V}
    (h : P.Connects S U) (htarget : (P.orient h).target ∈ T) :
    P.Connects S T := by
  classical
  by_cases hSU : P.source ∈ S ∧ P.target ∈ U
  · exact Or.inl ⟨hSU.1, by simpa [orient, hSU] using htarget⟩
  · rcases h with h | h
    · exact False.elim (hSU h)
    · exact Or.inr ⟨by simpa [orient, hSU, reverse] using htarget, h.2⟩

theorem orient_isEndpoint (P : GraphPath G) {S T : Finset V}
    (h : P.Connects S T) {v : V} :
    (P.orient h).IsEndpoint v ↔ P.IsEndpoint v := by
  classical
  by_cases hst : P.source ∈ S ∧ P.target ∈ T
  · simp [orient, hst, IsEndpoint]
  · simp [orient, hst, IsEndpoint, reverse, or_comm]

/-- Orient an unoriented segment so that it runs from `x` to `y`.

This is the singleton-endpoint specialization used in rerouting arguments:
the stored orientation of a transversal subpath is irrelevant, and the local
replacement chooses whichever orientation has the required endpoints. -/
def orientBetween (P : GraphPath G) {x y : V}
    (h : P.Connects {x} {y}) : GraphPath G :=
  P.orient h

@[simp] theorem orientBetween_vertexSet (P : GraphPath G) {x y : V}
    (h : P.Connects {x} {y}) :
    (P.orientBetween h).vertexSet = P.vertexSet := by
  simp [orientBetween]

@[simp] theorem orientBetween_edgeSet (P : GraphPath G) {x y : V}
    (h : P.Connects {x} {y}) :
    (P.orientBetween h).edgeSet = P.edgeSet := by
  simp [orientBetween]

@[simp] theorem orientBetween_source (P : GraphPath G) {x y : V}
    (h : P.Connects {x} {y}) :
    (P.orientBetween h).source = x := by
  classical
  have hx : (P.orient h).source ∈ ({x} : Finset V) :=
    P.orient_source_mem h
  simpa [orientBetween] using hx

@[simp] theorem orientBetween_target (P : GraphPath G) {x y : V}
    (h : P.Connects {x} {y}) :
    (P.orientBetween h).target = y := by
  classical
  have hy : (P.orient h).target ∈ ({y} : Finset V) :=
    P.orient_target_mem h
  simpa [orientBetween] using hy

/-- Given a path connecting `S` to `T`, orient it from `S` to `T`, truncate at
the first hit of `T`, and then discard the initial part before the last hit of
`S`.  The resulting path has the same orientation convention and has no
internal vertices in `S ∪ T`.

This is the formal terminal-clean version of the phrase “an `S`-`T` path” in
many graph-theory proofs of Menger's theorem. -/
noncomputable def cleanBetweenTerminalSets
    (P : GraphPath G) {S T : Finset V} (h : P.Connects S T) :
    GraphPath G := by
  classical
  let O := P.orient h
  let hT : (O.vertexSet ∩ T).Nonempty :=
    ⟨O.target, Finset.mem_inter.2
      ⟨GraphPath.target_mem_vertexSet O,
        GraphPath.orient_target_mem P h⟩⟩
  let R := O.cleanPrefixToSet T hT
  let hS : (R.vertexSet ∩ S).Nonempty :=
    ⟨R.source, Finset.mem_inter.2
      ⟨GraphPath.source_mem_vertexSet R,
        by simpa [R, O] using GraphPath.orient_source_mem P h⟩⟩
  exact R.cleanSuffixFromSet S hS

theorem cleanBetweenTerminalSets_vertexSet_subset
    (P : GraphPath G) {S T : Finset V} (h : P.Connects S T) :
    (P.cleanBetweenTerminalSets h).vertexSet ⊆ P.vertexSet := by
  classical
  let O := P.orient h
  let hT : (O.vertexSet ∩ T).Nonempty :=
    ⟨O.target, Finset.mem_inter.2
      ⟨GraphPath.target_mem_vertexSet O,
        GraphPath.orient_target_mem P h⟩⟩
  let R := O.cleanPrefixToSet T hT
  let hS : (R.vertexSet ∩ S).Nonempty :=
    ⟨R.source, Finset.mem_inter.2
      ⟨GraphPath.source_mem_vertexSet R,
        by simpa [R, O] using GraphPath.orient_source_mem P h⟩⟩
  intro v hv
  have hvR : v ∈ R.vertexSet :=
    R.cleanSuffixFromSet_vertexSet_subset S hS hv
  have hvO : v ∈ O.vertexSet :=
    O.cleanPrefixToSet_vertexSet_subset T hT hvR
  simpa [O] using hvO

theorem cleanBetweenTerminalSets_connects
    (P : GraphPath G) {S T : Finset V} (h : P.Connects S T) :
    (P.cleanBetweenTerminalSets h).Connects S T := by
  classical
  let O := P.orient h
  let hT : (O.vertexSet ∩ T).Nonempty :=
    ⟨O.target, Finset.mem_inter.2
      ⟨GraphPath.target_mem_vertexSet O,
        GraphPath.orient_target_mem P h⟩⟩
  let R := O.cleanPrefixToSet T hT
  let hS : (R.vertexSet ∩ S).Nonempty :=
    ⟨R.source, Finset.mem_inter.2
      ⟨GraphPath.source_mem_vertexSet R,
        by simpa [R, O] using GraphPath.orient_source_mem P h⟩⟩
  exact Or.inl
    ⟨by
      exact R.cleanSuffixFromSet_source_mem S hS,
     by
      exact O.cleanPrefixToSet_target_mem T hT⟩

theorem cleanBetweenTerminalSets_source_mem
    (P : GraphPath G) {S T : Finset V} (h : P.Connects S T) :
    (P.cleanBetweenTerminalSets h).source ∈ S := by
  classical
  let O := P.orient h
  let hT : (O.vertexSet ∩ T).Nonempty :=
    ⟨O.target, Finset.mem_inter.2
      ⟨GraphPath.target_mem_vertexSet O,
        GraphPath.orient_target_mem P h⟩⟩
  let R := O.cleanPrefixToSet T hT
  let hS : (R.vertexSet ∩ S).Nonempty :=
    ⟨R.source, Finset.mem_inter.2
      ⟨GraphPath.source_mem_vertexSet R,
        by simpa [R, O] using GraphPath.orient_source_mem P h⟩⟩
  exact R.cleanSuffixFromSet_source_mem S hS

theorem cleanBetweenTerminalSets_target_mem
    (P : GraphPath G) {S T : Finset V} (h : P.Connects S T) :
    (P.cleanBetweenTerminalSets h).target ∈ T := by
  classical
  let O := P.orient h
  let hT : (O.vertexSet ∩ T).Nonempty :=
    ⟨O.target, Finset.mem_inter.2
      ⟨GraphPath.target_mem_vertexSet O,
        GraphPath.orient_target_mem P h⟩⟩
  let R := O.cleanPrefixToSet T hT
  let hS : (R.vertexSet ∩ S).Nonempty :=
    ⟨R.source, Finset.mem_inter.2
      ⟨GraphPath.source_mem_vertexSet R,
        by simpa [R, O] using GraphPath.orient_source_mem P h⟩⟩
  exact O.cleanPrefixToSet_target_mem T hT

/-- The terminal-clean segment has no internal vertex in either terminal set. -/
theorem cleanBetweenTerminalSets_internallyDisjointFromSet_union
    (P : GraphPath G) {S T : Finset V} (h : P.Connects S T) :
    (P.cleanBetweenTerminalSets h).InternallyDisjointFromSet (S ∪ T) := by
  classical
  let O := P.orient h
  let hT : (O.vertexSet ∩ T).Nonempty :=
    ⟨O.target, Finset.mem_inter.2
      ⟨GraphPath.target_mem_vertexSet O,
        GraphPath.orient_target_mem P h⟩⟩
  let R := O.cleanPrefixToSet T hT
  let hS : (R.vertexSet ∩ S).Nonempty :=
    ⟨R.source, Finset.mem_inter.2
      ⟨GraphPath.source_mem_vertexSet R,
        by simpa [R, O] using GraphPath.orient_source_mem P h⟩⟩
  intro v hv hST
  have hvR : v ∈ R.vertexSet :=
    R.cleanSuffixFromSet_vertexSet_subset S hS (by
      simpa [cleanBetweenTerminalSets, O, hT, R, hS] using hv)
  have hSuffixClean :
      (R.cleanSuffixFromSet S hS).InternallyDisjointFromSet S :=
    R.cleanSuffixFromSet_internallyDisjointFromSet S hS
  have hPrefixClean :
      R.InternallyDisjointFromSet T := by
    simpa [R] using O.cleanPrefixToSet_internallyDisjointFromSet T hT
  rcases Finset.mem_union.1 hST with hvS | hvT
  · rcases hSuffixClean
        (by simpa [cleanBetweenTerminalSets, O, hT, R, hS] using hv) hvS with
      hsource | htarget
    · exact Or.inl hsource
    · exact Or.inr htarget
  · rcases hPrefixClean hvR hvT with
      hsource | htarget
    · have hsource_mem_suffix :
          R.source ∈ (R.cleanSuffixFromSet S hS).vertexSet := by
        simpa [hsource, cleanBetweenTerminalSets, O, hT, R, hS] using hv
      have hsource_eq :
          R.source = R.lastHitVertex S hS := by
        exact R.eq_lastHitVertex_of_mem_dropUntil_of_mem_set S hS
          (by simpa [cleanSuffixFromSet] using hsource_mem_suffix)
          (by
            simpa [R, O] using GraphPath.orient_source_mem P h)
      have hv_source : v = R.lastHitVertex S hS := hsource.trans hsource_eq
      exact Or.inl (by
        exact hv_source)
    · exact Or.inr (by
        exact htarget)

/-- Concatenate two graph paths whose endpoints match.

The proof that the appended walk is still a path is kept explicit; later
arguments usually derive it from disjointness hypotheses. -/
def appendWithEq (P Q : GraphPath G) (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    GraphPath G where
  source := P.source
  target := Q.target
  walk := P.walk.append (Q.walk.copy h.symm rfl)
  isPath := hpath

omit [DecidableEq V] in
@[simp] theorem appendWithEq_source (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    (P.appendWithEq Q h hpath).source = P.source := rfl

omit [DecidableEq V] in
@[simp] theorem appendWithEq_target (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    (P.appendWithEq Q h hpath).target = Q.target := rfl

theorem appendWithEq_vertexSet_subset (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    (P.appendWithEq Q h hpath).vertexSet ⊆ P.vertexSet ∪ Q.vertexSet := by
  classical
  intro v hv
  simp only [vertexSet, appendWithEq, Finset.mem_union, List.mem_toFinset,
    _root_.SimpleGraph.Walk.mem_support_append_iff,
    _root_.SimpleGraph.Walk.support_copy] at hv ⊢
  exact hv

/-- The left constituent path is contained in a concatenation. -/
theorem left_vertexSet_subset_appendWithEq (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    P.vertexSet ⊆ (P.appendWithEq Q h hpath).vertexSet := by
  classical
  intro v hv
  simp [appendWithEq, vertexSet,
    _root_.SimpleGraph.Walk.mem_support_append_iff] at hv ⊢
  exact Or.inl hv

/-- The right constituent path is contained in a concatenation. -/
theorem right_vertexSet_subset_appendWithEq (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    Q.vertexSet ⊆ (P.appendWithEq Q h hpath).vertexSet := by
  classical
  intro v hv
  simp [appendWithEq, vertexSet,
    _root_.SimpleGraph.Walk.mem_support_append_iff] at hv ⊢
  exact Or.inr hv

private theorem appendWithEq_vertexIndex_left (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath)
    {v : V} (hv : v ∈ P.vertexSet) :
    (P.appendWithEq Q h hpath).vertexIndex v = P.vertexIndex v := by
  classical
  have hvSupport : v ∈ P.walk.support := by
    simpa [vertexSet] using hv
  change
    (P.walk.append (Q.walk.copy h.symm rfl)).support.idxOf v =
      P.walk.support.idxOf v
  rw [_root_.SimpleGraph.Walk.support_append,
    List.idxOf_append_of_mem hvSupport]

private theorem appendWithEq_vertexIndex_right (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath)
    {v : V} (hv : v ∈ Q.vertexSet) :
    (P.appendWithEq Q h hpath).vertexIndex v =
      P.walk.length + Q.vertexIndex v := by
  classical
  by_cases hvsource : v = Q.source
  · subst v
    calc
      (P.appendWithEq Q h hpath).vertexIndex Q.source =
          (P.appendWithEq Q h hpath).vertexIndex P.target :=
        congrArg (P.appendWithEq Q h hpath).vertexIndex h.symm
      _ = P.vertexIndex P.target :=
        appendWithEq_vertexIndex_left P Q h hpath
          (GraphPath.target_mem_vertexSet P)
      _ = P.walk.length := P.target_vertexIndex
      _ = P.walk.length + Q.vertexIndex Q.source := by simp
  · have hvSupport : v ∈ Q.walk.support := by
      simpa [vertexSet] using hv
    have hvTail : v ∈ Q.walk.support.tail := by
      rw [← _root_.SimpleGraph.Walk.cons_tail_support Q.walk] at hvSupport
      exact (List.mem_cons.mp hvSupport).resolve_left hvsource
    have hnodup :
        (P.walk.support ++
          (Q.walk.copy h.symm rfl).support.tail).Nodup := by
      simpa only [_root_.SimpleGraph.Walk.support_append] using
        hpath.support_nodup
    have hdisj :
        List.Disjoint P.walk.support
          (Q.walk.copy h.symm rfl).support.tail :=
      List.disjoint_of_nodup_append hnodup
    have hvCopyTail :
        v ∈ (Q.walk.copy h.symm rfl).support.tail := by
      simpa using hvTail
    have hvNotP : v ∉ P.walk.support := by
      intro hvP
      exact hdisj hvP hvCopyTail
    have hsourcev : Q.source ≠ v := Ne.symm hvsource
    have hidxQ :
        Q.walk.support.idxOf v = Q.walk.support.tail.idxOf v + 1 := by
      calc
        Q.walk.support.idxOf v =
            (Q.source :: Q.walk.support.tail).idxOf v := by
          rw [_root_.SimpleGraph.Walk.cons_tail_support Q.walk]
        _ = Nat.succ (Q.walk.support.tail.idxOf v) :=
          List.idxOf_cons_ne _ hsourcev
        _ = Q.walk.support.tail.idxOf v + 1 := by omega
    change
      (P.walk.append (Q.walk.copy h.symm rfl)).support.idxOf v =
        P.walk.length + Q.walk.support.idxOf v
    rw [_root_.SimpleGraph.Walk.support_append,
      List.idxOf_append_of_notMem hvNotP]
    simp only [_root_.SimpleGraph.Walk.support_copy]
    rw [P.walk.length_support, hidxQ]
    omega

/-- A `Before` relation in the left component is preserved by concatenation. -/
theorem before_appendWithEq_of_left (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath)
    {a b : V} (hab : P.Before a b) :
    (P.appendWithEq Q h hpath).Before a b := by
  classical
  have hab' := (P.before_iff_vertexIndex_le).1 hab
  refine ((P.appendWithEq Q h hpath).before_iff_vertexIndex_le).2
    ⟨P.left_vertexSet_subset_appendWithEq Q h hpath hab'.1,
      P.left_vertexSet_subset_appendWithEq Q h hpath hab'.2.1, ?_⟩
  rw [appendWithEq_vertexIndex_left P Q h hpath hab'.1,
    appendWithEq_vertexIndex_left P Q h hpath hab'.2.1]
  exact hab'.2.2

/-- A `Before` relation in the right component is preserved by concatenation;
the path proof rules out an earlier occurrence of every non-glue vertex. -/
theorem before_appendWithEq_of_right (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath)
    {a b : V} (hab : Q.Before a b) :
    (P.appendWithEq Q h hpath).Before a b := by
  classical
  have hab' := (Q.before_iff_vertexIndex_le).1 hab
  refine ((P.appendWithEq Q h hpath).before_iff_vertexIndex_le).2
    ⟨P.right_vertexSet_subset_appendWithEq Q h hpath hab'.1,
      P.right_vertexSet_subset_appendWithEq Q h hpath hab'.2.1, ?_⟩
  rw [appendWithEq_vertexIndex_right P Q h hpath hab'.1,
    appendWithEq_vertexIndex_right P Q h hpath hab'.2.1]
  exact Nat.add_le_add_left hab'.2.2 P.walk.length

/-- Every left-component vertex occurs before every right-component vertex.
This is non-strict at the shared glue endpoint. -/
theorem before_appendWithEq_of_mem_left_of_mem_right (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath)
    {a b : V} (ha : a ∈ P.vertexSet) (hb : b ∈ Q.vertexSet) :
    (P.appendWithEq Q h hpath).Before a b := by
  have haGlue :
      (P.appendWithEq Q h hpath).Before a P.target :=
    P.before_appendWithEq_of_left Q h hpath (P.before_target_of_mem ha)
  have hGlueB :
      (P.appendWithEq Q h hpath).Before Q.source b :=
    P.before_appendWithEq_of_right Q h hpath (Q.source_before_of_mem hb)
  exact (P.appendWithEq Q h hpath).before_trans haGlue (by simpa [h] using hGlueB)

/-- A concatenated path uses only edges from the two concatenated pieces. -/
theorem appendWithEq_edgeSet_subset (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hpath : (P.walk.append (Q.walk.copy h.symm rfl)).IsPath) :
    (P.appendWithEq Q h hpath).edgeSet ⊆ P.edgeSet ∪ Q.edgeSet := by
  classical
  simp [edgeSet, appendWithEq]

/-- If two simple paths meet only at the endpoint where they are glued, then
their concatenation is again a simple path. -/
theorem appendWithEq_isPath_of_inter_subset_target (P Q : GraphPath G)
    (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    (P.walk.append (Q.walk.copy h.symm rfl)).IsPath := by
  classical
  rw [_root_.SimpleGraph.Walk.isPath_def,
    _root_.SimpleGraph.Walk.support_append]
  refine List.Nodup.append P.isPath.support_nodup ?hQtail ?hdisj
  · have hQcopy :
        (Q.walk.copy h.symm rfl).support.Nodup := by
      simpa using Q.isPath.support_nodup
    exact List.Nodup.sublist (List.tail_sublist _) hQcopy
  · rw [List.disjoint_iff_ne]
    intro a ha b hb hab
    subst b
    have ha_fin : a ∈ P.vertexSet := by
      simpa [vertexSet] using ha
    have hb_support : a ∈ (Q.walk.copy h.symm rfl).support :=
      List.mem_of_mem_tail hb
    have hb_fin : a ∈ Q.vertexSet := by
      simpa [vertexSet] using hb_support
    have ha_target : a = P.target := hinter ha_fin hb_fin
    have hnot_target_tail :
        P.target ∉ (Q.walk.copy h.symm rfl).support.tail := by
      have hnot_source_tail : Q.source ∉ Q.walk.support.tail := by
        have hcons : (Q.source :: Q.walk.support.tail).Nodup := by
          rw [_root_.SimpleGraph.Walk.cons_tail_support Q.walk]
          exact Q.isPath.support_nodup
        exact (List.nodup_cons.mp hcons).1
      simpa [h] using hnot_source_tail
    exact hnot_target_tail (by simpa [ha_target] using hb)

/-- Concatenate two paths when their only common vertices lie at the glued
endpoint. -/
noncomputable def appendWithEqOfInterSubsetTarget
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    GraphPath G :=
  P.appendWithEq Q h (P.appendWithEq_isPath_of_inter_subset_target Q h hinter)

@[simp] theorem appendWithEqOfInterSubsetTarget_source
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    (P.appendWithEqOfInterSubsetTarget Q h hinter).source = P.source :=
  rfl

@[simp] theorem appendWithEqOfInterSubsetTarget_target
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    (P.appendWithEqOfInterSubsetTarget Q h hinter).target = Q.target :=
  rfl

/-- Endpoint witness for a concatenation whose first path starts in `S` and
second path ends in `T`. -/
theorem appendWithEqOfInterSubsetTarget_connects
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target)
    {S T : Finset V} (hsource : P.source ∈ S) (htarget : Q.target ∈ T) :
    (P.appendWithEqOfInterSubsetTarget Q h hinter).Connects S T :=
  Or.inl ⟨by simpa using hsource, by simpa using htarget⟩

/-- Concatenating two internally clean paths at a glue vertex outside the
forbidden set remains internally clean. -/
theorem appendWithEqOfInterSubsetTarget_internallyDisjointFromSet
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target)
    {U : Finset V}
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.InternallyDisjointFromSet U)
    (hglue : P.target ∉ U) :
    (P.appendWithEqOfInterSubsetTarget Q h hinter).InternallyDisjointFromSet U := by
  intro v hv hvU
  have hvUnion :
      v ∈ P.vertexSet ∪ Q.vertexSet :=
    P.appendWithEq_vertexSet_subset Q h
      (P.appendWithEq_isPath_of_inter_subset_target Q h hinter) hv
  rcases Finset.mem_union.1 hvUnion with hvP | hvQ
  · rcases hP hvP hvU with hsource | htarget
    · exact Or.inl (by simp [hsource])
    · exact False.elim (hglue (by simpa [htarget] using hvU))
  · rcases hQ hvQ hvU with hsource | htarget
    · exact False.elim (hglue (by simpa [h, hsource] using hvU))
    · exact Or.inr (by simp [htarget])

/-- The left constituent path is contained in a concatenation built using
`appendWithEqOfInterSubsetTarget`. -/
theorem left_vertexSet_subset_appendWithEqOfInterSubsetTarget
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    P.vertexSet ⊆
      (P.appendWithEqOfInterSubsetTarget Q h hinter).vertexSet := by
  exact P.left_vertexSet_subset_appendWithEq Q h
    (P.appendWithEq_isPath_of_inter_subset_target Q h hinter)

/-- The right constituent path is contained in a concatenation built using
`appendWithEqOfInterSubsetTarget`. -/
theorem right_vertexSet_subset_appendWithEqOfInterSubsetTarget
    (P Q : GraphPath G) (h : P.target = Q.source)
    (hinter :
      ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ Q.vertexSet → v = P.target) :
    Q.vertexSet ⊆
      (P.appendWithEqOfInterSubsetTarget Q h hinter).vertexSet := by
  exact P.right_vertexSet_subset_appendWithEq Q h
    (P.appendWithEq_isPath_of_inter_subset_target Q h hinter)

/-- Append a suffix contained in a terminal region `U` to a path that starts
outside `U` and is internally disjoint from `U`. -/
noncomputable def appendWithEqOfInternallyDisjointFromSet
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource : P.source ∉ U) :
    GraphPath G :=
  P.appendWithEqOfInterSubsetTarget Q h
    (fun {v} hvP hvQ =>
      P.eq_target_of_internallyDisjointFromSet_of_subset_of_source_not_mem
        Q hP hQ hsource (v := v) hvP hvQ)

@[simp] theorem appendWithEqOfInternallyDisjointFromSet_source
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource : P.source ∉ U) :
    (P.appendWithEqOfInternallyDisjointFromSet Q h hP hQ hsource).source =
      P.source :=
  by simp [appendWithEqOfInternallyDisjointFromSet]

@[simp] theorem appendWithEqOfInternallyDisjointFromSet_target
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource : P.source ∉ U) :
    (P.appendWithEqOfInternallyDisjointFromSet Q h hP hQ hsource).target =
      Q.target :=
  by simp [appendWithEqOfInternallyDisjointFromSet]

theorem appendWithEqOfInternallyDisjointFromSet_connects
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_not : P.source ∉ U)
    {S T : Finset V} (hsource : P.source ∈ S) (htarget : Q.target ∈ T) :
    (P.appendWithEqOfInternallyDisjointFromSet Q h hP hQ hsource_not).Connects S T :=
  Or.inl ⟨by simp [appendWithEqOfInternallyDisjointFromSet, hsource],
    by simp [appendWithEqOfInternallyDisjointFromSet, htarget]⟩

/-- Append a suffix contained in `U` to a path internally disjoint from `U`,
assuming only that the source of the first path is not on the appended suffix.
This is the form used in Menger splicing, where the source may itself be a
terminal vertex in `U` but is known not to lie on the particular suffix. -/
noncomputable def appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_not : P.source ∉ Q.vertexSet) :
    GraphPath G :=
  P.appendWithEqOfInterSubsetTarget Q h
    (fun {v} hvP hvQ =>
      by
        rcases hP hvP (hQ hvQ) with hsource | htarget
        · exact False.elim (hsource_not (by simpa [hsource] using hvQ))
        · exact htarget)

@[simp] theorem appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix_source
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_not : P.source ∉ Q.vertexSet) :
    (P.appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix
      Q h hP hQ hsource_not).source = P.source :=
  rfl

@[simp] theorem appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix_target
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_not : P.source ∉ Q.vertexSet) :
    (P.appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix
      Q h hP hQ hsource_not).target = Q.target :=
  rfl

theorem appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix_connects
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_not : P.source ∉ Q.vertexSet)
    {S T : Finset V} (hsource : P.source ∈ S) (htarget : Q.target ∈ T) :
    (P.appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix
      Q h hP hQ hsource_not).Connects S T :=
  Or.inl ⟨by simpa using hsource, by simpa using htarget⟩

/-- Variant of
`appendWithEqOfInternallyDisjointFromSetOfSourceNotMemSuffix` allowing the
first path's source to lie on the appended suffix only in the degenerate case
where that source is also the glue vertex. -/
noncomputable def appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_only : P.source ∈ Q.vertexSet → P.source = P.target) :
    GraphPath G :=
  P.appendWithEqOfInterSubsetTarget Q h
    (fun {v} hvP hvQ =>
      by
        rcases hP hvP (hQ hvQ) with hsource | htarget
        · exact hsource.trans (hsource_only (by simpa [hsource] using hvQ))
        · exact htarget)

@[simp] theorem appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget_source
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_only : P.source ∈ Q.vertexSet → P.source = P.target) :
    (P.appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget
      Q h hP hQ hsource_only).source = P.source :=
  rfl

@[simp] theorem appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget_target
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_only : P.source ∈ Q.vertexSet → P.source = P.target) :
    (P.appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget
      Q h hP hQ hsource_only).target = Q.target :=
  rfl

theorem appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget_connects
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource_only : P.source ∈ Q.vertexSet → P.source = P.target)
    {S T : Finset V} (hsource : P.source ∈ S) (htarget : Q.target ∈ T) :
    (P.appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget
      Q h hP hQ hsource_only).Connects S T :=
  Or.inl ⟨by simpa using hsource, by simpa using htarget⟩

/-- Append a path internally disjoint from `U` to a prefix contained in `U`,
allowing the second path's target to lie on the prefix only in the degenerate
case where the second path starts and ends at the glued vertex.

This is the target-end symmetric form of
`appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget`. -/
noncomputable def appendWithEqOfSubsetInternallyDisjointFromSetOfTargetOnlyAtSource
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.vertexSet ⊆ U)
    (hQ : Q.InternallyDisjointFromSet U)
    (htarget_only : Q.target ∈ P.vertexSet → Q.target = Q.source) :
    GraphPath G :=
  P.appendWithEqOfInterSubsetTarget Q h
    (fun {v} hvP hvQ =>
      by
        rcases hQ hvQ (hP hvP) with hsource | htarget
        · exact hsource.trans h.symm
        · exact htarget.trans
            ((htarget_only (by simpa [htarget] using hvP)).trans h.symm))

@[simp] theorem appendWithEqOfSubsetInternallyDisjointFromSetOfTargetOnlyAtSource_source
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.vertexSet ⊆ U)
    (hQ : Q.InternallyDisjointFromSet U)
    (htarget_only : Q.target ∈ P.vertexSet → Q.target = Q.source) :
    (P.appendWithEqOfSubsetInternallyDisjointFromSetOfTargetOnlyAtSource
      Q h hP hQ htarget_only).source = P.source :=
  rfl

@[simp] theorem appendWithEqOfSubsetInternallyDisjointFromSetOfTargetOnlyAtSource_target
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.vertexSet ⊆ U)
    (hQ : Q.InternallyDisjointFromSet U)
    (htarget_only : Q.target ∈ P.vertexSet → Q.target = Q.source) :
    (P.appendWithEqOfSubsetInternallyDisjointFromSetOfTargetOnlyAtSource
      Q h hP hQ htarget_only).target = Q.target :=
  rfl

theorem appendWithEqOfSubsetInternallyDisjointFromSetOfTargetOnlyAtSource_connects
    (P Q : GraphPath G) {U : Finset V} (h : P.target = Q.source)
    (hP : P.vertexSet ⊆ U)
    (hQ : Q.InternallyDisjointFromSet U)
    (htarget_only : Q.target ∈ P.vertexSet → Q.target = Q.source)
    {S T : Finset V} (hsource : P.source ∈ S) (htarget : Q.target ∈ T) :
    (P.appendWithEqOfSubsetInternallyDisjointFromSetOfTargetOnlyAtSource
      Q h hP hQ htarget_only).Connects S T :=
  Or.inl ⟨by simpa using hsource, by simpa using htarget⟩

/-- If a path is internally disjoint from a terminal region `U`, then it is
disjoint from any path contained in `U` as soon as neither endpoint lies on that
contained path. -/
theorem nodeDisjoint_of_internallyDisjointFromSet_of_subset_of_endpoints_not_mem
    (P Q : GraphPath G) {U : Finset V}
    (hP : P.InternallyDisjointFromSet U)
    (hQ : Q.vertexSet ⊆ U)
    (hsource : P.source ∉ Q.vertexSet)
    (htarget : P.target ∉ Q.vertexSet) :
    P.NodeDisjoint Q := by
  rw [NodeDisjoint, Finset.disjoint_left]
  intro v hvP hvQ
  rcases hP hvP (hQ hvQ) with hsrc | htgt
  · exact hsource (by simpa [hsrc] using hvQ)
  · exact htarget (by simpa [htgt] using hvQ)

omit [DecidableEq V] in
theorem connects_comm (P : GraphPath G) (S T : Finset V) :
    P.Connects S T ↔ P.Connects T S := by
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · intro h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- Any two vertices on a graph path are connected by a subpath contained in
the original path.  The returned path is unoriented: it may run from `x` to
`y` or from `y` to `x`. -/
theorem exists_segment_connects_of_mem_vertexSet
    (P : GraphPath G) {x y : V}
    (hx : x ∈ P.vertexSet) (hy : y ∈ P.vertexSet) :
    ∃ Q : GraphPath G,
      Q.Connects ({x} : Finset V) ({y} : Finset V) ∧
        Q.vertexSet ⊆ P.vertexSet := by
  classical
  by_cases hxy : P.vertexIndex x ≤ P.vertexIndex y
  · let hbefore : P.Before x y :=
      (P.before_iff_vertexIndex_le).2 ⟨hx, hy, hxy⟩
    refine ⟨P.segmentOfBefore hbefore, ?_, ?_⟩
    · exact Or.inl ⟨by simp, by simp⟩
    · exact P.segmentOfBefore_vertexSet_subset hbefore
  · have hyx : P.vertexIndex y ≤ P.vertexIndex x :=
      Nat.le_of_lt (Nat.lt_of_not_ge hxy)
    let hbefore : P.Before y x :=
      (P.before_iff_vertexIndex_le).2 ⟨hy, hx, hyx⟩
    refine ⟨P.segmentOfBefore hbefore, ?_, ?_⟩
    · exact Or.inr ⟨by simp, by simp⟩
    · exact P.segmentOfBefore_vertexSet_subset hbefore

end GraphPath


end SimpleGraph

end Erdos73Infrastructure
