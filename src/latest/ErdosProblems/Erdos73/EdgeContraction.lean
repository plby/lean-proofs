/-
Adapted from the Apache-2.0-licensed polynomial-grid-minor-theorem development,
https://github.com/EdouardBonnet/polynomial-grid-minor-theorem,
commit fe2848173913a00d85c64d2a17af63f2cf0d4fbf,
proofs/Lax17Proofs/Source/TreewidthSparsifierSection2.lean, single-edge contraction.
Only the independent branch-set/projection chain is included; no sparsifier
or grid-minor interface is imported. Namespace/import and Lean 4.33 adaptations.
-/
import ErdosProblems.Erdos73.GraphPaths
import ErdosProblems.Erdos73.MinorModels

namespace Erdos73Infrastructure.SimpleGraph.TreewidthSparsifier
universe u v w
open scoped Classical
variable {V : Type u} [DecidableEq V]


/-- Vertices of the graph obtained by contracting the edge `u -- v`.

The vertex `merged` represents the contracted edge, and `keep x` represents an
original vertex different from both endpoints of the contracted edge. -/
inductive EdgeContractVertex (V : Type u) (u v : V) where
  | merged : EdgeContractVertex V u v
  | keep : {x : V // x ≠ u ∧ x ≠ v} → EdgeContractVertex V u v
deriving DecidableEq

namespace EdgeContractVertex

variable {u v : V}

noncomputable instance instFintype [Fintype V] :
    Fintype (EdgeContractVertex V u v) := by
  classical
  refine
    Fintype.ofEquiv (Unit ⊕ {x : V // x ≠ u ∧ x ≠ v}) ?_
  refine
    { toFun := fun z =>
        match z with
        | Sum.inl _ => merged
        | Sum.inr x => keep x
      invFun := fun x =>
        match x with
        | merged => Sum.inl ()
        | keep z => Sum.inr z
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    cases z with
    | inl z => cases z <;> rfl
    | inr z => rfl
  · intro x
    cases x <;> rfl

/-- The branch set represented by one vertex after contracting `u -- v`. -/
noncomputable def branchSet (x : EdgeContractVertex V u v) : Finset V :=
  match x with
  | merged => {u, v}
  | keep z => {z.1}

@[simp] theorem branchSet_merged :
    branchSet (V := V) (u := u) (v := v) merged = ({u, v} : Finset V) :=
  rfl

@[simp] theorem branchSet_keep (z : {x : V // x ≠ u ∧ x ≠ v}) :
    branchSet (keep z : EdgeContractVertex V u v) = ({z.1} : Finset V) :=
  rfl

/-- The canonical vertex representing an original non-endpoint vertex. -/
def ofVertex (x : V) (hx : x ≠ u ∧ x ≠ v) :
    EdgeContractVertex V u v :=
  keep ⟨x, hx⟩

/-- Project an original vertex to the graph where `u -- v` is contracted. -/
noncomputable def projection (x : V) : EdgeContractVertex V u v :=
  if hx : x = u ∨ x = v then
    merged
  else
    ofVertex x ⟨fun hxu => hx (Or.inl hxu), fun hxv => hx (Or.inr hxv)⟩

@[simp] theorem projection_eq_merged_of_eq_left :
    projection (V := V) (u := u) (v := v) u = merged := by
  simp [projection]

@[simp] theorem projection_eq_merged_of_eq_right :
    projection (V := V) (u := u) (v := v) v = merged := by
  simp [projection]

theorem projection_eq_of_ne {x : V} (hxu : x ≠ u) (hxv : x ≠ v) :
    projection (V := V) (u := u) (v := v) x =
      ofVertex (V := V) (u := u) (v := v) x ⟨hxu, hxv⟩ := by
  simp [projection, hxu, hxv]

@[simp] theorem projection_eq_merged_iff {x : V} :
    projection (V := V) (u := u) (v := v) x = merged ↔
      x = u ∨ x = v := by
  by_cases hx : x = u ∨ x = v
  · simp [projection, hx]
  · constructor
    · intro h
      have hkeep :
          ofVertex (V := V) (u := u) (v := v) x
              ⟨fun hxu => hx (Or.inl hxu), fun hxv => hx (Or.inr hxv)⟩ =
            merged := by
        simpa [projection, hx] using h
      cases hkeep
    · intro hx'
      exact (hx hx').elim

/-- Equality after edge-contraction projection either comes from equality
before projection, or from both original vertices being endpoints of the
contracted edge. -/
theorem eq_or_endpoint_pair_of_projection_eq {x y : V}
    (h :
      projection (V := V) (u := u) (v := v) x =
        projection (V := V) (u := u) (v := v) y) :
    x = y ∨ (x = u ∨ x = v) ∧ (y = u ∨ y = v) := by
  by_cases hx : x = u ∨ x = v
  · exact Or.inr ⟨hx, by
      rw [← projection_eq_merged_iff (V := V) (u := u) (v := v)]
      simpa [projection, hx] using h.symm⟩
  · by_cases hy : y = u ∨ y = v
    · have hxmerged :
          projection (V := V) (u := u) (v := v) x = merged := by
        simpa [projection, hy] using h
      exact False.elim (hx
        ((projection_eq_merged_iff (V := V) (u := u) (v := v)).1 hxmerged))
    · left
      have hkeep :
          ofVertex (V := V) (u := u) (v := v) x
              ⟨fun hxu => hx (Or.inl hxu), fun hxv => hx (Or.inr hxv)⟩ =
            ofVertex (V := V) (u := u) (v := v) y
              ⟨fun hyu => hy (Or.inl hyu), fun hyv => hy (Or.inr hyv)⟩ := by
        simpa [projection, hx, hy] using h
      injection hkeep with hsub
      exact congrArg Subtype.val hsub

@[simp] theorem mem_branchSet_ofVertex
    (x : V) (hx : x ≠ u ∧ x ≠ v) :
    x ∈ branchSet (ofVertex (V := V) (u := u) (v := v) x hx) := by
  simp [ofVertex]

/-- Projection sends a vertex to a contracted vertex whose branch set contains
the original vertex. -/
theorem mem_branchSet_projection (x : V) :
    x ∈ branchSet (projection (V := V) (u := u) (v := v) x) := by
  by_cases hx : x = u ∨ x = v
  · rcases hx with rfl | rfl
    · simp
    · simp
  · simp [projection, hx, ofVertex]

@[simp] theorem mem_branchSet_merged_left :
    u ∈ branchSet (V := V) (u := u) (v := v) merged := by
  simp

@[simp] theorem mem_branchSet_merged_right :
    v ∈ branchSet (V := V) (u := u) (v := v) merged := by
  simp

/-- Every contracted-edge vertex has a nonempty branch set. -/
theorem branchSet_nonempty (x : EdgeContractVertex V u v) :
    (branchSet x).Nonempty := by
  cases x with
  | merged =>
      exact ⟨u, by simp⟩
  | keep z =>
      exact ⟨z.1, by simp⟩

/-- Distinct contracted-edge vertices have disjoint branch sets. -/
theorem branchSet_disjoint {x y : EdgeContractVertex V u v}
    (hxy : x ≠ y) :
    Disjoint (branchSet x) (branchSet y) := by
  classical
  cases x with
  | merged =>
      cases y with
      | merged => exact (hxy rfl).elim
      | keep z =>
          rw [Finset.disjoint_left]
          intro a ha hb
          have haz : a = z.1 := by simpa using hb
          have hauv : a = u ∨ a = v := by simpa using ha
          rcases hauv with rfl | rfl
          · exact z.2.1 haz.symm
          · exact z.2.2 haz.symm
  | keep z =>
      cases y with
      | merged =>
          rw [Finset.disjoint_left]
          intro a ha hb
          have haz : a = z.1 := by simpa using ha
          have hauv : a = u ∨ a = v := by simpa using hb
          rcases hauv with rfl | rfl
          · exact z.2.1 haz.symm
          · exact z.2.2 haz.symm
      | keep w =>
          rw [Finset.disjoint_left]
          intro a ha hb
          have haz : a = z.1 := by simpa using ha
          have haw : a = w.1 := by simpa using hb
          apply hxy
          apply congrArg keep
          exact Subtype.ext (haz.symm.trans haw)

/-- A representative original vertex for each contracted vertex.  The merged
vertex is represented by the left endpoint. -/
def representative (x : EdgeContractVertex V u v) : V :=
  match x with
  | merged => u
  | keep z => z.1

theorem representative_injective (huv : u ≠ v) :
    Function.Injective (representative (V := V) (u := u) (v := v)) := by
  intro x y hxy
  cases x with
  | merged =>
      cases y with
      | merged => rfl
      | keep z =>
          exfalso
          exact z.2.1 hxy.symm
  | keep z =>
      cases y with
      | merged =>
          exfalso
          exact z.2.1 hxy
      | keep w =>
          apply congrArg keep
          exact Subtype.ext hxy

theorem representative_not_surjective (huv : u ≠ v) :
    ¬ Function.Surjective
      (representative (V := V) (u := u) (v := v)) := by
  intro hsurj
  rcases hsurj v with ⟨x, hx⟩
  cases x with
  | merged =>
      exact huv hx
  | keep z =>
      exact z.2.2 hx

theorem card_lt_of_ne [Fintype V] (huv : u ≠ v) :
    Fintype.card (EdgeContractVertex V u v) < Fintype.card V :=
  Fintype.card_lt_of_injective_not_surjective
    (representative (V := V) (u := u) (v := v))
    (representative_injective (V := V) (u := u) (v := v) huv)
    (representative_not_surjective (V := V) (u := u) (v := v) huv)

end EdgeContractVertex

/-- The simple graph obtained from `G` by contracting the edge `u -- v`.

Two contracted vertices are adjacent when some original edge runs between their
branch sets.  Loops created by the contraction are discarded. -/
noncomputable def contractEdgeGraph
    (G : _root_.SimpleGraph V) {u v : V} (_huv : G.Adj u v) :
    _root_.SimpleGraph (EdgeContractVertex V u v) where
  Adj x y :=
    x ≠ y ∧
      ∃ a ∈ EdgeContractVertex.branchSet x,
        ∃ b ∈ EdgeContractVertex.branchSet y, G.Adj a b
  symm := ⟨by
    intro x y hxy
    rcases hxy with ⟨hne, a, ha, b, hb, hab⟩
    exact ⟨hne.symm, b, hb, a, ha, hab.symm⟩⟩
  loopless := ⟨by
    intro x hxx
    exact hxx.1 rfl⟩

namespace contractEdgeGraph

variable {G : _root_.SimpleGraph V} {u v : V} {huv : G.Adj u v}

@[simp] theorem adj_iff (x y : EdgeContractVertex V u v) :
    (contractEdgeGraph G huv).Adj x y ↔
      x ≠ y ∧
        ∃ a ∈ EdgeContractVertex.branchSet x,
          ∃ b ∈ EdgeContractVertex.branchSet y, G.Adj a b :=
  Iff.rfl

/-- An original edge whose endpoints project to distinct contracted vertices
gives an edge in the contracted graph. -/
theorem projection_adj_of_adj_of_ne {x y : V}
    (hxy : G.Adj x y)
    (hne :
      EdgeContractVertex.projection (V := V) (u := u) (v := v) x ≠
        EdgeContractVertex.projection (V := V) (u := u) (v := v) y) :
    (contractEdgeGraph G huv).Adj
      (EdgeContractVertex.projection (V := V) (u := u) (v := v) x)
      (EdgeContractVertex.projection (V := V) (u := u) (v := v) y) := by
  exact ⟨hne, x,
    EdgeContractVertex.mem_branchSet_projection (V := V) (u := u) (v := v) x,
    y,
    EdgeContractVertex.mem_branchSet_projection (V := V) (u := u) (v := v) y,
    hxy⟩

namespace ProjectionWalk

/-- Project a walk to the contracted-edge graph, suppressing steps whose
endpoints are identified by the contraction. -/
noncomputable def ofWalk : {x y : V} → (W : G.Walk x y) →
    (contractEdgeGraph G huv).Walk
      (EdgeContractVertex.projection (V := V) (u := u) (v := v) x)
      (EdgeContractVertex.projection (V := V) (u := u) (v := v) y)
  | x, _, _root_.SimpleGraph.Walk.nil' _ =>
      _root_.SimpleGraph.Walk.nil
  | x, z, _root_.SimpleGraph.Walk.cons' _ y _ h W => by
      let ih := ofWalk W
      by_cases hsame :
        EdgeContractVertex.projection (V := V) (u := u) (v := v) x =
          EdgeContractVertex.projection (V := V) (u := u) (v := v) y
      · exact ih.copy hsame.symm rfl
      · exact _root_.SimpleGraph.Walk.cons
          (projection_adj_of_adj_of_ne (G := G) (huv := huv) h hsame) ih

/-- Every vertex of a projected walk is the projection of some vertex of the
original walk. -/
theorem support_subset_projection : {x y : V} → (W : G.Walk x y) →
    ∀ z ∈ (ofWalk (G := G) (huv := huv) W).support,
      ∃ a ∈ W.support,
        EdgeContractVertex.projection (V := V) (u := u) (v := v) a = z
  | x, _, _root_.SimpleGraph.Walk.nil' _ => by
      intro z hz
      have hz' :
          z = EdgeContractVertex.projection (V := V) (u := u) (v := v) x := by
        simpa [ofWalk] using hz
      exact ⟨x, by simp, hz'.symm⟩
  | x, _, _root_.SimpleGraph.Walk.cons' _ y _ h W => by
      intro z hz
      by_cases hsame :
        EdgeContractVertex.projection (V := V) (u := u) (v := v) x =
          EdgeContractVertex.projection (V := V) (u := u) (v := v) y
      · have hzTail : z ∈ (ofWalk (G := G) (huv := huv) W).support := by
          simpa [ofWalk, hsame] using hz
        rcases support_subset_projection W z hzTail with
          ⟨a, ha, haz⟩
        exact ⟨a, by simp [ha], haz⟩
      · have hzCons :
            z = EdgeContractVertex.projection (V := V) (u := u) (v := v) x ∨
              z ∈ (ofWalk (G := G) (huv := huv) W).support := by
          simpa [ofWalk, hsame, _root_.SimpleGraph.Walk.support_cons] using hz
        rcases hzCons with hzHead | hzTail
        · exact ⟨x, by simp, hzHead.symm⟩
        · rcases support_subset_projection W z hzTail with
            ⟨a, ha, haz⟩
          exact ⟨a, by simp [ha], haz⟩

/-- Turn a projected walk into a simple graph path. -/
noncomputable def toGraphPath (R : GraphPath G) :
    GraphPath (contractEdgeGraph G huv) where
  source := EdgeContractVertex.projection (V := V) (u := u) (v := v) R.source
  target := EdgeContractVertex.projection (V := V) (u := u) (v := v) R.target
  walk := (ofWalk (G := G) (huv := huv) R.walk).toPath.val
  isPath := (ofWalk (G := G) (huv := huv) R.walk).toPath.property

/-- Vertices of the projected graph path come from projecting vertices of the
original path. -/
theorem toGraphPath_vertexSet_subset_projection (R : GraphPath G) :
    ∀ z ∈ (toGraphPath (G := G) (huv := huv) R).vertexSet,
      ∃ a ∈ R.vertexSet,
        EdgeContractVertex.projection (V := V) (u := u) (v := v) a = z := by
  classical
  intro z hz
  have hzSupport :
      z ∈ ((ofWalk (G := G) (huv := huv) R.walk).toPath :
        (contractEdgeGraph G huv).Walk
          (EdgeContractVertex.projection (V := V) (u := u) (v := v) R.source)
          (EdgeContractVertex.projection (V := V) (u := u) (v := v) R.target)).support := by
    simpa [toGraphPath, GraphPath.vertexSet] using hz
  have hzWalk :
      z ∈ (ofWalk (G := G) (huv := huv) R.walk).support :=
    _root_.SimpleGraph.Walk.support_toPath_subset_support
      (ofWalk (G := G) (huv := huv) R.walk) hzSupport
  rcases support_subset_projection (G := G) (huv := huv) R.walk z hzWalk with
    ⟨a, ha, haz⟩
  exact ⟨a, by simpa [GraphPath.vertexSet] using ha, haz⟩

end ProjectionWalk

/-- Branch sets of vertices in the contracted-edge graph are connected in the
original graph. -/
theorem branch_connected (huv : G.Adj u v) (x : EdgeContractVertex V u v) :
    (G.induce {a : V | a ∈ EdgeContractVertex.branchSet x}).Connected := by
  classical
  cases x with
  | merged =>
      have hset :
          {a : V | a ∈ ({u, v} : Finset V)} = ({u, v} : Set V) := by
        ext a
        simp
      rw [EdgeContractVertex.branchSet_merged, hset]
      exact _root_.SimpleGraph.induce_pair_connected_of_adj (G := G) huv
  | keep z =>
      have hset : {a : V | a ∈ EdgeContractVertex.branchSet (.keep z)} = {z.1} := by
        ext a
        simp
      rw [hset]
      exact _root_.SimpleGraph.Connected.of_subsingleton

/-- The canonical branch-set model witnessing an edge contraction as a minor. -/
noncomputable def minorModel :
    MinorModel (contractEdgeGraph G huv) G where
  branchSet := EdgeContractVertex.branchSet
  branch_nonempty := EdgeContractVertex.branchSet_nonempty
  branch_connected := branch_connected (G := G) huv
  branch_disjoint := by
    intro x y hxy
    exact EdgeContractVertex.branchSet_disjoint hxy
  adjacent := by
    intro x y hxy
    exact hxy.2

/-- Contracting an edge produces a minor of the original graph. -/
theorem isMinor :
    IsMinor (contractEdgeGraph G huv) G := by
  exact ⟨minorModel (G := G) (huv := huv)⟩

end contractEdgeGraph

/-- Image of a finite vertex set under the edge-contraction projection. -/
noncomputable def edgeContractImageSet
    {W : Type w} [DecidableEq W] {a b : W}
    (A : Finset W) : Finset (EdgeContractVertex W a b) :=
  A.attach.image fun x =>
    EdgeContractVertex.projection (V := W) (u := a) (v := b) x.1

@[simp] theorem mem_edgeContractImageSet_projection
    {W : Type w} [DecidableEq W] {a b : W}
    {A : Finset W} {x : W} (hx : x ∈ A) :
    EdgeContractVertex.projection (V := W) (u := a) (v := b) x ∈
      edgeContractImageSet (a := a) (b := b) A := by
  classical
  exact Finset.mem_image.mpr ⟨⟨x, hx⟩, by simp, rfl⟩

end Erdos73Infrastructure.SimpleGraph.TreewidthSparsifier
