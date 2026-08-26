/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

open scoped Sym2

namespace Erdos547b.TreePartition

open SimpleGraph

universe u

variable {V : Type u}

/-- The vertices weakly below `x` when a connected graph is rooted at `r`.
In a tree this is precisely the vertex set of the rooted subtree at `x`. -/
noncomputable def rootedDescendants [Fintype V] (G : SimpleGraph V) (r x : V) : Finset V :=
  Finset.univ.filter fun y => G.dist r y = G.dist r x + G.dist x y

/-- Set-valued version, useful on connected-component subtypes where a `Finite`
instance is available without choosing decidable membership. -/
def rootedDescendantsSet (G : SimpleGraph V) (r x : V) : Set V :=
  {y | G.dist r y = G.dist r x + G.dist x y}

@[simp] theorem mem_rootedDescendants [Fintype V] {G : SimpleGraph V} {r x y : V} :
    y ∈ rootedDescendants G r x ↔ G.dist r y = G.dist r x + G.dist x y := by
  simp [rootedDescendants]

@[simp] theorem self_mem_rootedDescendants [Fintype V] (G : SimpleGraph V) (r x : V) :
    x ∈ rootedDescendants G r x := by
  simp

@[simp] theorem rootedDescendants_root [Fintype V] (G : SimpleGraph V)
    (r : V) : rootedDescendants G r r = Finset.univ := by
  ext y
  simp

/-- Zhao's `m`-tree condition (Definition 5.3): every rooted subtree below a
non-root vertex has at most `m` vertices.  The whole tree can be much larger. -/
def IsRootedMTree [Fintype V] (m : ℕ) (G : SimpleGraph V) (r : V) : Prop :=
  G.IsTree ∧ ∀ x, x ≠ r → (rootedDescendants G r x).card ≤ m

/-- The same `m`-tree predicate stated with `Set.ncard`. -/
def IsRootedMTreeNcard (m : ℕ) (G : SimpleGraph V) (r : V) : Prop :=
  G.IsTree ∧ ∀ x, x ≠ r → (rootedDescendantsSet G r x).ncard ≤ m

theorem IsRootedMTree.isTree [Fintype V] {m : ℕ} {G : SimpleGraph V} {r : V}
    (h : IsRootedMTree m G r) : G.IsTree := h.1

theorem IsRootedMTree.card_rootedDescendants_le [Fintype V]
    {m : ℕ} {G : SimpleGraph V} {r x : V} (h : IsRootedMTree m G r) (hx : x ≠ r) :
    (rootedDescendants G r x).card ≤ m := h.2 x hx

/-- A non-root vertex of a rooted tree has a unique adjacent vertex one level
closer to the root.  This is the parent used throughout Zhao's construction. -/
theorem existsUnique_parent
    {T : SimpleGraph V} (hT : T.IsTree) (r : V) {x : V} (hx : x ≠ r) :
    ∃! p : V, T.Adj p x ∧ T.dist r p + 1 = T.dist r x := by
  obtain ⟨w, hwPath, hwLength⟩ := hT.connected.exists_path_of_dist r x
  have hwNotNil : ¬w.Nil := SimpleGraph.Walk.not_nil_of_ne hx.symm
  refine ⟨w.penultimate, ⟨w.adj_penultimate hwNotNil, ?_⟩, ?_⟩
  · have hDrop : w.dropLast.length = T.dist r w.penultimate :=
      SimpleGraph.length_eq_dist_of_subwalk hwLength
        ((SimpleGraph.Walk.isSubwalk_rfl w).dropLast)
    calc
      T.dist r w.penultimate + 1 = w.dropLast.length + 1 := by rw [hDrop]
      _ = w.length := w.length_dropLast_add_one hwNotNil
      _ = T.dist r x := hwLength
  · intro q hq
    obtain ⟨v, hvPath, hvLength⟩ := hT.connected.exists_path_of_dist r q
    let v' : T.Walk r x := v.concat hq.1
    have hv'Length : v'.length = T.dist r x := by
      simp only [v', SimpleGraph.Walk.length_concat, hvLength]
      exact hq.2
    have hv'Path : v'.IsPath := v'.isPath_of_length_eq_dist hv'Length
    have hv'eq : v' = w := (hT.existsUnique_path r x).unique hv'Path hwPath
    have hpen := congrArg SimpleGraph.Walk.penultimate hv'eq
    simpa only [v', SimpleGraph.Walk.penultimate_concat] using hpen

/-- The parent selected from `existsUnique_parent`. -/
noncomputable def parent {T : SimpleGraph V} (hT : T.IsTree) (r : V)
    {x : V} (hx : x ≠ r) : V :=
  (existsUnique_parent hT r hx).exists.choose

theorem parent_adj {T : SimpleGraph V} (hT : T.IsTree) (r : V)
    {x : V} (hx : x ≠ r) : T.Adj (parent hT r hx) x :=
  (existsUnique_parent hT r hx).exists.choose_spec.1

theorem parent_dist_add_one {T : SimpleGraph V} (hT : T.IsTree) (r : V)
    {x : V} (hx : x ≠ r) : T.dist r (parent hT r hx) + 1 = T.dist r x :=
  (existsUnique_parent hT r hx).exists.choose_spec.2

theorem eq_parent_of_adj_of_dist_add_one {T : SimpleGraph V} (hT : T.IsTree) (r : V)
    {x p : V} (hx : x ≠ r) (hadj : T.Adj p x)
    (hdist : T.dist r p + 1 = T.dist r x) : p = parent hT r hx :=
  (existsUnique_parent hT r hx).unique ⟨hadj, hdist⟩
    (existsUnique_parent hT r hx).exists.choose_spec

/-- The root-distance parity changes across every edge of a tree. -/
theorem rootParity_ne_of_adj
    {T : SimpleGraph V} (hT : T.IsTree) (r : V) {x y : V} (hxy : T.Adj x y) :
    T.dist r x % 2 ≠ T.dist r y % 2 := by
  rcases hT.dist_eq_dist_add_one_of_adj r hxy with h | h
  · rw [h]
    omega
  · rw [h]
    omega

/-- `y` is a child of `x` in the orientation of a tree away from `r`. -/
def IsChild (T : SimpleGraph V) (r x y : V) : Prop :=
  T.Adj x y ∧ T.dist r y = T.dist r x + 1

/-- Zhao's `m`-vertex: a large rooted branch all of whose immediate child
branches are small. -/
def IsMVertex [Fintype V] (T : SimpleGraph V) (r : V) (m : ℕ) (x : V) : Prop :=
  m < (rootedDescendants T r x).card ∧
    ∀ y : V, IsChild T r x y → (rootedDescendants T r y).card ≤ m

theorem dist_eq_one_add_dist_of_child_of_mem_rootedDescendants [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) {r x y z : V} (hxy : IsChild T r x y)
    (hz : z ∈ rootedDescendants T r y) : T.dist x z = 1 + T.dist y z := by
  rw [mem_rootedDescendants] at hz
  have hxyDist : T.dist x y = 1 := T.dist_eq_one_iff_adj.mpr hxy.1
  have hUpper : T.dist x z ≤ 1 + T.dist y z := by
    simpa only [hxyDist] using
      (hT.connected.dist_triangle (u := x) (v := y) (w := z))
  have hLevel : T.dist r y = T.dist r x + 1 := hxy.2
  have hTriangle := hT.connected.dist_triangle (u := r) (v := x) (w := z)
  have hLower : 1 + T.dist y z ≤ T.dist x z := by omega
  exact Nat.le_antisymm hUpper hLower

theorem rootedDescendants_mono_of_child [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) {r x y : V} (hxy : IsChild T r x y) :
    rootedDescendants T r y ⊆ rootedDescendants T r x := by
  intro z hz
  rw [mem_rootedDescendants] at hz ⊢
  have hLevel : T.dist r y = T.dist r x + 1 := hxy.2
  have hxz := dist_eq_one_add_dist_of_child_of_mem_rootedDescendants hT hxy
    (mem_rootedDescendants.mpr hz)
  omega

/-- Distinct child-subtrees of a rooted tree are vertex-disjoint. -/
theorem disjoint_rootedDescendants_of_distinct_children [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) {r x y z : V}
    (hy : IsChild T r x y) (hz : IsChild T r x z) (hyz : y ≠ z) :
    Disjoint (rootedDescendants T r y) (rootedDescendants T r z) := by
  rw [Finset.disjoint_left]
  intro w hwy hwz
  obtain ⟨py, hpyPath, hpyLength⟩ := hT.connected.exists_path_of_dist y w
  obtain ⟨pz, hpzPath, hpzLength⟩ := hT.connected.exists_path_of_dist z w
  let py' : T.Walk x w := py.cons hy.1
  let pz' : T.Walk x w := pz.cons hz.1
  have hxyw := dist_eq_one_add_dist_of_child_of_mem_rootedDescendants hT hy hwy
  have hxzw := dist_eq_one_add_dist_of_child_of_mem_rootedDescendants hT hz hwz
  have hpy'Length : py'.length = T.dist x w := by
    simp only [py', SimpleGraph.Walk.length_cons, hpyLength]
    omega
  have hpz'Length : pz'.length = T.dist x w := by
    simp only [pz', SimpleGraph.Walk.length_cons, hpzLength]
    omega
  have hpy'Path : py'.IsPath := py'.isPath_of_length_eq_dist hpy'Length
  have hpz'Path : pz'.IsPath := pz'.isPath_of_length_eq_dist hpz'Length
  have hpEq : py' = pz' := (hT.existsUnique_path x w).unique hpy'Path hpz'Path
  have hsnd := congrArg SimpleGraph.Walk.snd hpEq
  exact hyz (by simpa only [py', pz', SimpleGraph.Walk.snd_cons] using hsnd)

/-- The finite separator step behind Zhao's tree carving: if the whole rooted
tree has more than `m` vertices, a deepest rooted subtree with more than `m`
vertices has all of its child-subtrees of size at most `m`. -/
theorem exists_large_rootedDescendants_with_small_children [Fintype V]
    (T : SimpleGraph V) (r : V) (m : ℕ) (hm : m < Fintype.card V) :
    ∃ x : V, m < (rootedDescendants T r x).card ∧
      ∀ y : V, IsChild T r x y → (rootedDescendants T r y).card ≤ m := by
  let large : Finset V :=
    Finset.univ.filter fun x => m < (rootedDescendants T r x).card
  have hr : r ∈ large := by
    simp [large, hm]
  obtain ⟨x, hxLarge, hxMax⟩ :=
    Finset.exists_max_image large (fun z => T.dist r z) ⟨r, hr⟩
  refine ⟨x, (Finset.mem_filter.mp hxLarge).2, ?_⟩
  intro y hy
  by_contra hmy
  have hyLarge : y ∈ large := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_of_not_ge hmy⟩
  have hMax := hxMax y hyLarge
  have hLevel : T.dist r y = T.dist r x + 1 := hy.2
  omega

theorem exists_isMVertex [Fintype V]
    (T : SimpleGraph V) (r : V) (m : ℕ) (hm : m < Fintype.card V) :
    ∃ x : V, IsMVertex T r m x :=
  exists_large_rootedDescendants_with_small_children T r m hm

/-- The exact finite family of root--parent edges removed in Zhao Definition 6.2.
Indices are zero-based here, so the cut edges are indexed by `j ≠ 0`. -/
def zhaoCutEdges [DecidableEq V] {k : ℕ} (roots : Fin k → V)
    (parent : ∀ j : Fin k, j.val ≠ 0 → V) : Finset (Sym2 V) :=
  Finset.univ.image fun j : {j : Fin k // j.val ≠ 0} =>
    s(roots j.1, parent j.1 j.2)

/-- A literal Lean encoding of Zhao Definition 6.2.  The components are the
connected components after deleting exactly the recorded root--parent edges.
The last two fields are respectively the parity-class root bound and Zhao's
reconnection rule. -/
structure ZhaoForestPartition [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (globalRoot : V) (m : ℕ) where
  numParts : ℕ
  numParts_pos : 0 < numParts
  roots : Fin numParts → V
  parent : ∀ j : Fin numParts, j.val ≠ 0 → V
  cut_adj : ∀ j hj, T.Adj (roots j) (parent j hj)
  components : Fin numParts ≃
    (T.deleteEdges (↑(zhaoCutEdges roots parent) : Set (Sym2 V))).ConnectedComponent
  root_mem : ∀ i, roots i ∈ (components i).supp
  first_root : roots ⟨0, numParts_pos⟩ = globalRoot
  parentPart : ∀ j : Fin numParts, j.val ≠ 0 → Fin numParts
  parent_mem : ∀ j hj, parent j hj ∈ (components (parentPart j hj)).supp
  parent_earlier : ∀ j hj, (parentPart j hj).val < j.val
  component_mTree : ∀ i, IsRootedMTreeNcard m (components i).toSimpleGraph
    ⟨roots i, root_mem i⟩
  parity_root_bound : ∀ q : Fin 2,
    (Finset.univ.filter fun i => T.dist globalRoot (roots i) % 2 = q.val).card ≤
      (Fintype.card V + m) / (m + 1)
  reconnect_rule : ∀ j hj,
    parent j hj = roots (parentPart j hj) ∨
      T.dist globalRoot (roots j) % 2 =
        T.dist globalRoot (roots (parentPart j hj)) % 2

/-- Deleting arbitrary edges from a tree leaves a forest. -/
theorem isAcyclic_deleteEdges_of_isTree
    {T : SimpleGraph V} (hT : T.IsTree) (s : Set (Sym2 V)) :
    (T.deleteEdges s).IsAcyclic :=
  hT.isAcyclic.anti (T.deleteEdges_le s)

/-- Consequently every component of a tree after edge deletion is itself a tree. -/
theorem isTree_deleteEdges_connectedComponent_of_isTree
    {T : SimpleGraph V} (hT : T.IsTree) (s : Set (Sym2 V))
    (c : (T.deleteEdges s).ConnectedComponent) : c.toSimpleGraph.IsTree :=
  (isAcyclic_deleteEdges_of_isTree hT s).isTree_connectedComponent c

end Erdos547b.TreePartition
