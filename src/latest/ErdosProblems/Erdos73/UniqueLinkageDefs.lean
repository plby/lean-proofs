/-
Adapted from the Apache-2.0-licensed polynomial-grid-minor-theorem development,
https://github.com/EdouardBonnet/polynomial-grid-minor-theorem,
commit fe2848173913a00d85c64d2a17af63f2cf0d4fbf,
proofs/Lax17Proofs/Source/{PseudoGridSlicingDefs,PseudoGridSlicing,UniqueLinkageOrdering}.lean.
Local changes: isolate the unique-linkage dependency chain, namespace and import
paths, and Lean 4.33 compatibility. The paper's current arXiv numbering is
Lemma 4.6 (the source comments refer to Lemma 4.5).
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import ErdosProblems.Erdos73.Menger

namespace Erdos73Infrastructure
universe u v w
namespace SimpleGraph

namespace PerfectPathPacking

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B : Finset V}

/-- The linkage uses every vertex of the ambient graph.  In Section 4.2 this
is applied after replacing the graph by `H''`, whose vertices are exactly the
vertices of the row linkage. -/
def SpansVertices (R : PerfectPathPacking G A B) : Prop :=
  ∀ v : V, v ∈ R.toPathPacking.vertexSet

/-- The perfect linkage is unique, up to its edge set.  This matches the form
needed by the Robertson--Seymour slicing lemma: every perfect `A`--`B` linkage
in the same graph has the same trace. -/
def IsUniqueLinkage (R : PerfectPathPacking G A B) : Prop :=
  R.SpansVertices ∧
    ∀ R' : PerfectPathPacking G A B,
      R'.toPathPacking.edgeSet = R.toPathPacking.edgeSet

end PerfectPathPacking

namespace PathSlicing

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B S T : Finset V} {M : ℕ}
variable {R : PerfectPathPacking G A B}

/-- A path crosses the threshold `t` of a ranking if it contains vertices on
both sides of the cut `{v | rank v < t}` / `{v | t ≤ rank v}`.

This is the form used in Lemma 4.5: after deleting the separator `S_t`, there
is no path connecting the lower side to the upper side.  The lower/upper
vertices need not be the endpoints of the path. -/
def GraphPathCrossesRankThreshold (rank : V → ℕ) (t : ℕ)
    (P : GraphPath G) : Prop :=
  ∃ y ∈ P.vertexSet, ∃ z ∈ P.vertexSet, rank y < t ∧ t ≤ rank z

/-- The formal output of Chuzhoy--Tan Lemma 4.5.

The paper states this as a bijection `μ : V(G) -> {1, ..., |V(G)|}`.  We use a
zero-based ranking into `ℕ`; injectivity plus `rank_lt_card` is the same finite
data.  The separator field says that the threshold separator `S_t` blocks every
path whose endpoints are on different sides of the threshold. -/
structure LinkageOrdering
    {V : Type u} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
    {A B : Finset V} (R : PerfectPathPacking G A B) where
  /-- The zero-based Robertson--Seymour topological order. -/
  rank : V → ℕ
  /-- The ranking is injective. -/
  rank_injective : Function.Injective rank
  /-- Every rank lies below the number of vertices. -/
  rank_lt_card : ∀ v : V, rank v < Fintype.card V
  /-- Along each linkage path, strict path order implies strict rank order. -/
  row_strict :
    ∀ r ⦃u v : V⦄,
      u ∈ (R.path r).vertexSet →
        v ∈ (R.path r).vertexSet →
          (R.path r).Before u v →
            u ≠ v →
              rank u < rank v
  /-- The unique row vertex selected for threshold `t`; in the paper this is
  the first vertex of the row whose `μ`-value is at least `t`, or the row's
  last vertex if no such vertex exists.  We use zero-based ranks, so `t = 0`
  gives the source endpoint and `t = |V|` gives the target endpoint. -/
  separatorVertex : ℕ → R.Index → V
  /-- The selected threshold vertex lies on its row. -/
  separatorVertex_mem :
    ∀ t r, separatorVertex t r ∈ (R.path r).vertexSet
  /-- Threshold `0` selects the first endpoint of every row. -/
  separatorVertex_zero :
    ∀ r, separatorVertex 0 r = (R.path r).source
  /-- Threshold `|V|` selects the last endpoint of every row. -/
  separatorVertex_card :
    ∀ r, separatorVertex (Fintype.card V) r = (R.path r).target
  /-- Vertices with rank below the threshold occur before the selected
  threshold vertex on their row. -/
  below_before_separator :
    ∀ t r ⦃v : V⦄,
      v ∈ (R.path r).vertexSet →
        rank v < t →
          (R.path r).Before v (separatorVertex t r)
  /-- Vertices with rank at or above the threshold occur after the selected
  threshold vertex on their row. -/
  separator_before_above :
    ∀ t r ⦃v : V⦄,
      v ∈ (R.path r).vertexSet →
        t ≤ rank v →
          (R.path r).Before (separatorVertex t r) v
  /-- Threshold vertices are monotone along each row. -/
  separatorVertex_monotone :
    ∀ r ⦃s t : ℕ⦄, s ≤ t →
      (R.path r).Before (separatorVertex s r) (separatorVertex t r)
  /-- The threshold separator `S_t`. -/
  separatorSet : ℕ → Finset V
  /-- The threshold separator is exactly the set of selected row vertices. -/
  separatorSet_eq :
    ∀ t, separatorSet t =
      Finset.univ.image fun r : R.Index => separatorVertex t r
  /-- Later threshold separators are contained in the earlier separator plus
  the earlier upper side.  This is the set-theoretic fact used in
  Observation 4.7 to prove monotonicity of `Q1(S_t)`. -/
  separatorSet_subset_separator_union_above :
    ∀ ⦃s t : ℕ⦄, s ≤ t →
      separatorSet t ⊆ separatorSet s ∪
        (Finset.univ.filter fun v : V => s ≤ rank v)
  /-- Advancing the threshold by one can only remove row-separator vertices
  whose rank is exactly the old threshold.  In the paper's construction this
  is immediate from choosing, on each row, the first vertex whose order is at
  least the threshold.  It is the structural input behind Observation 4.7's
  one-step growth bound for `Q1(S_t)`. -/
  separatorSet_sdiff_succ_subset_rankLevel :
    ∀ ⦃t : ℕ⦄, t < Fintype.card V →
      separatorSet t \ separatorSet (t + 1) ⊆
        (Finset.univ.filter fun v : V => rank v = t)
  /-- Every threshold separator has at most one vertex from each row path. -/
  separator_card_le : ∀ t : ℕ, (separatorSet t).card ≤ R.card
  /-- The separator blocks all paths that contain vertices on both sides of the
  threshold. -/
  separator_blocks :
    ∀ (t : ℕ) (P : GraphPath G),
      GraphPathCrossesRankThreshold rank t P →
        ∃ v ∈ P.vertexSet, v ∈ separatorSet t

namespace LinkageOrdering

variable {V : Type u} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B S T : Finset V} {R : PerfectPathPacking G A B}

/-- The vertices ranked before threshold `t`. -/
noncomputable def belowSet (theta : LinkageOrdering R) (t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => theta.rank v < t

/-- The vertices ranked at or after threshold `t`. -/
noncomputable def aboveSet (theta : LinkageOrdering R) (t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => t ≤ theta.rank v

end LinkageOrdering

/-- The directed dependency relation from Appendix B of Chuzhoy--Tan.

`LinkageDependency R u v` means that the auxiliary directed graph used to prove
Lemma 4.5 contains the directed edge `u -> v`.  Type-1 dependencies follow the
orientation of a row path.  Type-2 dependencies say that, on some row, a later
witness vertex adjacent to `v` forces every earlier vertex on that row to
precede `v` in the topological ordering. -/
def LinkageDependency
    (R : PerfectPathPacking G A B) (u v : V) : Prop :=
  (∃ r : R.Index,
    u ∈ (R.path r).vertexSet ∧
      v ∈ (R.path r).vertexSet ∧
        (R.path r).Before u v ∧ u ≠ v) ∨
    ∃ r r' : R.Index,
      r ≠ r' ∧
        u ∈ (R.path r).vertexSet ∧
          v ∈ (R.path r').vertexSet ∧
            ∃ w : V,
              w ∈ (R.path r).vertexSet ∧
                (R.path r).Before u w ∧
                  u ≠ w ∧ G.Adj w v


variable [Fintype V]

omit [Fintype V] in
/-- Appendix B, Observation B.1.  If `x` appears strictly before `y` on a row
and the dependency digraph has an edge `y -> z`, then it also has the edge
`x -> z`. -/
theorem linkageDependency_of_before_of_linkageDependency
    {R : PerfectPathPacking G A B} {x y z : V} {r : R.Index}
    (hxy : (R.path r).Before x y) (hxy_ne : x ≠ y)
    (hyz : LinkageDependency R y z) :
    LinkageDependency R x z := by
  classical
  have hxyData := ((R.path r).before_iff_vertexIndex_le).1 hxy
  have hx : x ∈ (R.path r).vertexSet := hxyData.1
  have hy : y ∈ (R.path r).vertexSet := hxyData.2.1
  rcases hyz with hyzType1 | hyzType2
  · rcases hyzType1 with ⟨r', hyr', hzr', hyzBefore, hyz_ne⟩
    have hrr' : r' = r := by
      by_contra hne
      exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hne)
        hyr' hy
    subst r'
    refine Or.inl ⟨r, hx, hzr', (R.path r).before_trans hxy hyzBefore, ?_⟩
    intro hxz
    have hyx : (R.path r).Before y x := by
      simpa [hxz] using hyzBefore
    exact hxy_ne ((R.path r).before_antisymm hxy hyx)
  · rcases hyzType2 with
      ⟨r', r'', hr_ne, hyr', hzr'', w, hwr', hywBefore, hyw_ne, hwz⟩
    have hrr' : r' = r := by
      by_contra hne
      exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hne)
        hyr' hy
    subst r'
    refine Or.inr
      ⟨r, r'', hr_ne, hx, hzr'', w, hwr',
        (R.path r).before_trans hxy hywBefore, ?_, hwz⟩
    intro hxw
    have hwy : (R.path r).Before w y := by
      simpa [hxw] using hxy
    exact hyw_ne ((R.path r).before_antisymm hywBefore hwy)

/-- The sorted list used to turn an injective ordered key on a finite type into
a zero-based ranking. -/
noncomputable def sortedByKey {α β : Type*} [Fintype α] [LinearOrder β]
    (key : α → β) (hkey : Function.Injective key) : List α := by
  classical
  letI : LinearOrder α := LinearOrder.lift' key hkey
  exact (Finset.univ : Finset α).sort (· ≤ ·)

/-- The zero-based rank of an element in the finite list sorted by `key`. -/
noncomputable def rankByKey {α β : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder β] (key : α → β) (hkey : Function.Injective key) (a : α) : ℕ :=
  (sortedByKey key hkey).idxOf a

theorem mem_sortedByKey {α β : Type*} [Fintype α] [LinearOrder β]
    (key : α → β) (hkey : Function.Injective key) (a : α) :
    a ∈ sortedByKey key hkey := by
  classical
  letI : LinearOrder α := LinearOrder.lift' key hkey
  simp [sortedByKey]

theorem sortedByKey_nodup {α β : Type*} [Fintype α] [LinearOrder β]
    (key : α → β) (hkey : Function.Injective key) :
    (sortedByKey key hkey).Nodup := by
  classical
  letI : LinearOrder α := LinearOrder.lift' key hkey
  simp [sortedByKey]

theorem sortedByKey_length {α β : Type*} [Fintype α] [LinearOrder β]
    (key : α → β) (hkey : Function.Injective key) :
    (sortedByKey key hkey).length = Fintype.card α := by
  classical
  letI : LinearOrder α := LinearOrder.lift' key hkey
  simp [sortedByKey]

theorem rankByKey_lt_card {α β : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder β] (key : α → β) (hkey : Function.Injective key) (a : α) :
    rankByKey key hkey a < Fintype.card α := by
  classical
  have hmem : a ∈ sortedByKey key hkey := mem_sortedByKey key hkey a
  simpa [rankByKey, sortedByKey_length key hkey] using
    (List.idxOf_lt_length_iff.2 hmem)

theorem rankByKey_injective {α β : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder β] (key : α → β) (hkey : Function.Injective key) :
    Function.Injective (rankByKey key hkey) := by
  classical
  intro a b h
  have ha : a ∈ sortedByKey key hkey := mem_sortedByKey key hkey a
  exact (List.idxOf_inj ha).1 (by simpa [rankByKey] using h)

theorem key_le_of_rankByKey_le {α β : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder β] (key : α → β) {a b : α}
    (hkey : Function.Injective key)
    (h : rankByKey key hkey a ≤ rankByKey key hkey b) :
    key a ≤ key b := by
  classical
  letI : LinearOrder α := LinearOrder.lift' key hkey
  let l := sortedByKey key hkey
  have haMem : a ∈ l := by simpa [l] using mem_sortedByKey key hkey a
  have hbMem : b ∈ l := by simpa [l] using mem_sortedByKey key hkey b
  have haLt : l.idxOf a < l.length := List.idxOf_lt_length_iff.2 haMem
  have hbLt : l.idxOf b < l.length := List.idxOf_lt_length_iff.2 hbMem
  let ia : Fin l.length := ⟨l.idxOf a, haLt⟩
  let ib : Fin l.length := ⟨l.idxOf b, hbLt⟩
  have hPair : l.Pairwise (fun x y : α => x ≤ y) := by
    change ((Finset.univ : Finset α).sort (· ≤ ·)).Pairwise
      (fun x y : α => x ≤ y)
    exact Finset.pairwise_sort (s := (Finset.univ : Finset α))
      (r := (· ≤ ·))
  have hiaib : ia ≤ ib := by
    exact h
  have hleAlpha : l.get ia ≤ l.get ib :=
    hPair.rel_get_of_le hiaib
  have hle : key (l.get ia) ≤ key (l.get ib) := by
    exact hleAlpha
  have hgeta : l.get ia = a := by
    exact List.idxOf_get (a := a) (l := l) haLt
  have hgetb : l.get ib = b := by
    exact List.idxOf_get (a := b) (l := l) hbLt
  calc
    key a = key (l.get ia) := by rw [hgeta]
    _ ≤ key (l.get ib) := hle
    _ = key b := by rw [hgetb]

theorem rankByKey_lt_of_key_lt {α β : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder β] (key : α → β) (hkey : Function.Injective key)
    {a b : α} (hltKey : key a < key b) :
    rankByKey key hkey a < rankByKey key hkey b := by
  classical
  by_contra hnot
  have hleRank : rankByKey key hkey b ≤ rankByKey key hkey a :=
    Nat.le_of_not_gt hnot
  have hleKey : key b ≤ key a := key_le_of_rankByKey_le key hkey hleRank
  exact (not_le_of_gt hltKey) hleKey


end PathSlicing
end SimpleGraph
end Erdos73Infrastructure

