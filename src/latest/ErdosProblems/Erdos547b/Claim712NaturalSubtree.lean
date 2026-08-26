/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.TreePartition
import ErdosProblems.Erdos547b.Lemma59

namespace SimpleGraphRose547

open SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoLemma59
open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable local instance (T : SimpleGraph V) : T.LocallyFinite := fun _ =>
  Fintype.ofFinite _

/-- The children of `x` in the orientation of a tree away from `r`. -/
noncomputable def children (T : SimpleGraph V) (r x : V) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun y => IsChild T r x y

@[simp] theorem mem_children {T : SimpleGraph V} {r x y : V} :
    y ∈ children T r x ↔ IsChild T r x y := by
  classical
  simp [children]

/-- A graph-level natural rooted subtree: choose a vertex `x` and retain
some whole branches rooted at children of `x`.  Allowing arbitrary `x`
incorporates Zhao's repeated `descend` constructor. -/
noncomputable def IsNaturalVertexSet (T : SimpleGraph V) (r : V) (S : Finset V) : Prop := by
  classical
  exact ∃ (x : V) (kept : Finset V),
      kept ⊆ children T r x ∧
      S = insert x (kept.biUnion fun y => rootedDescendants T r y)

theorem root_not_mem_rootedDescendants_child
    {T : SimpleGraph V} {r x y : V} (hy : IsChild T r x y) :
    x ∉ rootedDescendants T r y := by
  rw [mem_rootedDescendants]
  have hxy : T.dist y x = 1 := by
    rw [T.dist_comm]
    exact T.dist_eq_one_iff_adj.mpr hy.1
  rw [hy.2, hxy]
  omega

/-- Every strict descendant of `x` lies below a unique first child of `x`.
Only existence is needed for the cardinal decomposition below. -/
theorem exists_child_of_mem_rootedDescendants
    {T : SimpleGraph V} (hT : T.IsTree) {r x z : V}
    (hz : z ∈ rootedDescendants T r x) (hzx : z ≠ x) :
    ∃ y : V, IsChild T r x y ∧ z ∈ rootedDescendants T r y := by
  obtain ⟨p, hpPath, hpLength⟩ := hT.connected.exists_path_of_dist x z
  have hpNotNil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hzx.symm
  let y := p.snd
  have hxy : T.Adj x y := p.adj_snd hpNotNil
  have hxyDist : T.dist x y = 1 := T.dist_eq_one_iff_adj.mpr hxy
  have htailLength : p.tail.length = T.dist y z :=
    SimpleGraph.length_eq_dist_of_subwalk hpLength
      ((SimpleGraph.Walk.isSubwalk_rfl p).tail)
  have hsplit : T.dist x z = 1 + T.dist y z := by
    rw [← hpLength, ← htailLength]
    have hlen := p.length_tail_add_one hpNotNil
    omega
  have hzroot := (mem_rootedDescendants.mp hz)
  rcases hT.dist_eq_dist_add_one_of_adj r hxy with hup | hdown
  · have htriangle := hT.connected.dist_triangle (u := r) (v := y) (w := z)
    omega
  · refine ⟨y, ⟨hxy, hdown⟩, ?_⟩
    rw [mem_rootedDescendants]
    omega

/-- The descendants of `x` decompose as `x` and the pairwise-disjoint
descendant branches at the children of `x`. -/
theorem rootedDescendants_eq_insert_biUnion_children
    {T : SimpleGraph V} (hT : T.IsTree) (r x : V) :
    rootedDescendants T r x =
      insert x ((children T r x).biUnion fun y => rootedDescendants T r y) := by
  classical
  ext z
  constructor
  · intro hz
    by_cases hzx : z = x
    · simp [hzx]
    · obtain ⟨y, hy, hzy⟩ := exists_child_of_mem_rootedDescendants hT hz hzx
      simp only [Finset.mem_insert, Finset.mem_biUnion]
      exact Or.inr ⟨y, mem_children.mpr hy, hzy⟩
  · simp only [Finset.mem_insert, Finset.mem_biUnion]
    rintro (rfl | ⟨y, hy, hz⟩)
    · exact self_mem_rootedDescendants T r _
    · exact rootedDescendants_mono_of_child hT (mem_children.mp hy) hz

theorem pairwiseDisjoint_rootedDescendants_children
    {T : SimpleGraph V} (hT : T.IsTree) (r x : V) :
    ((children T r x : Finset V) : Set V).PairwiseDisjoint
      (fun y => rootedDescendants T r y) := by
  classical
  intro y hy z hz hyz
  exact disjoint_rootedDescendants_of_distinct_children hT
    (mem_children.mp hy) (mem_children.mp hz) hyz

/-- Cardinal form of the child-branch decomposition. -/
theorem card_rootedDescendants_eq_one_add_sum_children
    {T : SimpleGraph V} (hT : T.IsTree) (r x : V) :
    (rootedDescendants T r x).card =
      1 + ∑ y ∈ children T r x, (rootedDescendants T r y).card := by
  classical
  rw [rootedDescendants_eq_insert_biUnion_children hT]
  have hxnot : x ∉ (children T r x).biUnion (fun y => rootedDescendants T r y) := by
    intro hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact root_not_mem_rootedDescendants_child (mem_children.mp hy) hxy
  rw [Finset.card_insert_of_notMem hxnot, Finset.card_biUnion
    (pairwiseDisjoint_rootedDescendants_children hT r x)]
  omega

/-- Greedy prefix selection, in the form needed after decomposing a rooted
tree into its child branches. -/
theorem exists_take_sum_in_half_open_interval
    (q : ℕ) (hq : 0 < q) (weights : List ℕ)
    (hsmall : ∀ a ∈ weights, a < q)
    (htotal : q ≤ 1 + weights.sum) :
    ∃ i : ℕ, q ≤ 1 + (weights.take i).sum ∧
      1 + (weights.take i).sum < 2 * q ∧
        (q = 1 ∨ 1 + (weights.take i).sum < 2 * q - 1) := by
  let P : ℕ → Prop := fun i => q ≤ 1 + (weights.take i).sum
  have hex : ∃ i, P i := by
    refine ⟨weights.length, ?_⟩
    simpa [P] using htotal
  let i := Nat.find hex
  have hi : P i := Nat.find_spec hex
  refine ⟨i, hi, ?_, ?_⟩
  · by_cases hi0 : i = 0
    · simp only [hi0, List.take_zero, List.sum_nil, add_zero]
      omega
    · let j := i - 1
      have hji : j < i := by simp only [j]; omega
      have hnot : ¬ P j := Nat.find_min hex hji
      have hjlt : 1 + (weights.take j).sum < q := by
        simp only [P] at hnot
        omega
      have hilen : i ≤ weights.length :=
        Nat.find_min' hex (m := weights.length) (by simpa [P] using htotal)
      have hjlen : j < weights.length := by omega
      have hisucc : j + 1 = i := by simp only [j]; omega
      have hw : weights[j] < q := hsmall weights[j] (List.getElem_mem hjlen)
      rw [← hisucc, List.sum_take_succ weights j hjlen]
      omega
  · by_cases hq1 : q = 1
    · exact Or.inl hq1
    · right
      by_cases hi0 : i = 0
      · simp only [hi0, List.take_zero, List.sum_nil, add_zero]
        omega
      · let j := i - 1
        have hji : j < i := by simp only [j]; omega
        have hnot : ¬ P j := Nat.find_min hex hji
        have hjlt : 1 + (weights.take j).sum < q := by
          simp only [P] at hnot
          omega
        have hilen : i ≤ weights.length :=
          Nat.find_min' hex (m := weights.length) (by simpa [P] using htotal)
        have hjlen : j < weights.length := by omega
        have hisucc : j + 1 = i := by simp only [j]; omega
        have hw : weights[j] < q := hsmall weights[j] (List.getElem_mem hjlen)
        rw [← hisucc, List.sum_take_succ weights j hjlen]
        omega

/-- Direct SimpleGraph form of Zhao's Fact 7.9(1).  The selected set is an
actual natural rooted subtree of the original tree, not merely a rose-tree
code.  The lower bound is the integral form of `k / 2`. -/
theorem exists_naturalVertexSet_card
    {T : SimpleGraph V} (hT : T.IsTree) (r : V) (k : ℕ)
    (hk2 : 2 ≤ k) (hk : k ≤ Fintype.card V) :
    ∃ S : Finset V, IsNaturalVertexSet T r S ∧
      (k + 1) / 2 ≤ S.card ∧ S.card < k := by
  let q := (k + 1) / 2
  have hq : 0 < q := by simp only [q]; omega
  have hqk : q < k := by simp only [q]; omega
  have hqcard : q ≤ Fintype.card V := by
    exact (by simp only [q]; omega : q ≤ k).trans hk
  have hm : q - 1 < Fintype.card V := by omega
  obtain ⟨x, hxlarge, hxsmall⟩ :=
    exists_large_rootedDescendants_with_small_children T r (q - 1) hm
  let cs := (children T r x).toList
  let weights := cs.map fun y => (rootedDescendants T r y).card
  have hsmall : ∀ a ∈ weights, a < q := by
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    have hyChild : IsChild T r x y := mem_children.mp (by
      simpa only [cs, Finset.mem_toList] using hy)
    have := hxsmall y hyChild
    omega
  have htotal : q ≤ 1 + weights.sum := by
    have hcard := card_rootedDescendants_eq_one_add_sum_children hT r x
    have hsumList (s : Finset V) :
        (s.toList.map fun y => (rootedDescendants T r y).card).sum =
          ∑ y ∈ s, (rootedDescendants T r y).card := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih => simp [ha, ih]
    have hsum : weights.sum = ∑ y ∈ children T r x,
        (rootedDescendants T r y).card := by
      simpa only [weights, cs] using hsumList (children T r x)
    rw [hsum]
    omega
  obtain ⟨i, hiLower, hiUpper, hiSharp⟩ :=
    exists_take_sum_in_half_open_interval q hq weights hsmall htotal
  let kept : Finset V := (cs.take i).toFinset
  let S : Finset V := insert x (kept.biUnion fun y => rootedDescendants T r y)
  have hkept : kept ⊆ children T r x := by
    intro y hy
    have hyList : y ∈ cs.take i := by simpa only [kept, List.mem_toFinset] using hy
    have hyCs : y ∈ cs := List.mem_of_mem_take hyList
    simpa only [cs, Finset.mem_toList] using hyCs
  have hpair : ((kept : Finset V) : Set V).PairwiseDisjoint
      (fun y => rootedDescendants T r y) := by
    intro y hy z hz hyz
    exact pairwiseDisjoint_rootedDescendants_children hT r x
      (hkept hy) (hkept hz) hyz
  have hxnot : x ∉ kept.biUnion (fun y => rootedDescendants T r y) := by
    intro hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact root_not_mem_rootedDescendants_child (mem_children.mp (hkept hy)) hxy
  have hcsNodup : cs.Nodup := by
    exact Finset.nodup_toList (children T r x)
  have htakeNodup : (cs.take i).Nodup := hcsNodup.take
  have hScard : S.card = 1 + (weights.take i).sum := by
    rw [show S = insert x (kept.biUnion fun y => rootedDescendants T r y) by rfl,
      Finset.card_insert_of_notMem hxnot, Finset.card_biUnion hpair]
    rw [List.sum_toFinset (fun y => (rootedDescendants T r y).card) htakeNodup]
    simp only [kept, weights, cs, List.map_take]
    omega
  refine ⟨S, ⟨x, kept, hkept, rfl⟩, ?_, ?_⟩
  · rw [hScard]
    exact hiLower
  · rw [hScard]
    by_cases hq1 : q = 1
    · have : 2 * q ≤ k := by simpa [hq1] using hk2
      exact hiUpper.trans_le this
    · exact (hiSharp.resolve_left hq1).trans_le (by simp only [q]; omega)

/-! ### Structural consequences in the original graph -/

/-- The vertex set obtained from explicit natural-subtree witnesses. -/
noncomputable def naturalVertices (T : SimpleGraph V) (r x : V)
    (kept : Finset V) : Finset V := by
  classical
  exact insert x (kept.biUnion fun y => rootedDescendants T r y)

/-- The witness-exposing form of `IsNaturalVertexSet`. -/
def IsNaturalVertexSetAt (T : SimpleGraph V) (r x : V) (S : Finset V) : Prop :=
  ∃ kept : Finset V, kept ⊆ children T r x ∧ S = naturalVertices T r x kept

theorem isNaturalVertexSet_iff_exists_at {T : SimpleGraph V} {r : V} {S : Finset V} :
    IsNaturalVertexSet T r S ↔ ∃ x, IsNaturalVertexSetAt T r x S := by
  constructor
  · rintro ⟨x, kept, hkept, rfl⟩
    exact ⟨x, kept, hkept, rfl⟩
  · rintro ⟨x, kept, hkept, rfl⟩
    exact ⟨x, kept, hkept, rfl⟩

/-- Fact 7.9(1) with the selected attachment root retained explicitly for
all downstream splitting and gluing arguments. -/
theorem exists_naturalVertexSetAt_card
    {T : SimpleGraph V} (hT : T.IsTree) (r : V) (k : ℕ)
    (hk2 : 2 ≤ k) (hk : k ≤ Fintype.card V) :
    ∃ (x : V) (S : Finset V), IsNaturalVertexSetAt T r x S ∧
      (k + 1) / 2 ≤ S.card ∧ S.card < k := by
  obtain ⟨S, hS, hlo, hhi⟩ := exists_naturalVertexSet_card hT r k hk2 hk
  rw [isNaturalVertexSet_iff_exists_at] at hS
  obtain ⟨x, hx⟩ := hS
  exact ⟨x, S, hx, hlo, hhi⟩

@[simp] theorem mem_naturalVertices {T : SimpleGraph V} {r x v : V}
    {kept : Finset V} :
    v ∈ naturalVertices T r x kept ↔
      v = x ∨ ∃ y ∈ kept, v ∈ rootedDescendants T r y := by
  classical
  simp [naturalVertices, eq_comm]

/-- A shortest path from the root of a descendant branch to a vertex in the
branch never leaves that branch. -/
theorem support_shortestPath_subset_rootedDescendants
    {T : SimpleGraph V} (hT : T.IsTree) {r x v : V}
    (hv : v ∈ rootedDescendants T r x)
    (p : T.Walk x v) (hpLength : p.length = T.dist x v) :
    ∀ z ∈ p.support, z ∈ rootedDescendants T r x := by
  intro z hz
  have htake : (p.takeUntil z hz).length = T.dist x z :=
    SimpleGraph.length_eq_dist_of_subwalk hpLength (p.isSubwalk_takeUntil hz)
  have hdrop : (p.dropUntil z hz).length = T.dist z v :=
    SimpleGraph.length_eq_dist_of_subwalk hpLength (p.isSubwalk_dropUntil hz)
  have hsumWalk := congrArg SimpleGraph.Walk.length (p.take_spec hz)
  have hsplit : T.dist x v = T.dist x z + T.dist z v := by
    simp only [SimpleGraph.Walk.length_append] at hsumWalk
    omega
  have hvDist := mem_rootedDescendants.mp hv
  have hupper := hT.connected.dist_triangle (u := r) (v := x) (w := z)
  have hlower := hT.connected.dist_triangle (u := r) (v := z) (w := v)
  rw [mem_rootedDescendants]
  omega

/-- Every rooted-descendant branch induces a connected subgraph. -/
theorem connected_induce_rootedDescendants
    {T : SimpleGraph V} (hT : T.IsTree) (r x : V) :
    (T.induce (rootedDescendants T r x : Set V)).Connected := by
  apply T.induce_connected_of_patches x (by simp)
  intro v hv
  obtain ⟨p, hpPath, hpLength⟩ := hT.connected.exists_path_of_dist x v
  let P : Set V := {z | z ∈ p.support}
  have hPsub : P ⊆ (rootedDescendants T r x : Set V) := by
    intro z hz
    exact support_shortestPath_subset_rootedDescendants hT hv p hpLength z hz
  have hxP : x ∈ P := p.start_mem_support
  have hvP : v ∈ P := p.end_mem_support
  refine ⟨P, hPsub, hxP, hvP, ?_⟩
  exact (p.connected_induce_support) ⟨x, hxP⟩ ⟨v, hvP⟩

/-- An edge incident to a non-root vertex of a rooted-descendant branch
cannot leave that branch. -/
theorem adj_mem_rootedDescendants_of_mem_of_ne
    {T : SimpleGraph V} (hT : T.IsTree) {r x u v : V}
    (hu : u ∈ rootedDescendants T r x) (hux : u ≠ x)
    (huv : T.Adj u v) : v ∈ rootedDescendants T r x := by
  have huDist := mem_rootedDescendants.mp hu
  rcases hT.dist_eq_dist_add_one_of_adj r huv with hup | hdown
  · have hur : u ≠ r := by
      intro hur
      subst u
      have hrr : T.dist r r = 0 := T.dist_self
      have hrxZero : T.dist r x = 0 := by omega
      have : r = x := hT.connected.dist_eq_zero_iff.mp hrxZero
      exact hux this
    obtain ⟨q, hqPath, hqLength⟩ := hT.connected.exists_path_of_dist x u
    have hqNotNil : ¬q.Nil := SimpleGraph.Walk.not_nil_of_ne hux.symm
    let w := q.penultimate
    have hwu : T.Adj w u := q.adj_penultimate hqNotNil
    have hdropLength : q.dropLast.length = T.dist x w :=
      SimpleGraph.length_eq_dist_of_subwalk hqLength
        ((SimpleGraph.Walk.isSubwalk_rfl q).dropLast)
    have hxw : T.dist x w + 1 = T.dist x u := by
      have hlen := q.length_dropLast_add_one hqNotNil
      omega
    have hrwUpper := hT.connected.dist_triangle (u := r) (v := x) (w := w)
    have hruLower := hT.connected.dist_triangle (u := r) (v := w) (w := u)
    have hwuDist : T.dist w u = 1 := T.dist_eq_one_iff_adj.mpr hwu
    have hrw : T.dist r w + 1 = T.dist r u := by omega
    have hvParent : v = parent hT r hur :=
      eq_parent_of_adj_of_dist_add_one hT r hur huv.symm (by omega)
    have hwParent : w = parent hT r hur :=
      eq_parent_of_adj_of_dist_add_one hT r hur hwu hrw
    rw [hvParent, ← hwParent, mem_rootedDescendants]
    omega
  · have htri := hT.connected.dist_triangle (u := r) (v := x) (w := v)
    rcases hT.dist_eq_dist_add_one_of_adj x huv with hback | hforward
    · omega
    · rw [mem_rootedDescendants]
      omega

/-- A natural vertex set induces a connected graph. -/
theorem IsNaturalVertexSetAt.connected
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S) :
    (T.induce (S : Set V)).Connected := by
  obtain ⟨kept, hkept, rfl⟩ := hS
  apply T.induce_connected_of_patches x (by simp [naturalVertices])
  intro v hv
  change v ∈ naturalVertices T r x kept at hv
  rw [mem_naturalVertices] at hv
  rcases hv with hvx | ⟨y, hyKept, hvDesc⟩
  · subst v
    refine ⟨{x}, ?_, by simp, by simp, ?_⟩
    · intro z hz
      change z ∈ naturalVertices T r x kept
      rw [mem_naturalVertices]
      exact Or.inl (by simpa using hz)
    · exact SimpleGraph.Reachable.refl _
  · let D : Set V := (rootedDescendants T r y : Finset V)
    let P : Set V := {x} ∪ D
    have hyChild : IsChild T r x y := mem_children.mp (hkept hyKept)
    have hDconn : (T.induce D).Connected := connected_induce_rootedDescendants hT r y
    have hPconn : (T.induce P).Connected := by
      apply T.connected_induce_union (s := {x}) (t := D)
        (by simp) hDconn.preconnected (v := x) (w := y)
      · simp
      · exact self_mem_rootedDescendants T r y
      · exact hyChild.1
    have hPsub : P ⊆ (naturalVertices T r x kept : Finset V) := by
      intro z hz
      rcases hz with hz | hz
      · change z ∈ naturalVertices T r x kept
        rw [mem_naturalVertices]
        exact Or.inl (by simpa using hz)
      · change z ∈ naturalVertices T r x kept
        rw [mem_naturalVertices]
        exact Or.inr ⟨y, hyKept, hz⟩
    have hxP : x ∈ P := by simp [P]
    have hvP : v ∈ P := Or.inr hvDesc
    exact ⟨P, hPsub, hxP, hvP, hPconn ⟨x, hxP⟩ ⟨v, hvP⟩⟩

/-- A natural vertex set of a tree itself induces a tree. -/
theorem IsNaturalVertexSetAt.isTree
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S) :
    (T.induce (S : Set V)).IsTree :=
  ⟨hS.connected hT, hT.isAcyclic.induce _⟩

/-- The natural subtree's only possible attachment vertex is its selected
root `x`. -/
theorem IsNaturalVertexSetAt.singleBoundary
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S) :
    ∀ ⦃u v : V⦄, u ∈ S → v ∉ S → T.Adj u v → u = x := by
  obtain ⟨kept, hkept, rfl⟩ := hS
  intro u v hu hv huv
  rw [mem_naturalVertices] at hu
  rcases hu with hux | ⟨y, hy, huy⟩
  · exact hux
  · by_contra hux
    by_cases huyEq : u = y
    · subst u
      have hyChild := mem_children.mp (hkept hy)
      rcases hT.dist_eq_dist_add_one_of_adj r huv with hup | hdown
      · have hyr : y ≠ r := by
          intro hyr
          subst y
          have := hyChild.2
          simp only [T.dist_self] at this
          omega
        have hvParent : v = parent hT r hyr :=
          eq_parent_of_adj_of_dist_add_one hT r hyr huv.symm (by omega)
        have hxParent : x = parent hT r hyr :=
          eq_parent_of_adj_of_dist_add_one hT r hyr hyChild.1 hyChild.2.symm
        apply hv
        rw [mem_naturalVertices]
        exact Or.inl (hvParent.trans hxParent.symm)
      · apply hv
        rw [mem_naturalVertices]
        refine Or.inr ⟨y, hy, ?_⟩
        rw [mem_rootedDescendants]
        have hyvdist : T.dist y v = 1 := T.dist_eq_one_iff_adj.mpr huv
        omega
    · have hvDesc := adj_mem_rootedDescendants_of_mem_of_ne hT huy huyEq huv
      apply hv
      rw [mem_naturalVertices]
      exact Or.inr ⟨y, hy, hvDesc⟩

/-- If the original global root belongs to a natural subtree selected at
`x`, then `x` is that global root. -/
theorem IsNaturalVertexSetAt.selectedRoot_eq_of_globalRoot_mem
    {T : SimpleGraph V} {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S) (hr : r ∈ S) : x = r := by
  obtain ⟨kept, hkept, rfl⟩ := hS
  rw [mem_naturalVertices] at hr
  rcases hr with hr | ⟨y, hy, hry⟩
  · exact hr.symm
  · have hyChild := mem_children.mp (hkept hy)
    have hryDist := mem_rootedDescendants.mp hry
    have hrr : T.dist r r = 0 := T.dist_self
    have hryZero : T.dist r y = 0 := by omega
    have hlevel := hyChild.2
    omega

/-- Outside vertices whose only possible neighbour is the attachment root.
For a connected tree these are precisely the one-vertex components of the
induced complement. -/
noncomputable def complementRootLeaves (T : SimpleGraph V) (x : V)
    (S : Finset V) : Finset V := by
  classical
  exact (Finset.univ \ S).filter fun v => ∀ ⦃w⦄, T.Adj v w → w = x

/-- The remaining (non-singleton-component) part of the complement. -/
noncomputable def complementNonisolated (T : SimpleGraph V) (x : V)
    (S : Finset V) : Finset V := by
  classical
  exact (Finset.univ \ S) \ complementRootLeaves T x S

@[simp] theorem mem_complementRootLeaves {T : SimpleGraph V} {x v : V}
    {S : Finset V} :
    v ∈ complementRootLeaves T x S ↔
      v ∉ S ∧ ∀ ⦃w⦄, T.Adj v w → w = x := by
  classical
  simp [complementRootLeaves]

@[simp] theorem mem_complementNonisolated {T : SimpleGraph V} {x v : V}
    {S : Finset V} :
    v ∈ complementNonisolated T x S ↔
      v ∉ S ∧ v ∉ complementRootLeaves T x S := by
  classical
  simp [complementNonisolated]

/-- For a natural subtree, `complementRootLeaves` is exactly the set of
isolated vertices in the induced complement. -/
theorem IsNaturalVertexSetAt.mem_complementRootLeaves_iff_isolated
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S) {v : V} :
    v ∈ complementRootLeaves T x S ↔
      v ∉ S ∧ ∀ ⦃w⦄, w ∉ S → ¬ T.Adj v w := by
  constructor
  · intro hv
    have hv' := mem_complementRootLeaves.mp hv
    refine ⟨hv'.1, ?_⟩
    intro w hw hAdj
    have hwx := hv'.2 hAdj
    subst w
    exact hw (by
      obtain ⟨kept, hkept, rfl⟩ := hS
      simp [naturalVertices])
  · rintro ⟨hvS, hviso⟩
    rw [mem_complementRootLeaves]
    refine ⟨hvS, ?_⟩
    intro w hvw
    by_contra hwx
    by_cases hwS : w ∈ S
    · exact hwx (hS.singleBoundary hT hwS hvS hvw.symm)
    · exact hviso hwS hvw

/-- Thus the complementary core consists exactly of vertices having a
neighbour that also lies outside the natural subtree. -/
theorem IsNaturalVertexSetAt.mem_complementNonisolated_iff
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S) {v : V} :
    v ∈ complementNonisolated T x S ↔
      v ∉ S ∧ ∃ w, w ∉ S ∧ T.Adj v w := by
  rw [mem_complementNonisolated]
  constructor
  · rintro ⟨hvS, hvL⟩
    rw [hS.mem_complementRootLeaves_iff_isolated hT] at hvL
    push Not at hvL
    obtain ⟨w, hwS, hvw⟩ := hvL hvS
    exact ⟨hvS, w, hwS, hvw⟩
  · rintro ⟨hvS, w, hwS, hvw⟩
    refine ⟨hvS, ?_⟩
    rw [hS.mem_complementRootLeaves_iff_isolated hT]
    push Not
    intro
    exact ⟨w, hwS, hvw⟩

/-- Every isolated complementary vertex is an ordinary degree-one leaf
attached to the selected root. -/
theorem IsNaturalVertexSetAt.degree_eq_one_of_mem_complementRootLeaves
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S) {v : V}
    (hv : v ∈ complementRootLeaves T x S) : T.degree v = 1 := by
  rw [degree_eq_one_iff_existsUnique_adj]
  refine ⟨x, ?_, ?_⟩
  · have hvS := (mem_complementRootLeaves.mp hv).1
    have hvx : v ≠ x := by
      intro hvx
      subst v
      apply hvS
      obtain ⟨kept, hkept, rfl⟩ := hS
      simp [naturalVertices]
    obtain ⟨p, hpPath⟩ := hT.connected.exists_isPath v x
    have hpNotNil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hvx
    have hvw : T.Adj v p.snd := p.adj_snd hpNotNil
    have hsnd : p.snd = x := (mem_complementRootLeaves.mp hv).2 hvw
    simpa [hsnd] using hvw
  · intro w hvw
    exact (mem_complementRootLeaves.mp hv).2 hvw

/-- The exact `C₁, C₂, L` split expected by `RootedForestGlue712`: `C₂=S`,
`C₁` is the nonisolated complement, and `L` consists of omitted root leaves. -/
theorem IsNaturalVertexSetAt.complement_split
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S) :
    let C₁ := complementNonisolated T x S
    let L := complementRootLeaves T x S
    Disjoint C₁ S ∧ Disjoint C₁ L ∧ Disjoint S L ∧
      (C₁ ∪ S) ∪ L = Finset.univ ∧
      (∀ z ∈ L, ∀ ⦃w⦄, T.Adj z w → w = x) ∧
      (∀ ⦃u v⦄, u ∈ C₁ → v ∈ S → T.Adj u v → v = x) := by
  classical
  dsimp only
  have hboundary := hS.singleBoundary hT
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro z hzC hzS
    exact (mem_complementNonisolated.mp hzC).1 hzS
  · exact Finset.sdiff_disjoint
  · rw [Finset.disjoint_left]
    intro z hzS hzL
    exact (mem_complementRootLeaves.mp hzL).1 hzS
  · ext z
    by_cases hzS : z ∈ S
    · simp [hzS]
    · by_cases hzL : z ∈ complementRootLeaves T x S
      · simp [hzS, hzL]
      · have hzC : z ∈ complementNonisolated T x S := by
          simp [hzS, hzL]
        simp [hzC]
  · intro z hzL w hzw
    exact (mem_complementRootLeaves.mp hzL).2 hzw
  · intro u v hu hv huv
    exact hboundary hv (mem_complementNonisolated.mp hu).1 huv.symm

/-! ### The nonisolated complementary rooted forest -/

/-- Attachment roots of the nonisolated complementary forest. -/
noncomputable def complementRoots (T : SimpleGraph V) (x : V) (S : Finset V) :
    Finset {v // v ∈ complementNonisolated T x S} := by
  classical
  exact Finset.univ.filter fun v => T.Adj v x

@[simp] theorem mem_complementRoots {T : SimpleGraph V} {x : V} {S : Finset V}
    {v : {v // v ∈ complementNonisolated T x S}} :
    v ∈ complementRoots T x S ↔ T.Adj v x := by
  classical
  simp [complementRoots]

/-- A complementary-core vertex is a forest root exactly when it has an
edge to the selected natural subtree.  The endpoint there is necessarily
the selected attachment root `x`. -/
theorem IsNaturalVertexSetAt.mem_complementRoots_iff_exists_adj_selected
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S)
    (v : {v // v ∈ complementNonisolated T x S}) :
    v ∈ complementRoots T x S ↔ ∃ w ∈ S, T.Adj v w := by
  have hxS : x ∈ S := by
    obtain ⟨kept, hkept, rfl⟩ := hS
    simp [naturalVertices]
  constructor
  · intro hv
    exact ⟨x, hxS, (mem_complementRoots.mp hv)⟩
  · rintro ⟨w, hwS, hvw⟩
    have hwx := hS.singleBoundary hT hwS
      (mem_complementNonisolated.mp v.property).1 hvw.symm
    rw [mem_complementRoots]
    simpa [hwx] using hvw

/-- The cone over the nonisolated complement is a tree.  Connectivity is
proved by following parent pointers toward `x`; acyclicity follows from the
obvious embedding of the cone back into the original tree. -/
theorem IsNaturalVertexSetAt.rootedForestCone_complement_isTree
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S) :
    (rootedForestCone
      (T.induce (complementNonisolated T x S : Set V))
      (complementRoots T x S)).IsTree := by
  classical
  let C₁ := complementNonisolated T x S
  let F := T.induce (C₁ : Set V)
  let R := complementRoots T x S
  let K := rootedForestCone F R
  have hxS : x ∈ S := by
    obtain ⟨kept, hkept, rfl⟩ := hS
    simp [naturalVertices]
  have hxC : x ∉ C₁ := fun hx => (mem_complementNonisolated.mp hx).1 hxS
  have hreach : ∀ u : {v // v ∈ C₁}, K.Reachable none (some u) := by
    intro u
    induction hn : T.dist x u using Nat.strong_induction_on generalizing u with
    | h n ih =>
      have hux : (u : V) ≠ x := by
        intro hux
        exact hxC (by simpa [hux] using u.property)
      let p := parent hT x hux
      have hpu : T.Adj p u := parent_adj hT x hux
      have hpdist : T.dist x p + 1 = T.dist x u := parent_dist_add_one hT x hux
      by_cases hpS : p ∈ S
      · have hpx : p = x := hS.singleBoundary hT hpS
          (mem_complementNonisolated.mp u.property).1 hpu
        have huR : u ∈ R := by
          rw [show R = complementRoots T x S by rfl, mem_complementRoots]
          simpa [hpx] using hpu.symm
        exact (show K.Adj none (some u) by
          simpa [K, rootedForestCone] using huR).reachable
      · have hpC : p ∈ C₁ := by
          rw [show C₁ = complementNonisolated T x S by rfl,
            hS.mem_complementNonisolated_iff hT]
          exact ⟨hpS, u, (mem_complementNonisolated.mp u.property).1, hpu⟩
        let pu : {v // v ∈ C₁} := ⟨p, hpC⟩
        have hpLt : T.dist x pu < n := by
          change T.dist x p < n
          rw [← hn]
          omega
        have hprev : K.Reachable none (some pu) := ih _ hpLt pu rfl
        have hadj : K.Adj (some pu) (some u) := by
          simpa [K, F, rootedForestCone] using hpu
        exact hprev.trans hadj.reachable
  have hconn : K.Connected := by
    rw [K.connected_iff_exists_forall_reachable]
    refine ⟨none, ?_⟩
    intro z
    cases z with
    | none => exact SimpleGraph.Reachable.refl _
    | some u => exact hreach u
  let e : K ↪g T := {
    toFun := fun
      | none => x
      | some u => u
    inj' := by
      intro a b hab
      cases a with
      | none =>
          cases b with
          | none => rfl
          | some b =>
              exfalso
              change x = (b : V) at hab
              have : x ∈ C₁ := by simpa [hab] using b.property
              exact hxC this
      | some a =>
          cases b with
          | none =>
              exfalso
              change (a : V) = x at hab
              have : x ∈ C₁ := by simpa [← hab] using a.property
              exact hxC this
          | some b => simp only [Option.some.injEq, Subtype.ext_iff] at hab ⊢; exact hab
    map_rel_iff' := by
      intro a b
      cases a with
      | none =>
          cases b with
          | none => simp [K, rootedForestCone]
          | some b => simp [K, R, rootedForestCone, complementRoots, T.adj_comm]
      | some a =>
          cases b with
          | none => simp [K, R, rootedForestCone, complementRoots]
          | some b => simp [K, F, rootedForestCone] }
  have hac : K.IsAcyclic := hT.isAcyclic.embedding e
  exact ⟨hconn, hac⟩

/-! ### Canonical roots of the complementary components -/

/-- In a finite rooted tree, every non-root vertex lies below a unique
child of the root.  This is the abstract uniqueness fact used to assign
each vertex of the complementary forest to its prescribed attachment
root. -/
theorem existsUnique_child_rootedBranch
    {A : Type*} [Fintype A] [DecidableEq A]
    {K : SimpleGraph A} (hK : K.IsTree) (z : A) {v : A} (hv : v ≠ z) :
    ∃! a : A, IsChild K z z a ∧ v ∈ rootedDescendants K z a := by
  have hvAll : v ∈ rootedDescendants K z z := by simp
  obtain ⟨a, haChild, hvBranch⟩ :=
    exists_child_of_mem_rootedDescendants hK hvAll hv
  refine ⟨a, ⟨haChild, hvBranch⟩, ?_⟩
  intro b hb
  by_contra hab
  have hdisj := disjoint_rootedDescendants_of_distinct_children
    hK hb.1 haChild hab
  exact (Finset.disjoint_left.mp hdisj) hb.2 hvBranch

/-- Every vertex of the nonisolated complement lies in the rooted branch
of a unique attachment root.  The branches here are taken in the cone,
rooted at its added vertex `none`; deleting `none` gives exactly the
components of the complementary forest. -/
theorem IsNaturalVertexSetAt.existsUnique_complementRoot_branch
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S)
    (v : {u // u ∈ complementNonisolated T x S}) :
    let F := T.induce (complementNonisolated T x S : Set V)
    let R := complementRoots T x S
    let K := rootedForestCone F R
    ∃! a : {u // u ∈ complementNonisolated T x S},
      a ∈ R ∧ some v ∈ rootedDescendants K none (some a) := by
  classical
  dsimp only
  let F := T.induce (complementNonisolated T x S : Set V)
  let R := complementRoots T x S
  let K := rootedForestCone F R
  have hK : K.IsTree := hS.rootedForestCone_complement_isTree hT
  have hvNe : (some v : Option {u // u ∈ complementNonisolated T x S}) ≠ none := by
    simp
  obtain ⟨a, ha, haUnique⟩ := existsUnique_child_rootedBranch hK none hvNe
  cases a with
  | none => exact (ha.1.1.ne rfl).elim
  | some a =>
      have haR : a ∈ R := by
        simpa [K, rootedForestCone] using ha.1.1
      refine ⟨a, ⟨haR, ha.2⟩, ?_⟩
      intro b hb
      have hbAdj : K.Adj none (some b) := by
        simpa only [K, rootedForestCone] using hb.1
      have hbChild : IsChild K none none (some b) := by
        refine ⟨hbAdj, ?_⟩
        have hdist : K.dist none (some b) = 1 := K.dist_eq_one_iff_adj.mpr hbAdj
        simpa using hdist
      have hsome : some b = some a := haUnique (some b) ⟨hbChild, hb.2⟩
      simpa using hsome

/-- The canonical attachment root of the complementary component
containing `v`. -/
noncomputable def IsNaturalVertexSetAt.componentRoot
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S)
    (v : {u // u ∈ complementNonisolated T x S}) :
    {a // a ∈ complementRoots T x S} := by
  classical
  let hex := hS.existsUnique_complementRoot_branch hT v
  exact ⟨hex.exists.choose, hex.exists.choose_spec.1⟩

@[simp] theorem IsNaturalVertexSetAt.componentRoot_mem
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S)
    (v : {u // u ∈ complementNonisolated T x S}) :
    (hS.componentRoot hT v).val ∈ complementRoots T x S :=
  (hS.componentRoot hT v).property

theorem IsNaturalVertexSetAt.componentRoot_branch
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S)
    (v : {u // u ∈ complementNonisolated T x S}) :
    let F := T.induce (complementNonisolated T x S : Set V)
    let R := complementRoots T x S
    let K := rootedForestCone F R
    some v ∈ rootedDescendants K none (some (hS.componentRoot hT v).val) := by
  classical
  dsimp only
  exact (hS.existsUnique_complementRoot_branch hT v).exists.choose_spec.2

theorem IsNaturalVertexSetAt.eq_componentRoot_of_mem_branch
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S)
    (v a : {u // u ∈ complementNonisolated T x S})
    (haR : a ∈ complementRoots T x S)
    (haBranch :
      let F := T.induce (complementNonisolated T x S : Set V)
      let R := complementRoots T x S
      let K := rootedForestCone F R
      some v ∈ rootedDescendants K none (some a)) :
    a = (hS.componentRoot hT v).val := by
  classical
  let hex := hS.existsUnique_complementRoot_branch hT v
  change a = hex.exists.choose
  exact hex.unique ⟨haR, haBranch⟩ hex.exists.choose_spec

/-- An attachment root is the canonical root of its own complementary
component. -/
theorem IsNaturalVertexSetAt.componentRoot_eq_self_of_mem
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S)
    (a : {u // u ∈ complementNonisolated T x S})
    (haR : a ∈ complementRoots T x S) :
    hS.componentRoot hT a = ⟨a, haR⟩ := by
  classical
  apply Subtype.ext
  symm
  apply hS.eq_componentRoot_of_mem_branch hT a a haR
  exact self_mem_rootedDescendants _ _ _

/-- Adjacent vertices of the complementary core have the same canonical
component root. -/
theorem IsNaturalVertexSetAt.componentRoot_eq_of_adj
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S)
    {u v : {z // z ∈ complementNonisolated T x S}}
    (huv : T.Adj u v) :
    hS.componentRoot hT u = hS.componentRoot hT v := by
  classical
  let F := T.induce (complementNonisolated T x S : Set V)
  let R := complementRoots T x S
  let K := rootedForestCone F R
  let a : {z // z ∈ complementNonisolated T x S} := (hS.componentRoot hT u).val
  have hK : K.IsTree := hS.rootedForestCone_complement_isTree hT
  have huvK : K.Adj (some u) (some v) := by
    simpa [K, F, rootedForestCone] using huv
  have huBranch : some u ∈ rootedDescendants K none (some a) := by
    simpa [K, F, R, a] using hS.componentRoot_branch hT u
  have hvBranch : some v ∈ rootedDescendants K none (some a) := by
    by_cases hua : u = a
    · have huvAK : K.Adj (some a) (some v) := by simpa [hua] using huvK
      have haR : a ∈ R := by
        simpa [R, a] using hS.componentRoot_mem hT u
      have haAdj : K.Adj none (some a) := by
        simpa [K, rootedForestCone] using haR
      have hda : K.dist none (some a) = 1 := K.dist_eq_one_iff_adj.mpr haAdj
      have hdav : K.dist (some a) (some v) = 1 :=
        K.dist_eq_one_iff_adj.mpr huvAK
      rcases hK.dist_eq_dist_add_one_of_adj none huvAK with hback | hforward
      · have hdvZero : K.dist none (some v) = 0 := by omega
        have : (none : Option {z // z ∈ complementNonisolated T x S}) = some v :=
          hK.connected.dist_eq_zero_iff.mp hdvZero
        simp at this
      · rw [mem_rootedDescendants]
        omega
    · exact adj_mem_rootedDescendants_of_mem_of_ne hK huBranch
        (by simpa using hua) huvK
  apply Subtype.ext
  change (hS.componentRoot hT u).val = (hS.componentRoot hT v).val
  simpa [a] using (hS.eq_componentRoot_of_mem_branch hT v a
    (by simpa [R, a] using hS.componentRoot_mem hT u)
    (by simpa [K, F, R] using hvBranch))

/-- Component-wise distance parity flips across every complementary-core
edge.  This is the parity statement needed to orient each component from
its own prescribed attachment root. -/
theorem IsNaturalVertexSetAt.componentRootParity_ne_of_adj
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S)
    {u v : {z // z ∈ complementNonisolated T x S}}
    (huv : T.Adj u v) :
    T.dist (hS.componentRoot hT u).val u % 2 ≠
      T.dist (hS.componentRoot hT v).val v % 2 := by
  have hroot := hS.componentRoot_eq_of_adj hT huv
  rw [← hroot]
  exact rootParity_ne_of_adj hT (hS.componentRoot hT u).val huv

/-- Every complementary component counted by `complementRoots` contains at
least two vertices.  Equivalently, the attachment-root count is at most half
the order of the nonisolated complementary forest. -/
theorem IsNaturalVertexSetAt.two_mul_card_complementRoots_le
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S) :
    2 * (complementRoots T x S).card ≤
      (complementNonisolated T x S).card := by
  classical
  let C₁ := complementNonisolated T x S
  let R := complementRoots T x S
  have hxS : x ∈ S := by
    obtain ⟨kept, hkept, rfl⟩ := hS
    simp [naturalVertices]
  have hex (a : {u // u ∈ R}) : ∃ w, w ∉ S ∧ T.Adj a w := by
    have haC : (a : V) ∈ C₁ := a.val.property
    exact (hS.mem_complementNonisolated_iff hT).mp haC |>.2
  let partner : {u // u ∈ R} → V := fun a => (hex a).choose
  have partner_out (a : {u // u ∈ R}) : partner a ∉ S :=
    (hex a).choose_spec.1
  have adj_partner (a : {u // u ∈ R}) : T.Adj a (partner a) :=
    (hex a).choose_spec.2
  have root_adj (a : {u // u ∈ R}) : T.Adj a x := by
    have ha : a.val ∈ complementRoots T x S := by simpa [R] using a.property
    exact mem_complementRoots.mp ha
  have partner_mem_C₁ (a : {u // u ∈ R}) : partner a ∈ C₁ := by
    rw [show C₁ = complementNonisolated T x S by rfl,
      hS.mem_complementNonisolated_iff hT]
    exact ⟨partner_out a, a, (mem_complementNonisolated.mp a.val.property).1,
      (adj_partner a).symm⟩
  have partner_not_root (a : {u // u ∈ R}) :
      (⟨partner a, partner_mem_C₁ a⟩ : {v // v ∈ C₁}) ∉ R := by
    intro haR
    have hpx : T.Adj (partner a) x := by
      have : (⟨partner a, partner_mem_C₁ a⟩ : {v // v ∈ C₁}) ∈
          complementRoots T x S := by simpa [R] using haR
      exact mem_complementRoots.mp this
    have hda : T.dist x a = 1 := T.dist_eq_one_iff_adj.mpr (root_adj a).symm
    have hdp : T.dist x (partner a) = 1 := T.dist_eq_one_iff_adj.mpr hpx.symm
    exact (hT.dist_ne_of_adj x (adj_partner a)) (by omega)
  have partner_injective : Function.Injective partner := by
    intro a b hab
    have hpaNe : partner a ≠ x := by
      intro h
      exact partner_out a (h ▸ hxS)
    have hda : T.dist x a = 1 := T.dist_eq_one_iff_adj.mpr (root_adj a).symm
    have hpaLevel : T.dist x a + 1 = T.dist x (partner a) := by
      rcases hT.dist_eq_dist_add_one_of_adj x (adj_partner a) with hback | hforward
      · have hzero : T.dist x (partner a) = 0 := by omega
        have hzero' : T.dist (partner a) x = 0 := by simpa [T.dist_comm] using hzero
        exact (hpaNe (hT.connected.dist_eq_zero_iff.mp hzero')).elim
      · exact hforward.symm
    have haParent : (a : V) = parent hT x hpaNe :=
      eq_parent_of_adj_of_dist_add_one hT x hpaNe (adj_partner a) hpaLevel
    have hpbNe : partner b ≠ x := by
      intro h
      exact partner_out b (h ▸ hxS)
    have hdb : T.dist x b = 1 := T.dist_eq_one_iff_adj.mpr (root_adj b).symm
    have hpbLevel : T.dist x b + 1 = T.dist x (partner b) := by
      rcases hT.dist_eq_dist_add_one_of_adj x (adj_partner b) with hback | hforward
      · have hzero : T.dist x (partner b) = 0 := by omega
        have hzero' : T.dist (partner b) x = 0 := by simpa [T.dist_comm] using hzero
        exact (hpbNe (hT.connected.dist_eq_zero_iff.mp hzero')).elim
      · exact hforward.symm
    have hbParent : (b : V) = parent hT x hpbNe :=
      eq_parent_of_adj_of_dist_add_one hT x hpbNe (adj_partner b) hpbLevel
    have hbAdjA : T.Adj b (partner a) := by simpa [hab] using adj_partner b
    have hbLevelA : T.dist x b + 1 = T.dist x (partner a) := by
      simpa [hab] using hpbLevel
    have hbParentA : (b : V) = parent hT x hpaNe :=
      eq_parent_of_adj_of_dist_add_one hT x hpaNe hbAdjA hbLevelA
    apply Subtype.ext
    apply Subtype.ext
    exact haParent.trans hbParentA.symm
  let NR : Finset {v // v ∈ C₁} := Finset.univ \ R
  let f : {u // u ∈ R} → {v // v ∈ NR} := fun a =>
    ⟨⟨partner a, partner_mem_C₁ a⟩, by
      simp only [NR, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact partner_not_root a⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply partner_injective
    exact congrArg (fun z : {v // v ∈ NR} => ((z : {v // v ∈ C₁}) : V)) hab
  have hle : R.card ≤ NR.card := by
    rw [← Fintype.card_coe R, ← Fintype.card_coe NR]
    exact Fintype.card_le_of_injective f hf
  have hNR : NR.card = C₁.card - R.card := by
    rw [show NR = Finset.univ \ R by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_univ,
      Fintype.card_coe]
  dsimp only [C₁, R] at hle hNR ⊢
  omega

/-! ### Explicit bipartition and cardinal splits -/

/-- The vertices of `U` at a prescribed parity from `x`. -/
noncomputable def parityPart (T : SimpleGraph V) (x : V) (U : Finset V)
    (q : ℕ) : Finset V := by
  classical
  exact U.filter fun v => T.dist x v % 2 = q

@[simp] theorem mem_parityPart {T : SimpleGraph V} {x v : V} {U : Finset V}
    {q : ℕ} : v ∈ parityPart T x U q ↔ v ∈ U ∧ T.dist x v % 2 = q := by
  classical
  simp [parityPart]

theorem parityPart_zero_union_one (T : SimpleGraph V) (x : V) (U : Finset V) :
    parityPart T x U 0 ∪ parityPart T x U 1 = U := by
  classical
  ext v
  simp only [Finset.mem_union, mem_parityPart]
  constructor
  · rintro (⟨hv, -⟩ | ⟨hv, -⟩) <;> exact hv
  · intro hv
    have hmod := Nat.mod_lt (T.dist x v) (by omega : 0 < 2)
    rcases Nat.eq_zero_or_pos (T.dist x v % 2) with hzero | hpos
    · exact Or.inl ⟨hv, hzero⟩
    · exact Or.inr ⟨hv, by omega⟩

theorem disjoint_parityPart_zero_one (T : SimpleGraph V) (x : V) (U : Finset V) :
    Disjoint (parityPart T x U 0) (parityPart T x U 1) := by
  classical
  rw [Finset.disjoint_left]
  intro v hv0 hv1
  have h0 := (mem_parityPart.mp hv0).2
  have h1 := (mem_parityPart.mp hv1).2
  omega

/-- Each distance-parity class in a tree is independent. -/
theorem isIndepSet_parityPart
    {T : SimpleGraph V} (hT : T.IsTree) (x : V) (U : Finset V) (q : ℕ) :
    T.IsIndepSet (parityPart T x U q : Set V) := by
  rw [T.isIndepSet_iff]
  intro u hu v hv huv
  intro hadj
  have hparity := rootParity_ne_of_adj hT x hadj
  exact hparity ((mem_parityPart.mp hu).2.trans (mem_parityPart.mp hv).2.symm)

theorem card_parityPart_zero_add_one
    (T : SimpleGraph V) (x : V) (U : Finset V) :
    (parityPart T x U 0).card + (parityPart T x U 1).card = U.card := by
  rw [← Finset.card_union_of_disjoint (disjoint_parityPart_zero_one T x U),
    parityPart_zero_union_one]

/-- The two explicit card splits used for `C₁` and the selected subtree with
its attachment root removed. -/
theorem IsNaturalVertexSetAt.complement_and_selected_card_splits
    {T : SimpleGraph V} {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S) :
    (parityPart T x (complementNonisolated T x S) 0).card +
        (parityPart T x (complementNonisolated T x S) 1).card =
          (complementNonisolated T x S).card ∧
      (parityPart T x (S.erase x) 0).card +
        (parityPart T x (S.erase x) 1).card = (S.erase x).card := by
  exact ⟨card_parityPart_zero_add_one T x _, card_parityPart_zero_add_one T x _⟩

theorem IsNaturalVertexSetAt.complement_and_selected_independent_parts
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : IsNaturalVertexSetAt T r x S) :
    T.IsIndepSet (parityPart T x (complementNonisolated T x S) 0 : Set V) ∧
      T.IsIndepSet (parityPart T x (complementNonisolated T x S) 1 : Set V) ∧
      T.IsIndepSet (parityPart T x (S.erase x) 0 : Set V) ∧
      T.IsIndepSet (parityPart T x (S.erase x) 1 : Set V) := by
  exact ⟨isIndepSet_parityPart hT x _ 0,
    isIndepSet_parityPart hT x _ 1,
    isIndepSet_parityPart hT x _ 0,
    isIndepSet_parityPart hT x _ 1⟩

#print axioms exists_naturalVertexSet_card
#print axioms exists_naturalVertexSetAt_card
#print axioms IsNaturalVertexSetAt.connected
#print axioms IsNaturalVertexSetAt.isTree
#print axioms IsNaturalVertexSetAt.singleBoundary
#print axioms IsNaturalVertexSetAt.mem_complementRootLeaves_iff_isolated
#print axioms IsNaturalVertexSetAt.mem_complementNonisolated_iff
#print axioms IsNaturalVertexSetAt.degree_eq_one_of_mem_complementRootLeaves
#print axioms IsNaturalVertexSetAt.complement_split
#print axioms IsNaturalVertexSetAt.rootedForestCone_complement_isTree
#print axioms existsUnique_child_rootedBranch
#print axioms IsNaturalVertexSetAt.existsUnique_complementRoot_branch
#print axioms IsNaturalVertexSetAt.componentRoot_branch
#print axioms IsNaturalVertexSetAt.componentRoot_eq_self_of_mem
#print axioms IsNaturalVertexSetAt.componentRoot_eq_of_adj
#print axioms IsNaturalVertexSetAt.componentRootParity_ne_of_adj
#print axioms IsNaturalVertexSetAt.two_mul_card_complementRoots_le
#print axioms isIndepSet_parityPart
#print axioms IsNaturalVertexSetAt.complement_and_selected_card_splits
#print axioms IsNaturalVertexSetAt.complement_and_selected_independent_parts

end SimpleGraphRose547
