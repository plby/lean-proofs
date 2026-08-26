/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

namespace ZhaoFact79

open scoped BigOperators

/-- A finite greedy packing lemma in exactly the numerical form used in
Zhao's Fact 7.9.  If the available pieces all have weight less than `q`, and
together with a distinguished root of weight one they have total weight at
least `q`, then some initial collection has weight in `[q, 2*q)`.  Except for
the degenerate case `q = 1`, the sharper upper bound `2*q-1` holds. -/
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
  by_cases hi0 : i = 0
  · simp only [hi0, List.take_zero, List.sum_nil, add_zero]
    omega
  · let j := i - 1
    have hji : j < i := by
      simp only [j]
      omega

    have hnot : ¬P j := Nat.find_min hex hji
    have hjlt : 1 + (weights.take j).sum < q := by
      simp only [P] at hnot
      omega
    have hilen : i ≤ weights.length := by
      exact Nat.find_min' hex (m := weights.length) (by simpa [P] using htotal)
    have hjlen : j < weights.length := by omega
    have hisucc : j + 1 = i := by
      simp only [j]
      omega
    have hw : weights[j] < q := hsmall weights[j] (List.getElem_mem hjlen)
    rw [← hisucc, List.sum_take_succ weights j hjlen]
    omega
  by_cases hq1 : q = 1
  · exact Or.inl hq1
  · right
    by_cases hi0 : i = 0
    · simp only [hi0, List.take_zero, List.sum_nil, add_zero]
      omega
    · let j := i - 1
      have hji : j < i := by
        simp only [j]
        omega
      have hnot : ¬P j := Nat.find_min hex hji
      have hjlt : 1 + (weights.take j).sum < q := by
        simp only [P] at hnot
        omega
      have hilen : i ≤ weights.length := by
        exact Nat.find_min' hex (m := weights.length) (by simpa [P] using htotal)
      have hjlen : j < weights.length := by omega
      have hisucc : j + 1 = i := by
        simp only [j]
        omega
      have hw : weights[j] < q := hsmall weights[j] (List.getElem_mem hjlen)
      rw [← hisucc, List.sum_take_succ weights j hjlen]
      omega

/-- The same greedy packing argument without a distinguished root weight.
Positivity of `q` forces the chosen prefix to be nonempty. -/
theorem exists_take_sum_in_half_open_interval_zero
    (q : ℕ) (hq : 0 < q) (weights : List ℕ)
    (hsmall : ∀ a ∈ weights, a < q)
    (htotal : q ≤ weights.sum) :
    ∃ i : ℕ, q ≤ (weights.take i).sum ∧
      (weights.take i).sum < 2 * q - 1 := by
  let P : ℕ → Prop := fun i => q ≤ (weights.take i).sum
  have hex : ∃ i, P i := by
    refine ⟨weights.length, ?_⟩
    simpa [P] using htotal
  let i := Nat.find hex
  have hi : P i := Nat.find_spec hex
  refine ⟨i, hi, ?_⟩
  have hi0 : i ≠ 0 := by
    intro hzero
    have : q ≤ 0 := by simpa [P, hzero] using hi
    omega
  let j := i - 1
  have hji : j < i := by
    simp only [j]
    omega
  have hnot : ¬P j := Nat.find_min hex hji
  have hjlt : (weights.take j).sum < q := by
    simp only [P] at hnot
    omega
  have hilen : i ≤ weights.length := by
    exact Nat.find_min' hex (m := weights.length) (by simpa [P] using htotal)
  have hjlen : j < weights.length := by omega
  have hisucc : j + 1 = i := by
    simp only [j]
    omega
  have hw : weights[j] < q := hsmall weights[j] (List.getElem_mem hjlen)
  rw [← hisucc, List.sum_take_succ weights j hjlen]
  omega

/- Finite rooted ordered trees and their child forests.  The mutual
presentation avoids any nested-recursion principle; it is equivalent to the
usual rose-tree datatype. -/
mutual
  inductive RootedTree where
    | node (children : RootedForest) : RootedTree
  inductive RootedForest where
    | nil : RootedForest
    | cons (head : RootedTree) (tail : RootedForest) : RootedForest
end

namespace RootedForest

def toList : RootedForest → List RootedTree
  | .nil => []
  | .cons t ts => t :: ts.toList

def ofList : List RootedTree → RootedForest
  | [] => .nil
  | t :: ts => .cons t (.ofList ts)

@[simp] theorem toList_ofList (ts : List RootedTree) :
    (ofList ts).toList = ts := by
  induction ts <;> simp [ofList, toList, *]

@[simp] theorem ofList_toList : ∀ children : RootedForest,
    ofList children.toList = children
  | .nil => rfl
  | .cons t ts => by simp [toList, ofList, ofList_toList ts]

end RootedForest

namespace RootedTree

open RootedForest

mutual
  /-- Number of vertices. -/
  def vertexCount : RootedTree → ℕ
    | .node children => 1 + forestVertexCount children
  /-- Sum of vertex counts over a child forest. -/
  def forestVertexCount : RootedForest → ℕ
    | .nil => 0
    | .cons t ts => vertexCount t + forestVertexCount ts
end

mutual
  /-- Number of leaves, counting the singleton root as one leaf. -/
  def leafCount : RootedTree → ℕ
    | .node .nil => 1
    | .node children@(.cons _ _) => forestLeafCount children
  /-- Sum of leaf counts over a nonempty or empty child forest. -/
  def forestLeafCount : RootedForest → ℕ
    | .nil => 0
    | .cons t ts => leafCount t + forestLeafCount ts
end

@[simp] theorem forestVertexCount_ofList (ts : List RootedTree) :
    forestVertexCount (RootedForest.ofList ts) = (ts.map vertexCount).sum := by
  induction ts <;> simp [RootedForest.ofList, forestVertexCount, *]

@[simp] theorem forestLeafCount_ofList (ts : List RootedTree) :
    forestLeafCount (RootedForest.ofList ts) = (ts.map leafCount).sum := by
  induction ts <;> simp [RootedForest.ofList, forestLeafCount, *]

@[simp] theorem vertexCount_node (children : RootedForest) :
    vertexCount (.node children) = 1 + forestVertexCount children := rfl

@[simp] theorem vertexCount_node_ofList (children : List RootedTree) :
    vertexCount (.node (.ofList children)) =
      1 + (children.map vertexCount).sum := by simp

@[simp] theorem leafCount_node_nil : leafCount (.node .nil) = 1 := by
  simp [leafCount]

@[simp] theorem leafCount_node_ofList_cons (t : RootedTree) (ts : List RootedTree) :
    leafCount (.node (.ofList (t :: ts))) =
      leafCount t + (ts.map leafCount).sum := by
  simp [RootedForest.ofList, leafCount, forestLeafCount]

theorem leafCount_node_ofList_of_ne_nil (children : List RootedTree)
    (hchildren : children ≠ []) :
    leafCount (.node (.ofList children)) =
      (children.map leafCount).sum := by
  cases children with
  | nil => exact (hchildren rfl).elim
  | cons t ts => simp

theorem vertexCount_pos (t : RootedTree) : 0 < vertexCount t := by
  cases t
  simp

mutual
  theorem leafCount_pos (t : RootedTree) : 0 < leafCount t := by
    cases t with
    | node children =>
        cases children with
        | nil => simp
        | cons u us =>
            simp only [leafCount, forestLeafCount]
            have hu := leafCount_pos u
            omega
end

/-- `s` is a natural subtree of `t` in Zhao's sense: either it is rooted at
the root of `t` and is obtained by discarding a collection of whole child
branches, or it is natural inside one child branch. -/
inductive IsNatural : RootedTree → RootedTree → Prop
  | rooted {children : RootedForest} {kept : List RootedTree}
      (h : kept.Sublist children.toList) :
      IsNatural (.node children) (.node (.ofList kept))
  | descend {children : RootedForest} {child s : RootedTree}
      (hc : child ∈ children.toList) (h : IsNatural child s) :
      IsNatural (.node children) s

theorem isNatural_refl (t : RootedTree) : IsNatural t t := by
  cases t with
  | node children =>
      simpa using
        (IsNatural.rooted (children := children) (kept := children.toList) (.refl _))

theorem IsNatural.trans {t s u : RootedTree} (hts : IsNatural t s)
    (hsu : IsNatural s u) : IsNatural t u := by
  induction hts with
  | @rooted children kept hsub =>
      cases hsu with
      | @rooted _ kept' hsub' =>
          have hsub'' : kept'.Sublist kept := by simpa using hsub'
          exact .rooted (hsub''.trans hsub)
      | @descend _ child u hc hcu =>
          have hc' : child ∈ kept := by simpa using hc
          exact .descend (hsub.subset hc') hcu
  | descend hc h ih => exact .descend hc (ih hsu)

theorem vertexCount_le_forestVertexCount_of_mem :
    ∀ (children : RootedForest) (t : RootedTree),
      t ∈ children.toList → vertexCount t ≤ forestVertexCount children
  | .nil, t => by simp [RootedForest.toList]
  | .cons u us, t => by
      simp only [RootedForest.toList, List.mem_cons]
      intro h
      rcases h with rfl | h
      · simp [forestVertexCount]
      · exact (vertexCount_le_forestVertexCount_of_mem us t h).trans
          (Nat.le_add_left _ _)

theorem vertexCount_lt_node_of_mem {children : RootedForest} {t : RootedTree}
    (h : t ∈ children.toList) : vertexCount t < vertexCount (.node children) := by
  rw [vertexCount_node]
  have hle := vertexCount_le_forestVertexCount_of_mem children t h
  omega

/-- The structural core of Fact 7.9(1), with an abstract target lower bound
`q`.  The two last numerical hypotheses are precisely the estimates needed
for the exceptional case `q = 1` and the ordinary greedy-packing case. -/
theorem exists_natural_vertexCount_aux
    (t : RootedTree) (k q : ℕ) (hq : 0 < q) (hqk : q < k)
    (hone : q = 1 → 2 ≤ k) (hmany : q ≠ 1 → 2 * q - 1 ≤ k)
    (ht : q ≤ vertexCount t) :
    ∃ s : RootedTree, IsNatural t s ∧
      q ≤ vertexCount s ∧ vertexCount s < k := by
  induction hn : vertexCount t using Nat.strong_induction_on generalizing t with
  | h n ih =>
    cases t with
    | node children =>
      let cs := children.toList
      by_cases hchild : ∃ child ∈ cs, q ≤ vertexCount child
      · obtain ⟨child, hmem, hlarge⟩ := hchild
        have hchildlt : vertexCount child < n := by
          rw [← hn]
          exact vertexCount_lt_node_of_mem hmem
        obtain ⟨s, hnat, hlo, hhi⟩ :=
          ih (vertexCount child) hchildlt child hlarge rfl
        exact ⟨s, .descend hmem hnat, hlo, hhi⟩
      · have hsmall : ∀ a ∈ cs.map vertexCount, a < q := by
          intro a ha
          rw [List.mem_map] at ha
          obtain ⟨child, hmem, rfl⟩ := ha
          by_contra hnlt
          exact hchild ⟨child, hmem, Nat.le_of_not_gt hnlt⟩
        have htotal : q ≤ 1 + (cs.map vertexCount).sum := by
          simpa only [cs, vertexCount_node, ← forestVertexCount_ofList,
            RootedForest.ofList_toList] using ht
        obtain ⟨i, hlo, hupper, hsharp⟩ :=
          exists_take_sum_in_half_open_interval q hq (cs.map vertexCount) hsmall htotal
        let kept := cs.take i
        have hcount : vertexCount (.node (.ofList kept)) =
            1 + ((cs.map vertexCount).take i).sum := by
          simp only [vertexCount_node_ofList, kept, List.map_take]
        refine ⟨.node (.ofList kept), .rooted (List.take_sublist i cs), ?_, ?_⟩
        · simpa only [hcount] using hlo
        · rw [hcount]
          by_cases hq1 : q = 1
          · exact hupper.trans_le (by simpa [hq1] using hone hq1)
          · exact (hsharp.resolve_left hq1).trans_le (hmany hq1)

/-- Zhao's Fact 7.9(1), with the necessary `2 ≤ k` correction to the
printed statement.  The lower inequality is the exact integral reading of
`k/2 ≤ v(T')`, namely `⌈k/2⌉ ≤ v(T')`. -/
theorem fact7_9_vertices (t : RootedTree) (k : ℕ) (hk2 : 2 ≤ k)
    (hk : k ≤ vertexCount t) :
    ∃ s : RootedTree, IsNatural t s ∧
      (k + 1) / 2 ≤ vertexCount s ∧ vertexCount s < k := by
  let q := (k + 1) / 2
  have hq : 0 < q := by
    simp only [q]
    omega
  have hqk : q < k := by
    simp only [q]
    omega
  have hqt : q ≤ vertexCount t := by
    exact (by simp only [q]; omega : q ≤ k).trans hk
  apply exists_natural_vertexCount_aux t k q hq hqk
  · intro
    exact hk2
  · intro
    simp only [q]
    omega
  · exact hqt

/-- The leaf-count analogue of the structural core.  It differs from the
vertex proof only at a leaf (whose root contributes one) and at an internal
root (whose leaves are exactly the disjoint union of its child leaves). -/
theorem exists_natural_leafCount_aux
    (t : RootedTree) (k q : ℕ) (hq : 0 < q) (hqk : q < k)
    (hmany : q ≠ 1 → 2 * q - 1 ≤ k)
    (ht : q ≤ leafCount t) :
    ∃ s : RootedTree, IsNatural t s ∧
      q ≤ leafCount s ∧ leafCount s < k := by
  induction hn : vertexCount t using Nat.strong_induction_on generalizing t with
  | h n ih =>
    cases t with
    | node children =>
      cases children with
      | nil =>
          have hq1 : q = 1 := by
            simp only [leafCount_node_nil] at ht
            omega
          refine ⟨.node .nil, isNatural_refl _, ?_, ?_⟩
          · simpa [hq1]
          · simpa [hq1] using hqk
      | cons child₀ children₀ =>
          let children : RootedForest := .cons child₀ children₀
          let cs := children.toList
          have hcs : cs ≠ [] := by simp [cs, children, RootedForest.toList]
          by_cases hchild : ∃ child ∈ cs, q ≤ leafCount child
          · obtain ⟨child, hmem, hlarge⟩ := hchild
            have hchildlt : vertexCount child < n := by
              rw [← hn]
              exact vertexCount_lt_node_of_mem hmem
            obtain ⟨s, hnat, hlo, hhi⟩ :=
              ih (vertexCount child) hchildlt child hlarge rfl
            exact ⟨s, .descend hmem hnat, hlo, hhi⟩
          · have hsmall : ∀ a ∈ cs.map leafCount, a < q := by
              intro a ha
              rw [List.mem_map] at ha
              obtain ⟨child, hmem, rfl⟩ := ha
              by_contra hnlt
              exact hchild ⟨child, hmem, Nat.le_of_not_gt hnlt⟩
            have htotal : q ≤ (cs.map leafCount).sum := by
              have hleaf : leafCount (.node children) =
                  (cs.map leafCount).sum := by
                rw [show children = RootedForest.ofList cs by
                  exact (RootedForest.ofList_toList children).symm]
                exact leafCount_node_ofList_of_ne_nil cs hcs
              simpa only [children, hleaf] using ht
            obtain ⟨i, hlo, hupper⟩ :=
              exists_take_sum_in_half_open_interval_zero q hq (cs.map leafCount)
                hsmall htotal
            let kept := cs.take i
            have hkept : kept ≠ [] := by
              intro hempty
              have : q ≤ 0 := by
                simpa only [kept, ← List.map_take, hempty, List.map_nil,
                  List.sum_nil] using hlo
              omega
            have hcount : leafCount (.node (.ofList kept)) =
                ((cs.map leafCount).take i).sum := by
              rw [leafCount_node_ofList_of_ne_nil kept hkept]
              simp only [kept, List.map_take]
            have hq1 : q ≠ 1 := by
              intro hq1
              have hmem₀ : child₀ ∈ cs := by
                simp [cs, children, RootedForest.toList]
              have hlt := hsmall (leafCount child₀) (by
                exact List.mem_map.mpr ⟨child₀, hmem₀, rfl⟩)
              have hpos := leafCount_pos child₀
              omega
            refine ⟨.node (.ofList kept), .rooted (List.take_sublist i cs), ?_, ?_⟩
            · simpa only [hcount] using hlo
            · rw [hcount]
              exact hupper.trans_le (hmany hq1)

/-- Zhao's Fact 7.9(2), again with the necessary correction `2 ≤ k`.
The leaf count is the leaf count of the resulting natural subtree itself. -/
theorem fact7_9_leaves (t : RootedTree) (k : ℕ) (hk2 : 2 ≤ k)
    (hk : k ≤ leafCount t) :
    ∃ s : RootedTree, IsNatural t s ∧
      (k + 1) / 2 ≤ leafCount s ∧ leafCount s < k := by
  let q := (k + 1) / 2
  have hq : 0 < q := by
    simp only [q]
    omega
  have hqk : q < k := by
    simp only [q]
    omega
  have hqt : q ≤ leafCount t := by
    exact (by simp only [q]; omega : q ≤ k).trans hk
  apply exists_natural_leafCount_aux t k q hq hqk
  · intro
    simp only [q]
    omega
  · exact hqt

end RootedTree

end ZhaoFact79

#print axioms ZhaoFact79.exists_take_sum_in_half_open_interval
#print axioms ZhaoFact79.RootedTree.fact7_9_vertices
#print axioms ZhaoFact79.RootedTree.fact7_9_leaves
