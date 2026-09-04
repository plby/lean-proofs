/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreRigidity
import ErdosProblems.Erdos916.Connectivity

/-!
# The density left after deleting false twins

This file isolates the numerical part of the false-twin route to Erdős
Problem 916.  Two nonadjacent degree-three vertices delete exactly six edges.
Thus, in a `(2,3)` circuit, deleting a degree-three false-twin pair leaves a
graph with `e + 4 = 2 * v`.  The statements are phrased for the actual induced
graph on the remaining vertex subtype, so that cycle and component arguments
can consume them without translating from a graph with two isolated vertices.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The vertex type obtained by deleting two specified vertices. -/
abbrev PairDeletedVertices (u v : V) := {w : V // w ≠ u ∧ w ≠ v}

/-- The induced graph obtained by deleting two specified vertices. -/
def pairDeleted (G : SimpleGraph V) (u v : V) :
    SimpleGraph (PairDeletedVertices u v) :=
  G.induce fun w => w ≠ u ∧ w ≠ v

noncomputable instance pairDeletedAdjDecidable (G : SimpleGraph V) (u v : V) :
    DecidableRel (pairDeleted G u v).Adj :=
  Classical.decRel _

namespace pairDeleted

noncomputable local instance componentFintype {W : Type*} [Finite W]
    {H : SimpleGraph W} (C : H.ConnectedComponent) : Fintype C :=
  Fintype.ofFinite C

noncomputable local instance componentSupportFintype {W : Type*} [Finite W]
    {H : SimpleGraph W} (C : H.ConnectedComponent) : Fintype C.supp :=
  Fintype.ofFinite C.supp

noncomputable local instance componentAdjDecidable {W : Type*}
    {H : SimpleGraph W} (C : H.ConnectedComponent) :
    DecidableRel C.toSimpleGraph.Adj :=
  Classical.decRel _

/-- A connected component is graph-isomorphic to the induced graph on its
ambient support. -/
noncomputable def componentIsoInduce {W : Type*} {H : SimpleGraph W}
    (C : H.ConnectedComponent) :
    C.toSimpleGraph ≃g H.induce C.supp where
  toEquiv := Equiv.refl C
  map_rel_iff' := Iff.rfl

/-- The component carrier is equivalent to its support finset. -/
noncomputable def componentEquivSupportFinset {W : Type*} [Fintype W]
    [DecidableEq W] {H : SimpleGraph W} (C : H.ConnectedComponent) :
    C ≃ C.supp.toFinset where
  toFun x := ⟨x.1, by
    rw [Set.mem_toFinset]
    exact x.2⟩
  invFun x := ⟨x.1, by
    change H.connectedComponentMk x.1 = C
    have hx := x.2
    rw [Set.mem_toFinset] at hx
    change H.connectedComponentMk x.1 = C at hx
    exact hx⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

/-- `(2,3)` sparsity restricts to every nontrivial connected component. -/
theorem component_sparse_of_is23Sparse
    {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (hsparse : Is23Sparse H) (C : H.ConnectedComponent)
    (hC2 : 2 ≤ Fintype.card C) :
    C.toSimpleGraph.edgeFinset.card + 3 ≤ 2 * Fintype.card C := by
  classical
  let S : Finset W := C.supp.toFinset
  have hScard : S.card = Fintype.card C := by
    calc
      S.card = Fintype.card S := by simp
      _ = Fintype.card C :=
        Fintype.card_congr (componentEquivSupportFinset C).symm
  have hbound := hsparse S (by simpa only [hScard] using hC2)
  let e : C.toSimpleGraph ≃g H.induce (S : Set W) :=
    { toEquiv := componentEquivSupportFinset C
      map_rel_iff' := Iff.rfl }
  have hedge := e.card_edgeFinset_eq
  rw [← hedge, hScard] at hbound
  exact hbound

/-- Componentwise `(2,3)` sparsity turns the exact `(2,4)` count into
connectedness.  If there were two components, summing the component bounds
would give `e + 6 ≤ 2v`, contradicting `e + 4 = 2v`. -/
theorem connected_of_has24Count_of_component_sparse
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] [Nonempty W]
    (hcount : H.edgeFinset.card + 4 = 2 * Fintype.card W)
    (hsparse : ∀ C : H.ConnectedComponent,
      C.toSimpleGraph.edgeFinset.card + 3 ≤ 2 * Fintype.card C) :
    H.Connected := by
  classical
  by_contra hconn
  have hnpre : ¬H.Preconnected := by
    intro hp
    exact hconn (SimpleGraph.Connected.mk hp)
  simp only [SimpleGraph.Preconnected] at hnpre
  push Not at hnpre
  obtain ⟨x, y, hxy⟩ := hnpre
  have hcompNe : H.connectedComponentMk x ≠ H.connectedComponentMk y := by
    exact fun h => hxy (ConnectedComponent.exact h)
  have htwo : 2 ≤ Fintype.card H.ConnectedComponent := by
    rw [show (2 : ℕ) = 1 + 1 by omega]
    exact Fintype.one_lt_card_iff.mpr
      ⟨H.connectedComponentMk x, H.connectedComponentMk y, hcompNe⟩
  have hsum := Finset.sum_le_sum
    (fun C (_ : C ∈ (Finset.univ : Finset H.ConnectedComponent)) => hsparse C)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  rw [← Finset.mul_sum, H.sum_card_edgeFinset_connectedComponents,
    H.sum_card_connectedComponents] at hsum
  have hsix : 6 ≤ Fintype.card H.ConnectedComponent * 3 := by omega
  have hstrict : H.edgeFinset.card + 6 ≤ 2 * Fintype.card W :=
    le_trans (Nat.add_le_add_left hsix _) hsum
  omega

/-- Every component of a `(2,3)`-sparse graph satisfies the weaker bound
`e + 2 ≤ 2v`, including singleton components. -/
theorem component_weak_sparse_of_is23Sparse
    {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (hsparse : Is23Sparse H) (C : H.ConnectedComponent) :
    C.toSimpleGraph.edgeFinset.card + 2 ≤ 2 * Fintype.card C := by
  classical
  rw [← Nat.card_eq_fintype_card]
  by_cases hC2 : 2 ≤ Nat.card C
  · have hC2' : 2 ≤ Fintype.card C := by
      rw [← Nat.card_eq_fintype_card]
      exact hC2
    have h := component_sparse_of_is23Sparse hsparse C hC2'
    rw [← Nat.card_eq_fintype_card] at h
    omega
  · obtain ⟨z, hz⟩ := C.nonempty_supp
    let : Nonempty C := ⟨⟨z, hz⟩⟩
    have hpos : 0 < Nat.card C := Finite.card_pos
    have hcard : Nat.card C = 1 := by omega
    let : Subsingleton C :=
      Finite.card_le_one_iff_subsingleton.mp (by omega)
    have hedge : C.toSimpleGraph.edgeFinset = ∅ := by
      ext e
      cases e using Sym2.inductionOn with
      | _ x y =>
          have hxy : x = y := Subsingleton.elim x y
          subst y
          simp
    rw [hedge, Finset.card_empty, hcard]

/-- Every Laman-tight graph is connected.  Summing the weak component
bounds would lose at least four units if there were two components, whereas
the tight count loses only three. -/
theorem connected_of_is23Tight
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (htight : Is23Tight H) : H.Connected := by
  classical
  have hcardpos : 0 < Fintype.card W := by
    have hcount := htight.2
    omega
  let : Nonempty W := Fintype.card_pos_iff.mp hcardpos
  by_contra hconn
  have hnpre : ¬H.Preconnected := by
    intro hp
    exact hconn (SimpleGraph.Connected.mk hp)
  simp only [SimpleGraph.Preconnected] at hnpre
  push Not at hnpre
  obtain ⟨x, y, hxy⟩ := hnpre
  have hcompNe : H.connectedComponentMk x ≠ H.connectedComponentMk y := by
    exact fun h => hxy (ConnectedComponent.exact h)
  have hsum := Finset.sum_le_sum
    (fun C (_ : C ∈ (Finset.univ : Finset H.ConnectedComponent)) =>
      component_weak_sparse_of_is23Sparse htight.1 C)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  rw [← Finset.mul_sum, H.sum_card_edgeFinset_connectedComponents,
    H.sum_card_connectedComponents] at hsum
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hsum
  let : Nontrivial H.ConnectedComponent :=
    ⟨⟨H.connectedComponentMk x, H.connectedComponentMk y, hcompNe⟩⟩
  have htwo : 2 ≤ Nat.card H.ConnectedComponent := Finite.one_lt_card
  have hfour : 4 ≤ Nat.card H.ConnectedComponent * 2 := by omega
  have hstrict : H.edgeFinset.card + 4 ≤ 2 * Nat.card W :=
    le_trans (Nat.add_le_add_left hfour _) hsum
  have hcount := htight.2
  rw [← Nat.card_eq_fintype_card] at hcount
  omega

/-- The remaining vertex type has exactly two fewer vertices. -/
theorem card_vertices {u v : V} (huv : u ≠ v) :
    Fintype.card (PairDeletedVertices u v) = Fintype.card V - 2 := by
  classical
  have h := Fintype.card_subtype_compl (fun w : V => w = u ∨ w = v)
  have hpair : Fintype.card {w : V // w = u ∨ w = v} = 2 := by
    rw [Fintype.card_subtype]
    change (Finset.univ.filter fun w : V => w = u ∨ w = v).card = 2
    rw [show Finset.univ.filter (fun w : V => w = u ∨ w = v) = {u, v} by
      ext w
      simp [eq_comm]]
    simp [huv]
  rw [hpair] at h
  simpa only [not_or] using h

private theorem card_deleteIncidenceSet_add_degree
    (H : SimpleGraph V) [DecidableRel H.Adj] (x : V) :
    (H.deleteIncidenceSet x).edgeFinset.card + H.degree x =
      H.edgeFinset.card := by
  rw [H.edgeFinset_deleteIncidenceSet_eq_sdiff x,
    ← H.card_incidenceFinset_eq_degree x]
  rw [Finset.card_sdiff_add_card,
    Finset.union_eq_left.mpr (H.incidenceFinset_subset x)]

/-- Deleting two nonadjacent degree-three vertices removes exactly six edges.
The additive statement avoids any truncated-subtraction side conditions. -/
theorem card_edges_add_six {u v : V}
    (huv : u ≠ v) (hnadj : ¬G.Adj u v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3) :
    (pairDeleted G u v).edgeFinset.card + 6 = G.edgeFinset.card := by
  classical
  let G₁ : SimpleGraph V := G.deleteIncidenceSet u
  let G₂ : SimpleGraph V := G₁.deleteIncidenceSet v
  let S : Set V := {w | w ≠ u ∧ w ≠ v}
  have hG₁v : G₁.degree v = 3 := by
    dsimp only [G₁]
    rw [degree_deleteIncidenceSet_of_not_adj
      (fun h => hnadj h.symm) huv.symm, hdv]
  have hsupport : G₂.support ⊆ S := by
    intro w hw
    have hw₁ : w ∈ G₁.support \ {v} :=
      support_deleteIncidenceSet_subset G₁ v hw
    have hwG₁ : w ∈ G₁.support := hw₁.1
    have hw₀ : w ∈ G.support \ {u} :=
      support_deleteIncidenceSet_subset G u hwG₁
    exact ⟨by simpa using hw₀.2, by simpa using hw₁.2⟩
  have hmap := G₂.map_edgeFinset_induce_of_support_subset hsupport
  have hcardInduce : (G₂.induce S).edgeFinset.card = G₂.edgeFinset.card := by
    have := congrArg Finset.card hmap
    simpa using this
  let e : G₂.induce S ≃g pairDeleted G u v := by
    refine { toEquiv := Equiv.refl _, map_rel_iff' := ?_ }
    intro a b
    simp only [G₂, G₁, S, pairDeleted, SimpleGraph.induce_adj,
      SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · intro hab
      exact ⟨⟨hab, a.2.1, b.2.1⟩, a.2.2, b.2.2⟩
    · rintro ⟨⟨hab, -, -⟩, -, -⟩
      exact hab
  have hedgePair : (pairDeleted G u v).edgeFinset.card = G₂.edgeFinset.card := by
    exact e.card_edgeFinset_eq.symm.trans hcardInduce
  have he₁ := card_deleteIncidenceSet_add_degree G u
  have he₂ := card_deleteIncidenceSet_add_degree G₁ v
  change G₁.edgeFinset.card + G.degree u = G.edgeFinset.card at he₁
  change G₂.edgeFinset.card + G₁.degree v = G₁.edgeFinset.card at he₂
  rw [hdu] at he₁
  rw [hG₁v] at he₂
  rw [hedgePair]
  omega

/-- A degree-three false-twin pair in a `(2,3)` circuit leaves the exact
`(2,4)` count `e + 4 = 2v`. -/
theorem has24Count
    (hcircuit : Is23Circuit G) {u v : V}
    (huv : u ≠ v) (hnadj : ¬G.Adj u v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3) :
    (pairDeleted G u v).edgeFinset.card + 4 =
      2 * Fintype.card (PairDeletedVertices u v) := by
  have hedge := card_edges_add_six huv hnadj hdu hdv
  have hverts := card_vertices huv
  have hcount := hcircuit.1
  dsimp [Has23CircuitCount] at hcount
  rw [hverts]
  omega

/-- Pair deletion inherits `(2,3)` sparsity from a circuit: every vertex set
in the deletion is a proper vertex set of the original graph. -/
theorem is23Sparse_of_is23Circuit
    (hcircuit : Is23Circuit G) {u v : V} :
    Is23Sparse (pairDeleted G u v) := by
  classical
  intro T hT2
  let inc : PairDeletedVertices u v ↪ V := Function.Embedding.subtype _
  let U : Finset V := T.map inc
  have hUcard : U.card = T.card := by simp [U]
  have huU : u ∉ U := by
    intro hu
    simp only [U, Finset.mem_map] at hu
    obtain ⟨w, -, hwu⟩ := hu
    exact w.2.1 (by simpa [inc] using hwu)
  have hUne : U ≠ Finset.univ := by
    intro hU
    exact huU (by rw [hU]; simp)
  have hbound := hcircuit.2 U (by omega) hUne
  have hsets :
      ((fun w : PairDeletedVertices u v => (w : V)) ''
          (T : Set (PairDeletedVertices u v))) = (U : Set V) := by
    ext x
    simp [U, inc]
  let e₀ :
      {w : PairDeletedVertices u v // w ∈ (T : Set (PairDeletedVertices u v))} ≃
        {x : V // x ∈ ((fun w : PairDeletedVertices u v => (w : V)) ''
          (T : Set (PairDeletedVertices u v)))} :=
    Equiv.Set.image (fun w : PairDeletedVertices u v => (w : V))
      (T : Set (PairDeletedVertices u v)) Subtype.val_injective
  let e :
      {w : PairDeletedVertices u v // w ∈ (T : Set (PairDeletedVertices u v))} ≃
        {x : V // x ∈ (U : Set V)} :=
    e₀.trans (Equiv.setCongr hsets)
  let gi :
      (pairDeleted G u v).induce (T : Set (PairDeletedVertices u v)) ≃g
        G.induce (U : Set V) := by
    refine { toEquiv := e, map_rel_iff' := ?_ }
    intro x y
    rfl
  have hinduce :
      ((pairDeleted G u v).induce
        (T : Set (PairDeletedVertices u v))).edgeFinset.card =
          (G.induce (U : Set V)).edgeFinset.card :=
    gi.card_edgeFinset_eq
  rw [hinduce]
  simpa only [hUcard] using hbound

/-- No vertex of a two-vertex deletion of a genuine circuit is isolated.
Otherwise all of its ambient neighbours would be among the two deleted
vertices, contradicting the circuit minimum-degree bound. -/
theorem degree_pos_of_is23Circuit
    (hcircuit : Is23Circuit G) (hcard : 4 ≤ Fintype.card V)
    {u v : V} (huv : u ≠ v) (w : PairDeletedVertices u v) :
    0 < (pairDeleted G u v).degree w := by
  classical
  by_contra hnot
  have hzero : (pairDeleted G u v).degree w = 0 := by omega
  have hmin : 3 ≤ G.degree w.1 := hcircuit.degree_three_le hcard w.1
  have hsub : G.neighborFinset w.1 ⊆ ({u, v} : Finset V) := by
    intro z hz
    by_contra hzpair
    have hzuv : z ≠ u ∧ z ≠ v := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hzpair
    let z' : PairDeletedVertices u v := ⟨z, hzuv⟩
    have hwz : (pairDeleted G u v).Adj w z' := by
      change G.Adj w.1 z
      simpa only [SimpleGraph.mem_neighborFinset] using hz
    have hpos : 0 < (pairDeleted G u v).degree w := by
      rw [← (pairDeleted G u v).card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨z', by simpa using hwz⟩
    omega
  have hle := Finset.card_le_card hsub
  have hpair : ({u, v} : Finset V).card = 2 := by simp [huv]
  rw [G.card_neighborFinset_eq_degree, hpair] at hle
  omega

/-- Consequently every connected component of the pair deletion has at
least two vertices. -/
theorem two_le_card_component_of_is23Circuit
    (hcircuit : Is23Circuit G) (hcard : 4 ≤ Fintype.card V)
    {u v : V} (huv : u ≠ v)
    (C : (pairDeleted G u v).ConnectedComponent) :
    2 ≤ Fintype.card C := by
  classical
  obtain ⟨z, hz⟩ := C.nonempty_supp
  let zC : C := ⟨z, hz⟩
  have hpos : 0 < (pairDeleted G u v).degree zC.1 :=
    degree_pos_of_is23Circuit hcircuit hcard huv zC.1
  have hdeg : 0 < C.toSimpleGraph.degree zC := by
    rw [degree_connectedComponent (pairDeleted G u v) C zC]
    exact hpos
  have hlt := C.toSimpleGraph.degree_lt_card_verts zC
  omega

/-- The graph left after deleting a distinct nonadjacent cubic pair from a
`(2,3)` circuit is connected.  This is the component-counting step in the
ordinary false-twin route. -/
theorem connected_of_is23Circuit
    (hcircuit : Is23Circuit G) (hcard : 4 ≤ Fintype.card V)
    {u v : V} (huv : u ≠ v) (hnadj : ¬G.Adj u v)
    (hdu : G.degree u = 3) (hdv : G.degree v = 3) :
    (pairDeleted G u v).Connected := by
  classical
  have hdelcard := card_vertices (V := V) huv
  let : Nonempty (PairDeletedVertices u v) :=
    Fintype.card_pos_iff.mp (by rw [hdelcard]; omega)
  apply connected_of_has24Count_of_component_sparse
    (pairDeleted G u v) (has24Count hcircuit huv hnadj hdu hdv)
  intro C
  apply component_sparse_of_is23Sparse
    (is23Sparse_of_is23Circuit hcircuit) C
  exact two_le_card_component_of_is23Circuit hcircuit hcard huv C

end pairDeleted

end Erdos916
