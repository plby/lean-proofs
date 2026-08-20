/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.Induction
import ErdosProblems.Erdos916.StructuralCore
import ErdosProblems.Erdos916.CoreMaxCycle
import ErdosProblems.Erdos916.CoreAHT
import ErdosProblems.Erdos916.ThreeTerminalCut
import ErdosProblems.Erdos916.ThreeTerminalPath

/-!
# Thomassen--Toft core adapters for Erdős Problem 916

This file records the exact logical bridges between the two formulations of
the Thomassen--Toft structural theorem used by the development:

* `VertexTwoConnectedCorePrinciple` is the stronger, pointed version used by
  the end-block induction.  One distinguished vertex may have small degree.
* `VertexTwoConnectedReductionPrinciple` is the unpointed minimum-degree-three
  statement needed by the density induction.
* `MaxCycleLocalReductionPrinciple` is the remaining local analysis after the
  Bondy--Vince maximum-chordless-cycle theorem has produced a unique
  complementary bridge which attaches to every rim vertex.

All the implications below are theorem-level adapters: they neither add a
graph-theoretic assumption nor hide a structural conclusion.
-/

namespace Erdos916

open SimpleGraph
open Erdos751.BV

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Displays of the two small possible rims -/

/-- A named display of a three-cycle. -/
structure TriangleDisplay (C : Cycle (G := G)) where
  r0 : V
  r1 : V
  r2 : V
  adj01 : G.Adj r0 r1
  adj12 : G.Adj r1 r2
  adj20 : G.Adj r2 r0
  ne01 : r0 ≠ r1
  ne02 : r0 ≠ r2
  ne12 : r1 ≠ r2
  verts_eq : C.verts (G := G) = {r0, r1, r2}

/-- A named display of a four-cycle in cyclic order. -/
structure FourCycleDisplay (C : Cycle (G := G)) where
  r0 : V
  r1 : V
  r2 : V
  r3 : V
  adj01 : G.Adj r0 r1
  adj12 : G.Adj r1 r2
  adj23 : G.Adj r2 r3
  adj30 : G.Adj r3 r0
  ne01 : r0 ≠ r1
  ne02 : r0 ≠ r2
  ne03 : r0 ≠ r3
  ne12 : r1 ≠ r2
  ne13 : r1 ≠ r3
  ne23 : r2 ≠ r3
  verts_eq : C.verts (G := G) = {r0, r1, r2, r3}

/-- Between two distinct vertices of a cycle, one of the two cyclic arcs
avoids any prescribed third vertex.  The selected arc is a simple path and
uses only vertices of the original cycle. -/
theorem Cycle.exists_path_between_avoiding
    (C : Cycle (G := G)) {x y z : V}
    (hxC : x ∈ C.vSet (G := G)) (hyC : y ∈ C.vSet (G := G))
    (hzC : z ∈ C.vSet (G := G))
    (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) :
    ∃ A : G.Walk x y, A.IsPath ∧ z ∉ A.support ∧
      ∀ v, v ∈ A.support → v ∈ C.vSet (G := G) := by
  classical
  have hxSupport : x ∈ C.walk.support := by
    have hxVerts : x ∈ C.verts (G := G) :=
      (C.mem_vSet_iff (G := G)).mp hxC
    simpa only [Cycle.verts, List.mem_toFinset] using hxVerts
  let r := C.walk.rotate x hxSupport
  have hrCycle : r.IsCycle := C.isCycle.rotate hxSupport
  have hySupport : y ∈ r.support := by
    have hyOld : y ∈ C.walk.support := by
      have hyVerts : y ∈ C.verts (G := G) :=
        (C.mem_vSet_iff (G := G)).mp hyC
      simpa only [Cycle.verts, List.mem_toFinset] using hyVerts
    have hySub : y ∈ C.walk.toSubgraph.verts := by
      simpa only [SimpleGraph.Walk.mem_verts_toSubgraph] using hyOld
    have : y ∈ r.toSubgraph.verts := by
      simpa only [r, SimpleGraph.Walk.toSubgraph_rotate] using hySub
    simpa only [SimpleGraph.Walk.mem_verts_toSubgraph] using this
  let a1 := r.takeUntil y hySupport
  let a2 := (r.dropUntil y hySupport).reverse
  have ha1Path : a1.IsPath := hrCycle.isPath_takeUntil hySupport
  have ha1NotNil : ¬a1.Nil := by
    intro hnil
    have hymem : y ∈ a1.support := by simp [a1]
    have hyx : y = x := by
      simpa [SimpleGraph.Walk.nil_iff_support_eq.mp hnil] using hymem
    exact hxy hyx.symm
  have hrDecomp : r = a1.append (r.dropUntil y hySupport) := by
    have h := SimpleGraph.Walk.take_spec (p := r) (h := hySupport)
    simpa only [a1] using h.symm
  have hdropPath : (r.dropUntil y hySupport).IsPath := by
    have hcyc : (a1.append (r.dropUntil y hySupport)).IsCycle := by
      rw [← hrDecomp]
      exact hrCycle
    exact SimpleGraph.Walk.IsCycle.isPath_of_append_right
      (p := a1) (q := r.dropUntil y hySupport) ha1NotNil hcyc
  have ha2Path : a2.IsPath := hdropPath.reverse
  have ha1Cycle : ∀ v : V, v ∈ a1.support → v ∈ C.vSet (G := G) := by
    intro v hv
    have hvr : v ∈ r.support :=
      SimpleGraph.Walk.support_takeUntil_subset_support _ _ hv
    have hvOld : v ∈ C.walk.support := by
      have hvSub : v ∈ r.toSubgraph.verts := by
        simpa only [SimpleGraph.Walk.mem_verts_toSubgraph] using hvr
      have : v ∈ C.walk.toSubgraph.verts := by
        simpa only [r, SimpleGraph.Walk.toSubgraph_rotate] using hvSub
      simpa only [SimpleGraph.Walk.mem_verts_toSubgraph] using this
    apply (C.mem_vSet_iff (G := G)).mpr
    simpa only [Cycle.verts, List.mem_toFinset] using hvOld
  have ha2Cycle : ∀ v : V, v ∈ a2.support → v ∈ C.vSet (G := G) := by
    intro v hv
    have hvdrop : v ∈ (r.dropUntil y hySupport).support := by
      simpa only [a2, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hv
    have hvr : v ∈ r.support :=
      SimpleGraph.Walk.support_dropUntil_subset_support _ _ hvdrop
    have hvOld : v ∈ C.walk.support := by
      have hvSub : v ∈ r.toSubgraph.verts := by
        simpa only [SimpleGraph.Walk.mem_verts_toSubgraph] using hvr
      have : v ∈ C.walk.toSubgraph.verts := by
        simpa only [r, SimpleGraph.Walk.toSubgraph_rotate] using hvSub
      simpa only [SimpleGraph.Walk.mem_verts_toSubgraph] using this
    apply (C.mem_vSet_iff (G := G)).mpr
    simpa only [Cycle.verts, List.mem_toFinset] using hvOld
  have hzNotA2OfA1 : z ∈ a1.support → z ∉ a2.support := by
    intro hz1 hz2
    have htail :
        (a1.support.tail ++ (r.dropUntil y hySupport).support.tail).Nodup := by
      have htail' :
          (a1.append (r.dropUntil y hySupport)).support.tail.Nodup := by
        rw [← hrDecomp]
        exact hrCycle.2
      simpa [SimpleGraph.Walk.tail_support_append] using htail'
    have hdis :
        List.Disjoint a1.support.tail
          (r.dropUntil y hySupport).support.tail := by
      intro a ha hb
      exact ((List.nodup_append.mp htail).2.2 a ha a hb) rfl
    have hzTail1 : z ∈ a1.support.tail := by
      have : z = x ∨ z ∈ a1.support.tail := by
        simpa only [a1] using
          (SimpleGraph.Walk.mem_support_iff (p := a1) (w := z)).mp hz1
      exact this.resolve_left hzx
    have hzTail2 : z ∈ (r.dropUntil y hySupport).support.tail := by
      have hzdrop : z ∈ (r.dropUntil y hySupport).support := by
        simpa only [a2, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz2
      have : z = y ∨ z ∈ (r.dropUntil y hySupport).support.tail := by
        simpa using
          (SimpleGraph.Walk.mem_support_iff
            (p := r.dropUntil y hySupport) (w := z)).mp hzdrop
      exact this.resolve_left hzy
    exact (List.disjoint_left.mp hdis) hzTail1 hzTail2
  let A : G.Walk x y := if hz1 : z ∈ a1.support then a2 else a1
  have hAPath : A.IsPath := by
    by_cases hz1 : z ∈ a1.support
    · simp only [A, hz1, dite_true]
      exact ha2Path
    · simp only [A, hz1, dite_false]
      exact ha1Path
  have hACycle : ∀ v : V, v ∈ A.support → v ∈ C.vSet (G := G) := by
    intro v hv
    by_cases hz1 : z ∈ a1.support
    · exact ha2Cycle v (by simpa only [A, hz1, dite_true] using hv)
    · exact ha1Cycle v (by simpa only [A, hz1, dite_false] using hv)
  have hzNotA : z ∉ A.support := by
    by_cases hz1 : z ∈ a1.support
    · simpa only [A, hz1, dite_true] using hzNotA2OfA1 hz1
    · simpa only [A, hz1, dite_false] using hz1
  exact ⟨A, hAPath, hzNotA, hACycle⟩

/-- The local hub construction used in the Thomassen--Toft attachment
analysis.  An outside path joining neighbours of two rim vertices and
passing through a neighbour of a third rim vertex closes with the rim arc
which avoids that third vertex.  The third vertex then has its two rim
neighbours and the prescribed outside neighbour on the new cycle. -/
theorem hasWheelWitness_of_external_path_through
    (C : Cycle (G := G)) {p z q a b c : V}
    (hpC : p ∈ C.vSet (G := G)) (hzC : z ∈ C.vSet (G := G))
    (hqC : q ∈ C.vSet (G := G))
    (hzp : G.Adj z p) (hzq : G.Adj z q)
    (hpa : G.Adj p a) (hzb : G.Adj z b) (hcq : G.Adj c q)
    (hpq : p ≠ q) (hzpne : z ≠ p) (hzqne : z ≠ q)
    (P : G.Walk a c) (hP : P.IsPath) (hbP : b ∈ P.support)
    (hPout : ∀ v, v ∈ P.support → v ∉ C.vSet (G := G)) :
    HasWheelWitness G := by
  classical
  let L : G.Walk p a := .cons hpa .nil
  let R : G.Walk c q := .cons hcq .nil
  have hL : L.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [L, G.ne_of_adj hpa]
  have hR : R.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [R, G.ne_of_adj hcq]
  have hpNotP : p ∉ P.support := by
    intro hpP
    exact hPout p hpP hpC
  have hqNotP : q ∉ P.support := by
    intro hqP
    exact hPout q hqP hqC
  let Q₀ : G.Walk p c := L.append P
  have hQ₀ : Q₀.IsPath := by
    apply Erdos916.Walk.IsPath.append_of_support_inter_eq_endpoint hL hP
    intro x hxL hxP
    have hx : x = p ∨ x = a := by
      simpa [L] using hxL
    exact hx.resolve_left (fun h => hpNotP (h ▸ hxP))
  let Q : G.Walk p q := Q₀.append R
  have hQ : Q.IsPath := by
    apply Erdos916.Walk.IsPath.append_of_support_inter_eq_endpoint hQ₀ hR
    intro x hxQ₀ hxR
    have hxR' : x = c ∨ x = q := by
      simpa [R] using hxR
    rcases hxR' with hxc | hxq
    · exact hxc
    · exfalso
      have hqQ₀ : q ∈ Q₀.support := by simpa only [hxq] using hxQ₀
      have hxParts : q ∈ L.support ∨ q ∈ P.support := by
        simpa only [Q₀, SimpleGraph.Walk.mem_support_append_iff] using hqQ₀
      rcases hxParts with hqL | hqP
      · have : q = p ∨ q = a := by
          simpa [L] using hqL
        rcases this with hqp | hqa
        · exact hpq hqp.symm
        · exact hqNotP (by simpa only [hqa] using P.start_mem_support)
      · exact hqNotP hqP
  have hQsupport {v : V} (hv : v ∈ Q.support) :
      v = p ∨ v ∈ P.support ∨ v = q := by
    have hvParts : v ∈ Q₀.support ∨ v ∈ R.support := by
      simpa only [Q, SimpleGraph.Walk.mem_support_append_iff] using hv
    rcases hvParts with hvQ₀ | hvR
    · have hvParts' : v ∈ L.support ∨ v ∈ P.support := by
        simpa only [Q₀, SimpleGraph.Walk.mem_support_append_iff] using hvQ₀
      rcases hvParts' with hvL | hvP
      · have : v = p ∨ v = a := by
          simpa [L] using hvL
        rcases this with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl P.start_mem_support)
      · exact Or.inr (Or.inl hvP)
    · have : v = c ∨ v = q := by
        simpa [R] using hvR
      rcases this with rfl | rfl
      · exact Or.inr (Or.inl P.end_mem_support)
      · exact Or.inr (Or.inr rfl)
  obtain ⟨A, hA, hzA, hAC⟩ :=
    Erdos916.Cycle.exists_path_between_avoiding G C hqC hpC hzC
      hpq.symm hzqne hzpne
  have hdis : List.Disjoint Q.support.tail A.support.tail := by
    rw [List.disjoint_left]
    intro v hvQ hvA
    have hvQmem : v ∈ Q.support := List.mem_of_mem_tail hvQ
    have hvAmem : v ∈ A.support := List.mem_of_mem_tail hvA
    have hvC : v ∈ C.vSet (G := G) := hAC v hvAmem
    rcases hQsupport hvQmem with rfl | hvP | rfl
    · have hnodup := hQ.support_nodup
      rw [Q.support_eq_cons] at hnodup
      exact (List.nodup_cons.mp hnodup).1 hvQ
    · exact hPout v hvP hvC
    · have hnodup := hA.support_nodup
      rw [A.support_eq_cons] at hnodup
      exact (List.nodup_cons.mp hnodup).1 hvA
  let W : G.Walk p p := Q.append A
  have hQlen : 1 < Q.length := by
    simp only [Q, Q₀, L, R, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
    omega
  have hW : W.IsCycle := by
    exact hQ.isCycle_append hA hdis (Or.inl hQlen)
  have hzNotQ : z ∉ Q.support := by
    intro hzQ
    rcases hQsupport hzQ with hzp' | hzP | hzq'
    · exact hzpne hzp'
    · exact hPout z hzP hzC
    · exact hzqne hzq'
  have hzNotW : z ∉ W.support := by
    intro hzW
    have : z ∈ Q.support ∨ z ∈ A.support := by
      simpa only [W, SimpleGraph.Walk.mem_support_append_iff] using hzW
    exact this.elim hzNotQ hzA
  have hpW : p ∈ W.support := W.start_mem_support
  have hqW : q ∈ W.support := by
    apply Q.support_subset_support_append_left A
    exact Q.end_mem_support
  have hbW : b ∈ W.support := by
    apply Q.support_subset_support_append_left A
    apply Q₀.support_subset_support_append_left R
    apply L.support_subset_support_append_right P
    exact hbP
  have hpb : p ≠ b := by
    intro h
    subst b
    exact hPout p hbP hpC
  have hqb : q ≠ b := by
    intro h
    subst b
    exact hPout q hbP hqC
  refine ⟨p, W, z, hW, hzNotW, ?_⟩
  have hpMem : p ∈ G.neighborFinset z ∩ W.support.toFinset := by
    exact Finset.mem_inter.mpr ⟨by simpa using hzp, by simpa using hpW⟩
  have hqMem : q ∈ G.neighborFinset z ∩ W.support.toFinset := by
    exact Finset.mem_inter.mpr ⟨by simpa using hzq, by simpa using hqW⟩
  have hbMem : b ∈ G.neighborFinset z ∩ W.support.toFinset := by
    exact Finset.mem_inter.mpr ⟨by simpa using hzb, by simpa using hbW⟩
  have hthree := Finset.two_lt_card_iff.mpr
    ⟨p, q, b, hpMem, hqMem, hbMem, hpq, hpb, hqb⟩
  omega

/-- A paper cycle of length three can be displayed as a triangle. -/
theorem Cycle.triangleDisplay_of_length_eq_three
    (C : Cycle (G := G)) (hlen : C.length (G := G) = 3) :
    Nonempty (TriangleDisplay G C) := by
  classical
  let r0 := C.walk.getVert 0
  let r1 := C.walk.getVert 1
  let r2 := C.walk.getVert 2
  have hwalk : C.walk.length = 3 := hlen
  have hne (i j : ℕ) (hi : i ≤ 2) (hj : j ≤ 2) (hij : i ≠ j) :
      C.walk.getVert i ≠ C.walk.getVert j := by
    intro heq
    have heqIdx := C.isCycle.getVert_injOn'
      (show i ≤ C.walk.length - 1 by omega)
      (show j ≤ C.walk.length - 1 by omega) heq
    exact hij heqIdx
  have hadj01 : G.Adj r0 r1 := by
    simpa only [r0, r1] using C.walk.adj_getVert_succ (i := 0) (by omega)
  have hadj12 : G.Adj r1 r2 := by
    simpa only [r1, r2] using C.walk.adj_getVert_succ (i := 1) (by omega)
  have hadj20 : G.Adj r2 r0 := by
    have h := C.walk.adj_getVert_succ (i := 2) (by omega)
    rw [show 2 + 1 = C.walk.length by omega, C.walk.getVert_length] at h
    simpa only [r0, r2, Walk.getVert_zero] using h
  have hverts : C.verts (G := G) = {r0, r1, r2} := by
    ext z
    constructor
    · intro hz
      have hz' : z ∈ C.walk.support := by
        simpa only [Cycle.verts, List.mem_toFinset] using hz
      obtain ⟨i, hiz, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hz'
      rw [hwalk] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton]
      interval_cases i
      · exact Or.inl (by simpa only [r0] using hiz.symm)
      · exact Or.inr (Or.inl (by simpa only [r1] using hiz.symm))
      · exact Or.inr (Or.inr (by simpa only [r2] using hiz.symm))
      · apply Or.inl
        rw [← hiz]
        change C.walk.getVert 3 = C.walk.getVert 0
        rw [show 3 = C.walk.length by omega, C.walk.getVert_length,
          C.walk.getVert_zero]
    · intro hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · simpa only [Cycle.verts, List.mem_toFinset, r0] using
          C.walk.getVert_mem_support (i := 0)
      · simpa only [Cycle.verts, List.mem_toFinset, r1] using
          C.walk.getVert_mem_support (i := 1)
      · simpa only [Cycle.verts, List.mem_toFinset, r2] using
          C.walk.getVert_mem_support (i := 2)
  exact ⟨
    { r0 := r0
      r1 := r1
      r2 := r2
      adj01 := hadj01
      adj12 := hadj12
      adj20 := hadj20
      ne01 := hne 0 1 (by omega) (by omega) (by omega)
      ne02 := hne 0 2 (by omega) (by omega) (by omega)
      ne12 := hne 1 2 (by omega) (by omega) (by omega)
      verts_eq := hverts }⟩

/-- A paper cycle of length four can be displayed as a simple four-cycle. -/
theorem Cycle.fourCycleDisplay_of_length_eq_four
    (C : Cycle (G := G)) (hlen : C.length (G := G) = 4) :
    Nonempty (FourCycleDisplay G C) := by
  classical
  let r0 := C.walk.getVert 0
  let r1 := C.walk.getVert 1
  let r2 := C.walk.getVert 2
  let r3 := C.walk.getVert 3
  have hwalk : C.walk.length = 4 := hlen
  have hne (i j : ℕ) (hi : i ≤ 3) (hj : j ≤ 3) (hij : i ≠ j) :
      C.walk.getVert i ≠ C.walk.getVert j := by
    intro heq
    have heqIdx := C.isCycle.getVert_injOn'
      (show i ≤ C.walk.length - 1 by omega)
      (show j ≤ C.walk.length - 1 by omega) heq
    exact hij heqIdx
  have hadj01 : G.Adj r0 r1 := by
    simpa only [r0, r1] using C.walk.adj_getVert_succ (i := 0) (by omega)
  have hadj12 : G.Adj r1 r2 := by
    simpa only [r1, r2] using C.walk.adj_getVert_succ (i := 1) (by omega)
  have hadj23 : G.Adj r2 r3 := by
    simpa only [r2, r3] using C.walk.adj_getVert_succ (i := 2) (by omega)
  have hadj30 : G.Adj r3 r0 := by
    have h := C.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3 + 1 = C.walk.length by omega, C.walk.getVert_length] at h
    simpa only [r0, r3, Walk.getVert_zero] using h
  have hverts : C.verts (G := G) = {r0, r1, r2, r3} := by
    ext z
    constructor
    · intro hz
      have hz' : z ∈ C.walk.support := by
        simpa only [Cycle.verts, List.mem_toFinset] using hz
      obtain ⟨i, hiz, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hz'
      rw [hwalk] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton]
      interval_cases i
      · exact Or.inl (by simpa only [r0] using hiz.symm)
      · exact Or.inr (Or.inl (by simpa only [r1] using hiz.symm))
      · exact Or.inr (Or.inr (Or.inl (by simpa only [r2] using hiz.symm)))
      · exact Or.inr (Or.inr (Or.inr (by simpa only [r3] using hiz.symm)))
      · apply Or.inl
        rw [← hiz]
        change C.walk.getVert 4 = C.walk.getVert 0
        rw [show 4 = C.walk.length by omega, C.walk.getVert_length,
          C.walk.getVert_zero]
    · intro hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · simpa only [Cycle.verts, List.mem_toFinset, r0] using
          C.walk.getVert_mem_support (i := 0)
      · simpa only [Cycle.verts, List.mem_toFinset, r1] using
          C.walk.getVert_mem_support (i := 1)
      · simpa only [Cycle.verts, List.mem_toFinset, r2] using
          C.walk.getVert_mem_support (i := 2)
      · simpa only [Cycle.verts, List.mem_toFinset, r3] using
          C.walk.getVert_mem_support (i := 3)
  exact ⟨
    { r0 := r0
      r1 := r1
      r2 := r2
      r3 := r3
      adj01 := hadj01
      adj12 := hadj12
      adj23 := hadj23
      adj30 := hadj30
      ne01 := hne 0 1 (by omega) (by omega) (by omega)
      ne02 := hne 0 2 (by omega) (by omega) (by omega)
      ne03 := hne 0 3 (by omega) (by omega) (by omega)
      ne12 := hne 1 2 (by omega) (by omega) (by omega)
      ne13 := hne 1 3 (by omega) (by omega) (by omega)
      ne23 := hne 2 3 (by omega) (by omega) (by omega)
      verts_eq := hverts }⟩

/-- Any two distinct vertices of a displayed triangle are adjacent. -/
theorem TriangleDisplay.adj_of_mem
    {C : Cycle (G := G)} (T : TriangleDisplay G C)
    {a b : V} (ha : a ∈ C.verts (G := G))
    (hb : b ∈ C.verts (G := G)) (hab : a ≠ b) :
    G.Adj a b := by
  rw [T.verts_eq] at ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact (hab rfl).elim
  · exact T.adj01
  · exact T.adj20.symm
  · exact T.adj01.symm
  · exact (hab rfl).elim
  · exact T.adj12
  · exact T.adj20
  · exact T.adj12.symm
  · exact (hab rfl).elim

/-- Two two-element subsets covering a three-element set share one element
and have distinct remaining elements. -/
theorem exists_common_and_distinct_of_two_pairs_cover_three
    (U A B : Finset V) (hU : U.card = 3)
    (hA : A.card = 2) (hB : B.card = 2)
    (hAU : A ⊆ U) (hBU : B ⊆ U) (hcover : U ⊆ A ∪ B) :
    ∃ r a b : V,
      r ∈ A ∧ r ∈ B ∧ a ∈ A ∧ b ∈ B ∧
        r ≠ a ∧ r ≠ b ∧ a ≠ b := by
  classical
  have hunionSub : A ∪ B ⊆ U := Finset.union_subset hAU hBU
  have hunionCard : (A ∪ B).card = 3 := by
    apply Nat.le_antisymm
    · simpa only [hU] using Finset.card_le_card hunionSub
    · simpa only [hU] using Finset.card_le_card hcover
  have hinterCard : (A ∩ B).card = 1 := by
    have h := Finset.card_union_add_card_inter A B
    omega
  obtain ⟨r, hinterEq⟩ := Finset.card_eq_one.mp hinterCard
  have hrInter : r ∈ A ∩ B := by rw [hinterEq]; simp
  have hrA : r ∈ A := (Finset.mem_inter.mp hrInter).1
  have hrB : r ∈ B := (Finset.mem_inter.mp hrInter).2
  have hAer : (A.erase r).card = 1 := by
    rw [Finset.card_erase_of_mem hrA, hA]
  have hBer : (B.erase r).card = 1 := by
    rw [Finset.card_erase_of_mem hrB, hB]
  obtain ⟨a, haer⟩ := Finset.card_pos.mp (by omega : 0 < (A.erase r).card)
  obtain ⟨b, hber⟩ := Finset.card_pos.mp (by omega : 0 < (B.erase r).card)
  have ha := Finset.mem_erase.mp haer
  have hb := Finset.mem_erase.mp hber
  have hab : a ≠ b := by
    intro hab
    subst b
    have haInter : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha.2, hb.2⟩
    rw [hinterEq] at haInter
    exact ha.1 (by simpa only [Finset.mem_singleton] using haInter)
  exact ⟨r, a, b, hrA, hrB, ha.2, hb.2, ha.1.symm, hb.1.symm, hab⟩

/-- A displayed five-cycle and a hub adjacent to three displayed rim
vertices give a wheel witness. -/
theorem hasWheelWitness_of_fiveCycle_threeSpokes
    {r0 r1 r2 r3 r4 x : V}
    (h01 : G.Adj r0 r1) (h12 : G.Adj r1 r2)
    (h23 : G.Adj r2 r3) (h34 : G.Adj r3 r4)
    (h40 : G.Adj r4 r0)
    (hx0 : G.Adj x r0) (hx2 : G.Adj x r2) (hx4 : G.Adj x r4)
    (h01ne : r0 ≠ r1) (h02ne : r0 ≠ r2) (h03ne : r0 ≠ r3)
    (h04ne : r0 ≠ r4) (h12ne : r1 ≠ r2) (h13ne : r1 ≠ r3)
    (h14ne : r1 ≠ r4) (h23ne : r2 ≠ r3) (h24ne : r2 ≠ r4)
    (h34ne : r3 ≠ r4)
    (hxr0 : x ≠ r0) (hxr1 : x ≠ r1) (hxr2 : x ≠ r2)
    (hxr3 : x ≠ r3) (hxr4 : x ≠ r4) :
    HasWheelWitness G := by
  let p : G.Walk r0 r0 :=
    .cons h01 (.cons h12 (.cons h23 (.cons h34 (.cons h40 .nil))))
  have hp : p.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def]
    constructor
    · rw [SimpleGraph.Walk.isTrail_def]
      simp [p, h01ne, h02ne, h03ne, h04ne, h12ne, h13ne, h14ne,
        h23ne, h24ne, h34ne, h01ne.symm, h02ne.symm, h03ne.symm,
        h04ne.symm, h12ne.symm, h13ne.symm, h14ne.symm, h23ne.symm,
        h24ne.symm, h34ne.symm]
    constructor
    · simp [p]
    · simp [p, h01ne, h02ne, h03ne, h04ne, h12ne, h13ne, h14ne,
        h23ne, h24ne, h34ne, h01ne.symm, h02ne.symm, h03ne.symm,
        h04ne.symm, h12ne.symm, h13ne.symm, h14ne.symm, h23ne.symm,
        h24ne.symm, h34ne.symm]
  refine ⟨r0, p, x, hp, ?_, ?_⟩
  · simp [p, hxr0, hxr1, hxr2, hxr3, hxr4]
  · have h0 : r0 ∈ G.neighborFinset x ∩ p.support.toFinset := by simp [p, hx0]
    have h2 : r2 ∈ G.neighborFinset x ∩ p.support.toFinset := by simp [p, hx2]
    have h4 : r4 ∈ G.neighborFinset x ∩ p.support.toFinset := by simp [p, hx4]
    have hthree := Finset.two_lt_card_iff.mpr
      ⟨r0, r2, r4, h0, h2, h4, h02ne, h04ne, h24ne⟩
    omega

/-! ## Elementary consequences in the no-wheel branch -/

/-- The unique-bridge field says intrinsically that the full complement of
the selected cycle is connected: every outside vertex belongs to the same
connected component represented by `M.bridge`. -/
theorem MaxCycleCertificate.complement_connected
    (M : MaxCycleCertificate G) :
    (G.induce (M.cycle.vSet (G := G))ᶜ).Connected := by
  have heq : bridgeSet (G := G) M.cycle M.bridge =
      (M.cycle.vSet (G := G))ᶜ := by
    apply Set.Subset.antisymm
    · exact bridgeSet_subset_compl_vSet (G := G) M.cycle M.bridge
    · intro x hx
      exact (M.mem_bridge_iff_not_mem_cycle G x).mpr hx
  rw [← heq]
  exact M.bridge_connected G

/-- In the single-block case of the complement, distinct attachments of
the two outer vertices of a consecutive rim triple force a wheel.  The
vertex-two-connected three-terminal theorem supplies an outside path through
the middle attachment, and `hasWheelWitness_of_external_path_through` closes
that path along the rim arc avoiding the middle rim vertex. -/
theorem MaxCycleCertificate.hasWheelWitness_of_distinct_outer_attachments
    (M : MaxCycleCertificate G) {p z q a b c : V}
    (hpC : p ∈ M.cycle.vSet (G := G))
    (hzC : z ∈ M.cycle.vSet (G := G))
    (hqC : q ∈ M.cycle.vSet (G := G))
    (hzp : G.Adj z p) (hzq : G.Adj z q)
    (hpa : G.Adj p a) (hzb : G.Adj z b) (hcq : G.Adj c q)
    (haB : a ∈ bridgeSet (G := G) M.cycle M.bridge)
    (hbB : b ∈ bridgeSet (G := G) M.cycle M.bridge)
    (hcB : c ∈ bridgeSet (G := G) M.cycle M.bridge)
    (hpq : p ≠ q) (hzpne : z ≠ p) (hzqne : z ≠ q)
    (hac : a ≠ c)
    (hdelete : ∀ d : {v : V // v ∉ M.cycle.vSet (G := G)},
      ((G.induce (M.cycle.vSet (G := G))ᶜ).induce
        (fun w => w ≠ d)).Connected) :
    HasWheelWitness G := by
  classical
  let B : Set V := (M.cycle.vSet (G := G))ᶜ
  have haout : a ∉ M.cycle.vSet (G := G) :=
    mem_bridge_imp_not_mem_cycle (G := G) M.cycle M.bridge haB
  have hbout : b ∉ M.cycle.vSet (G := G) :=
    mem_bridge_imp_not_mem_cycle (G := G) M.cycle M.bridge hbB
  have hcout : c ∉ M.cycle.vSet (G := G) :=
    mem_bridge_imp_not_mem_cycle (G := G) M.cycle M.bridge hcB
  let aB : B := ⟨a, haout⟩
  let bB : B := ⟨b, hbout⟩
  let cB : B := ⟨c, hcout⟩
  have hacB : aB ≠ cB := fun h => hac (congrArg Subtype.val h)
  have hconnB : (G.induce B).Connected := by
    simpa only [B] using M.complement_connected G
  obtain ⟨Psub, hPsub, hbPsub⟩ :
      ∃ Psub : (G.induce B).Walk aB cB,
        Psub.IsPath ∧ bB ∈ Psub.support := by
    by_cases hab : a = b
    · have habB : aB = bB := by apply Subtype.ext; exact hab
      obtain ⟨Psub, hPsub⟩ :=
        hconnB.preconnected.exists_isPath aB cB
      exact ⟨Psub, hPsub, by simpa only [← habB] using Psub.start_mem_support⟩
    · by_cases hbc : b = c
      · have hbcB : bB = cB := by apply Subtype.ext; exact hbc
        obtain ⟨Psub, hPsub⟩ :=
          hconnB.preconnected.exists_isPath aB cB
        exact ⟨Psub, hPsub, by simpa only [hbcB] using Psub.end_mem_support⟩
      · have habB : aB ≠ bB := fun h => hab (congrArg Subtype.val h)
        have hbcB : bB ≠ cB := fun h => hbc (congrArg Subtype.val h)
        have hdeleteB : ∀ d : B,
            ((G.induce B).induce (fun w => w ≠ d)).Connected := by
          intro d
          dsimp only [B] at d ⊢
          exact hdelete d
        exact exists_rooted_three_path habB hacB hbcB hconnB hdeleteB
  let inc : G.induce B →g G :=
    (SimpleGraph.Embedding.induce (G := G) (s := B)).toHom
  let P : G.Walk a c := Psub.map inc
  have hP : P.IsPath := hPsub.map Subtype.val_injective
  have hbP : b ∈ P.support := by
    change b ∈ (Psub.map inc).support
    rw [SimpleGraph.Walk.support_map]
    have : b ∈ Psub.support.map inc :=
      List.mem_map.mpr ⟨bB, hbPsub, by rfl⟩
    simpa only [inc] using this
  have hPout : ∀ v, v ∈ P.support →
      v ∉ M.cycle.vSet (G := G) := by
    intro v hv
    have hv' : v ∈ Psub.support.map inc := by
      change v ∈ (Psub.map inc).support at hv
      rw [SimpleGraph.Walk.support_map] at hv
      exact hv
    obtain ⟨w, -, hw⟩ := List.mem_map.mp hv'
    have hval : (w : V) = v := by
      have hinc : inc w = (w : V) := by rfl
      exact hinc.symm.trans hw
    rw [← hval]
    simpa only [B, Set.mem_compl_iff] using w.2
  exact hasWheelWitness_of_external_path_through G M.cycle
    hpC hzC hqC hzp hzq hpa hzb hcq hpq hzpne hzqne
    P hP hbP hPout

/-- Consequently, in a wheel-free graph whose cycle complement is itself
vertex-two-connected, any selected attachments of three consecutive rim
vertices have the forced alternating pattern: the outer attachments agree,
and the middle attachment is different. -/
theorem MaxCycleCertificate.attachment_alternation_of_complement_twoConnected
    (M : MaxCycleCertificate G) (hno : ¬HasWheelWitness G)
    {p z q a b c : V}
    (hpC : p ∈ M.cycle.vSet (G := G))
    (hzC : z ∈ M.cycle.vSet (G := G))
    (hqC : q ∈ M.cycle.vSet (G := G))
    (hzp : G.Adj z p) (hzq : G.Adj z q)
    (hpa : G.Adj p a) (hzb : G.Adj z b) (hcq : G.Adj c q)
    (haB : a ∈ bridgeSet (G := G) M.cycle M.bridge)
    (hbB : b ∈ bridgeSet (G := G) M.cycle M.bridge)
    (hcB : c ∈ bridgeSet (G := G) M.cycle M.bridge)
    (hpq : p ≠ q) (hzpne : z ≠ p) (hzqne : z ≠ q)
    (hdelete : ∀ d : {v : V // v ∉ M.cycle.vSet (G := G)},
      ((G.induce (M.cycle.vSet (G := G))ᶜ).induce
        (fun w => w ≠ d)).Connected) :
    a = c ∧ b ≠ a := by
  classical
  have hac : a = c := by
    by_contra hne
    exact hno (M.hasWheelWitness_of_distinct_outer_attachments G
      hpC hzC hqC hzp hzq hpa hzb hcq haB hbB hcB
      hpq hzpne hzqne hne hdelete)
  refine ⟨hac, ?_⟩
  intro hba
  have hp : p ∈ G.neighborFinset a ∩ M.cycle.verts (G := G) := by
    exact Finset.mem_inter.mpr ⟨by simpa using hpa.symm,
      (M.cycle.mem_vSet_iff (G := G)).mp hpC⟩
  have hz : z ∈ G.neighborFinset a ∩ M.cycle.verts (G := G) := by
    exact Finset.mem_inter.mpr ⟨by
      simpa only [SimpleGraph.mem_neighborFinset] using
        (show G.Adj a z by simpa only [hba] using hzb.symm),
      (M.cycle.mem_vSet_iff (G := G)).mp hzC⟩
  have hq : q ∈ G.neighborFinset a ∩ M.cycle.verts (G := G) := by
    exact Finset.mem_inter.mpr ⟨by
      simpa only [SimpleGraph.mem_neighborFinset] using
        (show G.Adj a q by simpa only [hac] using hcq),
      (M.cycle.mem_vSet_iff (G := G)).mp hqC⟩
  have hthree : 3 ≤
      (G.neighborFinset a ∩ M.cycle.verts (G := G)).card := by
    have := Finset.two_lt_card_iff.mpr
      ⟨p, z, q, hp, hz, hq, hzpne.symm, hpq, hzqne⟩
    omega
  exact hno (M.hasWheelWitness_of_three_neighbors G a haB hthree)

/-- Relative to a maximum-cycle certificate, the neighbours of a bridge
vertex split exactly into its neighbours on the cycle and its neighbours in
the same complementary bridge. -/
theorem MaxCycleCertificate.neighborFinset_eq_cycle_union_bridge
    (M : MaxCycleCertificate G) (x : V) :
    G.neighborFinset x =
      (G.neighborFinset x ∩ M.cycle.verts (G := G)) ∪
      (G.neighborFinset x \ M.cycle.verts (G := G)) := by
  classical
  ext y
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- A cycle vertex and a vertex of a complementary bridge cannot coincide. -/
theorem MaxCycleCertificate.disjoint_cycle_bridge_neighborFinsets
    (M : MaxCycleCertificate G) (x : V) :
    Disjoint
      (G.neighborFinset x ∩ M.cycle.verts (G := G))
      (G.neighborFinset x \ M.cycle.verts (G := G)) := by
  classical
  exact Finset.disjoint_of_subset_left Finset.inter_subset_right
    Finset.disjoint_sdiff

/-- If the graph has no wheel, minimum degree three forces every vertex of
the unique complementary bridge to have a neighbour in that bridge.  Thus
the bridge cannot be a singleton; this is the first local reduction in the
Thomassen--Toft analysis. -/
theorem MaxCycleCertificate.exists_adj_in_bridge_of_noWheel
    (M : MaxCycleCertificate G) (hno : ¬HasWheelWitness G)
    (hmin : ∀ v : V, 3 ≤ G.degree v) {x : V}
    (hxB : x ∈ bridgeSet (G := G) M.cycle M.bridge) :
    ∃ y : V, y ∈ bridgeSet (G := G) M.cycle M.bridge ∧ G.Adj x y := by
  classical
  let NC := G.neighborFinset x ∩ M.cycle.verts (G := G)
  let NB := G.neighborFinset x \ M.cycle.verts (G := G)
  have hsplit : G.neighborFinset x = NC ∪ NB := by
    simpa only [NC, NB] using M.neighborFinset_eq_cycle_union_bridge G x
  have hdis : Disjoint NC NB := by
    simpa only [NC, NB] using M.disjoint_cycle_bridge_neighborFinsets G x
  have hcardSplit : G.degree x = NC.card + NB.card := by
    rw [← G.card_neighborFinset_eq_degree, hsplit,
      Finset.card_union_of_disjoint hdis]
  have hcycle : NC.card ≤ 2 := by
    simpa only [NC] using M.card_neighbors_on_cycle_le_two_of_noWheel G hno hxB
  have hbridge : 0 < NB.card := by
    have := hmin x
    omega
  obtain ⟨y, hyNB⟩ := Finset.card_pos.mp hbridge
  have hy := Finset.mem_sdiff.mp hyNB
  have hyCycle : y ∉ M.cycle.vSet (G := G) := by
    simpa only [Cycle.vSet, M.cycle.mem_vSet_iff] using hy.2
  exact ⟨y, (M.mem_bridge_iff_not_mem_cycle G y).2 hyCycle,
    by simpa only [SimpleGraph.mem_neighborFinset] using hy.1⟩

/-- Equivalently, the carrier of the complementary bridge has at least two
vertices in the no-wheel branch. -/
theorem MaxCycleCertificate.two_le_ncard_bridge_of_noWheel
    (M : MaxCycleCertificate G) (hno : ¬HasWheelWitness G)
    (hmin : ∀ v : V, 3 ≤ G.degree v) :
    2 ≤ (bridgeSet (G := G) M.cycle M.bridge).ncard := by
  classical
  obtain ⟨x, hx⟩ := ComponentCompl.nonempty (C := M.bridge)
  have hxB : x ∈ bridgeSet (G := G) M.cycle M.bridge := by
    simpa only [bridgeSet] using hx
  obtain ⟨y, hyB, hxy⟩ := M.exists_adj_in_bridge_of_noWheel G hno hmin hxB
  have hne : x ≠ y := hxy.ne
  have hone : 1 < (bridgeSet (G := G) M.cycle M.bridge).ncard :=
    (Set.one_lt_ncard (s := bridgeSet (G := G) M.cycle M.bridge)).mpr
      ⟨x, hxB, y, hyB, hne⟩
  omega

/-- In the two-vertex bridge case, every bridge vertex has exactly one
neighbour in the bridge.  Together with the no-wheel bound and minimum
degree three, this forces ambient degree three and exactly two neighbours on
the rim. -/
theorem MaxCycleCertificate.degree_eq_three_of_bridge_ncard_eq_two
    (M : MaxCycleCertificate G) (hno : ¬HasWheelWitness G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hBcard : (bridgeSet (G := G) M.cycle M.bridge).ncard = 2)
    {x : V} (hxB : x ∈ bridgeSet (G := G) M.cycle M.bridge) :
    G.degree x = 3 ∧
      (G.neighborFinset x ∩ M.cycle.verts (G := G)).card = 2 := by
  classical
  let Cverts := M.cycle.verts (G := G)
  let B : Finset V := Finset.univ \ Cverts
  let NC := G.neighborFinset x ∩ Cverts
  let NB := G.neighborFinset x \ Cverts
  have hBset : (B : Set V) = bridgeSet (G := G) M.cycle M.bridge := by
    ext y
    simp only [B, Cverts, Finset.coe_sdiff, Finset.coe_univ, Set.mem_diff,
      Set.mem_univ, true_and, Finset.mem_coe, M.mem_bridge_iff_not_mem_cycle]
    exact not_congr M.cycle.mem_vSet_iff
  have hBcardFin : B.card = 2 := by
    have hncard : (B : Set V).ncard = 2 := by
      rw [hBset]
      exact hBcard
    simpa only [Set.ncard_coe_finset] using hncard
  have hxBfin : x ∈ B := by
    change x ∈ (B : Set V)
    rw [hBset]
    exact hxB
  have hNBsub : NB ⊆ B.erase x := by
    intro y hy
    have hy' := Finset.mem_sdiff.mp hy
    have hxy : G.Adj x y := by
      simpa only [SimpleGraph.mem_neighborFinset] using hy'.1
    apply Finset.mem_erase.mpr
    refine ⟨hxy.ne.symm, ?_⟩
    simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact hy'.2
  have hNBle : NB.card ≤ 1 := by
    have hle := Finset.card_le_card hNBsub
    rw [Finset.card_erase_of_mem hxBfin, hBcardFin] at hle
    exact hle
  have hsplit : G.neighborFinset x = NC ∪ NB := by
    simpa only [NC, NB, Cverts] using
      M.neighborFinset_eq_cycle_union_bridge G x
  have hdis : Disjoint NC NB := by
    simpa only [NC, NB, Cverts] using
      M.disjoint_cycle_bridge_neighborFinsets G x
  have hdegree : G.degree x = NC.card + NB.card := by
    rw [← G.card_neighborFinset_eq_degree, hsplit,
      Finset.card_union_of_disjoint hdis]
  have hNCle : NC.card ≤ 2 := by
    simpa only [NC, Cverts] using
      M.card_neighbors_on_cycle_le_two_of_noWheel G hno hxB
  have hdegMin := hmin x
  have hdeg : G.degree x = 3 := by omega
  have hNC : NC.card = 2 := by omega
  exact ⟨hdeg, by simpa only [NC, Cverts] using hNC⟩

/-- Concrete data carried by a two-vertex complementary bridge. -/
structure TwoVertexBridgeData (M : MaxCycleCertificate G) where
  x : V
  y : V
  ne : x ≠ y
  x_mem : x ∈ bridgeSet (G := G) M.cycle M.bridge
  y_mem : y ∈ bridgeSet (G := G) M.cycle M.bridge
  bridge_eq : bridgeSet (G := G) M.cycle M.bridge = ({x, y} : Set V)
  adj : G.Adj x y
  degree_x : G.degree x = 3
  degree_y : G.degree y = 3
  card_cycle_neighbors_x :
    (G.neighborFinset x ∩ M.cycle.verts (G := G)).card = 2
  card_cycle_neighbors_y :
    (G.neighborFinset y ∩ M.cycle.verts (G := G)).card = 2
  cover : M.cycle.verts (G := G) ⊆
    (G.neighborFinset x ∩ M.cycle.verts (G := G)) ∪
      (G.neighborFinset y ∩ M.cycle.verts (G := G))

/-- Extract the two displayed bridge vertices, their joining edge, degrees,
and full rim-attachment cover. -/
theorem MaxCycleCertificate.exists_twoVertexBridgeData
    (M : MaxCycleCertificate G) (hno : ¬HasWheelWitness G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hBcard : (bridgeSet (G := G) M.cycle M.bridge).ncard = 2) :
    Nonempty (TwoVertexBridgeData G M) := by
  classical
  obtain ⟨x, hx⟩ := ComponentCompl.nonempty (C := M.bridge)
  have hxB : x ∈ bridgeSet (G := G) M.cycle M.bridge := by
    simpa only [bridgeSet] using hx
  have hone : 1 < (bridgeSet (G := G) M.cycle M.bridge).ncard := by omega
  obtain ⟨y, hyB, hyx⟩ :=
    (bridgeSet (G := G) M.cycle M.bridge).exists_ne_of_one_lt_ncard hone x
  have hxy : x ≠ y := hyx.symm
  have hpairSub : ({x, y} : Set V) ⊆
      bridgeSet (G := G) M.cycle M.bridge := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxB
    · exact hyB
  have hpairEq : ({x, y} : Set V) =
      bridgeSet (G := G) M.cycle M.bridge := by
    apply Set.eq_of_subset_of_ncard_le hpairSub
    rw [hBcard, Set.ncard_pair hxy]
  obtain ⟨z, hzB, hxz⟩ :=
    M.exists_adj_in_bridge_of_noWheel G hno hmin hxB
  have hzPair : z = x ∨ z = y := by
    have : z ∈ ({x, y} : Set V) := by rw [hpairEq]; exact hzB
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hxyAdj : G.Adj x y := by
    rcases hzPair with hzx | hzy
    · subst z
      exact (hxz.ne rfl).elim
    · simpa only [hzy] using hxz
  have hxDeg := M.degree_eq_three_of_bridge_ncard_eq_two
    G hno hmin hBcard hxB
  have hyDeg := M.degree_eq_three_of_bridge_ncard_eq_two
    G hno hmin hBcard hyB
  have hcover : M.cycle.verts (G := G) ⊆
      (G.neighborFinset x ∩ M.cycle.verts (G := G)) ∪
        (G.neighborFinset y ∩ M.cycle.verts (G := G)) := by
    intro c hc
    obtain ⟨z, hzBridge, hcz⟩ := M.exists_adj_bridge G
      (M.cycle.mem_vSet_iff.mpr hc)
    have hz : z = x ∨ z = y := by
      have : z ∈ ({x, y} : Set V) := by
        rw [hpairEq]
        exact hzBridge
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hz with rfl | rfl
    · exact Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨by simpa using hcz.symm, hc⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_inter.mpr ⟨by simpa using hcz.symm, hc⟩)
  exact ⟨
    { x := x
      y := y
      ne := hxy
      x_mem := hxB
      y_mem := hyB
      bridge_eq := hpairEq.symm
      adj := hxyAdj
      degree_x := hxDeg.1
      degree_y := hyDeg.1
      card_cycle_neighbors_x := hxDeg.2
      card_cycle_neighbors_y := hyDeg.2
      cover := hcover }⟩

/-- If the complementary bridge has two vertices in the no-wheel branch,
the maximum chordless rim has length at most four. -/
theorem MaxCycleCertificate.cycle_length_le_four_of_bridge_ncard_eq_two
    (M : MaxCycleCertificate G) (hno : ¬HasWheelWitness G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hBcard : (bridgeSet (G := G) M.cycle M.bridge).ncard = 2) :
    M.cycle.length (G := G) ≤ 4 := by
  classical
  obtain ⟨x, hxB⟩ := ComponentCompl.nonempty (C := M.bridge)
  have hxBridge : x ∈ bridgeSet (G := G) M.cycle M.bridge := by
    simpa only [bridgeSet] using hxB
  have hone : 1 < (bridgeSet (G := G) M.cycle M.bridge).ncard := by omega
  obtain ⟨y, hyBridge, hyx⟩ :=
    (bridgeSet (G := G) M.cycle M.bridge).exists_ne_of_one_lt_ncard hone x
  have hxy : x ≠ y := hyx.symm
  have hpairSub : ({x, y} : Set V) ⊆
      bridgeSet (G := G) M.cycle M.bridge := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxBridge
    · exact hyBridge
  have hpairEq : ({x, y} : Set V) =
      bridgeSet (G := G) M.cycle M.bridge := by
    apply Set.eq_of_subset_of_ncard_le hpairSub
    rw [hBcard, Set.ncard_pair hxy]
  let NX := G.neighborFinset x ∩ M.cycle.verts (G := G)
  let NY := G.neighborFinset y ∩ M.cycle.verts (G := G)
  have hNX : NX.card = 2 := by
    simpa only [NX] using
      (M.degree_eq_three_of_bridge_ncard_eq_two G hno hmin hBcard hxBridge).2
  have hNY : NY.card = 2 := by
    simpa only [NY] using
      (M.degree_eq_three_of_bridge_ncard_eq_two G hno hmin hBcard hyBridge).2
  have hcover : M.cycle.verts (G := G) ⊆ NX ∪ NY := by
    intro c hc
    have hcSet : c ∈ M.cycle.vSet (G := G) := by
      exact M.cycle.mem_vSet_iff.mpr hc
    obtain ⟨z, hzBridge, hcz⟩ := M.exists_adj_bridge G hcSet
    have hzEq : z = x ∨ z = y := by
      have hzMem : z ∈ ({x, y} : Set V) := by
        rw [hpairEq]
        exact hzBridge
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzMem
    rcases hzEq with rfl | rfl
    · apply Finset.mem_union_left
      exact Finset.mem_inter.mpr ⟨by simpa only [SimpleGraph.mem_neighborFinset] using hcz.symm, hc⟩
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨by simpa only [SimpleGraph.mem_neighborFinset] using hcz.symm, hc⟩
  have hcardCycle : (M.cycle.verts (G := G)).card ≤ 4 := by
    calc
      (M.cycle.verts (G := G)).card ≤ (NX ∪ NY).card := Finset.card_le_card hcover
      _ ≤ NX.card + NY.card := Finset.card_union_le NX NY
      _ = 4 := by omega
  change M.cycle.walk.length ≤ 4
  rw [← card_cycle_verts_eq_length G M.cycle]
  exact hcardCycle

/-- The three-cycle subcase of a two-vertex complementary bridge always
contains a wheel: the two attachment pairs overlap in one rim vertex, which
is the hub of a four-cycle through the two bridge vertices. -/
theorem MaxCycleCertificate.hasWheelWitness_of_bridge_two_cycle_three
    (M : MaxCycleCertificate G) (hno : ¬HasWheelWitness G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hBcard : (bridgeSet (G := G) M.cycle M.bridge).ncard = 2)
    (hlen : M.cycle.length (G := G) = 3) :
    HasWheelWitness G := by
  classical
  obtain ⟨D⟩ := M.exists_twoVertexBridgeData G hno hmin hBcard
  obtain ⟨T⟩ :=
    Erdos916.Cycle.triangleDisplay_of_length_eq_three G M.cycle hlen
  let U := M.cycle.verts (G := G)
  let NX := G.neighborFinset D.x ∩ U
  let NY := G.neighborFinset D.y ∩ U
  have hU : U.card = 3 := by
    change (M.cycle.verts (G := G)).card = 3
    rw [card_cycle_verts_eq_length G M.cycle]
    exact hlen
  have hNX : NX.card = 2 := by
    simpa only [NX, U] using D.card_cycle_neighbors_x
  have hNY : NY.card = 2 := by
    simpa only [NY, U] using D.card_cycle_neighbors_y
  obtain ⟨r, a, b, hrX, hrY, haX, hbY, hra, hrb, hab⟩ :=
    exists_common_and_distinct_of_two_pairs_cover_three
      U NX NY hU hNX hNY Finset.inter_subset_right
        Finset.inter_subset_right (by simpa only [U, NX, NY] using D.cover)
  have hrU : r ∈ U := Finset.inter_subset_right hrX
  have haU : a ∈ U := Finset.inter_subset_right haX
  have hbU : b ∈ U := Finset.inter_subset_right hbY
  have hxr : G.Adj D.x r := by
    simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hrX).1
  have hyr : G.Adj D.y r := by
    simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hrY).1
  have hxa : G.Adj D.x a := by
    simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp haX).1
  have hyb : G.Adj D.y b := by
    simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hbY).1
  have habAdj : G.Adj a b :=
    T.adj_of_mem G (by simpa only [U] using haU)
      (by simpa only [U] using hbU) hab
  have hxout : D.x ∉ M.cycle.vSet (G := G) :=
    mem_bridge_imp_not_mem_cycle (G := G) M.cycle M.bridge D.x_mem
  have hyout : D.y ∉ M.cycle.vSet (G := G) :=
    mem_bridge_imp_not_mem_cycle (G := G) M.cycle M.bridge D.y_mem
  have hx_ne (z : V) (hz : z ∈ U) : D.x ≠ z := by
    intro h
    apply hxout
    exact h.symm ▸ M.cycle.mem_vSet_iff.mpr (by simpa only [U] using hz)
  have hy_ne (z : V) (hz : z ∈ U) : D.y ≠ z := by
    intro h
    apply hyout
    exact h.symm ▸ M.cycle.mem_vSet_iff.mpr (by simpa only [U] using hz)
  exact hasWheelWitness_of_fourCycle_threeSpokes
    hxa habAdj hyb.symm D.adj.symm
    hxr.symm (T.adj_of_mem G (by simpa only [U] using hrU)
      (by simpa only [U] using hbU) hrb) hyr.symm
    (hx_ne b hbU) D.ne (hy_ne a haU).symm
    (hx_ne r hrU).symm hra hrb (hy_ne r hrU).symm

/-- The pointed form of the Thomassen--Toft theorem immediately implies the
unpointed vertex-two-connected reduction used by the density induction. -/
theorem vertexTwoConnectedReductionPrinciple_of_pointedCore
    (hcore : VertexTwoConnectedCorePrinciple.{u}) :
    VertexTwoConnectedReductionPrinciple.{u} := by
  intro W _ _ H _ hcard hconn hdelete hmin
  letI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  let x₀ : W := Classical.choice inferInstance
  have hdeg : MinDegreeThreeExcept H x₀ := by
    intro w _hw
    exact hmin w
  have hstruct : StructuralAlternative H x₀ :=
    @hcore W _ _ H _ x₀ (by omega) ⟨hconn, hdelete⟩ hdeg
  rcases hstruct with hW | ⟨R, _havoid⟩
  · exact Or.inl hW
  · exact Or.inr ⟨R⟩

/-- A pointwise local bridge-classification theorem is precisely the
universe-polymorphic proposition packaged as
`MaxCycleLocalReductionPrinciple`. -/
theorem maxCycleLocalReductionPrinciple_of_pointwise
    (hlocal : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj]
      (M : MaxCycleCertificate H),
        (∀ w : W, 3 ≤ H.degree w) →
        HasWheelWitness H ∨ Nonempty (K23Reduction H)) :
    MaxCycleLocalReductionPrinciple.{u} := by
  exact hlocal

/-- The local principle with the connectivity and finite-maximality data
which the Thomassen--Toft endblock surgeries actually use.  The chosen cycle
avoids `x₀`, its complement is represented by the certificate's unique
bridge, and no other cycle avoiding `x₀` has a larger rooted complement. -/
def MaximalTwoConnectedCycleLocalReductionPrinciple : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (x₀ : W) (M : MaxCycleCertificate H),
      VertexTwoConnected (G := H) →
      Nonseparating.IsAdmissibleCycle H ({x₀} : Set W) M.cycle →
      (∀ D : Cycle (G := H),
        Nonseparating.IsAdmissibleCycle H ({x₀} : Set W) D →
          Nonseparating.targetCard H D x₀ ≤
            Nonseparating.targetCard H M.cycle x₀) →
      (∀ w : W, 3 ≤ H.degree w) →
      HasWheelWitness H ∨ Nonempty (K23Reduction H)

/-- The maximal, vertex-two-connected local analysis is exactly sufficient
for the unpointed structural principle needed by the density induction. -/
theorem vertexTwoConnectedReductionPrinciple_of_maximalLocal
    (hlocal : MaximalTwoConnectedCycleLocalReductionPrinciple.{u}) :
    VertexTwoConnectedReductionPrinciple.{u} := by
  intro W _ _ H _ hcard hconn hdelete hmin
  letI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  let x₀ : W := Classical.choice inferInstance
  have h2 : VertexTwoConnected (G := H) :=
    vertexTwoConnected_of_induction_hypotheses H hconn hdelete
  obtain ⟨M, hM, hmax⟩ :=
    exists_maxCycleCertificate_of_pointed_hypotheses_maximal
      H (x₀ := x₀) (by omega) h2 (fun v _ => hmin v)
  exact hlocal W H x₀ M h2 hM hmax hmin

/-- The exact density-induction core follows from the local classification
of the unique complementary bridge of a Bondy--Vince maximum cycle. -/
theorem vertexTwoConnectedReductionPrinciple_of_localBridgeClassification
    (hlocal : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj]
      (M : MaxCycleCertificate H),
        (∀ w : W, 3 ≤ H.degree w) →
        HasWheelWitness H ∨ Nonempty (K23Reduction H)) :
    VertexTwoConnectedReductionPrinciple.{u} :=
  vertexTwoConnectedReductionPrinciple_of_maxCycleLocal
    (maxCycleLocalReductionPrinciple_of_pointwise hlocal)

end Erdos916
