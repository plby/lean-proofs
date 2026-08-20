/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreMaxCycleTree
import ErdosProblems.Erdos916.CoreTTLex

/-!
# Rerouting a maximum cycle through a bridge leaf

This file isolates the graph surgery common to the remaining tree-endblock
case.  A degree-three bridge leaf has exactly two rim neighbours.  Replacing
either rim arc between them by the two-edge path through the leaf gives an
ambient cycle; shortening it gives a chordless cycle supported inside the
chosen arc together with the leaf.
-/

namespace Erdos916

open SimpleGraph
open Erdos751.BV

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Connectedness of the unique complementary bridge is already enough for
the local N6 hub construction when two consecutive rim vertices share an
attachment.  A bridge path from that shared attachment to an attachment of
the next rim vertex is the outside path in
`hasWheelWitness_of_external_path_through`. -/
theorem MaxCycleCertificate.hasWheelWitness_of_shared_attachment_consecutive
    (M : MaxCycleCertificate G) {p z q a c : V}
    (hpC : p ∈ M.cycle.vSet (G := G))
    (hzC : z ∈ M.cycle.vSet (G := G))
    (hqC : q ∈ M.cycle.vSet (G := G))
    (hzp : G.Adj z p) (hzq : G.Adj z q)
    (hpa : G.Adj p a) (hza : G.Adj z a) (hcq : G.Adj c q)
    (haB : a ∈ bridgeSet G M.cycle M.bridge)
    (hcB : c ∈ bridgeSet G M.cycle M.bridge)
    (hpq : p ≠ q) (hzpne : z ≠ p) (hzqne : z ≠ q) :
    HasWheelWitness G := by
  classical
  let B : Set V := bridgeSet G M.cycle M.bridge
  let aB : B := ⟨a, by simpa only [B] using haB⟩
  let cB : B := ⟨c, by simpa only [B] using hcB⟩
  have hconn : (G.induce B).Connected := by
    simpa only [B] using M.bridge_connected G
  obtain ⟨Psub, hPsub⟩ := hconn.preconnected.exists_isPath aB cB
  let inc : G.induce B →g G :=
    (SimpleGraph.Embedding.induce (G := G) (s := B)).toHom
  let P : G.Walk a c := Psub.map inc
  have hP : P.IsPath := hPsub.map Subtype.val_injective
  have haP : a ∈ P.support := by
    exact P.start_mem_support
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
    exact mem_bridge_imp_not_mem_cycle
      (G := G) M.cycle M.bridge (by simpa only [B] using w.2)
  exact hasWheelWitness_of_external_path_through G M.cycle
    hpC hzC hqC hzp hzq hpa hza hcq hpq hzpne hzqne
    P hP haP hPout

/-- Two internally disjoint paths forming a cycle, together with three
displayed neighbours on their union, give a wheel witness. -/
theorem hasWheelWitness_of_path_append
    {u v k n₁ n₂ n₃ : V} (p : G.Walk u v) (q : G.Walk v u)
    (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : p.support.tail.Disjoint q.support.tail)
    (hlong : 1 < p.length ∨ 1 < q.length)
    (hkp : k ∉ p.support) (hkq : k ∉ q.support)
    (hkn₁ : G.Adj k n₁) (hkn₂ : G.Adj k n₂) (hkn₃ : G.Adj k n₃)
    (hn₁ : n₁ ∈ p.support ∨ n₁ ∈ q.support)
    (hn₂ : n₂ ∈ p.support ∨ n₂ ∈ q.support)
    (hn₃ : n₃ ∈ p.support ∨ n₃ ∈ q.support)
    (hn₁n₂ : n₁ ≠ n₂) (hn₁n₃ : n₁ ≠ n₃)
    (hn₂n₃ : n₂ ≠ n₃) :
    HasWheelWitness G := by
  let rim : G.Walk u u := p.append q
  have hrim : rim.IsCycle := hp.isCycle_append hq hdisj hlong
  have hkrim : k ∉ rim.support := by
    intro hk
    have : k ∈ p.support ∨ k ∈ q.support := by
      simpa only [rim, SimpleGraph.Walk.mem_support_append_iff] using hk
    exact this.elim hkp hkq
  refine ⟨u, rim, k, hrim, hkrim, ?_⟩
  have mem_rim {w : V} (hw : w ∈ p.support ∨ w ∈ q.support) :
      w ∈ rim.support := by
    simpa only [rim, SimpleGraph.Walk.mem_support_append_iff] using hw
  have hn₁' : n₁ ∈ G.neighborFinset k ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hkn₁, mem_rim hn₁⟩
  have hn₂' : n₂ ∈ G.neighborFinset k ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hkn₂, mem_rim hn₂⟩
  have hn₃' : n₃ ∈ G.neighborFinset k ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hkn₃, mem_rim hn₃⟩
  have hthree := Finset.two_lt_card_iff.mpr
    ⟨n₁, n₂, n₃, hn₁', hn₂', hn₃', hn₁n₂, hn₁n₃, hn₂n₃⟩
  omega

namespace Cycle

/-- On a cycle of length at least five, between any two distinct vertices one
of the two cyclic arcs omits two distinct internal vertices of the other arc.
The omitted vertices are explicitly kept away from both endpoints. -/
theorem exists_arc_avoiding_two_of_five_le
    (C : Cycle (G := G)) {u v : V}
    (huC : u ∈ C.vSet (G := G)) (hvC : v ∈ C.vSet (G := G))
    (huv : u ≠ v) (hlen : 5 ≤ C.length (G := G)) :
    ∃ A : G.Walk u v, A.IsPath ∧
      (∀ z, z ∈ A.support → z ∈ C.vSet (G := G)) ∧
      ∃ z₁ z₂ : V, z₁ ≠ z₂ ∧
        z₁ ∈ C.vSet (G := G) ∧ z₂ ∈ C.vSet (G := G) ∧
        z₁ ∉ A.support ∧ z₂ ∉ A.support ∧
        z₁ ≠ u ∧ z₁ ≠ v ∧ z₂ ≠ u ∧ z₂ ≠ v := by
  classical
  have huSupp : u ∈ C.walk.support :=
    (mem_cycle_vSet_iff_mem_support G C u).1 huC
  let r := C.walk.rotate u huSupp
  have hrCycle : r.IsCycle := C.isCycle.rotate huSupp
  have hvSupp : v ∈ r.support := by
    have hvOld : v ∈ C.walk.support :=
      (mem_cycle_vSet_iff_mem_support G C v).1 hvC
    have hvSub : v ∈ C.walk.toSubgraph.verts := by
      simpa only [SimpleGraph.Walk.mem_verts_toSubgraph] using hvOld
    have : v ∈ r.toSubgraph.verts := by
      simpa only [r, SimpleGraph.Walk.toSubgraph_rotate] using hvSub
    simpa only [SimpleGraph.Walk.mem_verts_toSubgraph] using this
  let A₁ := r.takeUntil v hvSupp
  let d := r.dropUntil v hvSupp
  let A₂ := d.reverse
  have hA₁ : A₁.IsPath := hrCycle.isPath_takeUntil hvSupp
  have hA₁ne : ¬A₁.Nil := by
    intro hn
    have hvA : v ∈ A₁.support := A₁.end_mem_support
    have hvu : v = u := by
      simpa [SimpleGraph.Walk.nil_iff_support_eq.mp hn] using hvA
    exact huv hvu.symm
  have hrDecomp : r = A₁.append d := by
    have h := SimpleGraph.Walk.take_spec (p := r) (h := hvSupp)
    simpa only [A₁, d] using h.symm
  have hdPath : d.IsPath := by
    have hc : (A₁.append d).IsCycle := by rw [← hrDecomp]; exact hrCycle
    exact SimpleGraph.Walk.IsCycle.isPath_of_append_right hA₁ne hc
  have hA₂ : A₂.IsPath := hdPath.reverse
  have hdne : ¬d.Nil := by
    intro hn
    have huD : u ∈ d.support := d.end_mem_support
    have huv' : u = v := by
      simpa [SimpleGraph.Walk.nil_iff_support_eq.mp hn] using huD
    exact huv huv'
  have hlenr : r.length = C.walk.length := by
    have hsum :
        (C.walk.takeUntil u huSupp).length +
            (C.walk.dropUntil u huSupp).length = C.walk.length := by
      have h := SimpleGraph.Walk.take_spec (p := C.walk) (h := huSupp)
      have hlen := congrArg (fun p => p.length) h
      simpa only [SimpleGraph.Walk.length_append] using hlen
    calc
      r.length = (C.walk.dropUntil u huSupp).length +
          (C.walk.takeUntil u huSupp).length := by
        simp [r, SimpleGraph.Walk.rotate]
      _ = C.walk.length := by omega
  have hlensum : A₁.length + d.length = r.length := by
    calc
      A₁.length + d.length = (A₁.append d).length := by simp
      _ = r.length := by rw [← hrDecomp]
  have hA₁pos : 0 < A₁.length :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mp hA₁ne
  have hdpos : 0 < d.length :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mp hdne
  have hlong : 3 ≤ A₁.length ∨ 3 ≤ d.length := by
    change 5 ≤ C.walk.length at hlen
    omega
  have hrToOld {z : V} (hz : z ∈ r.support) :
      z ∈ C.vSet (G := G) := by
    have hzSub : z ∈ r.toSubgraph.verts := by
      simpa only [SimpleGraph.Walk.mem_verts_toSubgraph] using hz
    have hzOldSub : z ∈ C.walk.toSubgraph.verts := by
      simpa only [r, SimpleGraph.Walk.toSubgraph_rotate] using hzSub
    have hzOld : z ∈ C.walk.support := by
      simpa only [SimpleGraph.Walk.mem_verts_toSubgraph] using hzOldSub
    exact (mem_cycle_vSet_iff_mem_support G C z).2 hzOld
  have hA₁cycle {z : V} (hz : z ∈ A₁.support) :
      z ∈ C.vSet (G := G) :=
    hrToOld (SimpleGraph.Walk.support_takeUntil_subset_support _ _ hz)
  have hdcycle {z : V} (hz : z ∈ d.support) :
      z ∈ C.vSet (G := G) :=
    hrToOld (SimpleGraph.Walk.support_dropUntil_subset_support _ _ hz)
  have hA₂cycle {z : V} (hz : z ∈ A₂.support) :
      z ∈ C.vSet (G := G) := by
    apply hdcycle
    simpa only [A₂, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
  have htail : (A₁.support.tail ++ d.support.tail).Nodup := by
    have h := hrCycle.2
    rw [hrDecomp] at h
    simpa only [SimpleGraph.Walk.tail_support_append] using h
  have hdis : List.Disjoint A₁.support.tail d.support.tail := by
    intro z hzA hzD
    exact ((List.nodup_append.mp htail).2.2 z hzA z hzD) rfl
  rcases hlong with hA₁long | hdlong
  · let z₁ := A₁.getVert 1
    let z₂ := A₁.getVert 2
    have hz₁A : z₁ ∈ A₁.support := A₁.getVert_mem_support 1
    have hz₂A : z₂ ∈ A₁.support := A₁.getVert_mem_support 2
    have hz₁u : z₁ ≠ u := by
      intro h
      have hi := hA₁.getVert_injOn
        (by exact (show 1 ≤ A₁.length by omega))
        (by exact Nat.zero_le A₁.length)
        (by simpa only [z₁, SimpleGraph.Walk.getVert_zero] using h)
      omega
    have hz₂u : z₂ ≠ u := by
      intro h
      have hi := hA₁.getVert_injOn
        (by exact (show 2 ≤ A₁.length by omega))
        (by exact Nat.zero_le A₁.length)
        (by simpa only [z₂, SimpleGraph.Walk.getVert_zero] using h)
      omega
    have hz₁v : z₁ ≠ v := by
      intro h
      have hi := hA₁.getVert_injOn
        (by exact (show 1 ≤ A₁.length by omega))
        (by exact le_rfl) (by
        simpa only [z₁, SimpleGraph.Walk.getVert_length] using h)
      omega
    have hz₂v : z₂ ≠ v := by
      intro h
      have hi := hA₁.getVert_injOn
        (by exact (show 2 ≤ A₁.length by omega))
        (by exact le_rfl) (by
        simpa only [z₂, SimpleGraph.Walk.getVert_length] using h)
      omega
    have hz₁₂ : z₁ ≠ z₂ := by
      intro h
      have hi := hA₁.getVert_injOn
        (by exact (show 1 ≤ A₁.length by omega))
        (by exact (show 2 ≤ A₁.length by omega)) h
      omega
    have hz₁tail : z₁ ∈ A₁.support.tail := by
      have := (SimpleGraph.Walk.mem_support_iff (p := A₁) (w := z₁)).1 hz₁A
      exact this.resolve_left hz₁u
    have hz₂tail : z₂ ∈ A₁.support.tail := by
      have := (SimpleGraph.Walk.mem_support_iff (p := A₁) (w := z₂)).1 hz₂A
      exact this.resolve_left hz₂u
    have hz₁A₂ : z₁ ∉ A₂.support := by
      intro hz
      have hzD : z₁ ∈ d.support := by
        simpa only [A₂, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
      have hzDtail : z₁ ∈ d.support.tail := by
        have := (SimpleGraph.Walk.mem_support_iff (p := d) (w := z₁)).1 hzD
        exact this.resolve_left hz₁v
      exact (List.disjoint_left.mp hdis) hz₁tail hzDtail
    have hz₂A₂ : z₂ ∉ A₂.support := by
      intro hz
      have hzD : z₂ ∈ d.support := by
        simpa only [A₂, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
      have hzDtail : z₂ ∈ d.support.tail := by
        have := (SimpleGraph.Walk.mem_support_iff (p := d) (w := z₂)).1 hzD
        exact this.resolve_left hz₂v
      exact (List.disjoint_left.mp hdis) hz₂tail hzDtail
    exact ⟨A₂, hA₂, fun _ hz => hA₂cycle hz,
      z₁, z₂, hz₁₂, hA₁cycle hz₁A, hA₁cycle hz₂A,
      hz₁A₂, hz₂A₂, hz₁u, hz₁v, hz₂u, hz₂v⟩
  · let z₁ := d.getVert 1
    let z₂ := d.getVert 2
    have hz₁D : z₁ ∈ d.support := d.getVert_mem_support 1
    have hz₂D : z₂ ∈ d.support := d.getVert_mem_support 2
    have hz₁v : z₁ ≠ v := by
      intro h
      have hi := hdPath.getVert_injOn
        (by exact (show 1 ≤ d.length by omega))
        (by exact Nat.zero_le d.length)
        (by simpa only [z₁, SimpleGraph.Walk.getVert_zero] using h)
      omega
    have hz₂v : z₂ ≠ v := by
      intro h
      have hi := hdPath.getVert_injOn
        (by exact (show 2 ≤ d.length by omega))
        (by exact Nat.zero_le d.length)
        (by simpa only [z₂, SimpleGraph.Walk.getVert_zero] using h)
      omega
    have hz₁u : z₁ ≠ u := by
      intro h
      have hi := hdPath.getVert_injOn
        (by exact (show 1 ≤ d.length by omega))
        (by exact le_rfl) (by
        simpa only [z₁, SimpleGraph.Walk.getVert_length] using h)
      omega
    have hz₂u : z₂ ≠ u := by
      intro h
      have hi := hdPath.getVert_injOn
        (by exact (show 2 ≤ d.length by omega))
        (by exact le_rfl) (by
        simpa only [z₂, SimpleGraph.Walk.getVert_length] using h)
      omega
    have hz₁₂ : z₁ ≠ z₂ := by
      intro h
      have hi := hdPath.getVert_injOn
        (by exact (show 1 ≤ d.length by omega))
        (by exact (show 2 ≤ d.length by omega)) h
      omega
    have hz₁Dtail : z₁ ∈ d.support.tail := by
      have := (SimpleGraph.Walk.mem_support_iff (p := d) (w := z₁)).1 hz₁D
      exact this.resolve_left hz₁v
    have hz₂Dtail : z₂ ∈ d.support.tail := by
      have := (SimpleGraph.Walk.mem_support_iff (p := d) (w := z₂)).1 hz₂D
      exact this.resolve_left hz₂v
    have hz₁A₁ : z₁ ∉ A₁.support := by
      intro hz
      have hzTail : z₁ ∈ A₁.support.tail := by
        have := (SimpleGraph.Walk.mem_support_iff (p := A₁) (w := z₁)).1 hz
        exact this.resolve_left hz₁u
      exact (List.disjoint_left.mp hdis) hzTail hz₁Dtail
    have hz₂A₁ : z₂ ∉ A₁.support := by
      intro hz
      have hzTail : z₂ ∈ A₁.support.tail := by
        have := (SimpleGraph.Walk.mem_support_iff (p := A₁) (w := z₂)).1 hz
        exact this.resolve_left hz₂u
      exact (List.disjoint_left.mp hdis) hzTail hz₂Dtail
    exact ⟨A₁, hA₁, fun _ hz => hA₁cycle hz,
      z₁, z₂, hz₁₂, hdcycle hz₁D, hdcycle hz₂D,
      hz₁A₁, hz₂A₁, hz₁u, hz₁v, hz₂u, hz₂v⟩

end Cycle

/-- The two named rim neighbours of a bridge leaf. -/
structure LeafRimPair {M : MaxCycleCertificate G}
    (L : BridgeLeafData G M) where
  left : V
  right : V
  ne : left ≠ right
  left_mem : left ∈ M.cycle.vSet (G := G)
  right_mem : right ∈ M.cycle.vSet (G := G)
  adj_left : G.Adj L.vertex left
  adj_right : G.Adj L.vertex right
  neighbors_eq :
    G.neighborFinset L.vertex ∩ M.cycle.verts (G := G) = {left, right}

namespace BridgeLeafData

variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {M : MaxCycleCertificate G}

/-- Enumerate the two rim neighbours supplied by `cycle_neighbors_card`. -/
theorem exists_leafRimPair (L : BridgeLeafData G M) :
    Nonempty (LeafRimPair G L) := by
  classical
  let N := G.neighborFinset L.vertex ∩ M.cycle.verts (G := G)
  have hNcard : N.card = 2 := by simpa only [N] using L.cycle_neighbors_card
  obtain ⟨u, v, huv, hN⟩ := Finset.card_eq_two.mp hNcard
  have huN : u ∈ N := by rw [hN]; simp
  have hvN : v ∈ N := by rw [hN]; simp
  refine ⟨{
    left := u
    right := v
    ne := huv
    left_mem := (M.cycle.mem_vSet_iff (G := G)).2 (Finset.mem_inter.mp huN).2
    right_mem := (M.cycle.mem_vSet_iff (G := G)).2 (Finset.mem_inter.mp hvN).2
    adj_left := by
      simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp huN).1
    adj_right := by
      simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hvN).1
    neighbors_eq := by simpa only [N] using hN }⟩

end BridgeLeafData

namespace TwoBridgeLeafData

variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {M : MaxCycleCertificate G}

/-- Select one of two distinct bridge leaves away from a prescribed root.
This local spelling avoids depending on any later convenience API. -/
theorem exists_leaf_avoiding (D : TwoBridgeLeafData G M) (x : V) :
    ∃ L : BridgeLeafData G M, L.vertex ≠ x := by
  by_cases hleft : D.left.vertex ≠ x
  · exact ⟨D.left, hleft⟩
  · have hleftEq : D.left.vertex = x := Classical.not_not.mp hleft
    refine ⟨D.right, ?_⟩
    intro hright
    exact D.ne (hleftEq.trans hright.symm)

end TwoBridgeLeafData

namespace LeafRimPair

variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {M : MaxCycleCertificate G} {L : BridgeLeafData G M}

/-- The bridge leaf is outside every arc of the selected rim. -/
theorem vertex_not_mem_arc (R : LeafRimPair G L)
    (A : G.Walk R.left R.right)
    (hAcycle : ∀ z, z ∈ A.support → z ∈ M.cycle.vSet (G := G)) :
    L.vertex ∉ A.support := by
  intro hL
  exact (mem_bridge_imp_not_mem_cycle
    (G := G) M.cycle M.bridge L.vertex_mem) (hAcycle L.vertex hL)

/-- The two-edge leaf path between the named rim neighbours. -/
def throughLeaf (R : LeafRimPair G L) : G.Walk R.left R.right :=
  .cons R.adj_left.symm (.cons R.adj_right .nil)

theorem throughLeaf_isPath (R : LeafRimPair G L) :
    R.throughLeaf.IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  simp [throughLeaf, R.ne, R.ne.symm, R.adj_left.ne,
    R.adj_left.ne.symm, R.adj_right.ne, R.adj_right.ne.symm]

theorem throughLeaf_support (R : LeafRimPair G L) :
    R.throughLeaf.support = [R.left, L.vertex, R.right] := by
  simp [throughLeaf]

/-- Splice the leaf path with the reverse of either simple rim arc. -/
theorem isCycle_throughLeaf_append_reverse
    (R : LeafRimPair G L) (A : G.Walk R.left R.right)
    (hA : A.IsPath)
    (hAcycle : ∀ z, z ∈ A.support → z ∈ M.cycle.vSet (G := G)) :
    (R.throughLeaf.append A.reverse).IsCycle := by
  have hP : R.throughLeaf.IsPath := R.throughLeaf_isPath
  have hAr : A.reverse.IsPath := hA.reverse
  have hdis : List.Disjoint R.throughLeaf.support.tail A.reverse.support.tail := by
    rw [List.disjoint_left]
    intro z hzP hzA
    have hzP' : z = L.vertex ∨ z = R.right := by
      simpa [R.throughLeaf_support] using hzP
    have hzAr : z ∈ A.support := by
      have : z ∈ A.reverse.support := List.mem_of_mem_tail hzA
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using this
    rcases hzP' with rfl | rfl
    · exact R.vertex_not_mem_arc A hAcycle hzAr
    · have hnodup := hAr.support_nodup
      rw [A.reverse.support_eq_cons] at hnodup
      exact (List.nodup_cons.mp hnodup).1 hzA
  exact hP.isCycle_append hAr hdis (Or.inl (by
    simp [throughLeaf]))

/-- Chordless form of the leaf reroute.  The extracted cycle uses only the
leaf and vertices of the selected rim arc. -/
theorem exists_chordless_cycle_vSet_subset_leaf_union_arc
    (R : LeafRimPair G L) (A : G.Walk R.left R.right)
    (hA : A.IsPath)
    (hAcycle : ∀ z, z ∈ A.support → z ∈ M.cycle.vSet (G := G)) :
    ∃ D : Cycle (G := G), D.IsChordless (G := G) ∧
      D.vSet (G := G) ⊆
        ({L.vertex} : Set V) ∪ {z : V | z ∈ A.support} := by
  let Q := R.throughLeaf.append A.reverse
  have hQ : Q.IsCycle := R.isCycle_throughLeaf_append_reverse A hA hAcycle
  have hsupport : ∀ z : V, z ∈ Q.support →
      z ∈ ({L.vertex} : Set V) ∪ {w : V | w ∈ A.support} := by
    intro z hz
    have hz' : z ∈ R.throughLeaf.support ∨ z ∈ A.reverse.support := by
      simpa only [Q, SimpleGraph.Walk.mem_support_append_iff] using hz
    rcases hz' with hzP | hzA
    · have hzP' : z = R.left ∨ z = L.vertex ∨ z = R.right := by
        simpa [R.throughLeaf_support] using hzP
      rcases hzP' with rfl | rfl | rfl
      · exact Or.inr A.start_mem_support
      · exact Or.inl (Set.mem_singleton L.vertex)
      · exact Or.inr A.end_mem_support
    · exact Or.inr (by
        change z ∈ A.support
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzA)
  exact exists_chordless_cycle_vSet_subset_of_isCycle G Q hQ
    (({L.vertex} : Set V) ∪ {z : V | z ∈ A.support}) hsupport

/-- A leaf reroute avoids any prescribed root outside both the leaf and the
chosen arc. -/
theorem exists_admissible_leaf_reroute
    (R : LeafRimPair G L) (A : G.Walk R.left R.right)
    (hA : A.IsPath)
    (hAcycle : ∀ z, z ∈ A.support → z ∈ M.cycle.vSet (G := G))
    {x : V} (hxL : x ≠ L.vertex)
    (hxA : x ∉ A.support) :
    ∃ D : Cycle (G := G),
      Nonseparating.IsAdmissibleCycle G ({x} : Set V) D ∧
      D.vSet (G := G) ⊆
        ({L.vertex} : Set V) ∪ {z : V | z ∈ A.support} := by
  obtain ⟨D, hDch, hDsub⟩ :=
    R.exists_chordless_cycle_vSet_subset_leaf_union_arc A hA hAcycle
  refine ⟨D, ⟨hDch, Set.disjoint_left.mpr ?_⟩, hDsub⟩
  intro z hzD hzx
  have hzx' : z = x := Set.mem_singleton_iff.mp hzx
  subst z
  rcases hDsub hzD with hxLeaf | hxArc
  · exact hxL (Set.mem_singleton_iff.mp hxLeaf)
  · exact hxA hxArc

/-- If the two rim attachments of a bridge leaf are adjacent, the shared
attachment hub construction closes immediately.  Hence in the no-wheel
four-cycle terminal they must be the opposite pair. -/
theorem hasWheelWitness_of_adj
    (R : LeafRimPair G L) (hadj : G.Adj R.left R.right) :
    HasWheelWitness G := by
  classical
  let N := G.neighborFinset R.right ∩ M.cycle.verts (G := G)
  have hNcard : N.card = 2 := by
    simpa only [N] using card_neighbors_on_chordless_cycle_eq_two
      G M.cycle M.chordless R.right_mem
  have hleftN : R.left ∈ N := by
    exact Finset.mem_inter.mpr ⟨by simpa using hadj.symm,
      (M.cycle.mem_vSet_iff (G := G)).1 R.left_mem⟩
  have herase : (N.erase R.left).card = 1 := by
    rw [Finset.card_erase_of_mem hleftN, hNcard]
  obtain ⟨q, hqerase⟩ := Finset.card_pos.mp (by omega : 0 < (N.erase R.left).card)
  have hq := Finset.mem_erase.mp hqerase
  have hqAdj : G.Adj R.right q := by
    have hqN := Finset.mem_inter.mp hq.2
    simpa only [SimpleGraph.mem_neighborFinset] using hqN.1
  have hqC : q ∈ M.cycle.vSet (G := G) :=
    (M.cycle.mem_vSet_iff (G := G)).2 (Finset.mem_inter.mp hq.2).2
  obtain ⟨c, hcB, hqc⟩ := M.exists_adj_bridge G hqC
  exact M.hasWheelWitness_of_shared_attachment_consecutive G
    R.left_mem R.right_mem hqC hadj.symm hqAdj
    R.adj_left.symm R.adj_right.symm hqc.symm
    L.vertex_mem hcB hq.1.symm R.ne.symm hqAdj.ne

/-- A four-cycle displayed relative to the two (necessarily opposite)
attachments of a bridge leaf.  The two `middle` vertices are the internal
vertices of the two length-two rim arcs between the attachments. -/
structure OppositeFourRimData
    (R : LeafRimPair G L) where
  middle₁ : V
  middle₂ : V
  middle_ne : middle₁ ≠ middle₂
  left_ne_middle₁ : R.left ≠ middle₁
  left_ne_middle₂ : R.left ≠ middle₂
  right_ne_middle₁ : R.right ≠ middle₁
  right_ne_middle₂ : R.right ≠ middle₂
  middle₁_mem : middle₁ ∈ M.cycle.vSet (G := G)
  middle₂_mem : middle₂ ∈ M.cycle.vSet (G := G)
  adj_left_middle₁ : G.Adj R.left middle₁
  adj_middle₁_right : G.Adj middle₁ R.right
  adj_left_middle₂ : G.Adj R.left middle₂
  adj_middle₂_right : G.Adj middle₂ R.right
  verts_eq :
    M.cycle.verts (G := G) =
      {R.left, R.right, middle₁, middle₂}

/-- On a chordless four-cycle a nonadjacent pair is an opposite pair, so
the other two vertices give the two length-two arcs between it. -/
theorem exists_oppositeFourRimData
    (R : LeafRimPair G L)
    (hlen : M.cycle.length (G := G) = 4)
    (hnotAdj : ¬G.Adj R.left R.right) :
    Nonempty (OppositeFourRimData R) := by
  classical
  obtain ⟨D⟩ :=
    Erdos916.Cycle.fourCycleDisplay_of_length_eq_four G M.cycle hlen
  have hl : R.left = D.r0 ∨ R.left = D.r1 ∨
      R.left = D.r2 ∨ R.left = D.r3 := by
    have h := (M.cycle.mem_vSet_iff (G := G)).1 R.left_mem
    rw [D.verts_eq] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hr : R.right = D.r0 ∨ R.right = D.r1 ∨
      R.right = D.r2 ∨ R.right = D.r3 := by
    have h := (M.cycle.mem_vSet_iff (G := G)).1 R.right_mem
    rw [D.verts_eq] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  rcases hl with hl | hl | hl | hl <;>
      rcases hr with hr | hr | hr | hr
  · exact (R.ne (hl.trans hr.symm)).elim
  · exact (hnotAdj (by simpa only [hl, hr] using D.adj01)).elim
  · refine ⟨{
      middle₁ := D.r1
      middle₂ := D.r3
      middle_ne := D.ne13
      left_ne_middle₁ := by simpa only [hl] using D.ne01
      left_ne_middle₂ := by simpa only [hl] using D.ne03
      right_ne_middle₁ := by simpa only [hr] using D.ne12.symm
      right_ne_middle₂ := by simpa only [hr] using D.ne23
      middle₁_mem := (M.cycle.mem_vSet_iff (G := G)).2 (by
        rw [D.verts_eq]; simp)
      middle₂_mem := (M.cycle.mem_vSet_iff (G := G)).2 (by
        rw [D.verts_eq]; simp)
      adj_left_middle₁ := by simpa only [hl] using D.adj01
      adj_middle₁_right := by simpa only [hr] using D.adj12
      adj_left_middle₂ := by simpa only [hl] using D.adj30.symm
      adj_middle₂_right := by simpa only [hr] using D.adj23.symm
      verts_eq := by
        ext z
        rw [D.verts_eq]
        simp only [hl, hr, Finset.mem_insert, Finset.mem_singleton]
        tauto }⟩
  · exact (hnotAdj (by simpa only [hl, hr] using D.adj30.symm)).elim
  · exact (hnotAdj (by simpa only [hl, hr] using D.adj01.symm)).elim
  · exact (R.ne (hl.trans hr.symm)).elim
  · exact (hnotAdj (by simpa only [hl, hr] using D.adj12)).elim
  · refine ⟨{
      middle₁ := D.r0
      middle₂ := D.r2
      middle_ne := D.ne02
      left_ne_middle₁ := by simpa only [hl] using D.ne01.symm
      left_ne_middle₂ := by simpa only [hl] using D.ne12
      right_ne_middle₁ := by simpa only [hr] using D.ne03.symm
      right_ne_middle₂ := by simpa only [hr] using D.ne23.symm
      middle₁_mem := (M.cycle.mem_vSet_iff (G := G)).2 (by
        rw [D.verts_eq]; simp)
      middle₂_mem := (M.cycle.mem_vSet_iff (G := G)).2 (by
        rw [D.verts_eq]; simp)
      adj_left_middle₁ := by simpa only [hl] using D.adj01.symm
      adj_middle₁_right := by simpa only [hr] using D.adj30.symm
      adj_left_middle₂ := by simpa only [hl] using D.adj12
      adj_middle₂_right := by simpa only [hr] using D.adj23
      verts_eq := by
        ext z
        rw [D.verts_eq]
        simp only [hl, hr, Finset.mem_insert, Finset.mem_singleton]
        tauto }⟩
  · refine ⟨{
      middle₁ := D.r1
      middle₂ := D.r3
      middle_ne := D.ne13
      left_ne_middle₁ := by simpa only [hl] using D.ne12.symm
      left_ne_middle₂ := by simpa only [hl] using D.ne23
      right_ne_middle₁ := by simpa only [hr] using D.ne01
      right_ne_middle₂ := by simpa only [hr] using D.ne03
      middle₁_mem := (M.cycle.mem_vSet_iff (G := G)).2 (by
        rw [D.verts_eq]; simp)
      middle₂_mem := (M.cycle.mem_vSet_iff (G := G)).2 (by
        rw [D.verts_eq]; simp)
      adj_left_middle₁ := by simpa only [hl] using D.adj12.symm
      adj_middle₁_right := by simpa only [hr] using D.adj01.symm
      adj_left_middle₂ := by simpa only [hl] using D.adj23
      adj_middle₂_right := by simpa only [hr] using D.adj30
      verts_eq := by
        ext z
        rw [D.verts_eq]
        simp only [hl, hr, Finset.mem_insert, Finset.mem_singleton]
        tauto }⟩
  · exact (hnotAdj (by simpa only [hl, hr] using D.adj12.symm)).elim
  · exact (R.ne (hl.trans hr.symm)).elim
  · exact (hnotAdj (by simpa only [hl, hr] using D.adj23)).elim
  · exact (hnotAdj (by simpa only [hl, hr] using D.adj30)).elim
  · refine ⟨{
      middle₁ := D.r0
      middle₂ := D.r2
      middle_ne := D.ne02
      left_ne_middle₁ := by simpa only [hl] using D.ne03.symm
      left_ne_middle₂ := by simpa only [hl] using D.ne23.symm
      right_ne_middle₁ := by simpa only [hr] using D.ne01.symm
      right_ne_middle₂ := by simpa only [hr] using D.ne12
      middle₁_mem := (M.cycle.mem_vSet_iff (G := G)).2 (by
        rw [D.verts_eq]; simp)
      middle₂_mem := (M.cycle.mem_vSet_iff (G := G)).2 (by
        rw [D.verts_eq]; simp)
      adj_left_middle₁ := by simpa only [hl] using D.adj30
      adj_middle₁_right := by simpa only [hr] using D.adj01
      adj_left_middle₂ := by simpa only [hl] using D.adj23.symm
      adj_middle₂_right := by simpa only [hr] using D.adj12.symm
      verts_eq := by
        ext z
        rw [D.verts_eq]
        simp only [hl, hr, Finset.mem_insert, Finset.mem_singleton]
        tauto }⟩
  · exact (hnotAdj (by simpa only [hl, hr] using D.adj23.symm)).elim
  · exact (R.ne (hl.trans hr.symm)).elim

/-- A displayed internal rim vertex different from both attachments is not
adjacent to the bridge leaf: the leaf has exactly the two named rim
neighbours. -/
theorem not_adj_vertex_of_cycle_mem
    (R : LeafRimPair G L) {m : V}
    (hmC : m ∈ M.cycle.vSet (G := G))
    (hml : m ≠ R.left) (hmr : m ≠ R.right) :
    ¬G.Adj L.vertex m := by
  intro hLm
  have hmN : m ∈
      G.neighborFinset L.vertex ∩ M.cycle.verts (G := G) :=
    Finset.mem_inter.mpr ⟨by simpa only [SimpleGraph.mem_neighborFinset] using hLm,
      (M.cycle.mem_vSet_iff (G := G)).1 hmC⟩
  rw [R.neighbors_eq] at hmN
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmN
  exact hmN.elim hml hmr

/-- The literal length-two old-rim arc used by a leaf exchange. -/
def twoEdgeArc (R : LeafRimPair G L) {m : V}
    (hlm : G.Adj R.left m) (hmr : G.Adj m R.right) :
    G.Walk R.left R.right :=
  .cons hlm (.cons hmr .nil)

theorem twoEdgeArc_isPath
    (R : LeafRimPair G L) {m : V}
    (hlm : G.Adj R.left m) (hmr : G.Adj m R.right) :
    (R.twoEdgeArc hlm hmr).IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  simp [twoEdgeArc, R.ne, R.ne.symm, hlm.ne, hlm.ne.symm,
    hmr.ne, hmr.ne.symm]

/-- The exact four-cycle obtained by replacing a two-edge rim arc by the
two-edge path through the bridge leaf. -/
def exactRerouteCycle
    (R : LeafRimPair G L) {m : V}
    (hlm : G.Adj R.left m) (hmr : G.Adj m R.right)
    (hmC : m ∈ M.cycle.vSet (G := G)) :
    Cycle (G := G) := by
  let A := R.twoEdgeArc hlm hmr
  let Q := R.throughLeaf.append A.reverse
  have hA : A.IsPath := R.twoEdgeArc_isPath hlm hmr
  have hAcycle : ∀ z, z ∈ A.support →
      z ∈ M.cycle.vSet (G := G) := by
    intro z hz
    have hz' : z = R.left ∨ z = m ∨ z = R.right := by
      simpa only [A, twoEdgeArc, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] using hz
    rcases hz' with rfl | rfl | rfl
    · exact R.left_mem
    · exact hmC
    · exact R.right_mem
  have hQ : Q.IsCycle := by
    simpa only [Q] using R.isCycle_throughLeaf_append_reverse A hA hAcycle
  exact
    { base := R.left
      walk := Q
      isCycle := hQ
      len_ge_three := hQ.three_le_length }

@[simp] theorem exactRerouteCycle_support
    (R : LeafRimPair G L) {m : V}
    (hlm : G.Adj R.left m) (hmr : G.Adj m R.right)
    (hmC : m ∈ M.cycle.vSet (G := G)) :
    (R.exactRerouteCycle hlm hmr hmC).walk.support =
      [R.left, L.vertex, R.right, m, R.left] := by
  simp [exactRerouteCycle, twoEdgeArc, throughLeaf]

theorem exactRerouteCycle_verts
    (R : LeafRimPair G L) {m : V}
    (hlm : G.Adj R.left m) (hmr : G.Adj m R.right)
    (hmC : m ∈ M.cycle.vSet (G := G)) :
    (R.exactRerouteCycle hlm hmr hmC).verts (G := G) =
      {R.left, L.vertex, R.right, m} := by
  ext z
  simp [Cycle.verts, R.exactRerouteCycle_support hlm hmr hmC,
    or_left_comm, or_comm]

theorem exactRerouteCycle_vSet
    (R : LeafRimPair G L) {m : V}
    (hlm : G.Adj R.left m) (hmr : G.Adj m R.right)
    (hmC : m ∈ M.cycle.vSet (G := G)) :
    (R.exactRerouteCycle hlm hmr hmC).vSet (G := G) =
      ({R.left, L.vertex, R.right, m} : Finset V) := by
  exact congrArg (fun s : Finset V => (s : Set V))
    (R.exactRerouteCycle_verts hlm hmr hmC)

/-- There are no possible chords in the exact leaf reroute: the two missing
pairs are the nonadjacent old attachments and the leaf with the omitted
internal rim vertex. -/
theorem exactRerouteCycle_isChordless
    (R : LeafRimPair G L) {m : V}
    (hlm : G.Adj R.left m) (hmr : G.Adj m R.right)
    (hmC : m ∈ M.cycle.vSet (G := G))
    (hml : m ≠ R.left) (hmr_ne : m ≠ R.right)
    (hnotAdj : ¬G.Adj R.left R.right) :
    (R.exactRerouteCycle hlm hmr hmC).IsChordless (G := G) := by
  unfold Cycle.IsChordless Cycle.IsChord
  rintro ⟨u, v, hu, hv, huv, hnotSub⟩
  have hLm : ¬G.Adj L.vertex m :=
    R.not_adj_vertex_of_cycle_mem hmC hml hmr_ne
  have hu' : u = R.left ∨ u = L.vertex ∨ u = R.right ∨ u = m := by
    rw [R.exactRerouteCycle_vSet hlm hmr hmC] at hu
    simpa only [Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] using hu
  have hv' : v = R.left ∨ v = L.vertex ∨ v = R.right ∨ v = m := by
    rw [R.exactRerouteCycle_vSet hlm hmr hmC] at hv
    simpa only [Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] using hv
  have hleftLeaf :
      ((R.exactRerouteCycle hlm hmr hmC).toSubgraph (G := G)).Adj
        R.left L.vertex := by
    change (R.exactRerouteCycle hlm hmr hmC).walk.toSubgraph.Adj
      R.left L.vertex
    have h := (R.exactRerouteCycle hlm hmr hmC).walk.toSubgraph_adj_getVert
      (i := 0) (by simp [exactRerouteCycle, twoEdgeArc, throughLeaf])
    simpa [exactRerouteCycle, twoEdgeArc, throughLeaf] using h
  have hLeafRight :
      ((R.exactRerouteCycle hlm hmr hmC).toSubgraph (G := G)).Adj
        L.vertex R.right := by
    change (R.exactRerouteCycle hlm hmr hmC).walk.toSubgraph.Adj
      L.vertex R.right
    have h := (R.exactRerouteCycle hlm hmr hmC).walk.toSubgraph_adj_getVert
      (i := 1) (by simp [exactRerouteCycle, twoEdgeArc, throughLeaf])
    simpa [exactRerouteCycle, twoEdgeArc, throughLeaf] using h
  have hRightMiddle :
      ((R.exactRerouteCycle hlm hmr hmC).toSubgraph (G := G)).Adj
        R.right m := by
    change (R.exactRerouteCycle hlm hmr hmC).walk.toSubgraph.Adj
      R.right m
    have h := (R.exactRerouteCycle hlm hmr hmC).walk.toSubgraph_adj_getVert
      (i := 2) (by simp [exactRerouteCycle, twoEdgeArc, throughLeaf])
    simpa [exactRerouteCycle, twoEdgeArc, throughLeaf] using h
  have hMiddleLeft :
      ((R.exactRerouteCycle hlm hmr hmC).toSubgraph (G := G)).Adj
        m R.left := by
    change (R.exactRerouteCycle hlm hmr hmC).walk.toSubgraph.Adj
      m R.left
    have h := (R.exactRerouteCycle hlm hmr hmC).walk.toSubgraph_adj_getVert
      (i := 3) (by simp [exactRerouteCycle, twoEdgeArc, throughLeaf])
    simpa [exactRerouteCycle, twoEdgeArc, throughLeaf] using h
  rcases hu' with rfl | rfl | rfl | rfl <;>
      rcases hv' with rfl | rfl | rfl | rfl
  · exact G.loopless.irrefl R.left huv
  · exact hnotSub hleftLeaf
  · exact hnotAdj huv
  · exact hnotSub hMiddleLeft.symm
  · exact hnotSub hleftLeaf.symm
  · exact G.loopless.irrefl L.vertex huv
  · exact hnotSub hLeafRight
  · exact hLm huv
  · exact hnotAdj huv.symm
  · exact hnotSub hLeafRight.symm
  · exact G.loopless.irrefl R.right huv
  · exact hnotSub hRightMiddle
  · exact hnotSub hMiddleLeft
  · exact hLm huv.symm
  · exact hnotSub hRightMiddle.symm
  · exact G.loopless.irrefl _ huv

end LeafRimPair

namespace LeafRimPair.OppositeFourRimData

variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {M : MaxCycleCertificate G} {L : BridgeLeafData G M}
variable {R : LeafRimPair G L}

def reroute₁ (O : OppositeFourRimData R) : Cycle (G := G) :=
  R.exactRerouteCycle O.adj_left_middle₁ O.adj_middle₁_right
    O.middle₁_mem

def reroute₂ (O : OppositeFourRimData R) : Cycle (G := G) :=
  R.exactRerouteCycle O.adj_left_middle₂ O.adj_middle₂_right
    O.middle₂_mem

theorem reroute₁_vSet (O : OppositeFourRimData R) :
    O.reroute₁.vSet (G := G) =
      ({R.left, L.vertex, R.right, O.middle₁} : Finset V) := by
  exact R.exactRerouteCycle_vSet _ _ _

theorem reroute₂_vSet (O : OppositeFourRimData R) :
    O.reroute₂.vSet (G := G) =
      ({R.left, L.vertex, R.right, O.middle₂} : Finset V) := by
  exact R.exactRerouteCycle_vSet _ _ _

theorem reroute₁_isChordless (O : OppositeFourRimData R)
    (hnotAdj : ¬G.Adj R.left R.right) :
    O.reroute₁.IsChordless (G := G) := by
  exact R.exactRerouteCycle_isChordless _ _ _
    O.left_ne_middle₁.symm O.right_ne_middle₁.symm hnotAdj

theorem reroute₂_isChordless (O : OppositeFourRimData R)
    (hnotAdj : ¬G.Adj R.left R.right) :
    O.reroute₂.IsChordless (G := G) := by
  exact R.exactRerouteCycle_isChordless _ _ _
    O.left_ne_middle₂.symm O.right_ne_middle₂.symm hnotAdj

/-- Exact carrier identity for either C4 leaf reroute.  Deleting the leaf
from the old bridge and inserting the omitted middle vertex gives precisely
the complement of the new four-cycle. -/
theorem reroute₁_compl_eq (O : OppositeFourRimData R) :
    (O.reroute₁.vSet (G := G))ᶜ =
      (bridgeSet G M.cycle M.bridge \ {L.vertex}) ∪ {O.middle₂} := by
  ext z
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff,
    Set.mem_singleton_iff]
  have hLout : L.vertex ∉ M.cycle.vSet (G := G) :=
    (M.mem_bridge_iff_not_mem_cycle G L.vertex).1 L.vertex_mem
  constructor
  · intro hz
    by_cases hzC : z ∈ M.cycle.vSet (G := G)
    · have hzOld := (M.cycle.mem_vSet_iff (G := G)).1 hzC
      rw [O.verts_eq] at hzOld
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzOld
      rcases hzOld with rfl | rfl | rfl | rfl
      · exact (hz (by rw [O.reroute₁_vSet]; simp)).elim
      · exact (hz (by rw [O.reroute₁_vSet]; simp)).elim
      · exact (hz (by rw [O.reroute₁_vSet]; simp)).elim
      · exact Or.inr rfl
    · refine Or.inl ⟨(M.mem_bridge_iff_not_mem_cycle G z).2 hzC, ?_⟩
      intro hzL
      subst z
      exact hz (by rw [O.reroute₁_vSet]; simp)
  · intro hz
    rcases hz with ⟨hzB, hzL⟩ | rfl
    · have hzC : z ∉ M.cycle.vSet (G := G) :=
        (M.mem_bridge_iff_not_mem_cycle G z).1 hzB
      intro hzNew
      rw [O.reroute₁_vSet] at hzNew
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hzNew
      rcases hzNew with rfl | rfl | rfl | rfl
      · exact hzC R.left_mem
      · exact hzL rfl
      · exact hzC R.right_mem
      · exact hzC O.middle₁_mem
    · intro hm₂
      rw [O.reroute₁_vSet] at hm₂
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hm₂
      rcases hm₂ with hm₂l | hm₂L | hm₂r | hm₂m₁
      · exact O.left_ne_middle₂ hm₂l.symm
      · exact hLout (hm₂L ▸ O.middle₂_mem)
      · exact O.right_ne_middle₂ hm₂r.symm
      · exact O.middle_ne hm₂m₁.symm

theorem reroute₂_compl_eq (O : OppositeFourRimData R) :
    (O.reroute₂.vSet (G := G))ᶜ =
      (bridgeSet G M.cycle M.bridge \ {L.vertex}) ∪ {O.middle₁} := by
  ext z
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff,
    Set.mem_singleton_iff]
  have hLout : L.vertex ∉ M.cycle.vSet (G := G) :=
    (M.mem_bridge_iff_not_mem_cycle G L.vertex).1 L.vertex_mem
  constructor
  · intro hz
    by_cases hzC : z ∈ M.cycle.vSet (G := G)
    · have hzOld := (M.cycle.mem_vSet_iff (G := G)).1 hzC
      rw [O.verts_eq] at hzOld
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzOld
      rcases hzOld with rfl | rfl | rfl | rfl
      · exact (hz (by rw [O.reroute₂_vSet]; simp)).elim
      · exact (hz (by rw [O.reroute₂_vSet]; simp)).elim
      · exact Or.inr rfl
      · exact (hz (by rw [O.reroute₂_vSet]; simp)).elim
    · refine Or.inl ⟨(M.mem_bridge_iff_not_mem_cycle G z).2 hzC, ?_⟩
      intro hzL
      subst z
      exact hz (by rw [O.reroute₂_vSet]; simp)
  · intro hz
    rcases hz with ⟨hzB, hzL⟩ | rfl
    · have hzC : z ∉ M.cycle.vSet (G := G) :=
        (M.mem_bridge_iff_not_mem_cycle G z).1 hzB
      intro hzNew
      rw [O.reroute₂_vSet] at hzNew
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hzNew
      rcases hzNew with rfl | rfl | rfl | rfl
      · exact hzC R.left_mem
      · exact hzL rfl
      · exact hzC R.right_mem
      · exact hzC O.middle₂_mem
    · intro hm₁
      rw [O.reroute₂_vSet] at hm₁
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hm₁
      rcases hm₁ with hm₁l | hm₁L | hm₁r | hm₁m₂
      · exact O.left_ne_middle₁ hm₁l.symm
      · exact hLout (hm₁L ▸ O.middle₁_mem)
      · exact O.right_ne_middle₁ hm₁r.symm
      · exact O.middle_ne hm₁m₂

/-- The only nonadjacent pairs in the displayed chordless C4 are its two
opposite pairs. -/
theorem classify_nonadjacent_pair
    (O : OppositeFourRimData R) {u v : V}
    (huC : u ∈ M.cycle.vSet (G := G))
    (hvC : v ∈ M.cycle.vSet (G := G))
    (huv : u ≠ v) (hnot : ¬G.Adj u v) :
    ({u, v} : Finset V) = {R.left, R.right} ∨
      ({u, v} : Finset V) = {O.middle₁, O.middle₂} := by
  have hu : u = R.left ∨ u = R.right ∨
      u = O.middle₁ ∨ u = O.middle₂ := by
    have h := (M.cycle.mem_vSet_iff (G := G)).1 huC
    rw [O.verts_eq] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hv : v = R.left ∨ v = R.right ∨
      v = O.middle₁ ∨ v = O.middle₂ := by
    have h := (M.cycle.mem_vSet_iff (G := G)).1 hvC
    rw [O.verts_eq] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  rcases hu with hu | hu | hu | hu <;>
      rcases hv with hv | hv | hv | hv
  · exact (huv (hu.trans hv.symm)).elim
  · exact Or.inl (by simpa only [hu, hv])
  · exact (hnot (by simpa only [hu, hv] using O.adj_left_middle₁)).elim
  · exact (hnot (by simpa only [hu, hv] using O.adj_left_middle₂)).elim
  · exact Or.inl (by
      simpa only [hu, hv] using
        (Finset.pair_comm R.right R.left))
  · exact (huv (hu.trans hv.symm)).elim
  · exact (hnot (by simpa only [hu, hv] using O.adj_middle₁_right.symm)).elim
  · exact (hnot (by simpa only [hu, hv] using O.adj_middle₂_right.symm)).elim
  · exact (hnot (by simpa only [hu, hv] using O.adj_left_middle₁.symm)).elim
  · exact (hnot (by simpa only [hu, hv] using O.adj_middle₁_right)).elim
  · exact (huv (hu.trans hv.symm)).elim
  · exact Or.inr (by simpa only [hu, hv])
  · exact (hnot (by simpa only [hu, hv] using O.adj_left_middle₂.symm)).elim
  · exact (hnot (by simpa only [hu, hv] using O.adj_middle₂_right)).elim
  · exact Or.inr (by
      simpa only [hu, hv] using
        (Finset.pair_comm O.middle₂ O.middle₁))
  · exact (huv (hu.trans hv.symm)).elim

end LeafRimPair.OppositeFourRimData

namespace BridgeLeafData

variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {M : MaxCycleCertificate G}

/-- Cardinality engine for the leaf exchange.  If a rerouted chordless cycle
omits two old rim vertices, and each of them still attaches to the connected
bridge with the used leaf deleted, then the rooted complement strictly grows.
This is the precise primary-maximality contradiction used to force a rim of
length at most four. -/
theorem targetCard_lt_of_reroute_omits_two
    (L : BridgeLeafData G M)
    {x : V} (hxB : x ∈ bridgeSet G M.cycle M.bridge)
    (hxL : x ≠ L.vertex)
    (hconn : (G.induce
      (bridgeSet G M.cycle M.bridge \ {L.vertex})).Connected)
    (D : Cycle (G := G)) (hDch : D.IsChordless (G := G))
    (hDdisj : Disjoint (D.vSet (G := G))
      (bridgeSet G M.cycle M.bridge \ {L.vertex}))
    {z₁ z₂ w₁ w₂ : V}
    (hz₁C : z₁ ∈ M.cycle.vSet (G := G))
    (hz₂C : z₂ ∈ M.cycle.vSet (G := G))
    (hz₁D : z₁ ∉ D.vSet (G := G))
    (hz₂D : z₂ ∉ D.vSet (G := G))
    (hzne : z₁ ≠ z₂)
    (hw₁ : w₁ ∈ bridgeSet G M.cycle M.bridge \ {L.vertex})
    (hw₂ : w₂ ∈ bridgeSet G M.cycle M.bridge \ {L.vertex})
    (hw₁z₁ : G.Adj w₁ z₁) (hw₂z₂ : G.Adj w₂ z₂) :
    Nonseparating.targetCard G M.cycle x <
      Nonseparating.targetCard G D x := by
  classical
  let B : Set V := bridgeSet G M.cycle M.bridge
  let S : Set V := B \ {L.vertex}
  have hxS : x ∈ S := by
    exact ⟨hxB, by simpa only [Set.mem_singleton_iff] using hxL⟩
  have hDadmS : Nonseparating.IsAdmissibleCycle G S D := by
    refine ⟨hDch, ?_⟩
    simpa only [S, B] using hDdisj
  have hSsub : S ⊆ Nonseparating.targetSet G D x :=
    Nonseparating.prescribed_subset_target G
      (by simpa only [S, B] using hconn) hDadmS hxS
  have hxDout : x ∉ D.vSet (G := G) :=
    Nonseparating.IsAdmissibleCycle.not_mem_cycle
      (G := G) hDadmS hxS
  have hw₁T : w₁ ∈ Nonseparating.targetSet G D x :=
    hSsub (by simpa only [S, B] using hw₁)
  have hw₂T : w₂ ∈ Nonseparating.targetSet G D x :=
    hSsub (by simpa only [S, B] using hw₂)
  have hz₁T : z₁ ∈ Nonseparating.targetSet G D x := by
    rw [Nonseparating.targetSet_eq_component G hxDout] at hw₁T ⊢
    exact ComponentCompl.mem_of_adj w₁ z₁ hw₁T hz₁D hw₁z₁
  have hz₂T : z₂ ∈ Nonseparating.targetSet G D x := by
    rw [Nonseparating.targetSet_eq_component G hxDout] at hw₂T ⊢
    exact ComponentCompl.mem_of_adj w₂ z₂ hw₂T hz₂D hw₂z₂
  have hz₁B : z₁ ∉ B := by
    intro hz
    exact (mem_bridge_imp_not_mem_cycle
      (G := G) M.cycle M.bridge (by simpa only [B] using hz)) hz₁C
  have hz₂B : z₂ ∉ B := by
    intro hz
    exact (mem_bridge_imp_not_mem_cycle
      (G := G) M.cycle M.bridge (by simpa only [B] using hz)) hz₂C
  let R : Set V := insert z₁ S
  have hRsub : R ⊆ Nonseparating.targetSet G D x := by
    intro z hz
    rcases hz with rfl | hzS
    · exact hz₁T
    · exact hSsub hzS
  have hz₂R : z₂ ∉ R := by
    intro hz
    rcases hz with hz21 | hzS
    · exact hzne hz21.symm
    · exact hz₂B (by simpa only [S, B] using hzS.1)
  have hproper : R ⊂ Nonseparating.targetSet G D x := by
    exact Set.ssubset_iff_subset_ne.mpr ⟨hRsub, fun heq =>
      hz₂R (heq ▸ hz₂T)⟩
  have hLmemB : L.vertex ∈ B := by simpa only [B] using L.vertex_mem
  have hz₁S : z₁ ∉ S := fun hz => hz₁B hz.1
  have hRcard : R.ncard = B.ncard := by
    rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
    change (insert z₁ S).toFinset.card = B.toFinset.card
    have hz₁Sto : z₁ ∉ S.toFinset := by
      simpa only [Set.mem_toFinset] using hz₁S
    rw [Set.toFinset_insert, Finset.card_insert_of_notMem hz₁Sto]
    have hSto : S.toFinset = B.toFinset.erase L.vertex := by
      ext z
      simp only [Set.mem_toFinset, Finset.mem_erase, S,
        Set.mem_sdiff, Set.mem_singleton_iff, B]
      tauto
    rw [hSto]
    exact Finset.card_erase_add_one
      (by simpa only [Set.mem_toFinset] using hLmemB)
  have hxCold : x ∉ M.cycle.vSet (G := G) :=
    (M.mem_bridge_iff_not_mem_cycle G x).1 hxB
  have hcomp :
      G.componentComplMk (K := M.cycle.vSet (G := G)) hxCold = M.bridge :=
    (SimpleGraph.ComponentCompl.mem_supp_iff
      (G := G) (K := M.cycle.vSet (G := G))
      (C := M.bridge) (v := x)).mp hxB |>.2
  have htargetOld : Nonseparating.targetSet G M.cycle x = B := by
    rw [Nonseparating.targetSet_eq_component G hxCold]
    simpa only [B, bridgeSet, hcomp]
  rw [Nonseparating.targetCard, htargetOld,
    Nonseparating.targetCard]
  rw [← hRcard]
  exact Set.ncard_lt_ncard hproper

end BridgeLeafData

namespace Nonseparating

/-- The secondary objective is literally the edge count of the graph
induced by the rooted target component. -/
theorem targetEdgeCard_eq_card_induce_targetSet
    (C : Cycle (G := G)) (x : V) :
    targetEdgeCard G C x =
      (G.induce (targetSet G C x)).edgeFinset.card := by
  classical
  unfold targetEdgeCard targetEdgeFinset
  have hfilter :
      G.edgeFinset.filter
          (fun e => (↑e.toFinset : Set V) ⊆ targetSet G C x) =
        G.edgeFinset.filter
          (fun e => e.toFinset ⊆ (targetSet G C x).toFinset) := by
    apply Finset.filter_congr
    intro e he
    constructor
    · intro h y hy
      simpa only [Set.mem_toFinset] using h hy
    · intro h y hy
      simpa only [Set.mem_toFinset] using h hy
  rw [hfilter]
  simpa only [Set.coe_toFinset] using
    G.card_filter_edgeFinset_toFinset_subset (targetSet G C x).toFinset

end Nonseparating

namespace InducedEdgeExchange

/-- Adjoining one vertex with an edge into a connected induced carrier
preserves connectedness. -/
theorem connected_insert_of_adj {S : Set V} {z w : V}
    (hS : (G.induce S).Connected) (hwS : w ∈ S)
    (hzw : G.Adj z w) :
    (G.induce (insert z S)).Connected := by
  let T : Set V := insert z S
  let wT : T := ⟨w, by exact Set.mem_insert_iff.mpr (Or.inr hwS)⟩
  let f : G.induce S →g G.induce T :=
    { toFun := fun v =>
        ⟨v.1, Set.mem_insert_iff.mpr (Or.inr v.2)⟩
      map_rel' := fun h => h }
  apply (connected_iff_exists_forall_reachable
    (G := G.induce T)).mpr
  refine ⟨wT, ?_⟩
  intro y
  have hy : y.1 = z ∨ y.1 ∈ S := by
    simpa only [T, Set.mem_insert_iff] using y.2
  rcases hy with hyz | hyS
  · have hadj : (G.induce T).Adj wT y := by
      change G.Adj w y.1
      simpa only [hyz] using hzw.symm
    exact hadj.reachable
  · let yS : S := ⟨y.1, hyS⟩
    have hreach := (hS ⟨w, hwS⟩ yS).map f
    simpa only [f, wT, yS] using hreach

/-- Flatten the double induction obtained by deleting one vertex from an
already induced graph. -/
def sdiffSingletonIso (S : Set V) (x : S) :
    G.induce (S \ {x.1}) ≃g
      (G.induce S).induce (({x} : Set S)ᶜ) := by
  let e : ↥(S \ ({x.1} : Set V)) ≃ ↥(({x} : Set S)ᶜ) :=
    { toFun := fun v =>
        ⟨⟨v.1, v.2.1⟩, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h
          exact v.2.2 (congrArg Subtype.val h)⟩
      invFun := fun v =>
        ⟨v.1.1, v.1.2, by
          simp only [Set.mem_singleton_iff]
          intro h
          apply v.2
          apply Subtype.ext
          exact h⟩
      left_inv := by intro v; apply Subtype.ext; rfl
      right_inv := by intro v; apply Subtype.ext; apply Subtype.ext; rfl }
  exact
    { toEquiv := e
      map_rel_iff' := by intro _ _; rfl }

/-- Removing a vertex from an induced carrier loses exactly its degree in
that induced graph, stated additively to avoid truncated subtraction. -/
theorem card_sdiff_add_degree (S : Set V) (x : S) :
    (G.induce (S \ {x.1})).edgeFinset.card +
        (G.induce S).degree x =
      (G.induce S).edgeFinset.card := by
  classical
  let H := G.induce S
  have hdel := H.card_edgeFinset_induce_compl_singleton x
  have hdelete := H.card_edgeFinset_deleteIncidenceSet x
  have hle := H.degree_le_card_edgeFinset x
  have hflat := (sdiffSingletonIso G S x).card_edgeFinset_eq
  calc
    (G.induce (S \ {x.1})).edgeFinset.card + H.degree x =
        (H.induce ({x} : Set S)ᶜ).edgeFinset.card + H.degree x := by
          rw [hflat]
    _ = (H.deleteIncidenceSet x).edgeFinset.card + H.degree x := by
          rw [hdel]
    _ = (H.edgeFinset.card - H.degree x) + H.degree x := by
          rw [hdelete]
    _ = H.edgeFinset.card := Nat.sub_add_cancel hle

end InducedEdgeExchange

namespace SimpleGraph.IsTree

/-- In a nontrivial finite tree, every vertex lies on a path
whose two endpoints are leaves.  We maximize only among paths containing
the prescribed vertex; the usual endpoint-extension proof for a longest
path then applies verbatim. -/
theorem exists_leaf_path_through
    {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) (a : V) (hne : ∃ b : V, b ≠ a) :
    ∃ u v : V, ∃ p : T.Walk u v,
      p.IsPath ∧ a ∈ p.support ∧ u ≠ v ∧
      T.degree u = 1 ∧ T.degree v = 1 := by
  classical
  let lengths : Set Nat :=
    {n | ∃ (u v : V) (p : T.Walk u v),
      p.IsPath ∧ a ∈ p.support ∧ p.length = n}
  have hfinite : lengths.Finite :=
    Set.Finite.subset (Set.finite_le_nat T.edgeFinset.card) (by
      intro n hn
      obtain ⟨u, v, p, hp, -, rfl⟩ := hn
      exact hp.isTrail.length_le_card_edgeFinset)
  have hzero : 0 ∈ lengths := by
    exact ⟨a, a, .nil, by simp, by simp, rfl⟩
  obtain ⟨n, hn, hmaxn⟩ :=
    hfinite.exists_maximal ⟨0, hzero⟩
  obtain ⟨u, v, p, hp, haP, hpLen⟩ := hn
  have hmax : ∀ (u' v' : V) (q : T.Walk u' v'),
      q.IsPath → a ∈ q.support → q.length ≤ p.length := by
    intro u' v' q hq haQ
    have hqmem : q.length ∈ lengths :=
      ⟨u', v', q, hq, haQ, rfl⟩
    by_contra hnot
    have hlt : p.length < q.length := Nat.lt_of_not_ge hnot
    have hback : q.length ≤ n := hmaxn hqmem (by
      simpa only [hpLen] using hlt.le)
    omega
  have hpNotNil : ¬p.Nil := by
    obtain ⟨b, hba⟩ := hne
    obtain ⟨q, hq⟩ := hT.connected.exists_isPath a b
    have hle := hmax a b q hq q.start_mem_support
    have hqpos : 0 < q.length :=
      SimpleGraph.Walk.not_nil_iff_lt_length.mp
        (SimpleGraph.Walk.not_nil_of_ne hba.symm)
    intro hnil
    have : p.length = 0 := SimpleGraph.Walk.length_eq_zero_iff.mpr hnil
    omega
  have hdegU : T.degree u = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    refine ⟨p.getVert 1, p.adj_snd hpNotNil, ?_⟩
    intro w huw
    apply hT.isAcyclic.eq_snd_of_adj_start hp huw
    have hnot : ¬(p.cons huw.symm).IsPath := by
      intro hq
      have hle := hmax w v (p.cons huw.symm) hq (by
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
        exact Or.inr haP)
      simp only [SimpleGraph.Walk.length_cons] at hle
      omega
    by_contra hwSupp
    exact hnot (hp.cons hwSupp)
  have hdegV : T.degree v = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    refine ⟨p.getVert (p.length - 1), p.adj_penultimate hpNotNil |>.symm, ?_⟩
    intro w hvw
    apply hT.isAcyclic.eq_penultimate_of_adj_end hp hvw
    have hnot : ¬(p.concat hvw).IsPath := by
      intro hq
      have hle := hmax u w (p.concat hvw) hq (by
        simp only [SimpleGraph.Walk.support_concat, List.mem_append,
          List.mem_singleton]
        exact Or.inl haP)
      simp only [SimpleGraph.Walk.length_concat] at hle
      omega
    by_contra hwSupp
    exact hnot (hp.concat hwSupp hvw)
  exact ⟨u, v, p, hp, haP, hp.nil_iff_eq.not.mp hpNotNil,
    hdegU, hdegV⟩

/-- Starting at a specified leaf, a longest path constrained to pass through
`a` ends at another leaf. -/
theorem exists_other_leaf_path_through
    {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) {l a : V} (hl : T.degree l = 1)
    (hla : l ≠ a) :
    ∃ k : V, ∃ p : T.Walk l k,
      p.IsPath ∧ a ∈ p.support ∧ l ≠ k ∧ T.degree k = 1 := by
  classical
  let lengths : Set Nat :=
    {n | ∃ (v : V) (p : T.Walk l v),
      p.IsPath ∧ a ∈ p.support ∧ p.length = n}
  obtain ⟨seed, hseed⟩ := hT.connected.exists_isPath l a
  have hfinite : lengths.Finite :=
    Set.Finite.subset (Set.finite_le_nat T.edgeFinset.card) (by
      intro n hn
      obtain ⟨v, p, hp, -, rfl⟩ := hn
      exact hp.isTrail.length_le_card_edgeFinset)
  have hseedMem : seed.length ∈ lengths :=
    ⟨a, seed, hseed, seed.end_mem_support, rfl⟩
  obtain ⟨n, hn, hmaxn⟩ :=
    hfinite.exists_maximal ⟨seed.length, hseedMem⟩
  obtain ⟨k, p, hp, haP, hpLen⟩ := hn
  have hmax : ∀ (v : V) (q : T.Walk l v),
      q.IsPath → a ∈ q.support → q.length ≤ p.length := by
    intro v q hq haQ
    have hqmem : q.length ∈ lengths := ⟨v, q, hq, haQ, rfl⟩
    by_contra hnot
    have hlt : p.length < q.length := Nat.lt_of_not_ge hnot
    have hback : q.length ≤ n := hmaxn hqmem (by
      simpa only [hpLen] using hlt.le)
    omega
  have hpNotNil : ¬p.Nil := by
    intro hnil
    have hpzero : p.length = 0 :=
      SimpleGraph.Walk.length_eq_zero_iff.mpr hnil
    have hseedNotNil : ¬seed.Nil :=
      SimpleGraph.Walk.not_nil_of_ne hla
    have hseedPos : 0 < seed.length :=
      SimpleGraph.Walk.not_nil_iff_lt_length.mp hseedNotNil
    have hle := hmax a seed hseed seed.end_mem_support
    omega
  have hdegK : T.degree k = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    refine ⟨p.getVert (p.length - 1), p.adj_penultimate hpNotNil |>.symm, ?_⟩
    intro w hkw
    apply hT.isAcyclic.eq_penultimate_of_adj_end hp hkw
    have hnot : ¬(p.concat hkw).IsPath := by
      intro hq
      have hle := hmax w (p.concat hkw) hq (by
        simp only [SimpleGraph.Walk.support_concat, List.mem_append,
          List.mem_singleton]
        exact Or.inl haP)
      simp only [SimpleGraph.Walk.length_concat] at hle
      omega
    by_contra hwSupp
    exact hnot (hp.concat hwSupp hkw)
  exact ⟨k, p, hp, haP, hp.nil_iff_eq.not.mp hpNotNil, hdegK⟩

end SimpleGraph.IsTree

namespace LexMaxCycleCertificate

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The secondary edge tie-breaker in its exact local form.  If a leaf
reroute replaces the leaf in the connected complement by one old rim
vertex, then that rim vertex has degree three.  The old target loses the
single bridge edge at the leaf; hence edge maximality permits only one new
edge from the inserted rim vertex into the surviving bridge. -/
theorem degree_eq_three_of_exact_leaf_reroute
    {x : V} (X : LexMaxCycleCertificate G ({x} : Set V) x)
    (L : BridgeLeafData G X.toMaxCycleCertificate)
    {z : V} (hzC : z ∈ X.cycle.vSet (G := G))
    (hLz : ¬G.Adj L.vertex z)
    (hxB : x ∈ bridgeSet G X.cycle X.bridge)
    (hxL : x ≠ L.vertex)
    (D : Cycle (G := G)) (hDch : D.IsChordless (G := G))
    (hDcompl : (D.vSet (G := G))ᶜ =
      (bridgeSet G X.cycle X.bridge \ {L.vertex}) ∪ {z})
    (hminz : 3 ≤ G.degree z) :
    G.degree z = 3 := by
  classical
  let M : MaxCycleCertificate G := X.toMaxCycleCertificate
  let B : Set V := bridgeSet G M.cycle M.bridge
  let S : Set V := B \ {L.vertex}
  let T : Set V := insert z S
  have hzB : z ∉ B := by
    intro hz
    exact (M.mem_bridge_iff_not_mem_cycle G z).1 hz hzC
  have hzS : z ∉ S := fun hz => hzB hz.1
  obtain ⟨w, hwB, hzw⟩ := M.exists_adj_bridge G hzC
  have hwL : w ≠ L.vertex := by
    intro h
    subst w
    exact hLz hzw.symm
  have hwS : w ∈ S :=
    ⟨hwB, by simpa only [Set.mem_singleton_iff] using hwL⟩
  let lB : B := ⟨L.vertex, by simpa only [B] using L.vertex_mem⟩
  have hSconn : (G.induce S).Connected := by
    let e := InducedEdgeExchange.sdiffSingletonIso G B lB
    apply e.connected_iff.mpr
    apply (M.bridge_connected G).induce_compl_singleton_of_degree_eq_one
    simpa only [B, lB, M] using L.bridge_degree_eq_one
  have hTconn : (G.induce T).Connected := by
    exact InducedEdgeExchange.connected_insert_of_adj G
      (by simpa only [S] using hSconn) hwS hzw
  have hcompT : (D.vSet (G := G))ᶜ = T := by
    simpa only [T, Set.insert_eq, S, B, M, Set.union_comm] using hDcompl
  have hxT : x ∈ T := by
    exact Set.mem_insert_iff.mpr (Or.inr
      ⟨by simpa only [B, M] using hxB,
        by simpa only [Set.mem_singleton_iff] using hxL⟩)
  have hxDout : x ∉ D.vSet (G := G) := by
    simpa only [← Set.mem_compl_iff, hcompT] using hxT
  have hDadm : Nonseparating.IsAdmissibleCycle G ({x} : Set V) D := by
    refine ⟨hDch, Set.disjoint_left.mpr ?_⟩
    intro y hyD hyx
    have hyx' : y = x := Set.mem_singleton_iff.mp hyx
    exact hxDout (hyx' ▸ hyD)
  have htargetNew : Nonseparating.targetSet G D x = T := by
    have hconnD : (G.induce (D.vSet (G := G))ᶜ).Connected := by
      rw [hcompT]
      exact hTconn
    exact ((Nonseparating.complement_connected_iff_target_eq G hxDout).1
      hconnD).trans hcompT
  have hxCold : x ∉ M.cycle.vSet (G := G) :=
    (M.mem_bridge_iff_not_mem_cycle G x).1
      (by simpa only [M, bridgeSet] using hxB)
  have hcompOld :
      G.componentComplMk (K := M.cycle.vSet (G := G)) hxCold = M.bridge :=
    (SimpleGraph.ComponentCompl.mem_supp_iff
      (G := G) (K := M.cycle.vSet (G := G))
      (C := M.bridge) (v := x)).mp
        (by simpa only [M, bridgeSet] using hxB) |>.2
  have htargetOld : Nonseparating.targetSet G M.cycle x = B := by
    rw [Nonseparating.targetSet_eq_component G hxCold, hcompOld]
    rfl
  have hTcard : T.ncard = B.ncard := by
    rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
    change (insert z S).toFinset.card = B.toFinset.card
    have hzSto : z ∉ S.toFinset := by
      simpa only [Set.mem_toFinset] using hzS
    rw [Set.toFinset_insert, Finset.card_insert_of_notMem hzSto]
    have hSto : S.toFinset = B.toFinset.erase L.vertex := by
      ext y
      simp only [Set.mem_toFinset, Finset.mem_erase, S,
        Set.mem_sdiff, Set.mem_singleton_iff]
      tauto
    rw [hSto]
    exact Finset.card_erase_add_one
      (by simpa only [Set.mem_toFinset, B] using L.vertex_mem)
  have htargetCardEq :
      Nonseparating.targetCard G D x =
        Nonseparating.targetCard G M.cycle x := by
    simp only [Nonseparating.targetCard, htargetNew, htargetOld, hTcard]
  have hedgeMax := X.edge_max_at_target D hDadm (by
    simpa only [M] using htargetCardEq)
  have htargetOldX : Nonseparating.targetSet G X.cycle x = B := by
    simpa only [M] using htargetOld
  have hedgeLe : (G.induce T).edgeFinset.card ≤
      (G.induce B).edgeFinset.card := by
    rw [Nonseparating.targetEdgeCard_eq_card_induce_targetSet,
      Nonseparating.targetEdgeCard_eq_card_induce_targetSet,
      htargetNew, htargetOldX] at hedgeMax
    exact hedgeMax
  have hold := InducedEdgeExchange.card_sdiff_add_degree G B lB
  have hLdegree : (G.induce B).degree lB = 1 := by
    simpa only [B, lB, M] using L.bridge_degree_eq_one
  have hold' : (G.induce S).edgeFinset.card + 1 =
      (G.induce B).edgeFinset.card := by
    rw [hLdegree] at hold
    simpa only [S] using hold
  let zT : T := ⟨z, Set.mem_insert_iff.mpr (Or.inl rfl)⟩
  have hTsdiff : T \ {z} = S := by
    ext y
    simp only [T, Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hyz | hyS, hyne⟩
      · exact (hyne hyz).elim
      · exact hyS
    · intro hyS
      refine ⟨Or.inr hyS, ?_⟩
      intro hyz
      subst y
      exact hzS hyS
  have hnew := InducedEdgeExchange.card_sdiff_add_degree G T zT
  have hnew' : (G.induce S).edgeFinset.card +
      (G.induce T).degree zT = (G.induce T).edgeFinset.card := by
    simpa only [zT, hTsdiff] using hnew
  have hzTdeg_le : (G.induce T).degree zT ≤ 1 := by
    omega
  have hoffSub :
      G.neighborFinset z \ M.cycle.verts (G := G) ⊆
        G.neighborFinset z ∩ T.toFinset := by
    intro y hy
    have hyAdj : G.Adj z y := by
      simpa only [SimpleGraph.mem_neighborFinset] using
        (Finset.mem_sdiff.mp hy).1
    have hyout : y ∉ M.cycle.vSet (G := G) := by
      simpa only [M.cycle.mem_vSet_iff] using (Finset.mem_sdiff.mp hy).2
    have hyB : y ∈ B := by
      exact (M.mem_bridge_iff_not_mem_cycle G y).2 hyout
    have hyL : y ≠ L.vertex := by
      intro h
      subst y
      exact hLz hyAdj
    refine Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hy).1, ?_⟩
    simp only [Set.mem_toFinset, T, Set.mem_insert_iff]
    exact Or.inr ⟨hyB, by
      simpa only [Set.mem_singleton_iff] using hyL⟩
  have hmap := G.map_neighborFinset_induce zT
  have hmapCard := congrArg Finset.card hmap
  have hinterCard :
      (G.neighborFinset z ∩ T.toFinset).card =
        (G.induce T).degree zT := by
    simpa only [Finset.card_map,
      SimpleGraph.card_neighborFinset_eq_degree] using hmapCard.symm
  have hoff_le :
      (G.neighborFinset z \ M.cycle.verts (G := G)).card ≤ 1 := by
    exact (Finset.card_le_card hoffSub).trans
      (by rw [hinterCard]; exact hzTdeg_le)
  have hoffEq := card_neighbors_off_chordless_cycle
    G M.cycle M.chordless hzC
  omega

/-- After the primary maximum has forced a C4, the two vertices opposite a
chosen bridge leaf's attachment pair have ambient degree exactly three. -/
theorem opposite_middle_degrees_eq_three
    {x : V} (X : LexMaxCycleCertificate G ({x} : Set V) x)
    (L : BridgeLeafData G X.toMaxCycleCertificate)
    (R : LeafRimPair G L)
    (O : LeafRimPair.OppositeFourRimData R)
    (hnotAdj : ¬G.Adj R.left R.right)
    (hxB : x ∈ bridgeSet G X.cycle X.bridge)
    (hxL : x ≠ L.vertex)
    (hmin : ∀ v : V, 3 ≤ G.degree v) :
    G.degree O.middle₁ = 3 ∧ G.degree O.middle₂ = 3 := by
  have hLm₁ : ¬G.Adj L.vertex O.middle₁ :=
    R.not_adj_vertex_of_cycle_mem O.middle₁_mem
      O.left_ne_middle₁.symm O.right_ne_middle₁.symm
  have hLm₂ : ¬G.Adj L.vertex O.middle₂ :=
    R.not_adj_vertex_of_cycle_mem O.middle₂_mem
      O.left_ne_middle₂.symm O.right_ne_middle₂.symm
  constructor
  · exact X.degree_eq_three_of_exact_leaf_reroute L O.middle₁_mem hLm₁
      hxB hxL O.reroute₂ (O.reroute₂_isChordless hnotAdj)
      O.reroute₂_compl_eq (hmin O.middle₁)
  · exact X.degree_eq_three_of_exact_leaf_reroute L O.middle₂_mem hLm₂
      hxB hxL O.reroute₁ (O.reroute₁_isChordless hnotAdj)
      O.reroute₁_compl_eq (hmin O.middle₂)

/-- If the attachment pair also has degree three, its displayed three
common neighbours exhaust both neighbourhoods, giving the exact false-twin
terminal required by the density reduction. -/
theorem attachment_falseTwins_of_degrees_eq_three
    {M : MaxCycleCertificate G}
    (L : BridgeLeafData G M) (R : LeafRimPair G L)
    (O : LeafRimPair.OppositeFourRimData R)
    (hleft : G.degree R.left = 3)
    (hright : G.degree R.right = 3) :
    AreFalseTwins G R.left R.right := by
  classical
  let N : Finset V := {O.middle₁, O.middle₂, L.vertex}
  have hm₁L : O.middle₁ ≠ L.vertex := by
    intro h
    exact (mem_bridge_imp_not_mem_cycle
      (G := G) M.cycle M.bridge L.vertex_mem) (h ▸ O.middle₁_mem)
  have hm₂L : O.middle₂ ≠ L.vertex := by
    intro h
    exact (mem_bridge_imp_not_mem_cycle
      (G := G) M.cycle M.bridge L.vertex_mem) (h ▸ O.middle₂_mem)
  have hNcard : N.card = 3 := by
    simp [N, O.middle_ne, hm₁L, hm₂L]
  have hNleft : N ⊆ G.neighborFinset R.left := by
    intro y hy
    simp only [N, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · simpa only [SimpleGraph.mem_neighborFinset] using O.adj_left_middle₁
    · simpa only [SimpleGraph.mem_neighborFinset] using O.adj_left_middle₂
    · simpa only [SimpleGraph.mem_neighborFinset] using R.adj_left.symm
  have hNright : N ⊆ G.neighborFinset R.right := by
    intro y hy
    simp only [N, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · simpa only [SimpleGraph.mem_neighborFinset] using O.adj_middle₁_right.symm
    · simpa only [SimpleGraph.mem_neighborFinset] using O.adj_middle₂_right.symm
    · simpa only [SimpleGraph.mem_neighborFinset] using R.adj_right.symm
  have hleftN : G.neighborFinset R.left = N := by
    apply (Finset.eq_of_subset_of_card_le hNleft ?_).symm
    rw [hNcard, G.card_neighborFinset_eq_degree, hleft]
  have hrightN : G.neighborFinset R.right = N := by
    apply (Finset.eq_of_subset_of_card_le hNright ?_).symm
    rw [hNcard, G.card_neighborFinset_eq_degree, hright]
  refine ⟨R.ne, ?_⟩
  ext y
  simpa only [SimpleGraph.mem_neighborSet, ← SimpleGraph.mem_neighborFinset,
    hleftN, hrightN]

/-- If another bridge leaf uses the opposite attachment pair of the displayed
four-cycle, the two displayed middle vertices have the same three neighbours.
Thus degree three makes them false twins. -/
theorem middle_falseTwins_of_opposite_leaf_attachments
    {M : MaxCycleCertificate G}
    {L K : BridgeLeafData G M}
    (R : LeafRimPair G L) (QK : LeafRimPair G K)
    (O : LeafRimPair.OppositeFourRimData R)
    (hpK : ({QK.left, QK.right} : Finset V) =
      {O.middle₁, O.middle₂})
    (hm₁ : G.degree O.middle₁ = 3)
    (hm₂ : G.degree O.middle₂ = 3) :
    AreFalseTwins G O.middle₁ O.middle₂ := by
  classical
  have hKm₁ : G.Adj K.vertex O.middle₁ := by
    have hmem : O.middle₁ ∈
        G.neighborFinset K.vertex ∩ M.cycle.verts (G := G) := by
      rw [QK.neighbors_eq, hpK]
      simp
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hmem).1
  have hKm₂ : G.Adj K.vertex O.middle₂ := by
    have hmem : O.middle₂ ∈
        G.neighborFinset K.vertex ∩ M.cycle.verts (G := G) := by
      rw [QK.neighbors_eq, hpK]
      simp
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hmem).1
  have hKout : K.vertex ∉ M.cycle.vSet (G := G) :=
    (M.mem_bridge_iff_not_mem_cycle G K.vertex).1 K.vertex_mem
  have hKleft : K.vertex ≠ R.left :=
    fun h => hKout (h ▸ R.left_mem)
  have hKright : K.vertex ≠ R.right :=
    fun h => hKout (h ▸ R.right_mem)
  let N : Finset V := {R.left, R.right, K.vertex}
  have hNcard : N.card = 3 := by
    have hlnot : R.left ∉ ({R.right, K.vertex} : Finset V) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨R.ne, hKleft.symm⟩
    have hrnot : R.right ∉ ({K.vertex} : Finset V) := by
      simpa only [Finset.mem_singleton] using hKright.symm
    change ({R.left, R.right, K.vertex} : Finset V).card = 3
    rw [Finset.card_insert_of_notMem hlnot,
      Finset.card_insert_of_notMem hrnot]
    simp
  have hNm₁ : N ⊆ G.neighborFinset O.middle₁ := by
    intro y hy
    simp only [N, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · simpa only [SimpleGraph.mem_neighborFinset] using
        O.adj_left_middle₁.symm
    · simpa only [SimpleGraph.mem_neighborFinset] using
        O.adj_middle₁_right
    · simpa only [SimpleGraph.mem_neighborFinset] using hKm₁.symm
  have hNm₂ : N ⊆ G.neighborFinset O.middle₂ := by
    intro y hy
    simp only [N, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · simpa only [SimpleGraph.mem_neighborFinset] using
        O.adj_left_middle₂.symm
    · simpa only [SimpleGraph.mem_neighborFinset] using
        O.adj_middle₂_right
    · simpa only [SimpleGraph.mem_neighborFinset] using hKm₂.symm
  have hm₁N : G.neighborFinset O.middle₁ = N := by
    apply (Finset.eq_of_subset_of_card_le hNm₁ ?_).symm
    rw [hNcard, G.card_neighborFinset_eq_degree, hm₁]
  have hm₂N : G.neighborFinset O.middle₂ = N := by
    apply (Finset.eq_of_subset_of_card_le hNm₂ ?_).symm
    rw [hNcard, G.card_neighborFinset_eq_degree, hm₂]
  refine ⟨O.middle_ne, ?_⟩
  ext y
  simpa only [SimpleGraph.mem_neighborSet, ← SimpleGraph.mem_neighborFinset,
    hm₁N, hm₂N]

/-- The sole surviving local configuration after the two exact C4 leaf
exchanges.  Both vertices opposite the leaf attachments have degree three;
one attachment endpoint still has degree at least four.  The published N6
endblock argument rules out precisely this configuration by producing a
wheel. -/
structure C4HighAttachmentData
    {x : V} (X : LexMaxCycleCertificate G ({x} : Set V) x) where
  leaf : BridgeLeafData G X.toMaxCycleCertificate
  pair : LeafRimPair G leaf
  opposite : LeafRimPair.OppositeFourRimData pair
  root_ne_leaf : x ≠ leaf.vertex
  attachments_not_adj : ¬G.Adj pair.left pair.right
  middle₁_degree : G.degree opposite.middle₁ = 3
  middle₂_degree : G.degree opposite.middle₂ = 3
  high_attachment : 4 ≤ G.degree pair.left ∨ 4 ≤ G.degree pair.right

/-- If two bridge leaves use the same opposite attachment pair and the
tree path between them passes through a bridge neighbour of the other rim
pair, that other rim vertex is a hub. -/
theorem hasWheelWitness_of_leaf_path_same_attachments
    {M : MaxCycleCertificate G}
    {L₁ L₂ : BridgeLeafData G M}
    (R₁ : LeafRimPair G L₁) (R₂ : LeafRimPair G L₂)
    {L : BridgeLeafData G M} {R : LeafRimPair G L}
    (O : LeafRimPair.OppositeFourRimData R)
    (hp₁ : ({R₁.left, R₁.right} : Finset V) = {R.left, R.right})
    (hp₂ : ({R₂.left, R₂.right} : Finset V) = {R.left, R.right})
    (hne : L₁.vertex ≠ L₂.vertex)
    {a : V} (haB : a ∈ bridgeSet G M.cycle M.bridge)
    (hma : G.Adj O.middle₁ a)
    (Psub : (G.induce (bridgeSet G M.cycle M.bridge)).Walk
      ⟨L₁.vertex, L₁.vertex_mem⟩ ⟨L₂.vertex, L₂.vertex_mem⟩)
    (hPsub : Psub.IsPath)
    (haPsub : (⟨a, haB⟩ : bridgeSet G M.cycle M.bridge) ∈
      Psub.support) :
    HasWheelWitness G := by
  classical
  have hL₁left : G.Adj L₁.vertex R.left := by
    have hmem : R.left ∈
        G.neighborFinset L₁.vertex ∩ M.cycle.verts (G := G) := by
      rw [R₁.neighbors_eq, hp₁]
      simp
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hmem).1
  have hL₂right : G.Adj L₂.vertex R.right := by
    have hmem : R.right ∈
        G.neighborFinset L₂.vertex ∩ M.cycle.verts (G := G) := by
      rw [R₂.neighbors_eq, hp₂]
      simp
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hmem).1
  let inc : G.induce (bridgeSet G M.cycle M.bridge) →g G :=
    (SimpleGraph.Embedding.induce
      (G := G) (s := bridgeSet G M.cycle M.bridge)).toHom
  let P : G.Walk L₁.vertex L₂.vertex := Psub.map inc
  have hP : P.IsPath := hPsub.map Subtype.val_injective
  have haP : a ∈ P.support := by
    change a ∈ (Psub.map inc).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨⟨a, haB⟩, haPsub, rfl⟩
  have hPout : ∀ y, y ∈ P.support →
      y ∉ M.cycle.vSet (G := G) := by
    intro y hy
    change y ∈ (Psub.map inc).support at hy
    rw [SimpleGraph.Walk.support_map] at hy
    obtain ⟨yb, -, rfl⟩ := List.mem_map.mp hy
    exact (M.mem_bridge_iff_not_mem_cycle G yb.1).1 yb.2
  have hL₁out : L₁.vertex ∉ M.cycle.vSet (G := G) :=
    (M.mem_bridge_iff_not_mem_cycle G L₁.vertex).1 L₁.vertex_mem
  have hL₂out : L₂.vertex ∉ M.cycle.vSet (G := G) :=
    (M.mem_bridge_iff_not_mem_cycle G L₂.vertex).1 L₂.vertex_mem
  have hL₁ne_left : L₁.vertex ≠ R.left :=
    fun h => hL₁out (h ▸ R.left_mem)
  have hL₁ne_right : L₁.vertex ≠ R.right :=
    fun h => hL₁out (h ▸ R.right_mem)
  have hL₁ne_m₂ : L₁.vertex ≠ O.middle₂ :=
    fun h => hL₁out (h ▸ O.middle₂_mem)
  have hL₂ne_left : L₂.vertex ≠ R.left :=
    fun h => hL₂out (h ▸ R.left_mem)
  have hL₂ne_right : L₂.vertex ≠ R.right :=
    fun h => hL₂out (h ▸ R.right_mem)
  have hL₂ne_m₂ : L₂.vertex ≠ O.middle₂ :=
    fun h => hL₂out (h ▸ O.middle₂_mem)
  let Q : G.Walk L₂.vertex L₁.vertex :=
    .cons hL₂right
      (.cons O.adj_middle₂_right.symm
        (.cons O.adj_left_middle₂.symm
          (.cons hL₁left.symm .nil)))
  have hQ : Q.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [Q, hne, hne.symm, hL₁ne_left, hL₁ne_right,
      hL₁ne_left.symm, hL₁ne_right.symm,
      hL₁ne_m₂, hL₁ne_m₂.symm,
      hL₂ne_left, hL₂ne_right, hL₂ne_m₂,
      R.ne, R.ne.symm, O.left_ne_middle₂,
      O.left_ne_middle₂.symm, O.right_ne_middle₂,
      O.right_ne_middle₂.symm]
  have hdis : List.Disjoint P.support.tail Q.support.tail := by
    rw [List.disjoint_left]
    intro y hyP hyQ
    have hyQ' : y = R.right ∨ y = O.middle₂ ∨
        y = R.left ∨ y = L₁.vertex := by
      simpa [Q] using hyQ
    have hyPfull : y ∈ P.support := List.mem_of_mem_tail hyP
    rcases hyQ' with rfl | rfl | rfl | rfl
    · exact hPout R.right hyPfull R.right_mem
    · exact hPout O.middle₂ hyPfull O.middle₂_mem
    · exact hPout R.left hyPfull R.left_mem
    · have hnodup := hP.support_nodup
      rw [P.support_eq_cons] at hnodup
      exact (List.nodup_cons.mp hnodup).1 hyP
  have hkP : O.middle₁ ∉ P.support := by
    intro h
    exact hPout O.middle₁ h O.middle₁_mem
  have hm₁neL₁ : O.middle₁ ≠ L₁.vertex := by
    intro h
    exact hL₁out (h ▸ O.middle₁_mem)
  have hm₁neL₂ : O.middle₁ ≠ L₂.vertex := by
    intro h
    exact hL₂out (h ▸ O.middle₁_mem)
  have hkQ : O.middle₁ ∉ Q.support := by
    simp [Q, O.middle_ne, O.middle_ne.symm,
      O.left_ne_middle₁, O.left_ne_middle₁.symm,
      O.right_ne_middle₁, O.right_ne_middle₁.symm,
      hm₁neL₂, hm₁neL₁]
  have ha_ne_left : a ≠ R.left := by
    intro h
    exact (M.mem_bridge_iff_not_mem_cycle G a).1 haB (h ▸ R.left_mem)
  have ha_ne_right : a ≠ R.right := by
    intro h
    exact (M.mem_bridge_iff_not_mem_cycle G a).1 haB (h ▸ R.right_mem)
  exact hasWheelWitness_of_path_append G P Q hP hQ hdis
    (Or.inr (by simp [Q])) hkP hkQ
    O.adj_left_middle₁.symm O.adj_middle₁_right hma
    (Or.inr (by simp [Q])) (Or.inr (by simp [Q])) (Or.inl haP)
    R.ne ha_ne_left.symm ha_ne_right.symm

/-- The complementary attachment pattern is even shorter: if the terminal
leaf uses the other opposite pair, close the leaf-to-leaf tree path through
that pair.  The first middle vertex sees the old attachment endpoint, its
bridge neighbour on the path, and the terminal leaf. -/
theorem hasWheelWitness_of_leaf_path_opposite_attachments
    {M : MaxCycleCertificate G}
    {L K : BridgeLeafData G M}
    (R : LeafRimPair G L) (QK : LeafRimPair G K)
    (O : LeafRimPair.OppositeFourRimData R)
    (hpK : ({QK.left, QK.right} : Finset V) =
      {O.middle₁, O.middle₂})
    (hne : L.vertex ≠ K.vertex)
    {a : V} (haB : a ∈ bridgeSet G M.cycle M.bridge)
    (hma : G.Adj O.middle₁ a) (haK : a ≠ K.vertex)
    (Psub : (G.induce (bridgeSet G M.cycle M.bridge)).Walk
      ⟨L.vertex, L.vertex_mem⟩ ⟨K.vertex, K.vertex_mem⟩)
    (hPsub : Psub.IsPath)
    (haPsub : (⟨a, haB⟩ : bridgeSet G M.cycle M.bridge) ∈
      Psub.support) :
    HasWheelWitness G := by
  classical
  have hKm₂ : G.Adj K.vertex O.middle₂ := by
    have hmem : O.middle₂ ∈
        G.neighborFinset K.vertex ∩ M.cycle.verts (G := G) := by
      rw [QK.neighbors_eq, hpK]
      simp
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hmem).1
  let inc : G.induce (bridgeSet G M.cycle M.bridge) →g G :=
    (SimpleGraph.Embedding.induce
      (G := G) (s := bridgeSet G M.cycle M.bridge)).toHom
  let P : G.Walk L.vertex K.vertex := Psub.map inc
  have hP : P.IsPath := hPsub.map Subtype.val_injective
  have haP : a ∈ P.support := by
    change a ∈ (Psub.map inc).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨⟨a, haB⟩, haPsub, rfl⟩
  have hPout : ∀ y, y ∈ P.support →
      y ∉ M.cycle.vSet (G := G) := by
    intro y hy
    change y ∈ (Psub.map inc).support at hy
    rw [SimpleGraph.Walk.support_map] at hy
    obtain ⟨yb, -, rfl⟩ := List.mem_map.mp hy
    exact (M.mem_bridge_iff_not_mem_cycle G yb.1).1 yb.2
  have hLout : L.vertex ∉ M.cycle.vSet (G := G) :=
    (M.mem_bridge_iff_not_mem_cycle G L.vertex).1 L.vertex_mem
  have hKout : K.vertex ∉ M.cycle.vSet (G := G) :=
    (M.mem_bridge_iff_not_mem_cycle G K.vertex).1 K.vertex_mem
  have hKne_m₂ : K.vertex ≠ O.middle₂ :=
    fun h => hKout (h ▸ O.middle₂_mem)
  have hKne_left : K.vertex ≠ R.left :=
    fun h => hKout (h ▸ R.left_mem)
  have hLne_m₂ : L.vertex ≠ O.middle₂ :=
    fun h => hLout (h ▸ O.middle₂_mem)
  have hLne_left : L.vertex ≠ R.left :=
    fun h => hLout (h ▸ R.left_mem)
  let Q : G.Walk K.vertex L.vertex :=
    .cons hKm₂
      (.cons O.adj_left_middle₂.symm
        (.cons R.adj_left.symm .nil))
  have hQ : Q.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [Q, hne, hne.symm, O.left_ne_middle₂,
      O.left_ne_middle₂.symm, hKne_m₂, hKne_left,
      hLne_m₂, hLne_m₂.symm, hLne_left, hLne_left.symm]
  have hdis : List.Disjoint P.support.tail Q.support.tail := by
    rw [List.disjoint_left]
    intro y hyP hyQ
    have hyQ' : y = O.middle₂ ∨ y = R.left ∨ y = L.vertex := by
      simpa [Q] using hyQ
    have hyPfull : y ∈ P.support := List.mem_of_mem_tail hyP
    rcases hyQ' with rfl | rfl | rfl
    · exact hPout O.middle₂ hyPfull O.middle₂_mem
    · exact hPout R.left hyPfull R.left_mem
    · have hnodup := hP.support_nodup
      rw [P.support_eq_cons] at hnodup
      exact (List.nodup_cons.mp hnodup).1 hyP
  have hkP : O.middle₁ ∉ P.support := by
    intro h
    exact hPout O.middle₁ h O.middle₁_mem
  have hm₁neK : O.middle₁ ≠ K.vertex := by
    intro h
    exact hKout (h ▸ O.middle₁_mem)
  have hm₁neL : O.middle₁ ≠ L.vertex := by
    intro h
    exact hLout (h ▸ O.middle₁_mem)
  have hkQ : O.middle₁ ∉ Q.support := by
    simp [Q, O.middle_ne, O.middle_ne.symm,
      O.left_ne_middle₁, O.left_ne_middle₁.symm,
      hm₁neK, hm₁neL]
  have ha_ne_left : a ≠ R.left := by
    intro h
    exact (M.mem_bridge_iff_not_mem_cycle G a).1 haB (h ▸ R.left_mem)
  exact hasWheelWitness_of_path_append G P Q hP hQ hdis
    (Or.inr (by simp [Q])) hkP hkQ
    O.adj_left_middle₁.symm hma (by
      have hKm₁ : G.Adj K.vertex O.middle₁ := by
        have hmem : O.middle₁ ∈
            G.neighborFinset K.vertex ∩ M.cycle.verts (G := G) := by
          rw [QK.neighbors_eq, hpK]
          simp
        simpa only [SimpleGraph.mem_neighborFinset] using
          (Finset.mem_inter.mp hmem).1
      exact hKm₁.symm)
    (Or.inr (by simp [Q])) (Or.inl haP) (Or.inl P.end_mem_support)
    ha_ne_left.symm (fun h => hKout (h ▸ R.left_mem)) haK

/-- The nominal high-attachment C4 terminal cannot survive in a wheel-free
acyclic bridge.  Start at its distinguished bridge leaf and take a longest
bridge-tree path constrained to pass through an off-rim neighbour of the
first middle vertex.  Its other endpoint is another bridge leaf.  If that
leaf repeats the original attachment pair, the path closes to a rim on which
the middle vertex has three spokes.  Otherwise it uses the opposite pair,
and the two degree-three middle vertices are false twins. -/
theorem falseTwins_of_c4HighAttachment_of_bridge_isAcyclic
    {x : V} (X : LexMaxCycleCertificate G ({x} : Set V) x)
    (hno : ¬HasWheelWitness G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hacyc : (G.induce
      (bridgeSet G X.cycle X.bridge)).IsAcyclic)
    (D : C4HighAttachmentData X) :
    ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 := by
  classical
  let M : MaxCycleCertificate G := X.toMaxCycleCertificate
  let B : Set V := bridgeSet G M.cycle M.bridge
  have hLm₁ : ¬G.Adj D.leaf.vertex D.opposite.middle₁ :=
    D.pair.not_adj_vertex_of_cycle_mem D.opposite.middle₁_mem
      D.opposite.left_ne_middle₁.symm
      D.opposite.right_ne_middle₁.symm
  obtain ⟨a, haB, hm₁a⟩ :=
    M.exists_adj_bridge G D.opposite.middle₁_mem
  have hLa : D.leaf.vertex ≠ a := by
    intro h
    apply hLm₁
    rw [h]
    exact hm₁a.symm
  let lB : B := ⟨D.leaf.vertex, by
    simpa only [B, M] using D.leaf.vertex_mem⟩
  let aB : B := ⟨a, by simpa only [B] using haB⟩
  have hlaB : lB ≠ aB := by
    intro h
    exact hLa (congrArg Subtype.val h)
  have htree : (G.induce B).IsTree :=
    { connected := by
        simpa only [B] using M.bridge_connected G
      isAcyclic := by
        simpa only [B, M] using hacyc }
  have hlDegree : (G.induce B).degree lB = 1 := by
    simpa only [B, lB, M] using D.leaf.bridge_degree_eq_one
  obtain ⟨kB, P, hP, haP, hlk, hkDegree⟩ :=
    htree.exists_other_leaf_path_through hlDegree hlaB
  obtain ⟨K, hKvertex⟩ :=
    M.bridgeLeafData_of_degree_eq_one hno hmin kB.2 (by
      simpa only [B] using hkDegree)
  let kB' : B := ⟨K.vertex, by
    simpa only [B] using K.vertex_mem⟩
  have hkk' : kB = kB' := by
    apply Subtype.ext
    exact hKvertex.symm
  let P' : (G.induce B).Walk lB kB' := P.copy rfl hkk'
  have hP' : P'.IsPath := by
    simpa only [P', SimpleGraph.Walk.isPath_copy] using hP
  have haP' : aB ∈ P'.support := by
    simpa only [P', SimpleGraph.Walk.support_copy] using haP
  have hLK : D.leaf.vertex ≠ K.vertex := by
    intro h
    apply hlk
    apply Subtype.ext
    exact h.trans hKvertex
  obtain ⟨QK⟩ := K.exists_leafRimPair
  have hQKnotAdj : ¬G.Adj QK.left QK.right := by
    intro hadj
    exact hno (QK.hasWheelWitness_of_adj hadj)
  have hpair := D.opposite.classify_nonadjacent_pair
    QK.left_mem QK.right_mem QK.ne hQKnotAdj
  rcases hpair with hsame | hopp
  · have hw := hasWheelWitness_of_leaf_path_same_attachments
      D.pair QK D.opposite rfl hsame hLK haB hm₁a P' hP' (by
        simpa only [aB, B, M] using haP')
    exact (hno hw).elim
  · exact ⟨D.opposite.middle₁, D.opposite.middle₂,
      middle_falseTwins_of_opposite_leaf_attachments
        D.pair QK D.opposite hopp
          D.middle₁_degree D.middle₂_degree,
      D.middle₁_degree⟩

/-- Primary target maximality forces a short rim in the acyclic-bridge
branch.  This is the complete large-rim part of the published N6 exchange. -/
theorem cycle_length_le_four_of_bridge_isAcyclic
    {x : V} (X : LexMaxCycleCertificate G ({x} : Set V) x)
    (hno : ¬HasWheelWitness G) (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hacyc : (G.induce
      (bridgeSet G X.cycle X.bridge)).IsAcyclic) :
    X.cycle.length (G := G) ≤ 4 := by
  classical
  let M : MaxCycleCertificate G := X.toMaxCycleCertificate
  by_contra hnot
  have hfive : 5 ≤ M.cycle.length (G := G) := by
    change ¬M.cycle.length (G := G) ≤ 4 at hnot
    omega
  have hxout : x ∉ M.cycle.vSet (G := G) := by
    have hxmem : x ∈ ({x} : Set V) := Set.mem_singleton x
    exact Nonseparating.IsAdmissibleCycle.not_mem_cycle
      (G := G) X.admissible hxmem
  have hxB : x ∈ bridgeSet G M.cycle M.bridge :=
    (M.mem_bridge_iff_not_mem_cycle G x).2 hxout
  have htwo : 2 ≤ (bridgeSet G M.cycle M.bridge).ncard :=
    M.two_le_ncard_bridge_of_noWheel G hno hmin
  obtain ⟨T⟩ := M.exists_twoBridgeLeafData_of_bridge_isAcyclic
    hno hmin htwo (by simpa only [M] using hacyc)
  obtain ⟨L, hxL⟩ := T.exists_leaf_avoiding x
  obtain ⟨R⟩ := L.exists_leafRimPair
  obtain ⟨A, hA, hAcycle, z₁, z₂, hz₁₂,
      hz₁C, hz₂C, hz₁A, hz₂A, hz₁u, hz₁v, hz₂u, hz₂v⟩ :=
    Erdos916.Cycle.exists_arc_avoiding_two_of_five_le
      G M.cycle R.left_mem R.right_mem R.ne hfive
  have hxA : x ∉ A.support := by
    intro hx
    exact hxout (hAcycle x hx)
  obtain ⟨D, hDadm, hDsub⟩ :=
    R.exists_admissible_leaf_reroute A hA hAcycle hxL hxA
  have hDdisj : Disjoint (D.vSet (G := G))
      (bridgeSet G M.cycle M.bridge \ {L.vertex}) := by
    rw [Set.disjoint_left]
    intro z hzD hzB
    rcases hDsub hzD with hzL | hzA'
    · exact hzB.2 (by simpa only [Set.mem_singleton_iff] using hzL)
    · exact (mem_bridge_imp_not_mem_cycle
        (G := G) M.cycle M.bridge hzB.1) (hAcycle z hzA')
  have hz₁L : z₁ ≠ L.vertex := by
    intro h
    subst z₁
    exact (mem_bridge_imp_not_mem_cycle
      (G := G) M.cycle M.bridge L.vertex_mem) hz₁C
  have hz₂L : z₂ ≠ L.vertex := by
    intro h
    subst z₂
    exact (mem_bridge_imp_not_mem_cycle
      (G := G) M.cycle M.bridge L.vertex_mem) hz₂C
  have hz₁D : z₁ ∉ D.vSet (G := G) := by
    intro hz
    rcases hDsub hz with hzL | hzA'
    · exact hz₁L (Set.mem_singleton_iff.mp hzL)
    · exact hz₁A hzA'
  have hz₂D : z₂ ∉ D.vSet (G := G) := by
    intro hz
    rcases hDsub hz with hzL | hzA'
    · exact hz₂L (Set.mem_singleton_iff.mp hzL)
    · exact hz₂A hzA'
  obtain ⟨w₁, hw₁B, hz₁w₁⟩ := M.exists_adj_bridge G hz₁C
  obtain ⟨w₂, hw₂B, hz₂w₂⟩ := M.exists_adj_bridge G hz₂C
  have hw₁L : w₁ ≠ L.vertex := by
    intro h
    subst w₁
    have hzN : z₁ ∈
        G.neighborFinset L.vertex ∩ M.cycle.verts (G := G) :=
      Finset.mem_inter.mpr ⟨by simpa using hz₁w₁.symm,
        (M.cycle.mem_vSet_iff (G := G)).1 hz₁C⟩
    rw [R.neighbors_eq] at hzN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzN
    exact hzN.elim hz₁u hz₁v
  have hw₂L : w₂ ≠ L.vertex := by
    intro h
    subst w₂
    have hzN : z₂ ∈
        G.neighborFinset L.vertex ∩ M.cycle.verts (G := G) :=
      Finset.mem_inter.mpr ⟨by simpa using hz₂w₂.symm,
        (M.cycle.mem_vSet_iff (G := G)).1 hz₂C⟩
    rw [R.neighbors_eq] at hzN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzN
    exact hzN.elim hz₂u hz₂v
  have hw₁ : w₁ ∈ bridgeSet G M.cycle M.bridge \ {L.vertex} :=
    ⟨hw₁B, by simpa only [Set.mem_singleton_iff] using hw₁L⟩
  have hw₂ : w₂ ∈ bridgeSet G M.cycle M.bridge \ {L.vertex} :=
    ⟨hw₂B, by simpa only [Set.mem_singleton_iff] using hw₂L⟩
  have hbridgeDelete :
      (G.induce (bridgeSet G M.cycle M.bridge \ {L.vertex})).Connected := by
    let B : Set V := bridgeSet G M.cycle M.bridge
    let lB : B := ⟨L.vertex, by simpa only [B] using L.vertex_mem⟩
    let e := InducedEdgeExchange.sdiffSingletonIso G B lB
    apply e.connected_iff.mpr
    apply (M.bridge_connected G).induce_compl_singleton_of_degree_eq_one
    simpa only [B, lB] using L.bridge_degree_eq_one
  have hlt := L.targetCard_lt_of_reroute_omits_two
    hxB hxL hbridgeDelete D hDadm.1 hDdisj
    hz₁C hz₂C hz₁D hz₂D hz₁₂ hw₁ hw₂ hz₁w₁.symm hz₂w₂.symm
  have hle := X.target_max D hDadm
  exact (Nat.not_lt_of_ge hle) hlt

/-- In the no-wheel acyclic branch the short rim is in fact a four-cycle:
on a triangle the leaf's two rim neighbours are adjacent, which is the
shared-attachment wheel case. -/
theorem cycle_length_eq_four_of_bridge_isAcyclic
    {x : V} (X : LexMaxCycleCertificate G ({x} : Set V) x)
    (hno : ¬HasWheelWitness G) (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hacyc : (G.induce
      (bridgeSet G X.cycle X.bridge)).IsAcyclic) :
    X.cycle.length (G := G) = 4 := by
  let M : MaxCycleCertificate G := X.toMaxCycleCertificate
  have hle := X.cycle_length_le_four_of_bridge_isAcyclic hno hmin hacyc
  have hge : 3 ≤ X.cycle.length (G := G) := X.cycle.len_ge_three
  have hthree_or_four :
      X.cycle.length (G := G) = 3 ∨ X.cycle.length (G := G) = 4 := by
    omega
  rcases hthree_or_four with hthree | hfour
  · have htwo : 2 ≤ (bridgeSet G M.cycle M.bridge).ncard :=
      M.two_le_ncard_bridge_of_noWheel G hno hmin
    obtain ⟨Tleaf⟩ := M.exists_twoBridgeLeafData_of_bridge_isAcyclic
      hno hmin htwo (by simpa only [M] using hacyc)
    obtain ⟨L, hxL⟩ := Tleaf.exists_leaf_avoiding x
    obtain ⟨R⟩ := L.exists_leafRimPair
    obtain ⟨Tri⟩ :=
      Erdos916.Cycle.triangleDisplay_of_length_eq_three G M.cycle (by
        simpa only [M] using hthree)
    have hadj : G.Adj R.left R.right :=
      Tri.adj_of_mem G
        ((M.cycle.mem_vSet_iff (G := G)).1 R.left_mem)
        ((M.cycle.mem_vSet_iff (G := G)).1 R.right_mem) R.ne
    exact (hno (R.hasWheelWitness_of_adj hadj)).elim
  · exact hfour

/-- Complete acyclic-bridge reduction through the edge-maximal C4 exchange,
leaving only the literal high-attachment N6 terminal. -/
theorem falseTwins_or_c4HighAttachment_of_bridge_isAcyclic
    {x : V} (X : LexMaxCycleCertificate G ({x} : Set V) x)
    (hno : ¬HasWheelWitness G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hacyc : (G.induce
      (bridgeSet G X.cycle X.bridge)).IsAcyclic) :
    (∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3) ∨
      Nonempty (C4HighAttachmentData X) := by
  let M : MaxCycleCertificate G := X.toMaxCycleCertificate
  have hxout : x ∉ M.cycle.vSet (G := G) := by
    exact Nonseparating.IsAdmissibleCycle.not_mem_cycle
      (G := G) X.admissible (Set.mem_singleton x)
  have hxB : x ∈ bridgeSet G M.cycle M.bridge :=
    (M.mem_bridge_iff_not_mem_cycle G x).2 hxout
  have htwo : 2 ≤ (bridgeSet G M.cycle M.bridge).ncard :=
    M.two_le_ncard_bridge_of_noWheel G hno hmin
  obtain ⟨Tleaf⟩ := M.exists_twoBridgeLeafData_of_bridge_isAcyclic
    hno hmin htwo (by simpa only [M] using hacyc)
  obtain ⟨L, hxL⟩ := Tleaf.exists_leaf_avoiding x
  obtain ⟨R⟩ := L.exists_leafRimPair
  have hnotAdj : ¬G.Adj R.left R.right := by
    intro hadj
    exact hno (R.hasWheelWitness_of_adj hadj)
  have hfour : M.cycle.length (G := G) = 4 := by
    simpa only [M] using
      X.cycle_length_eq_four_of_bridge_isAcyclic hno hmin hacyc
  obtain ⟨O⟩ := R.exists_oppositeFourRimData hfour hnotAdj
  have hmid := X.opposite_middle_degrees_eq_three L R O hnotAdj
    (by simpa only [M] using hxB) hxL hmin
  by_cases hl : G.degree R.left = 3
  · by_cases hr : G.degree R.right = 3
    · exact Or.inl ⟨R.left, R.right,
        attachment_falseTwins_of_degrees_eq_three L R O hl hr, hl⟩
    · exact Or.inr ⟨{
        leaf := L
        pair := R
        opposite := O
        root_ne_leaf := hxL
        attachments_not_adj := hnotAdj
        middle₁_degree := hmid.1
        middle₂_degree := hmid.2
        high_attachment := Or.inr (by
          have := hmin R.right
          omega) }⟩
  · exact Or.inr ⟨{
      leaf := L
      pair := R
      opposite := O
      root_ne_leaf := hxL
      attachments_not_adj := hnotAdj
      middle₁_degree := hmid.1
      middle₂_degree := hmid.2
      high_attachment := Or.inl (by
        have := hmin R.left
        omega) }⟩

/-- Ordinary false-twin terminal for the acyclic-bridge branch: a wheel-free
lexicographically maximal certificate has a degree-three false-twin pair.

This is directly consumable after `(2,3)`-circuit extraction.  For the
unconditional `K23Reduction` alternative one still has to prove that two
vertices in the common neighbourhood have degree three (or produce a wheel)
in the high-attachment subcase. -/
theorem exists_degree_three_falseTwins_of_bridge_isAcyclic
    {x : V} (X : LexMaxCycleCertificate G ({x} : Set V) x)
    (hno : ¬HasWheelWitness G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hacyc : (G.induce
      (bridgeSet G X.cycle X.bridge)).IsAcyclic) :
    ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 := by
  rcases X.falseTwins_or_c4HighAttachment_of_bridge_isAcyclic
      hno hmin hacyc with htwins | hhigh
  · exact htwins
  · obtain ⟨D⟩ := hhigh
    exact X.falseTwins_of_c4HighAttachment_of_bridge_isAcyclic
      hno hmin hacyc D

end LexMaxCycleCertificate

end Erdos916
