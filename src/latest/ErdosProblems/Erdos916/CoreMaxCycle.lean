/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.Induction
import ErdosProblems.Erdos916.Nonseparating

/-!
# The maximum-chordless-cycle reduction for Erdős Problem 916

This file packages the part of the Thomassen--Toft structural argument that is
already supplied by the Bondy--Vince maximum-cycle development in `Erdos751`.
For a vertex-two-connected graph of minimum degree at least three there is a
chordless cycle `C` and a component `B` of its complement such that `B` is the
only component and every vertex of `C` has a neighbour in `B`.

The elementary lemmas below also identify the immediate wheel case: if one
vertex of `B` sees three vertices of `C`, then `C` itself is the required rim.
Consequently, in the no-wheel branch every outside vertex has at most two
neighbours on the chosen cycle.
-/

namespace Erdos916

open SimpleGraph
open Erdos751.BV

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The concrete output of the Bondy--Vince maximum-chordless-cycle argument. -/
structure MaxCycleCertificate where
  cycle : Cycle (G := G)
  bridge : Bridge (G := G) cycle
  chordless : cycle.IsChordless (G := G)
  uniqueBridge : Subsingleton (Bridge (G := G) cycle)
  attach_eq : attachSet (G := G) cycle bridge = cycle.vSet (G := G)

/-- The hypotheses used by the density induction imply the Bondy--Vince
vertex-two-connected interface. -/
theorem vertexTwoConnected_of_induction_hypotheses
    (hconn : G.Connected)
    (hdelete : ∀ c : V, (G.induce (fun w : V => w ≠ c)).Connected) :
    VertexTwoConnected (G := G) :=
  ⟨hconn, hdelete⟩

/-- A finite vertex-two-connected graph of minimum degree at least three has
a maximum chordless cycle whose complement consists of one bridge and whose
bridge attaches to every cycle vertex. -/
theorem exists_maxCycleCertificate
    (hcard : 4 ≤ Fintype.card V)
    (h2 : VertexTwoConnected (G := G))
    (hmin : MinDegreeGE3 (G := G)) :
    Nonempty (MaxCycleCertificate G) := by
  classical
  have hch : ∃ C : Cycle (G := G), C.IsChordless (G := G) :=
    exists_chordless_cycle_of_h2_hδ3 (G := G) h2 hmin hcard
  have hne : Nonempty (Bridge (G := G) (Cmax (G := G) hch)) :=
    nonempty_bridge_Cmax_of_hδ3 (G := G) hmin hcard hch
  have hkey := BVDelta3_key_core (G := G) h2 hmin hcard hch hne
  exact ⟨
    { cycle := Cmax (G := G) hch
      bridge := Bmax (G := G) hch hne
      chordless := Cmax_isChordless (G := G) hch
      uniqueBridge := hkey.1
      attach_eq := hkey.2 }⟩

/-- Membership in the vertex set of a paper cycle is the same as membership
in the support of its underlying closed walk. -/
theorem mem_cycle_vSet_iff_mem_support (C : Cycle (G := G)) (v : V) :
    v ∈ C.vSet (G := G) ↔ v ∈ C.walk.support := by
  rw [C.mem_vSet_iff]
  simp only [Cycle.verts, List.mem_toFinset]

/-- A simple closed walk has as many distinct support vertices as edges. -/
theorem card_cycle_verts_eq_length (C : Cycle (G := G)) :
    (C.verts (G := G)).card = C.walk.length := by
  classical
  have htail : C.walk.support.tail.Nodup :=
    (Walk.isCycle_def C.walk).mp C.isCycle |>.2.2
  have hbaseTail : C.base ∈ C.walk.support.tail :=
    C.walk.end_mem_tail_support C.isCycle.not_nil
  have hsupport : C.walk.support = C.base :: C.walk.support.tail := by
    exact C.walk.cons_tail_support.symm
  rw [Cycle.verts, hsupport, List.toFinset_cons,
    Finset.insert_eq_of_mem (by simpa using hbaseTail)]
  rw [List.toFinset_card_of_nodup htail]
  have hlen := C.walk.length_support
  rw [hsupport] at hlen
  simp only [List.length_cons] at hlen
  omega

/-- The ambient graph induced by the vertex set of a cycle is connected. -/
theorem cycle_induce_vSet_connected (C : Cycle (G := G)) :
    (G.induce (C.vSet (G := G))).Connected := by
  have hwalk := C.walk.connected_induce_support
  have hset : C.vSet (G := G) = {v : V | v ∈ C.walk.support} := by
    ext v
    exact mem_cycle_vSet_iff_mem_support G C v
  rw [hset]
  exact hwalk

/-- If an ambient cycle walk is supported in `W`, then `W` contains a
chordless ambient cycle.  This packages the induced-subgraph extraction and
the subsequent map back to `G` used in the Bondy--Vince compression proof. -/
theorem exists_chordless_cycle_vSet_subset_of_isCycle
    {x : V} (P : G.Walk x x) (hP : P.IsCycle) (W : Set V)
    (hW : ∀ v : V, v ∈ P.support → v ∈ W) :
    ∃ C : Cycle (G := G),
      C.IsChordless (G := G) ∧ C.vSet (G := G) ⊆ W := by
  classical
  obtain ⟨hxW, _, Psub, hmap⟩ :=
    exists_walkSubtype (G := G) (p := P) hW
  let f := SimpleGraph.Embedding.induce (G := G) (s := W)
  have hPsubCycle : Psub.IsCycle := by
    have hinj : Function.Injective f.toHom := by
      intro a b hab
      exact f.injective hab
    have hmapped : (Psub.map f.toHom).IsCycle := by
      simpa [f, hmap] using hP
    exact (SimpleGraph.Walk.isCycle_map_iff_of_injective
      (p := Psub) (f := f.toHom) hinj).mp hmapped
  have hcycleInduced : ∃ C : Cycle (G := G.induce W), True := by
    refine ⟨
      { base := ⟨x, hxW⟩
        walk := Psub
        isCycle := hPsubCycle
        len_ge_three := by simpa using hPsubCycle.three_le_length }, trivial⟩
  obtain ⟨C, hCchordless⟩ :=
    exists_chordless_cycle_of_exists_cycle (G := G.induce W) hcycleInduced
  let D : Cycle (G := G) :=
    { base := f C.base
      walk := C.walk.map f.toHom
      isCycle := by
        have hinj : Function.Injective f.toHom := by
          intro a b hab
          exact f.injective hab
        exact (SimpleGraph.Walk.isCycle_map_iff_of_injective
          (p := C.walk) (f := f.toHom) hinj).mpr C.isCycle
      len_ge_three := by simpa using C.len_ge_three }
  have hDsupport : ∀ v : V, v ∈ D.walk.support → v ∈ W := by
    intro v hv
    have hv' : v ∈ C.walk.support.map f.toHom := by
      simpa [D, SimpleGraph.Walk.support_map] using hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv'
    exact a.property
  have hDchordless : D.IsChordless (G := G) := by
    intro hchord
    apply hCchordless
    obtain ⟨v, w, hvD, hwD, hvw, hnot⟩ := hchord
    have hvSupport : v ∈ D.walk.support := by
      have hvVerts : v ∈ D.verts (G := G) :=
        (D.mem_vSet_iff (G := G)).mp hvD
      simpa [Cycle.verts, D] using hvVerts
    have hwSupport : w ∈ D.walk.support := by
      have hwVerts : w ∈ D.verts (G := G) :=
        (D.mem_vSet_iff (G := G)).mp hwD
      simpa [Cycle.verts, D] using hwVerts
    let v' : W := ⟨v, hDsupport v hvSupport⟩
    let w' : W := ⟨w, hDsupport w hwSupport⟩
    refine ⟨v', w', ?_, ?_, ?_, ?_⟩
    · have hvMap : v ∈ C.walk.support.map f.toHom := by
        simpa [D, SimpleGraph.Walk.support_map] using hvSupport
      obtain ⟨a, ha, hfa⟩ := List.mem_map.mp hvMap
      have haeq : a = v' := by
        apply Subtype.ext
        simpa [f, v'] using hfa
      apply (C.mem_vSet_iff (G := G.induce W)).mpr
      simpa [Cycle.verts, haeq] using ha
    · have hwMap : w ∈ C.walk.support.map f.toHom := by
        simpa [D, SimpleGraph.Walk.support_map] using hwSupport
      obtain ⟨a, ha, hfa⟩ := List.mem_map.mp hwMap
      have haeq : a = w' := by
        apply Subtype.ext
        simpa [f, w'] using hfa
      apply (C.mem_vSet_iff (G := G.induce W)).mpr
      simpa [Cycle.verts, haeq] using ha
    · simpa [v', w'] using hvw
    · intro hsub
      apply hnot
      have hmapAdj : (C.walk.toSubgraph.map f.toHom).Adj v w := by
        refine ⟨v', w', ?_, rfl, rfl⟩
        simpa [Cycle.toSubgraph] using hsub
      simpa [D, Cycle.toSubgraph, SimpleGraph.Walk.toSubgraph_map] using hmapAdj
  refine ⟨D, hDchordless, ?_⟩
  intro v hv
  apply hDsupport v
  have hvVerts : v ∈ D.verts (G := G) :=
    (D.mem_vSet_iff (G := G)).mp hv
  simpa [Cycle.verts, D] using hvVerts

/-- Two distinct attachments of a complementary component can be joined
through that component and closed along the one arc of `C` which avoids a
third cycle vertex.  The resulting cycle uses only vertices of `C` and of
the chosen component, and omits the third vertex. -/
theorem exists_cycle_in_bridge_union_avoiding
    (C : Cycle (G := G)) (K : Bridge (G := G) C)
    {x y z : V} (hxy : x ≠ y)
    (hxK : x ∈ attachSet (G := G) C K)
    (hyK : y ∈ attachSet (G := G) C K)
    (hzC : z ∈ C.vSet (G := G)) (hzx : z ≠ x) (hzy : z ≠ y) :
    ∃ D : Cycle (G := G),
      D.IsChordless (G := G) ∧ z ∉ D.vSet (G := G) ∧
        D.vSet (G := G) ⊆
          C.vSet (G := G) ∪ bridgeSet (G := G) C K := by
  classical
  obtain ⟨Pxy, hPxyPath, hPxySupp, ⟨wK, hwK, hEdgeXw⟩⟩ :=
    exists_path_between_attach (G := G) (C := C) (K := K) hxK hyK hxy
  have hPxyOut :
      ∀ v : V, v ∈ Pxy.support → v ≠ x → v ≠ y →
        v ∉ C.vSet (G := G) := by
    intro v hv hvx hvy
    rcases hPxySupp v hv with rfl | rfl | hvK
    · exact (hvx rfl).elim
    · exact (hvy rfl).elim
    · exact mem_bridge_imp_not_mem_cycle (G := G) C K hvK
  have hxC : x ∈ C.vSet (G := G) := hxK.1
  have hyC : y ∈ C.vSet (G := G) := hyK.1
  have hxSupport : x ∈ C.walk.support := by
    have hxVerts : x ∈ C.verts (G := G) :=
      (C.mem_vSet_iff (G := G)).mp hxC
    simpa [Cycle.verts] using hxVerts
  let r := C.walk.rotate x hxSupport
  have hrCycle : r.IsCycle := C.isCycle.rotate hxSupport
  have hySupport : y ∈ r.support := by
    have hyOld : y ∈ C.walk.support := by
      have hyVerts : y ∈ C.verts (G := G) :=
        (C.mem_vSet_iff (G := G)).mp hyC
      simpa [Cycle.verts] using hyVerts
    have hySub : y ∈ C.walk.toSubgraph.verts := by
      simpa only [SimpleGraph.Walk.mem_verts_toSubgraph] using hyOld
    have : y ∈ r.toSubgraph.verts := by
      simpa [r, SimpleGraph.Walk.toSubgraph_rotate] using hySub
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
    have := SimpleGraph.Walk.take_spec (p := r) (h := hySupport)
    simpa [a1] using this
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
        simpa [r, SimpleGraph.Walk.toSubgraph_rotate] using hvSub
      simpa only [SimpleGraph.Walk.mem_verts_toSubgraph] using this
    apply (C.mem_vSet_iff (G := G)).mpr
    simpa [Cycle.verts] using hvOld
  have ha2Cycle : ∀ v : V, v ∈ a2.support → v ∈ C.vSet (G := G) := by
    intro v hv
    have hvdrop : v ∈ (r.dropUntil y hySupport).support := by
      simpa [a2, SimpleGraph.Walk.support_reverse] using hv
    have hvr : v ∈ r.support :=
      SimpleGraph.Walk.support_dropUntil_subset_support _ _ hvdrop
    have hvOld : v ∈ C.walk.support := by
      have hvSub : v ∈ r.toSubgraph.verts := by
        simpa only [SimpleGraph.Walk.mem_verts_toSubgraph] using hvr
      have : v ∈ C.walk.toSubgraph.verts := by
        simpa [r, SimpleGraph.Walk.toSubgraph_rotate] using hvSub
      simpa only [SimpleGraph.Walk.mem_verts_toSubgraph] using this
    apply (C.mem_vSet_iff (G := G)).mpr
    simpa [Cycle.verts] using hvOld
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
        simpa [a1] using
          (SimpleGraph.Walk.mem_support_iff (p := a1) (w := z)).mp hz1
      exact this.resolve_left hzx
    have hzTail2 : z ∈ (r.dropUntil y hySupport).support.tail := by
      have hzdrop : z ∈ (r.dropUntil y hySupport).support := by
        simpa [a2, SimpleGraph.Walk.support_reverse] using hz2
      have : z = y ∨ z ∈ (r.dropUntil y hySupport).support.tail := by
        simpa using
          (SimpleGraph.Walk.mem_support_iff
            (p := r.dropUntil y hySupport) (w := z)).mp hzdrop
      exact this.resolve_left hzy
    exact (List.disjoint_left.mp hdis) hzTail1 hzTail2
  let A : G.Walk x y := if hz1 : z ∈ a1.support then a2 else a1
  have hAPath : A.IsPath := by
    by_cases hz1 : z ∈ a1.support
    · simp [A, hz1, ha2Path]
    · simp [A, hz1, ha1Path]
  have hACycle : ∀ v : V, v ∈ A.support → v ∈ C.vSet (G := G) := by
    intro v hv
    by_cases hz1 : z ∈ a1.support
    · exact ha2Cycle v (by simpa [A, hz1] using hv)
    · exact ha1Cycle v (by simpa [A, hz1] using hv)
  have hzNotA : z ∉ A.support := by
    by_cases hz1 : z ∈ a1.support
    · simpa [A, hz1] using hzNotA2OfA1 hz1
    · simpa [A, hz1]
  let P := A.append Pxy.reverse
  have hrevPath : Pxy.reverse.IsPath := hPxyPath.reverse
  have hxyNotEdge : s(x, y) ∉ Pxy.edges := by
    intro hxyEdge
    cases Pxy with
    | nil => exact hxy rfl
    | @cons _ v _ hadj pTail =>
        have hxNotTail : x ∉ pTail.support := by
          have hnodup : (SimpleGraph.Walk.cons hadj pTail).support.Nodup :=
            hPxyPath.support_nodup
          simpa [SimpleGraph.Walk.support_cons] using
            (List.nodup_cons.mp (by simpa [SimpleGraph.Walk.support_cons] using hnodup)).1
        have hXw : s(x, wK) ∈ s(x, v) :: pTail.edges := by
          simpa using hEdgeXw
        have hXy : s(x, y) ∈ s(x, v) :: pTail.edges := by
          simpa using hxyEdge
        have hhead : s(x, wK) = s(x, v) := by
          rcases List.mem_cons.mp hXw with heq | htail
          · exact heq
          · exact (hxNotTail
              (pTail.fst_mem_support_of_mem_edges (by simpa using htail))).elim
        rcases List.mem_cons.mp hXy with heq | htail
        · have heq' : s(x, y) = s(x, wK) := by simpa [hhead] using heq
          have hwOut : wK ∉ C.vSet (G := G) :=
            mem_bridge_imp_not_mem_cycle (G := G) C K hwK
          rcases (Sym2.eq_iff.mp heq') with h | h
          · exact hwOut (by simpa [h.2] using hyC)
          · exact hwOut (by simpa [h.1] using hxC)
        · exact (hxNotTail
            (pTail.fst_mem_support_of_mem_edges (by simpa using htail))).elim
  have htailDisjoint :
      List.Disjoint A.support.tail Pxy.reverse.support.tail := by
    refine List.disjoint_left.mpr ?_
    intro v hvA hvP
    have hvC : v ∈ C.vSet (G := G) :=
      hACycle v (List.mem_of_mem_tail hvA)
    have hvPxy : v ∈ Pxy.support := by
      have : v ∈ Pxy.reverse.support := List.mem_of_mem_tail hvP
      simpa [SimpleGraph.Walk.support_reverse] using this
    have hxNotTail : x ∉ A.support.tail := by
      have hnodup := hAPath.support_nodup
      rw [(SimpleGraph.Walk.cons_tail_support (p := A)).symm] at hnodup
      exact (List.nodup_cons.mp hnodup).1
    have hyNotTail : y ∉ Pxy.reverse.support.tail := by
      have hnodup := hrevPath.support_nodup
      rw [(SimpleGraph.Walk.cons_tail_support (p := Pxy.reverse)).symm] at hnodup
      exact (List.nodup_cons.mp hnodup).1
    have hvx : v ≠ x := by
      intro h
      subst v
      exact hxNotTail hvA
    have hvy : v ≠ y := by
      intro h
      subst v
      exact hyNotTail hvP
    exact hPxyOut v hvPxy hvx hvy hvC
  have hPcycle : P.IsCycle := by
    have hedgeDisjoint : List.Disjoint A.edges Pxy.reverse.edges := by
      refine List.disjoint_left.mpr ?_
      intro e heA heP
      have heP' : e ∈ Pxy.edges := by
        simpa [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using heP
      rcases e with ⟨t, u⟩
      have htA : t ∈ A.support :=
        A.fst_mem_support_of_mem_edges (by simpa using heA)
      have huA : u ∈ A.support :=
        A.snd_mem_support_of_mem_edges (by simpa using heA)
      have htC : t ∈ C.vSet (G := G) := hACycle t htA
      have huC : u ∈ C.vSet (G := G) := hACycle u huA
      have htP : t ∈ Pxy.support :=
        Pxy.fst_mem_support_of_mem_edges (by simpa using heP')
      have huP : u ∈ Pxy.support :=
        Pxy.snd_mem_support_of_mem_edges (by simpa using heP')
      have htxy : t = x ∨ t = y := by
        by_contra h
        have htx : t ≠ x := fun h' => h (Or.inl h')
        have hty : t ≠ y := fun h' => h (Or.inr h')
        exact hPxyOut t htP htx hty htC
      have huxy : u = x ∨ u = y := by
        by_contra h
        have hux : u ≠ x := fun h' => h (Or.inl h')
        have huy : u ≠ y := fun h' => h (Or.inr h')
        exact hPxyOut u huP hux huy huC
      have htu : t ≠ u := by
        exact G.ne_of_adj (Pxy.adj_of_mem_edges (by simpa using heP'))
      have heq : s(t, u) = s(x, y) := by
        rcases htxy with rfl | rfl <;> rcases huxy with rfl | rfl
        · exact (htu rfl).elim
        · rfl
        · exact Sym2.eq_swap
        · exact (htu rfl).elim
      exact hxyNotEdge (by simpa [heq] using heP')
    have htrail : P.IsTrail := by
      have hnd : (A.edges ++ Pxy.reverse.edges).Nodup :=
        List.nodup_append'.mpr
          ⟨hAPath.isTrail.edges_nodup, hrevPath.isTrail.edges_nodup,
            hedgeDisjoint⟩
      simpa [P, SimpleGraph.Walk.isTrail_def,
        SimpleGraph.Walk.edges_append] using hnd
    have htail : P.support.tail.Nodup := by
      have hnd : (A.support.tail ++ Pxy.reverse.support.tail).Nodup :=
        List.nodup_append'.mpr
          ⟨hAPath.support_nodup.tail, hrevPath.support_nodup.tail,
            htailDisjoint⟩
      simpa [P, SimpleGraph.Walk.tail_support_append] using hnd
    have hnotNil : P ≠ SimpleGraph.Walk.nil := by
      intro hnil
      have hAnil : A.Nil :=
        (SimpleGraph.Walk.nil_append_iff.mp
          ((SimpleGraph.Walk.eq_nil_iff_nil.mp hnil))).1
      have hyMem : y ∈ A.support := A.end_mem_support
      have hyx : y = x := by
        simpa [SimpleGraph.Walk.nil_iff_support_eq.mp hAnil] using hyMem
      exact hxy hyx.symm
    exact (SimpleGraph.Walk.isCycle_def P).mpr ⟨htrail, hnotNil, htail⟩
  let W : Set V := fun v => v ∈ A.support ∨ v ∈ Pxy.support
  have hPW : ∀ v : V, v ∈ P.support → v ∈ W := by
    intro v hv
    have : v ∈ A.support ∨ v ∈ Pxy.reverse.support := by
      simpa [P, SimpleGraph.Walk.mem_support_append_iff] using hv
    rcases this with hv | hv
    · exact Or.inl hv
    · exact Or.inr (by
        simpa [SimpleGraph.Walk.support_reverse] using hv)
  obtain ⟨D, hDch, hDsubW⟩ :=
    exists_chordless_cycle_vSet_subset_of_isCycle G P hPcycle W hPW
  refine ⟨D, hDch, ?_, ?_⟩
  · intro hzD
    have hzW := hDsubW hzD
    rcases hzW with hzA | hzP
    · exact hzNotA hzA
    · exact hPxyOut z hzP hzx hzy hzC
  · intro v hvD
    rcases hDsubW hvD with hvA | hvP
    · exact Or.inl (hACycle v hvA)
    · rcases hPxySupp v hvP with rfl | rfl | hvK
      · exact Or.inl hxC
      · exact Or.inl hyC
      · exact Or.inr hvK

/-- In a chordless cycle, a cycle vertex has exactly its two cyclic
neighbours among the vertices of the cycle. -/
theorem card_neighbors_on_chordless_cycle_eq_two
    (C : Cycle (G := G)) (hch : C.IsChordless (G := G))
    {c : V} (hc : c ∈ C.vSet (G := G)) :
    (G.neighborFinset c ∩ C.verts (G := G)).card = 2 := by
  classical
  have hcSupport : c ∈ C.walk.support :=
    (mem_cycle_vSet_iff_mem_support G C c).mp hc
  have htwo : ((C.toSubgraph (G := G)).neighborSet c).ncard = 2 := by
    simpa only [Cycle.toSubgraph] using
      (C.isCycle.ncard_neighborSet_toSubgraph_eq_two
        (G := G) (h := hcSupport))
  have hsets :
      (↑(G.neighborFinset c ∩ C.verts (G := G)) : Set V) =
        (C.toSubgraph (G := G)).neighborSet c := by
    ext w
    constructor
    · intro hw
      have hwSet :
          w ∈ G.neighborSet c ∧ w ∈ (↑(C.verts (G := G)) : Set V) := by
        simpa only [Finset.coe_inter, SimpleGraph.coe_neighborFinset,
          Set.mem_inter_iff] using hw
      have hw' : G.Adj c w ∧ w ∈ C.vSet (G := G) := by
        exact ⟨(SimpleGraph.mem_neighborSet (G := G) c w).mp hwSet.1, hwSet.2⟩
      have hwSupport : w ∈ C.walk.support :=
        (mem_cycle_vSet_iff_mem_support G C w).mp hw'.2
      have hsubAdj : (C.toSubgraph (G := G)).Adj c w := by
        by_contra hn
        exact hch ⟨c, w, hc, hw'.2, hw'.1, hn⟩
      exact (SimpleGraph.Subgraph.mem_neighborSet
        (G' := C.toSubgraph (G := G)) c w).2 hsubAdj
    · intro hw
      have hsubAdj : (C.toSubgraph (G := G)).Adj c w :=
        (SimpleGraph.Subgraph.mem_neighborSet
          (G' := C.toSubgraph (G := G)) c w).1 hw
      have hAdj : G.Adj c w := (C.toSubgraph (G := G)).adj_sub hsubAdj
      have hwSupport : w ∈ C.walk.support := by
        have hwVerts : w ∈ (C.toSubgraph (G := G)).verts := hsubAdj.snd_mem
        simpa only [Cycle.toSubgraph, Walk.mem_verts_toSubgraph] using hwVerts
      have hwC : w ∈ C.verts (G := G) := by
        simpa only [Cycle.verts, List.mem_toFinset] using hwSupport
      simpa only [Finset.coe_inter, SimpleGraph.coe_neighborFinset,
        Set.mem_inter_iff, Cycle.vSet] using ⟨hAdj, hwC⟩
  have hcard :
      (↑(G.neighborFinset c ∩ C.verts (G := G)) : Set V).ncard = 2 := by
    rw [hsets]
    exact htwo
  simpa only [Set.ncard_coe_finset] using hcard

/-- Hence the neighbours of a cycle vertex off a chordless cycle account for
exactly its degree minus the two cyclic neighbours. -/
theorem card_neighbors_off_chordless_cycle
    (C : Cycle (G := G)) (hch : C.IsChordless (G := G))
    {c : V} (hc : c ∈ C.vSet (G := G)) :
    (G.neighborFinset c \ C.verts (G := G)).card + 2 = G.degree c := by
  have hsplit := Finset.card_sdiff_add_card_inter
    (G.neighborFinset c) (C.verts (G := G))
  have hin := card_neighbors_on_chordless_cycle_eq_two G C hch hc
  rw [hin, G.card_neighborFinset_eq_degree] at hsplit
  exact hsplit

namespace Nonseparating

/-- A two-connected graph of order at least two whose non-root vertices
have degree at least three contains an induced cycle avoiding the root.

Indeed, deleting the root leaves a connected graph.  Every remaining
vertex still has degree at least two, because deletion loses at most the
root itself as a neighbour.  The standard finite minimum-degree-two cycle
lemma then supplies a cycle in the deletion graph, which is mapped back and
shortened to a chordless ambient cycle. -/
theorem exists_admissible_cycle_singleton_of_vertexTwoConnected_minDegreeExcept
    (hcard : 2 ≤ Fintype.card V)
    (h2 : VertexTwoConnected (G := G)) {x₀ : V}
    (hdeg : ∀ v : V, v ≠ x₀ → 3 ≤ G.degree v) :
    ∃ C : Cycle (G := G), IsAdmissibleCycle G ({x₀} : Set V) C := by
  classical
  obtain ⟨y, hyx⟩ : ∃ y : V, y ≠ x₀ := by
    by_contra hno
    push Not at hno
    have hsub : Subsingleton V := ⟨fun a b => (hno a).trans (hno b).symm⟩
    have hle : Fintype.card V ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  have hconn : (G.induce (fun v : V => v ≠ x₀)).Connected := h2.2 x₀
  have hδ2 : MinDegreeGE2 (G := G.induce (fun v : V => v ≠ x₀)) := by
    intro v
    let N : Finset V :=
      G.neighborFinset v.1 ∩ Set.toFinset (fun w : V => w ≠ x₀)
    have hsub : G.neighborFinset v.1 ⊆ insert x₀ N := by
      intro w hw
      by_cases hwx : w = x₀
      · simp [hwx]
      · apply Finset.mem_insert_of_mem
        change w ∈ G.neighborFinset v.1 ∩ Set.toFinset (fun w : V => w ≠ x₀)
        exact Finset.mem_inter.mpr ⟨hw, Set.mem_toFinset.mpr hwx⟩
    have hcard : (G.neighborFinset v.1).card ≤ N.card + 1 :=
      (Finset.card_le_card hsub).trans (Finset.card_insert_le x₀ N)
    have hamb : 3 ≤ (G.neighborFinset v.1).card := by
      simpa only [G.card_neighborFinset_eq_degree] using hdeg v.1 v.2
    have htwo : 2 ≤ N.card := by omega
    have hmap := G.map_neighborFinset_induce
      (s := fun w : V => w ≠ x₀) v
    have hcardMap := congrArg Finset.card hmap
    rw [Finset.card_map] at hcardMap
    change 2 ≤ ((G.induce (fun w : V => w ≠ x₀)).neighborFinset v).card
    rw [hcardMap]
    exact htwo
  obtain ⟨Csub, -⟩ :=
    exists_cycle_of_connected_minDegreeGE2
      (G := G.induce (fun v : V => v ≠ x₀)) hconn hδ2 (by
        let y' : {v : V // v ≠ x₀} := ⟨y, hyx⟩
        have hydeg : 2 ≤ (G.induce (fun v : V => v ≠ x₀)).degree y' := hδ2 y'
        have hylt := (G.induce (fun v : V => v ≠ x₀)).degree_lt_card_verts y'
        omega)
  let f := SimpleGraph.Embedding.induce (G := G) (s := fun v : V => v ≠ x₀)
  let P : G.Walk (f Csub.base) (f Csub.base) := Csub.walk.map f.toHom
  have hP : P.IsCycle := Csub.isCycle.map f.injective
  have hPsupport : ∀ v : V, v ∈ P.support → v ∈ {v : V | v ≠ x₀} := by
    intro v hv
    have hv' : v ∈ Csub.walk.support.map f.toHom := by
      simpa only [P, SimpleGraph.Walk.support_map] using hv
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv'
    exact w.property
  obtain ⟨C, hCchordless, hCsub⟩ :=
    exists_chordless_cycle_vSet_subset_of_isCycle G P hP
      {v : V | v ≠ x₀} hPsupport
  refine ⟨C, hCchordless, Set.disjoint_left.mpr ?_⟩
  intro v hvC hvroot
  have hvx : v = x₀ := by simpa only [Set.mem_singleton_iff] using hvroot
  exact (hCsub hvC) hvx

/-- The strict-augmentation conclusion in the main (three-attachment) case
of Thomassen--Toft Lemma 2.  The component `B` contains the prescribed root,
`K` is another component with attachments `a,b`, and `z` is a third
attachment of `B`.  Replacing the appropriate `a`--`b` arc of `C` by a path
through `K` produces an admissible induced cycle whose rooted component
strictly contains the old one (it also contains `z`). -/
theorem exists_target_augmentation_of_third_attachment
    {S : Set V} (hS : (G.induce S).Connected) {x₀ : V} (hx₀S : x₀ ∈ S)
    {C : Cycle (G := G)} (hC : IsAdmissibleCycle G S C)
    (B K : Bridge (G := G) C)
    (hx₀B : x₀ ∈ bridgeSet (G := G) C B) (hKB : K ≠ B)
    {a b z : V} (hab : a ≠ b)
    (haK : a ∈ attachSet (G := G) C K)
    (hbK : b ∈ attachSet (G := G) C K)
    (hzB : z ∈ attachSet (G := G) C B)
    (hzab : z ∉ ({a, b} : Set V)) :
    ∃ D : Cycle (G := G), IsAdmissibleCycle G S D ∧
      targetCard G C x₀ < targetCard G D x₀ := by
  classical
  have hx₀out : x₀ ∉ C.vSet (G := G) :=
    IsAdmissibleCycle.not_mem_cycle (G := G) hC hx₀S
  have hBcomp :
      G.componentComplMk (K := C.vSet (G := G)) hx₀out = B := by
    exact (SimpleGraph.ComponentCompl.mem_supp_iff
      (G := G) (K := C.vSet (G := G)) (C := B) (v := x₀)).mp hx₀B |>.2
  have htargetB :
      targetSet G C x₀ = bridgeSet (G := G) C B := by
    rw [targetSet_eq_component G hx₀out]
    simpa only [bridgeSet, hBcomp]
  have hza : z ≠ a := by
    intro hza
    exact hzab (by simp [hza])
  have hzb : z ≠ b := by
    intro hzb
    exact hzab (by simp [hzb])
  obtain ⟨D, hDch, hzD, hDsub⟩ :=
    exists_cycle_in_bridge_union_avoiding G C K hab haK hbK hzB.1 hza hzb
  have hDBdisj :
      Disjoint (D.vSet (G := G)) (bridgeSet (G := G) C B) := by
    rw [Set.disjoint_left]
    intro v hvD hvB
    rcases hDsub hvD with hvC | hvK
    · exact (mem_bridge_imp_not_mem_cycle (G := G) C B hvB) hvC
    · have hdis :
          Disjoint (bridgeSet (G := G) C K)
            (bridgeSet (G := G) C B) :=
        disjoint_bridge_of_ne (G := G) (C := C) (K1 := K) (K2 := B) hKB
      exact Set.disjoint_left.mp hdis hvK hvB
  have hBconn :
      (G.induce (bridgeSet (G := G) C B)).Connected := by
    have htconn := targetSet_connected G hx₀out
    rw [htargetB] at htconn
    exact htconn
  have hBadm : IsAdmissibleCycle G (bridgeSet (G := G) C B) D :=
    ⟨hDch, hDBdisj⟩
  have hBsubNew :
      bridgeSet (G := G) C B ⊆ targetSet G D x₀ :=
    prescribed_subset_target G hBconn hBadm hx₀B
  have hSsubB : S ⊆ bridgeSet (G := G) C B := by
    intro v hvS
    have hvTarget := prescribed_subset_target G hS hC hx₀S hvS
    simpa only [htargetB] using hvTarget
  have hDSdisj : Disjoint (D.vSet (G := G)) S := by
    rw [Set.disjoint_left]
    intro v hvD hvS
    exact Set.disjoint_left.mp hDBdisj hvD (hSsubB hvS)
  have hDadm : IsAdmissibleCycle G S D := ⟨hDch, hDSdisj⟩
  have hx₀Dout : x₀ ∉ D.vSet (G := G) :=
    IsAdmissibleCycle.not_mem_cycle (G := G) hDadm hx₀S
  obtain ⟨bz, hbzB, hzbz⟩ := hzB.2
  have hbzNew : bz ∈ targetSet G D x₀ := hBsubNew hbzB
  have hzNew : z ∈ targetSet G D x₀ := by
    rw [targetSet_eq_component G hx₀Dout] at hbzNew ⊢
    exact ComponentCompl.mem_of_adj bz z hbzNew hzD hzbz.symm
  have htargetSub : targetSet G C x₀ ⊆ targetSet G D x₀ := by
    intro v hv
    apply hBsubNew
    simpa only [← htargetB] using hv
  have hzNotOld : z ∉ targetSet G C x₀ := by
    rw [htargetB]
    intro hzOld
    exact (mem_bridge_imp_not_mem_cycle (G := G) C B hzOld) hzB.1
  have hproper : targetSet G C x₀ ⊂ targetSet G D x₀ := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨htargetSub, ?_⟩
    intro heq
    exact hzNotOld (heq ▸ hzNew)
  refine ⟨D, hDadm, ?_⟩
  exact Set.ncard_lt_ncard hproper

/-- A convenient pointwise form of the preceding surgery.  If the rooted
component of a separating admissible cycle has at least three attachment
vertices, vertex-two-connectivity supplies a second component and two of its
attachments, and the third-attachment surgery strictly enlarges the target. -/
theorem exists_target_augmentation_of_three_attachments
    (h2 : VertexTwoConnected (G := G))
    {S : Set V} (hS : (G.induce S).Connected) {x₀ : V} (hx₀S : x₀ ∈ S)
    {C : Cycle (G := G)} (hC : IsAdmissibleCycle G S C)
    (hne : targetSet G C x₀ ≠ (C.vSet (G := G))ᶜ)
    (hthree : 3 ≤ (attachSet (G := G) C
      (G.componentComplMk
        (IsAdmissibleCycle.not_mem_cycle (G := G) hC hx₀S))).ncard) :
    ∃ D : Cycle (G := G), IsAdmissibleCycle G S D ∧
      targetCard G C x₀ < targetCard G D x₀ := by
  classical
  have hx₀out : x₀ ∉ C.vSet (G := G) :=
    IsAdmissibleCycle.not_mem_cycle (G := G) hC hx₀S
  have hdisc : ¬(G.induce (C.vSet (G := G))ᶜ).Connected := by
    intro hconn
    exact hne ((complement_connected_iff_target_eq G hx₀out).mp hconn)
  obtain ⟨y, hyout, hyTarget⟩ :=
    exists_outside_target_of_not_connected G hx₀out hdisc
  let B : Bridge (G := G) C := G.componentComplMk hx₀out
  let K : Bridge (G := G) C := G.componentComplMk hyout
  have hx₀B : x₀ ∈ bridgeSet (G := G) C B := by
    change x₀ ∈ (B : Set V)
    exact G.componentComplMk_mem hx₀out
  have hyK : y ∈ bridgeSet (G := G) C K := by
    change y ∈ (K : Set V)
    exact G.componentComplMk_mem hyout
  have hKB : K ≠ B := by
    intro hEq
    apply hyTarget
    rw [targetSet_eq_component G hx₀out]
    change y ∈ (B : Set V)
    simpa [hEq] using hyK
  obtain ⟨a, b, hab, haK, hbK⟩ := exists_two_attachments G h2 C K
  have hnotSubset :
      ¬attachSet (G := G) C B ⊆ ({a, b} : Set V) := by
    intro hsub
    have hcardle :
        (attachSet (G := G) C B).ncard ≤ ({a, b} : Set V).ncard :=
      Set.ncard_le_ncard hsub
    have hpairs : ({a, b} : Set V).ncard = 2 := by
      simp [hab]
    have hthree' : 3 ≤ (attachSet (G := G) C B).ncard := by
      simpa [B] using hthree
    rw [hpairs] at hcardle
    omega
  obtain ⟨z, hzB, hzab⟩ := Set.not_subset.mp hnotSubset
  exact exists_target_augmentation_of_third_attachment G hS hx₀S hC
    B K hx₀B hKB hab haK hbK hzB hzab

/-- The specialized Thomassen--Toft augmentation lemma needed for Problem
916.  Every admissible separating cycle can be replaced by one with a
strictly larger component containing `x₀`.  If that component has a third
attachment, the preceding compression applies directly.  Otherwise its two
attachments miss some cycle vertex `c`; the degree hypothesis gives an edge
from `c` into another component, whose second attachment supplies the same
compression with one of the original two attachments as the third vertex. -/
theorem targetAugmentationProperty_of_vertexTwoConnected_minDegreeExcept
    (h2 : VertexTwoConnected (G := G)) {x₀ : V}
    (hdeg : ∀ v : V, v ≠ x₀ → 3 ≤ G.degree v)
    {S : Set V} (hS : (G.induce S).Connected) (hx₀S : x₀ ∈ S)
    (_hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C) :
    TargetAugmentationProperty G S x₀ := by
  classical
  intro C hC hne
  have hx₀out : x₀ ∉ C.vSet (G := G) :=
    IsAdmissibleCycle.not_mem_cycle (G := G) hC hx₀S
  let B : Bridge (G := G) C := G.componentComplMk hx₀out
  have hx₀B : x₀ ∈ bridgeSet (G := G) C B := by
    change x₀ ∈ (B : Set V)
    exact G.componentComplMk_mem hx₀out
  obtain ⟨a, b, hab, haB, hbB⟩ := exists_two_attachments G h2 C B
  by_cases hBpair :
      attachSet (G := G) C B ⊆ ({a, b} : Set V)
  · have hvertsCard : 3 ≤ (C.verts (G := G)).card := by
      rw [card_cycle_verts_eq_length G C]
      exact C.len_ge_three
    have hvertsNotPair :
        ¬(↑(C.verts (G := G)) : Set V) ⊆ ({a, b} : Set V) := by
      intro hsub
      have hcardle :
          (↑(C.verts (G := G)) : Set V).ncard ≤
            ({a, b} : Set V).ncard :=
        Set.ncard_le_ncard hsub
      have hpairs : ({a, b} : Set V).ncard = 2 := by simp [hab]
      simp only [Set.ncard_coe_finset] at hcardle
      rw [hpairs] at hcardle
      omega
    obtain ⟨c, hcVerts, hcPair⟩ := Set.not_subset.mp hvertsNotPair
    have hcC : c ∈ C.vSet (G := G) :=
      (C.mem_vSet_iff (G := G)).mpr hcVerts
    have hcneX₀ : c ≠ x₀ := by
      intro h
      exact hx₀out (h ▸ hcC)
    have hcdeg : 3 ≤ G.degree c := hdeg c hcneX₀
    have hoff := card_neighbors_off_chordless_cycle G C hC.1 hcC
    have hoffPos :
        0 < (G.neighborFinset c \ C.verts (G := G)).card := by
      omega
    obtain ⟨v, hvOff⟩ := Finset.card_pos.mp hoffPos
    have hcv : G.Adj c v := by
      simpa using (Finset.mem_sdiff.mp hvOff).1
    have hvNotVerts : v ∉ C.verts (G := G) :=
      (Finset.mem_sdiff.mp hvOff).2
    have hvout : v ∉ C.vSet (G := G) := by
      intro hvC
      exact hvNotVerts ((C.mem_vSet_iff (G := G)).mp hvC)
    let K : Bridge (G := G) C := G.componentComplMk hvout
    have hvK : v ∈ bridgeSet (G := G) C K := by
      change v ∈ (K : Set V)
      exact G.componentComplMk_mem hvout
    have hcK : c ∈ attachSet (G := G) C K :=
      ⟨hcC, v, hvK, hcv⟩
    have hKB : K ≠ B := by
      intro hEq
      have hcB : c ∈ attachSet (G := G) C B := by
        simpa only [hEq] using hcK
      exact hcPair (hBpair hcB)
    obtain ⟨p, q, hpq, hpK, hqK⟩ := exists_two_attachments G h2 C K
    obtain ⟨d, hcd, hdK⟩ :
        ∃ d : V, c ≠ d ∧ d ∈ attachSet (G := G) C K := by
      by_cases hpc : p = c
      · refine ⟨q, ?_, hqK⟩
        intro hcq
        exact hpq (hpc.trans hcq)
      · exact ⟨p, (fun h ↦ hpc h.symm), hpK⟩
    have htargetPairNotSub :
        ¬({a, b} : Set V) ⊆ ({c, d} : Set V) := by
      intro hsub
      have haCD := hsub (by simp : a ∈ ({a, b} : Set V))
      have hbCD := hsub (by simp : b ∈ ({a, b} : Set V))
      have hca : c ≠ a := by
        intro h
        exact hcPair (by simp [h])
      have hcb : c ≠ b := by
        intro h
        exact hcPair (by simp [h])
      have had : a = d := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
          (haCD.resolve_left hca.symm)
      have hbd : b = d := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
          (hbCD.resolve_left hcb.symm)
      exact hab (had.trans hbd.symm)
    obtain ⟨z, hzPair, hzCD⟩ := Set.not_subset.mp htargetPairNotSub
    have hzB : z ∈ attachSet (G := G) C B := by
      rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff]
        using hzPair) with rfl | rfl
      · exact haB
      · exact hbB
    exact exists_target_augmentation_of_third_attachment G hS hx₀S hC
      B K hx₀B hKB hcd hcK hdK hzB hzCD
  · obtain ⟨z, hzB, hzPair⟩ := Set.not_subset.mp hBpair
    have hza : z ≠ a := by
      intro h
      exact hzPair (by simp [h])
    have hzb : z ≠ b := by
      intro h
      exact hzPair (by simp [h])
    have htripleSub :
        ({a, b, z} : Set V) ⊆ attachSet (G := G) C B := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · exact haB
      · exact hbB
      · exact hzB
    have hthree : 3 ≤ (attachSet (G := G) C B).ncard := by
      have hle := Set.ncard_le_ncard htripleSub
      have htriple : ({a, b, z} : Set V).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          intro h
          rcases h with hab' | haz
          · exact hab hab'
          · exact hza haz.symm)]
        rw [Set.ncard_insert_of_notMem (by
          simpa only [Set.mem_singleton_iff] using hzb.symm)]
        simp
      rw [htriple] at hle
      exact hle
    apply exists_target_augmentation_of_three_attachments G h2 hS hx₀S hC hne
    simpa [B] using hthree

/-- The requested `AlmostMinDegreeThree` interface is an immediate instance
of the slightly stronger fact above: the lower bound at the root itself is
not used because every admissible cycle avoids the root. -/
theorem targetAugmentationProperty_of_vertexTwoConnected_almostMinDegreeThree
    (h2 : VertexTwoConnected (G := G)) {x₀ : V}
    (hdeg : AlmostMinDegreeThree G x₀)
    {S : Set V} (hS : (G.induce S).Connected) (hx₀S : x₀ ∈ S)
    (hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C) :
    TargetAugmentationProperty G S x₀ :=
  targetAugmentationProperty_of_vertexTwoConnected_minDegreeExcept
    G h2 hdeg.2 hS hx₀S hseed

/-- Root-exception form of specialized Thomassen--Toft Lemma 2. -/
theorem exists_admissible_cycle_complement_connected_minDegreeExcept
    (h2 : VertexTwoConnected (G := G)) {x₀ : V}
    (hdeg : ∀ v : V, v ≠ x₀ → 3 ≤ G.degree v)
    {S : Set V} (hS : (G.induce S).Connected) (hx₀S : x₀ ∈ S)
    (hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C) :
    ∃ C : Cycle (G := G), IsAdmissibleCycle G S C ∧
      (G.induce (C.vSet (G := G))ᶜ).Connected := by
  let C := maximizingCycle G x₀ hseed
  have hC : IsAdmissibleCycle G S C := maximizingCycle_admissible G hseed
  have haug : TargetAugmentationProperty G S x₀ :=
    targetAugmentationProperty_of_vertexTwoConnected_minDegreeExcept
      G h2 hdeg hS hx₀S hseed
  refine ⟨C, hC, ?_⟩
  exact maximizingCycle_complement_connected_of_augmentation
    G hx₀S hseed haug

/-- Specialized Thomassen--Toft Lemma 2: under the stated hypotheses there
is an admissible induced cycle whose deletion leaves a connected graph. -/
theorem exists_admissible_cycle_complement_connected
    (h2 : VertexTwoConnected (G := G)) {x₀ : V}
    (hdeg : AlmostMinDegreeThree G x₀)
    {S : Set V} (hS : (G.induce S).Connected) (hx₀S : x₀ ∈ S)
    (hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C) :
    ∃ C : Cycle (G := G), IsAdmissibleCycle G S C ∧
      (G.induce (C.vSet (G := G))ᶜ).Connected := by
  exact exists_admissible_cycle_complement_connected_minDegreeExcept
    G h2 hdeg.2 hS hx₀S hseed

end Nonseparating

/-- A chordless cycle with connected nonempty complement and degree at least
three on its rim supplies every field of `MaxCycleCertificate`: the root
component is the unique bridge, and every rim vertex has an off-rim neighbour
in that bridge.  (The structure name records its original source, but none of
its fields asserts maximality.) -/
def maxCycleCertificate_of_complement_connected
    (C : Cycle (G := G)) (hch : C.IsChordless (G := G))
    (hconn : (G.induce (C.vSet (G := G))ᶜ).Connected)
    {x₀ : V} (hx₀out : x₀ ∉ C.vSet (G := G))
    (hrimdeg : ∀ c : V, c ∈ C.vSet (G := G) → 3 ≤ G.degree c) :
    MaxCycleCertificate G := by
  classical
  let B : Bridge (G := G) C := G.componentComplMk hx₀out
  have htargetAll :
      Nonseparating.targetSet G C x₀ = (C.vSet (G := G))ᶜ :=
    (Nonseparating.complement_connected_iff_target_eq G hx₀out).mp hconn
  have hbridgeEq (K : Bridge (G := G) C) : K = B := by
    obtain ⟨v, hvK'⟩ := ComponentCompl.nonempty (C := K)
    have hvK : v ∈ bridgeSet (G := G) C K := by
      simpa only [bridgeSet] using hvK'
    have hvout : v ∉ C.vSet (G := G) :=
      mem_bridge_imp_not_mem_cycle (G := G) C K hvK
    have hvTarget : v ∈ Nonseparating.targetSet G C x₀ := by
      rw [htargetAll]
      exact hvout
    have hvB : v ∈ bridgeSet (G := G) C B := by
      rw [Nonseparating.targetSet_eq_component G hx₀out] at hvTarget
      simpa only [B, bridgeSet] using hvTarget
    have hKcomp := (SimpleGraph.ComponentCompl.mem_supp_iff
      (G := G) (K := C.vSet (G := G)) (C := K) (v := v)).mp hvK
    have hBcomp := (SimpleGraph.ComponentCompl.mem_supp_iff
      (G := G) (K := C.vSet (G := G)) (C := B) (v := v)).mp hvB
    exact hKcomp.2.symm.trans hBcomp.2
  have hattach : attachSet (G := G) C B = C.vSet (G := G) := by
    apply Set.Subset.antisymm
    · intro c hc
      exact hc.1
    · intro c hcC
      have hoff := card_neighbors_off_chordless_cycle G C hch hcC
      have hoffPos :
          0 < (G.neighborFinset c \ C.verts (G := G)).card := by
        have := hrimdeg c hcC
        omega
      obtain ⟨v, hvOff⟩ := Finset.card_pos.mp hoffPos
      have hcv : G.Adj c v := by
        simpa using (Finset.mem_sdiff.mp hvOff).1
      have hvout : v ∉ C.vSet (G := G) := by
        intro hvC
        exact (Finset.mem_sdiff.mp hvOff).2
          ((C.mem_vSet_iff (G := G)).mp hvC)
      have hvTarget : v ∈ Nonseparating.targetSet G C x₀ := by
        rw [htargetAll]
        exact hvout
      have hvB : v ∈ bridgeSet (G := G) C B := by
        rw [Nonseparating.targetSet_eq_component G hx₀out] at hvTarget
        simpa only [B, bridgeSet] using hvTarget
      exact ⟨hcC, v, hvB, hcv⟩
  exact
    { cycle := C
      bridge := B
      chordless := hch
      uniqueBridge := ⟨fun K L ↦ (hbridgeEq K).trans (hbridgeEq L).symm⟩
      attach_eq := hattach }

/-- Root-exception form of the strongest direct certificate supplied by the
specialized TT lemma.  The resulting admissible cycle has connected
complement, a unique complementary bridge, and full attachment to that
bridge. -/
theorem exists_maxCycleCertificate_of_specialized_TT_minDegreeExcept
    (h2 : VertexTwoConnected (G := G)) {x₀ : V}
    (hdeg : ∀ v : V, v ≠ x₀ → 3 ≤ G.degree v)
    {S : Set V} (hS : (G.induce S).Connected) (hx₀S : x₀ ∈ S)
    (hseed : ∃ C : Cycle (G := G),
      Nonseparating.IsAdmissibleCycle G S C) :
    ∃ M : MaxCycleCertificate G,
      Nonseparating.IsAdmissibleCycle G S M.cycle := by
  obtain ⟨C, hC, hconn⟩ :=
    Nonseparating.exists_admissible_cycle_complement_connected_minDegreeExcept
      G h2 hdeg hS hx₀S hseed
  have hx₀out : x₀ ∉ C.vSet (G := G) :=
    Nonseparating.IsAdmissibleCycle.not_mem_cycle (G := G) hC hx₀S
  have hrimdeg : ∀ c : V, c ∈ C.vSet (G := G) → 3 ≤ G.degree c := by
    intro c hcC
    apply hdeg c
    intro hcx
    exact hx₀out (hcx ▸ hcC)
  let M := maxCycleCertificate_of_complement_connected G C hC.1 hconn hx₀out hrimdeg
  refine ⟨M, ?_⟩
  simpa only [M, maxCycleCertificate_of_complement_connected] using hC

/-- The preceding certificate can be chosen with the finite maximizing
property used in the TT surgery: no other admissible cycle has a larger
component containing the prescribed root. -/
theorem exists_maxCycleCertificate_of_specialized_TT_maximal
    (h2 : VertexTwoConnected (G := G)) {x₀ : V}
    (hdeg : ∀ v : V, v ≠ x₀ → 3 ≤ G.degree v)
    {S : Set V} (hS : (G.induce S).Connected) (hx₀S : x₀ ∈ S)
    (hseed : ∃ C : Cycle (G := G),
      Nonseparating.IsAdmissibleCycle G S C) :
    ∃ M : MaxCycleCertificate G,
      Nonseparating.IsAdmissibleCycle G S M.cycle ∧
      ∀ D : Cycle (G := G), Nonseparating.IsAdmissibleCycle G S D →
        Nonseparating.targetCard G D x₀ ≤
          Nonseparating.targetCard G M.cycle x₀ := by
  let C := Nonseparating.maximizingCycle G x₀ hseed
  have hC : Nonseparating.IsAdmissibleCycle G S C :=
    Nonseparating.maximizingCycle_admissible G hseed
  have haug : Nonseparating.TargetAugmentationProperty G S x₀ :=
    Nonseparating.targetAugmentationProperty_of_vertexTwoConnected_minDegreeExcept
      G h2 hdeg hS hx₀S hseed
  have hconn : (G.induce (C.vSet (G := G))ᶜ).Connected :=
    Nonseparating.maximizingCycle_complement_connected_of_augmentation
      G hx₀S hseed haug
  have hx₀out : x₀ ∉ C.vSet (G := G) :=
    Nonseparating.IsAdmissibleCycle.not_mem_cycle (G := G) hC hx₀S
  have hrimdeg : ∀ c : V, c ∈ C.vSet (G := G) → 3 ≤ G.degree c := by
    intro c hcC
    apply hdeg c
    intro hcx
    exact hx₀out (hcx ▸ hcC)
  let M := maxCycleCertificate_of_complement_connected
    G C hC.1 hconn hx₀out hrimdeg
  refine ⟨M, ?_, ?_⟩
  · simpa only [M, maxCycleCertificate_of_complement_connected] using hC
  · intro D hD
    have hle := Nonseparating.targetCard_le_max (x := x₀) G D hD
    have heq := Nonseparating.targetCard_maximizingCycle (x := x₀) G hseed
    change Nonseparating.targetCard G D x₀ ≤
      Nonseparating.targetCard G C x₀
    exact hle.trans_eq heq.symm

/-- The `AlmostMinDegreeThree` interface is a direct wrapper around the
root-exception certificate theorem. -/
theorem exists_maxCycleCertificate_of_specialized_TT
    (h2 : VertexTwoConnected (G := G)) {x₀ : V}
    (hdeg : Nonseparating.AlmostMinDegreeThree G x₀)
    {S : Set V} (hS : (G.induce S).Connected) (hx₀S : x₀ ∈ S)
    (hseed : ∃ C : Cycle (G := G),
      Nonseparating.IsAdmissibleCycle G S C) :
    ∃ M : MaxCycleCertificate G,
      Nonseparating.IsAdmissibleCycle G S M.cycle :=
  exists_maxCycleCertificate_of_specialized_TT_minDegreeExcept
    G h2 hdeg.2 hS hx₀S hseed

/-- Unconditional pointed certificate under exactly the hypotheses of the
two-connected structural core.  The seed required by TT Lemma 2 is obtained
inside `G - x₀`; its augmentation produces a nonseparating induced cycle
avoiding `x₀`, and therefore a unique fully attached complementary bridge. -/
theorem exists_maxCycleCertificate_of_pointed_hypotheses
    {x₀ : V} (hcard : 2 ≤ Fintype.card V)
    (h2 : VertexTwoConnected (G := G))
    (hdeg : ∀ v : V, v ≠ x₀ → 3 ≤ G.degree v) :
    ∃ M : MaxCycleCertificate G,
      Nonseparating.IsAdmissibleCycle G ({x₀} : Set V) M.cycle := by
  have hsingleton : (G.induce ({x₀} : Set V)).Connected := by
    exact ⟨SimpleGraph.Preconnected.of_subsingleton⟩
  have hx₀singleton : x₀ ∈ ({x₀} : Set V) := Set.mem_singleton x₀
  have hseed :=
    Nonseparating.exists_admissible_cycle_singleton_of_vertexTwoConnected_minDegreeExcept
      G hcard h2 hdeg
  exact exists_maxCycleCertificate_of_specialized_TT_minDegreeExcept
    G h2 hdeg hsingleton hx₀singleton hseed

/-- Maximal form of the unconditional pointed certificate. -/
theorem exists_maxCycleCertificate_of_pointed_hypotheses_maximal
    {x₀ : V} (hcard : 2 ≤ Fintype.card V)
    (h2 : VertexTwoConnected (G := G))
    (hdeg : ∀ v : V, v ≠ x₀ → 3 ≤ G.degree v) :
    ∃ M : MaxCycleCertificate G,
      Nonseparating.IsAdmissibleCycle G ({x₀} : Set V) M.cycle ∧
      ∀ D : Cycle (G := G),
        Nonseparating.IsAdmissibleCycle G ({x₀} : Set V) D →
          Nonseparating.targetCard G D x₀ ≤
            Nonseparating.targetCard G M.cycle x₀ := by
  have hsingleton : (G.induce ({x₀} : Set V)).Connected := by
    exact ⟨SimpleGraph.Preconnected.of_subsingleton⟩
  have hx₀singleton : x₀ ∈ ({x₀} : Set V) := Set.mem_singleton x₀
  have hseed :=
    Nonseparating.exists_admissible_cycle_singleton_of_vertexTwoConnected_minDegreeExcept
      G hcard h2 hdeg
  exact exists_maxCycleCertificate_of_specialized_TT_maximal
    G h2 hdeg hsingleton hx₀singleton hseed

/-- Three neighbours on the vertex set of a paper cycle give the exact wheel
witness used by Problem 916. -/
theorem hasWheelWitness_of_three_neighbors_on_cycle
    (C : Cycle (G := G)) (x : V)
    (hx : x ∉ C.vSet (G := G))
    (hthree : 3 ≤
      (G.neighborFinset x ∩ C.verts (G := G)).card) :
    HasWheelWitness G := by
  classical
  refine ⟨C.base, C.walk, x, C.isCycle, ?_, ?_⟩
  · simpa only [mem_cycle_vSet_iff_mem_support] using hx
  · simpa only [Cycle.verts] using hthree

/-- An outside vertex having three neighbours on the chosen maximum cycle is
already a wheel hub. -/
theorem MaxCycleCertificate.hasWheelWitness_of_three_neighbors
    (M : MaxCycleCertificate G) (x : V)
    (hxB : x ∈ bridgeSet (G := G) M.cycle M.bridge)
    (hthree : 3 ≤
      (G.neighborFinset x ∩ M.cycle.verts (G := G)).card) :
    HasWheelWitness G := by
  have hxout : x ∉ M.cycle.vSet (G := G) :=
    mem_bridge_imp_not_mem_cycle (G := G) M.cycle M.bridge hxB
  exact hasWheelWitness_of_three_neighbors_on_cycle G M.cycle x hxout hthree

/-- In the no-wheel branch, every vertex of the unique complementary bridge
has at most two neighbours on the maximum cycle. -/
theorem MaxCycleCertificate.card_neighbors_on_cycle_le_two_of_noWheel
    (M : MaxCycleCertificate G) (hno : ¬HasWheelWitness G)
    {x : V} (hxB : x ∈ bridgeSet (G := G) M.cycle M.bridge) :
    (G.neighborFinset x ∩ M.cycle.verts (G := G)).card ≤ 2 := by
  by_contra hnot
  have hthree : 3 ≤
      (G.neighborFinset x ∩ M.cycle.verts (G := G)).card := by
    omega
  exact hno (M.hasWheelWitness_of_three_neighbors G x hxB hthree)

/-- Every vertex of the maximum cycle has an actual adjacent vertex in its
unique complementary bridge. -/
theorem MaxCycleCertificate.exists_adj_bridge
    (M : MaxCycleCertificate G) {c : V}
    (hc : c ∈ M.cycle.vSet (G := G)) :
    ∃ x : V, x ∈ bridgeSet (G := G) M.cycle M.bridge ∧ G.Adj c x := by
  have hcatt : c ∈ attachSet (G := G) M.cycle M.bridge := by
    rw [M.attach_eq]
    exact hc
  exact hcatt.2

/-- Because the selected bridge is the unique component of the complement,
its carrier is exactly the complement of the maximum cycle. -/
theorem MaxCycleCertificate.mem_bridge_iff_not_mem_cycle
    (M : MaxCycleCertificate G) (x : V) :
    x ∈ bridgeSet (G := G) M.cycle M.bridge ↔
      x ∉ M.cycle.vSet (G := G) := by
  constructor
  · exact mem_bridge_imp_not_mem_cycle (G := G) M.cycle M.bridge
  · intro hx
    let K : Bridge (G := G) M.cycle :=
      G.componentComplMk (K := M.cycle.vSet (G := G)) hx
    have hxK : x ∈ bridgeSet (G := G) M.cycle K := by
      change x ∈ (K : Set V)
      dsimp only [K]
      exact G.componentComplMk_mem (K := M.cycle.vSet (G := G)) hx
    have hKB : K = M.bridge :=
      @Subsingleton.elim (Bridge (G := G) M.cycle) M.uniqueBridge K M.bridge
    simpa only [hKB] using hxK

/-- The carrier of the selected complementary bridge induces a connected
ambient subgraph. -/
theorem MaxCycleCertificate.bridge_connected (M : MaxCycleCertificate G) :
    (G.induce (bridgeSet (G := G) M.cycle M.bridge)).Connected := by
  obtain ⟨x, hx⟩ := ComponentCompl.nonempty (C := M.bridge)
  have hxB : x ∈ bridgeSet (G := G) M.cycle M.bridge := by
    simpa only [bridgeSet] using hx
  have hxout : x ∉ M.cycle.vSet (G := G) :=
    mem_bridge_imp_not_mem_cycle (G := G) M.cycle M.bridge hxB
  have heq : G.componentComplMk (K := M.cycle.vSet (G := G)) hxout = M.bridge :=
    (SimpleGraph.ComponentCompl.mem_supp_iff
      (G := G) (K := M.cycle.vSet (G := G))
      (C := M.bridge) (v := x)).mp hxB |>.2
  have hconn := Nonseparating.targetSet_connected G hxout
  rw [Nonseparating.targetSet_eq_component G hxout, heq] at hconn
  simpa only [bridgeSet] using hconn

/-- Cyclic-bridge branch of the TT analysis: if the unique complementary
bridge itself contains a cycle, then there is a second chordless cycle,
disjoint from the original rim, whose complement is connected.  This is the
exact nonseparating-cycle input for the cyclic-endblock case. -/
theorem MaxCycleCertificate.exists_disjoint_nonseparating_cycle_of_bridge_not_isAcyclic
    (M : MaxCycleCertificate G) (h2 : VertexTwoConnected (G := G))
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hcyc : ¬(G.induce
      (bridgeSet (G := G) M.cycle M.bridge)).IsAcyclic) :
    ∃ D : Cycle (G := G),
      Nonseparating.IsAdmissibleCycle
        G (M.cycle.vSet (G := G)) D ∧
      (G.induce (D.vSet (G := G))ᶜ).Connected := by
  classical
  simp only [SimpleGraph.IsAcyclic] at hcyc
  push Not at hcyc
  obtain ⟨v, Psub, hPsub⟩ := hcyc
  let f := SimpleGraph.Embedding.induce (G := G)
    (s := bridgeSet (G := G) M.cycle M.bridge)
  let P : G.Walk (f v) (f v) := Psub.map f.toHom
  have hP : P.IsCycle := hPsub.map f.injective
  have hPsupport : ∀ w : V, w ∈ P.support →
      w ∈ bridgeSet (G := G) M.cycle M.bridge := by
    intro w hw
    have hw' : w ∈ Psub.support.map f.toHom := by
      simpa only [P, SimpleGraph.Walk.support_map] using hw
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hw'
    exact z.property
  obtain ⟨D, hDchordless, hDsub⟩ :=
    exists_chordless_cycle_vSet_subset_of_isCycle G P hP
      (bridgeSet (G := G) M.cycle M.bridge) hPsupport
  have hDdisjoint :
      Disjoint (D.vSet (G := G)) (M.cycle.vSet (G := G)) := by
    rw [Set.disjoint_left]
    intro w hwD hwC
    exact (mem_bridge_imp_not_mem_cycle (G := G) M.cycle M.bridge
      (hDsub hwD)) hwC
  have hseed : ∃ D : Cycle (G := G),
      Nonseparating.IsAdmissibleCycle
        G (M.cycle.vSet (G := G)) D :=
    ⟨D, hDchordless, hDdisjoint⟩
  have hroot : M.cycle.base ∈ M.cycle.vSet (G := G) :=
    (mem_cycle_vSet_iff_mem_support G M.cycle M.cycle.base).mpr
      M.cycle.walk.start_mem_support
  exact Nonseparating.exists_admissible_cycle_complement_connected_minDegreeExcept
    G h2 (fun v _ => hmin v) (cycle_induce_vSet_connected G M.cycle)
      hroot hseed

/-- Certificate-level form of the cyclic-bridge exchange: the second
nonseparating cycle itself has a unique fully attached complementary bridge,
and its rim is disjoint from the original rim. -/
theorem MaxCycleCertificate.exists_disjoint_certificate_of_bridge_not_isAcyclic
    (M : MaxCycleCertificate G) (h2 : VertexTwoConnected (G := G))
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hcyc : ¬(G.induce
      (bridgeSet (G := G) M.cycle M.bridge)).IsAcyclic) :
    ∃ N : MaxCycleCertificate G,
      Disjoint (N.cycle.vSet (G := G)) (M.cycle.vSet (G := G)) := by
  obtain ⟨D, hD, hconn⟩ :=
    M.exists_disjoint_nonseparating_cycle_of_bridge_not_isAcyclic
      G h2 hmin hcyc
  have hroot : M.cycle.base ∈ M.cycle.vSet (G := G) :=
    (mem_cycle_vSet_iff_mem_support G M.cycle M.cycle.base).mpr
      M.cycle.walk.start_mem_support
  have hrootout : M.cycle.base ∉ D.vSet (G := G) :=
    Nonseparating.IsAdmissibleCycle.not_mem_cycle (G := G) hD hroot
  let N := maxCycleCertificate_of_complement_connected
    G D hD.1 hconn hrootout (fun v _ => hmin v)
  refine ⟨N, ?_⟩
  simpa only [N, maxCycleCertificate_of_complement_connected] using hD.2

/-- Acyclic-bridge branch of the TT analysis.  If the connected unique
bridge is a tree with at least two vertices, it has two distinct leaves.
In the no-wheel branch each such leaf has exactly one neighbour in the
bridge and exactly two on the rim, so minimum degree three forces its
ambient degree to be exactly three. -/
theorem MaxCycleCertificate.exists_two_degree_three_leaves_of_bridge_isAcyclic
    (M : MaxCycleCertificate G) (hno : ¬HasWheelWitness G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hcard : 2 ≤ (bridgeSet (G := G) M.cycle M.bridge).ncard)
    (hacyc : (G.induce
      (bridgeSet (G := G) M.cycle M.bridge)).IsAcyclic) :
    ∃ x y : V, x ≠ y ∧
      x ∈ bridgeSet (G := G) M.cycle M.bridge ∧
      y ∈ bridgeSet (G := G) M.cycle M.bridge ∧
      G.degree x = 3 ∧ G.degree y = 3 ∧
      (G.neighborFinset x ∩ M.cycle.verts (G := G)).card = 2 ∧
      (G.neighborFinset y ∩ M.cycle.verts (G := G)).card = 2 := by
  classical
  let B : Set V := bridgeSet (G := G) M.cycle M.bridge
  have hcardB : 2 ≤ B.ncard := by simpa only [B] using hcard
  have hcardType : 2 ≤ Fintype.card B := by
    rw [Set.fintypeCard_eq_ncard]
    exact hcardB
  letI : Nontrivial B := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have htree : (G.induce B).IsTree := by
    refine ⟨?_, ?_⟩
    · simpa only [B] using M.bridge_connected G
    · simpa only [B] using hacyc
  obtain ⟨x, y, hxy, hxleaf, hyleaf⟩ :=
    htree.exists_ne_and_degree_eq_one
  have leafData (z : B) (hzleaf : (G.induce B).degree z = 1) :
      G.degree z.1 = 3 ∧
        (G.neighborFinset z.1 ∩ M.cycle.verts (G := G)).card = 2 := by
    have hinter :
        G.neighborFinset z.1 ∩ B.toFinset =
          G.neighborFinset z.1 \ M.cycle.verts (G := G) := by
      ext w
      simp only [Finset.mem_inter, Set.mem_toFinset, Finset.mem_sdiff]
      rw [show w ∈ B ↔ w ∈ bridgeSet (G := G) M.cycle M.bridge by rfl,
        M.mem_bridge_iff_not_mem_cycle G w,
        M.cycle.mem_vSet_iff]
    have hmap := G.map_neighborFinset_induce (s := B) z
    have hcardMap := congrArg Finset.card hmap
    rw [Finset.card_map, hinter,
      SimpleGraph.card_neighborFinset_eq_degree] at hcardMap
    have hoff :
        (G.neighborFinset z.1 \ M.cycle.verts (G := G)).card = 1 := by
      omega
    have hsplit := Finset.card_sdiff_add_card_inter
      (G.neighborFinset z.1) (M.cycle.verts (G := G))
    rw [hoff, G.card_neighborFinset_eq_degree] at hsplit
    have hcycleLe := M.card_neighbors_on_cycle_le_two_of_noWheel G hno z.2
    have hzmin := hmin z.1
    constructor <;> omega
  obtain ⟨hxdeg, hxcycle⟩ := leafData x hxleaf
  obtain ⟨hydeg, hycycle⟩ := leafData y hyleaf
  refine ⟨x.1, y.1, ?_, x.2, y.2, hxdeg, hydeg, hxcycle, hycycle⟩
  intro heq
  exact hxy (Subtype.ext heq)

/-- Exact unconditional bridge dichotomy left by the maximum-cycle method.
Either the bridge contains a cycle, in which case TT Lemma 2 produces a
second disjoint nonseparating induced cycle, or the bridge is a tree and has
two distinct degree-three leaves with two rim attachments apiece. -/
theorem MaxCycleCertificate.second_cycle_or_two_degree_three_bridge_leaves
    (M : MaxCycleCertificate G) (h2 : VertexTwoConnected (G := G))
    (hno : ¬HasWheelWitness G) (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hcard : 2 ≤ (bridgeSet (G := G) M.cycle M.bridge).ncard) :
    (∃ D : Cycle (G := G),
      Nonseparating.IsAdmissibleCycle
        G (M.cycle.vSet (G := G)) D ∧
      (G.induce (D.vSet (G := G))ᶜ).Connected) ∨
    (∃ x y : V, x ≠ y ∧
      x ∈ bridgeSet (G := G) M.cycle M.bridge ∧
      y ∈ bridgeSet (G := G) M.cycle M.bridge ∧
      G.degree x = 3 ∧ G.degree y = 3 ∧
      (G.neighborFinset x ∩ M.cycle.verts (G := G)).card = 2 ∧
      (G.neighborFinset y ∩ M.cycle.verts (G := G)).card = 2) := by
  by_cases hacyc : (G.induce
      (bridgeSet (G := G) M.cycle M.bridge)).IsAcyclic
  · exact Or.inr
      (M.exists_two_degree_three_leaves_of_bridge_isAcyclic
        G hno hmin hcard hacyc)
  · exact Or.inl
      (M.exists_disjoint_nonseparating_cycle_of_bridge_not_isAcyclic
        G h2 hmin hacyc)

/-- The no-wheel bound therefore applies to every vertex outside the maximum
cycle, without mentioning the component representation. -/
theorem MaxCycleCertificate.card_neighbors_on_cycle_le_two_of_not_mem
    (M : MaxCycleCertificate G) (hno : ¬HasWheelWitness G)
    {x : V} (hx : x ∉ M.cycle.vSet (G := G)) :
    (G.neighborFinset x ∩ M.cycle.verts (G := G)).card ≤ 2 := by
  exact M.card_neighbors_on_cycle_le_two_of_noWheel G hno
    ((M.mem_bridge_iff_not_mem_cycle G x).2 hx)

/-- A degree-three vertex on a chordless cycle has a unique neighbour off
that cycle. -/
theorem card_neighbors_off_chordless_cycle_eq_one_of_degree_three
    (C : Cycle (G := G)) (hch : C.IsChordless (G := G))
    {c : V} (hc : c ∈ C.vSet (G := G)) (hdeg : G.degree c = 3) :
    (G.neighborFinset c \ C.verts (G := G)).card = 1 := by
  have h := card_neighbors_off_chordless_cycle G C hch hc
  omega

/-- Double-counting the edges between two finite vertex sets. -/
theorem sum_card_neighborFinset_inter_comm (A B : Finset V) :
    (∑ a ∈ A, (G.neighborFinset a ∩ B).card) =
      ∑ b ∈ B, (G.neighborFinset b ∩ A).card := by
  classical
  have hleft (a : V) :
      (G.neighborFinset a ∩ B).card =
        ∑ b ∈ B, if G.Adj a b then 1 else 0 := by
    have heq : G.neighborFinset a ∩ B = B.filter (G.Adj a) := by
      ext b
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        Finset.mem_filter]
      tauto
    rw [heq]
    exact Finset.card_filter (G.Adj a) B
  have hright (b : V) :
      (G.neighborFinset b ∩ A).card =
        ∑ a ∈ A, if G.Adj a b then 1 else 0 := by
    have heq : G.neighborFinset b ∩ A = A.filter (fun a => G.Adj a b) := by
      ext a
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        Finset.mem_filter]
      constructor
      · rintro ⟨hba, ha⟩
        exact ⟨ha, hba.symm⟩
      · rintro ⟨ha, hab⟩
        exact ⟨hab.symm, ha⟩
    rw [heq]
    exact Finset.card_filter (fun a => G.Adj a b) A
  simp_rw [hleft, hright]
  exact Finset.sum_comm

/-- In the no-wheel branch, double-counting the attachment edges bounds the
cycle length by twice the size of its unique complementary bridge. -/
theorem MaxCycleCertificate.card_cycle_le_twice_internalCard_of_noWheel
    (M : MaxCycleCertificate G) (hno : ¬HasWheelWitness G) :
    (M.cycle.verts (G := G)).card ≤
      2 * internalCard (G := G) M.cycle M.bridge := by
  classical
  let B : Finset V := internalFinset (G := G) M.cycle M.bridge
  have hleft : (M.cycle.verts (G := G)).card ≤
      ∑ c ∈ M.cycle.verts (G := G), (G.neighborFinset c ∩ B).card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro c hc
    obtain ⟨x, hxB, hcx⟩ := M.exists_adj_bridge G
      ((M.cycle.mem_vSet_iff (G := G)).2 hc)
    have hxBfin : x ∈ B := by
      simpa only [B, internalFinset, Set.mem_toFinset] using hxB
    have hxmem : x ∈ G.neighborFinset c ∩ B := by
      exact Finset.mem_inter.mpr ⟨by simpa using hcx, hxBfin⟩
    exact Finset.one_le_card.mpr ⟨x, hxmem⟩
  have hdouble :
      (∑ c ∈ M.cycle.verts (G := G), (G.neighborFinset c ∩ B).card) =
        ∑ x ∈ B, (G.neighborFinset x ∩ M.cycle.verts (G := G)).card :=
    sum_card_neighborFinset_inter_comm G (M.cycle.verts (G := G)) B
  have hright :
      (∑ x ∈ B, (G.neighborFinset x ∩ M.cycle.verts (G := G)).card) ≤
        ∑ _x ∈ B, 2 := by
    apply Finset.sum_le_sum
    intro x hx
    have hxB : x ∈ bridgeSet (G := G) M.cycle M.bridge := by
      simpa only [B, internalFinset, Set.mem_toFinset] using hx
    exact M.card_neighbors_on_cycle_le_two_of_noWheel G hno hxB
  have hsum : (∑ _x ∈ B, 2) = 2 * B.card := by simp [mul_comm]
  rw [hdouble] at hleft
  rw [hsum] at hright
  simpa only [B, internalCard] using hleft.trans hright

/-- The maximum-cycle result reduces the exact structural principle to one
local implication about its unique complementary bridge.  This is a useful
adapter for formalizing the remaining Thomassen--Toft bridge analysis without
repeating any maximum-choice argument. -/
def MaxCycleLocalReductionPrinciple : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (M : MaxCycleCertificate H),
      (∀ w : W, 3 ≤ H.degree w) →
      HasWheelWitness H ∨ Nonempty (K23Reduction H)

/-- Once the local unique-bridge analysis is supplied, the exact core needed
by `Induction.lean` follows immediately from the Bondy--Vince maximum cycle. -/
theorem vertexTwoConnectedReductionPrinciple_of_maxCycleLocal
    (hlocal : MaxCycleLocalReductionPrinciple.{u}) :
    VertexTwoConnectedReductionPrinciple.{u} := by
  intro W _ _ H _ hcard hconn hdelete hmin
  have h2 : VertexTwoConnected (G := H) :=
    vertexTwoConnected_of_induction_hypotheses H hconn hdelete
  obtain ⟨M⟩ := exists_maxCycleCertificate H hcard h2 hmin
  exact hlocal W H M hmin

end Erdos916
