import ErdosProblems.Erdos622.Hamiltonicity
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Hamilton paths in dense balanced bipartite graphs

This file proves the endpoint-sensitive bipartite Dirac lemma used in the
almost-bipartite case of the Draganić--Keevash--Müyesser argument.  Its main
ingredient is the bipartite Bondy--Chvátal operation: if `x` and `y` are in
opposite parts of size `k`, are not adjacent, and
`degree x + degree y > k`, adjoining `xy` does not change Hamiltonicity.
-/

open Finset
open scoped SimpleGraph
open scoped List

namespace Erdos622.BipartiteHamilton

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Walk

open SimpleGraph

private theorem dart_eq_of_fst_eq_of_nodup_dropLast {u v : V}
    {p : G.Walk u v} (hnodup : p.support.dropLast.Nodup)
    {d e : G.Dart} (hd : d ∈ p.darts) (he : e ∈ p.darts)
    (hfst : d.fst = e.fst) : d = e := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have hi' : i < p.support.dropLast.length := by simpa using hi
  have hj' : j < p.support.dropLast.length := by simpa using hj
  have hget : p.support.dropLast[i]'hi' = p.support.dropLast[j]'hj' := by
    simpa [p.fst_darts_getElem hi, p.fst_darts_getElem hj] using hfst
  have hij := (List.Nodup.getElem_inj_iff hnodup).mp hget
  subst j
  rfl

private theorem isHamiltonianCycle_of_length_and_tail_toFinset
    {a : V} {p : G.Walk a a}
    (hlen : p.length = Fintype.card V) (hV : 3 ≤ Fintype.card V)
    (hsupport : p.support.tail.toFinset = Finset.univ) :
    p.IsHamiltonianCycle := by
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_, hlen⟩
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_, by omega⟩
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_tail_of_not_nil p (by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, hlen]
    omega)]
  have hcard : p.support.tail.toFinset.card = p.support.tail.length := by
    rw [hsupport]
    simp [hlen]
  have hmulti : ((p.support.tail : Multiset V).toFinset.card =
      (p.support.tail : Multiset V).card) := by
    simpa using hcard
  simpa using Multiset.toFinset_card_eq_card_iff_nodup.mp hmulti

/-- The path-splicing step in the bipartite closure argument. -/
private theorem isHamiltonian_of_splice
    {u u' v v' : V} {p : G.Walk u u'}
    (hV : 3 ≤ Fintype.card V) (hp : p.support ~ Finset.univ.toList)
    (hne : v ≠ u') (hvu' : G.Adj v u') (hv'u : G.Adj v' u)
    (d : G.Dart) (hd : d ∈ p.darts) (hd₁ : d.fst = v) (hd₂ : d.snd = v') :
    G.IsHamiltonian := by
  have hv : v ∈ p.support := by simp [List.Perm.mem_iff hp]
  have hdropNonNil : ¬(p.dropUntil v hv).Nil :=
    SimpleGraph.Walk.not_nil_of_ne hne
  have hsnd : (p.dropUntil v hv).getVert 1 = v' := by
    have hsupport : p.support.Nodup := by
      rw [List.Perm.nodup_iff hp]
      exact Finset.nodup_toList _
    have hdrop : p.support.dropLast.Nodup :=
      p.support.dropLast_prefix.nodup hsupport
    have hfirst : (p.dropUntil v hv).firstDart hdropNonNil ∈ p.darts :=
      p.darts_dropUntil_subset_darts hv
        ((p.dropUntil v hv).firstDart_mem_darts hdropNonNil)
    have heq : (p.dropUntil v hv).firstDart hdropNonNil = d :=
      dart_eq_of_fst_eq_of_nodup_dropLast hdrop hfirst hd (by simp [hd₁])
    have := congrArg (fun z : G.Dart ↦ z.snd) heq
    simpa [hd₂] using this
  let q := (p.takeUntil _ hv)
    |>.append hvu'.toWalk
    |>.append (p.dropUntil v hv |>.tail |>.reverse.copy rfl hsnd)
    |>.append hv'u.toWalk
  suffices q.IsHamiltonianCycle from fun _ ↦ ⟨u, q, this⟩
  apply isHamiltonianCycle_of_length_and_tail_toFinset
  · have hsum : (p.takeUntil v hv).length + (p.dropUntil v hv).length =
        p.length := by
      have hwalk := congrArg SimpleGraph.Walk.length (p.take_spec hv)
      simpa only [SimpleGraph.Walk.length_append] using hwalk
    have hpLength : p.length + 1 = Fintype.card V := by
      calc
        p.length + 1 = p.support.length := by simp
        _ = Finset.univ.toList.length := List.Perm.length_eq hp
        _ = Fintype.card V := by simp
    have htail := SimpleGraph.Walk.length_tail_add_one hdropNonNil
    simp [q, add_assoc]
    omega
  · exact hV
  · simp only [SimpleGraph.Walk.tail_support_append,
      SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.tail_cons, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_reverse, List.tails_reverse,
      List.append_assoc, List.singleton_append, List.cons_append,
      List.toFinset_append, List.toFinset_cons, List.toFinset_reverse,
      List.toFinset_nil, insert_empty_eq, Finset.union_insert,
      Finset.eq_univ_iff_forall, Finset.mem_insert, Finset.mem_union,
      List.mem_toFinset, Finset.mem_singleton, Finset.notMem_empty,
      false_or, q]
    intro w
    by_contra hw
    simp only [not_or] at hw
    rcases hw with ⟨hw₁, hw₂, hw₃, hw₄⟩
    have hmemTail : w ∈ p.support.tail := by
      have hmem : w ∈ p.support := by simp [List.Perm.mem_iff hp]
      rw [SimpleGraph.Walk.support_eq_cons] at hmem
      simp only [List.mem_cons] at hmem
      exact hmem.resolve_left hw₄
    have hnotDrop : w ∉ (p.dropUntil v hv).support.tail := by
      have htailNonNil : (p.dropUntil v hv).support.tail ≠ [] := by
        have hpos : 0 < (p.dropUntil v hv).length :=
          SimpleGraph.Walk.not_nil_iff_lt_length.mp hdropNonNil
        apply List.ne_nil_of_length_pos
        rw [List.length_tail, SimpleGraph.Walk.length_support]
        omega
      have hlast : (p.dropUntil v hv).support.tail.getLast htailNonNil = u' := by
        rw [List.getLast_tail, SimpleGraph.Walk.getLast_support]
      have hdropLast :
          w ∉ (p.dropUntil v hv).support.tail.dropLast := by
        simpa only [List.tail_reverse, List.mem_reverse,
          SimpleGraph.Walk.support_tail_of_not_nil _ hdropNonNil] using hw₃
      intro hwm
      rw [← List.dropLast_append_getLast htailNonNil, hlast,
        List.mem_append, List.mem_singleton] at hwm
      exact hwm.elim hdropLast hw₁
    have happend : p.support.tail =
        (p.takeUntil v hv).support.tail ++
          (p.dropUntil v hv).support.tail := by
      rw [← SimpleGraph.Walk.tail_support_append, p.take_spec hv]
    simp only [happend, List.mem_append] at hmemTail
    exact hmemTail.elim hw₂ hnotDrop

end Walk

namespace Closure

open SimpleGraph

/-- A Hamilton cycle can be transferred back across one bipartite closure
edge.  The two finite parts must cover the vertices and have equal size. -/
theorem isHamiltonian_of_sup_edge
    {A B : Finset V} (hAB : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcover : A ∪ B = Finset.univ) (hcard : A.card = B.card)
    {x y : V} (hx : x ∈ A) (hy : y ∈ B) (hxy : ¬G.Adj x y)
    (hdeg : A.card < G.degree x + G.degree y)
    (hHam : (G ⊔ SimpleGraph.edge x y).IsHamiltonian) :
    G.IsHamiltonian := by
  have hxyNe : x ≠ y := by
    intro h
    subst y
    exact (Set.disjoint_left.mp hAB.disjoint) hx hy
  have hABfin : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    exact (Set.disjoint_left.mp hAB.disjoint) hzA hzB
  have hVcard : Fintype.card V = A.card + B.card := by
    rw [← Finset.card_univ, ← hcover, Finset.card_union_of_disjoint]
    exact hABfin
  have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
  have hVne : Fintype.card V ≠ 1 := by omega
  have hVtwo : Fintype.card V ≠ 2 := by
    intro htwo
    exact SimpleGraph.not_isHamiltonian_of_card_eq_two htwo hHam
  have hVthree : 3 ≤ Fintype.card V := by omega
  obtain ⟨a, p, hp⟩ := hHam hVne
  by_cases hall : ∀ d ∈ p.darts, G.Adj d.fst d.snd
  · have hedge : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
      intro e he
      simp only [SimpleGraph.Walk.edges, List.mem_map] at he
      obtain ⟨d, hd, rfl⟩ := he
      exact hall d hd
    let q := p.transfer G hedge
    exact fun _ ↦ ⟨a, q,
      SimpleGraph.Walk.IsHamiltonianCycle.transfer hp hedge⟩
  · push Not at hall
    obtain ⟨d, hd, hdG⟩ := hall
    have hdEdge : (SimpleGraph.edge x y).Adj d.fst d.snd := by
      exact ((SimpleGraph.sup_adj G (SimpleGraph.edge x y) d.fst d.snd).mp d.adj)
        |>.resolve_left hdG
    have hor : (d.fst = x ∧ d.snd = y) ∨
        (d.fst = y ∧ d.snd = x) :=
      ((SimpleGraph.edge_adj x y d.fst d.snd).mp hdEdge).1
    have transfer_oriented
        {p₀ : (G ⊔ SimpleGraph.edge x y).Walk a a}
        (hp₀ : p₀.IsHamiltonianCycle)
        (d₀ : (G ⊔ SimpleGraph.edge x y).Dart) (hd₀ : d₀ ∈ p₀.darts)
        (hdx : d₀.fst = x) (hdy : d₀.snd = y) : G.IsHamiltonian := by
      have hxSupport : x ∈ p₀.support := by
        have hdSupport : d₀.fst ∈ p₀.support :=
          SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts _ hd₀
        simpa only [hdx] using hdSupport
      let q := p₀.rotate x hxSupport
      have hq : q.IsHamiltonianCycle := hp₀.rotate hxSupport
      have hdq : d₀ ∈ q.darts := by
        simpa [q] using
          (List.IsRotated.mem_iff
            (SimpleGraph.Walk.rotate_darts p₀ x hxSupport)).mpr hd₀
      have qNonNil : ¬q.Nil := by
        erw [SimpleGraph.Walk.nil_rotate]
        exact hp₀.isCycle.not_nil
      have hfirst : q.firstDart qNonNil = d₀ := by
        apply Walk.dart_eq_of_fst_eq_of_nodup_dropLast
          hq.isCycle.nodup_dropLast_support
          (q.firstDart_mem_darts qNonNil) hdq
        simp [q, hdx]
      have qOne : q.getVert 1 = y := by
        have := congrArg
          (fun z : (G ⊔ SimpleGraph.edge x y).Dart ↦ z.snd) hfirst
        simpa [hdy] using this
      have hedgeNotTail : s(x, y) ∉ q.tail.edges := by
        have hqcons : q = SimpleGraph.Walk.cons (q.adj_snd qNonNil) q.tail :=
          (q.cons_tail_eq qNonNil).symm
        have hedges : q.edges = s(x, y) :: q.tail.edges := by
          simp only [hqcons, SimpleGraph.Walk.edges_cons]
          simpa using Or.inl qOne
        intro he
        have hn := hq.isCycle.edges_nodup
        rw [hedges] at hn
        exact List.not_nodup_cons_of_mem he hn
      have hdelete :
          (G ⊔ SimpleGraph.edge x y).deleteEdges {s(x, y)} = G := by
        rw [← SimpleGraph.edgeSet_inj]
        ext e
        simp only [SimpleGraph.edgeSet_deleteEdges,
          SimpleGraph.edgeSet_sup, Set.mem_sdiff, Set.mem_union,
          Set.mem_singleton_iff,
          SimpleGraph.edge_edgeSet_of_ne hxyNe]
        have hnot : s(x, y) ∉ G.edgeSet := hxy
        constructor
        · rintro ⟨hGe | he, hne⟩
          · exact hGe
          · exact (hne he).elim
        · intro hGe
          refine ⟨Or.inl hGe, ?_⟩
          intro he
          subst e
          exact hnot hGe
      let r := q.tail
        |>.toDeleteEdge s(x, y) hedgeNotTail
        |>.transfer G (by
          simp (config := {singlePass := true}) only [← hdelete]
          exact SimpleGraph.Walk.edges_subset_edgeSet _)
        |>.copy qOne rfl
      have hrPerm : r.support ~ Finset.univ.toList := by
        rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one]
          at hq
        simp only [SimpleGraph.Walk.transfer_transfer,
          SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_transfer,
          List.perm_iff_count, r]
        intro z
        rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)]
        simpa [SimpleGraph.Walk.support_tail_of_not_nil _ qNonNil] using hq.2 z
      let NX : Finset V := G.neighborFinset x
      let NY : Finset V := G.neighborFinset y
      let imageNext : Finset V := NX.image hq.next
      have hNXcard : NX.card = G.degree x := by
        simp [NX, SimpleGraph.card_neighborFinset_eq_degree]
      have hNYcard : NY.card = G.degree y := by
        simp [NY, SimpleGraph.card_neighborFinset_eq_degree]
      have himageCard : imageNext.card = NX.card := by
        exact Finset.card_image_of_injective _ hq.next_inj
      have hImageA : imageNext ⊆ A := by
        intro z hz
        obtain ⟨w, hwN, hwz⟩ := Finset.mem_image.mp hz
        have hwB : w ∈ B := hAB.mem_of_mem_adj hx
          ((G.mem_neighborFinset x w).mp hwN)
        obtain ⟨e, he, heFst, heSnd⟩ := hq.self_next_in_darts w
        have heAdj : (G ⊔ SimpleGraph.edge x y).Adj w z := by
          have := e.adj
          rw [heFst, heSnd] at this
          simpa only [hwz] using this
        have heG : G.Adj w z := by
          rcases (SimpleGraph.sup_adj G (SimpleGraph.edge x y) w z).mp heAdj with
            heG | heNew
          · exact heG
          · have heOr := ((SimpleGraph.edge_adj x y w z).mp heNew).1
            rcases heOr with h | h
            · exact ((Set.disjoint_left.mp hAB.disjoint) hx
                (h.1 ▸ hwB)).elim
            · have hxyG : G.Adj x y := by
                simpa [h.1] using (G.mem_neighborFinset x w).mp hwN
              exact (hxy hxyG).elim
        exact hAB.mem_of_mem_adj' hwB heG.symm
      have hNYA : NY ⊆ A := by
        intro z hz
        exact hAB.mem_of_mem_adj' hy
          ((G.mem_neighborFinset y z).mp hz).symm
      have hinter : (imageNext ∩ NY).Nonempty := by
        by_contra hempty
        have hdisj : Disjoint imageNext NY :=
          Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hempty)
        have hsub : imageNext ∪ NY ⊆ A := Finset.union_subset hImageA hNYA
        have hle := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj, himageCard,
          hNXcard, hNYcard] at hle
        omega
      obtain ⟨w, hw⟩ := hinter
      obtain ⟨hwImage, hwNY⟩ := Finset.mem_inter.mp hw
      obtain ⟨w', hw'NX, hwNext⟩ := Finset.mem_image.mp hwImage
      have hw'x : G.Adj w' x :=
        ((G.mem_neighborFinset x w').mp hw'NX).symm
      have hwy : G.Adj w y := (G.mem_neighborFinset y w).mp hwNY |>.symm
      have hw'ne : w' ≠ x := by
        intro h
        subst w'
        exact G.loopless.irrefl x hw'x
      obtain ⟨e, heq, heFst, heSnd⟩ := hq.self_next_in_darts w'
      have heTail : e ∈ q.tail.darts := by
        have hdartsNe : q.darts ≠ [] :=
          SimpleGraph.Walk.darts_eq_nil.not.mpr qNonNil
        have hdarts : q.darts = d₀ :: q.tail.darts := by
          calc
            q.darts = q.darts.head hdartsNe :: q.darts.tail :=
              (List.cons_head_tail hdartsNe).symm
            _ = d₀ :: q.tail.darts := by
              rw [SimpleGraph.Walk.head_darts_eq_firstDart, hfirst,
                SimpleGraph.Walk.darts_tail]
        have heMem : e ∈ d₀ :: q.tail.darts := hdarts ▸ heq
        apply (List.mem_cons.mp heMem).resolve_left
        intro heeq
        have hfst := congrArg
          (fun z : (G ⊔ SimpleGraph.edge x y).Dart ↦ z.fst) heeq
        exact hw'ne (by simpa [heFst, hdx] using hfst)
      obtain ⟨i, hi, hie⟩ := List.getElem_of_mem heTail
      have hiR : i < r.darts.length := by simpa [r] using hi
      let eR : G.Dart := r.darts[i]
      have heR : eR ∈ r.darts := List.getElem_mem hiR
      have heRFst : eR.fst = w' := by
        calc
          eR.fst = r.getVert i := by
            have hh := congrArg (fun z : G.Dart ↦ z.fst)
              (r.darts_getElem_eq_getVert i hiR)
            simpa [eR] using hh
          _ = q.tail.getVert i := by
            simp only [SimpleGraph.Walk.getVert_eq_getD_support,
              SimpleGraph.Walk.support_copy,
              SimpleGraph.Walk.support_transfer, r]
          _ = (q.tail.darts[i]).fst := by
            have hh := congrArg
              (fun z : (G ⊔ SimpleGraph.edge x y).Dart ↦ z.fst)
              (q.tail.darts_getElem_eq_getVert i hi)
            exact hh.symm
          _ = e.fst := by rw [hie]
          _ = w' := heFst
      have heRSnd : eR.snd = w := by
        calc
          eR.snd = r.getVert (i + 1) := by
            have hh := congrArg (fun z : G.Dart ↦ z.snd)
              (r.darts_getElem_eq_getVert i hiR)
            simpa [eR] using hh
          _ = q.tail.getVert (i + 1) := by
            simp only [SimpleGraph.Walk.getVert_eq_getD_support,
              SimpleGraph.Walk.support_copy,
              SimpleGraph.Walk.support_transfer, r]
          _ = (q.tail.darts[i]).snd := by
            have hh := congrArg
              (fun z : (G ⊔ SimpleGraph.edge x y).Dart ↦ z.snd)
              (q.tail.darts_getElem_eq_getVert i hi)
            exact hh.symm
          _ = e.snd := by rw [hie]
          _ = hq.next w' := heSnd
          _ = w := hwNext
      apply Walk.isHamiltonian_of_splice hVthree hrPerm hw'ne hw'x hwy eR heR
      · exact heRFst
      · exact heRSnd
    rcases hor with hor | hor
    · exact transfer_oriented hp d hd hor.1 hor.2
    · have hpRev : p.reverse.IsHamiltonianCycle := by
        rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
        exact ⟨hp.isCycle.reverse, by simpa using hp.length_eq⟩
      have hdRev : d.symm ∈ p.reverse.darts := by
        exact SimpleGraph.Walk.mem_darts_reverse.mpr (by simpa using hd)
      exact transfer_oriented hpRev d.symm hdRev (by simpa using hor.2)
        (by simpa using hor.1)

/-- Bipartite Dirac--Moon--Moser theorem in balanced finite-set form. -/
theorem isHamiltonian_of_balanced_bipartite
    {A B : Finset V} (hAB : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcover : A ∪ B = Finset.univ) (hcard : A.card = B.card)
    (hpart : 2 ≤ A.card)
    (hdeg : ∀ v : V, A.card + 1 ≤ 2 * G.degree v) :
    G.IsHamiltonian := by
  let K : SimpleGraph V := (⊤ : SimpleGraph V).between (A : Set V) (B : Set V)
  have hABfin : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    exact (Set.disjoint_left.mp hAB.disjoint) hzA hzB
  have hGK : G ≤ K := by
    intro u v huv
    exact SimpleGraph.between_adj.mpr
      ⟨by simpa using huv.ne, hAB.mem_of_adj huv⟩
  have hVcard : Fintype.card V = A.card + B.card := by
    rw [← Finset.card_univ, ← hcover,
      Finset.card_union_of_disjoint hABfin]
  have hKdegree : ∀ v : V, K.degree v = A.card := by
    intro v
    have hv : v ∈ A ∪ B := by simpa [hcover]
    rcases Finset.mem_union.mp hv with hvA | hvB
    · have hn : K.neighborFinset v = B := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset]
        constructor
        · intro hvw
          rcases (SimpleGraph.between_adj.mp hvw).2 with h | h
          · exact h.2
          · exact ((Set.disjoint_left.mp hAB.disjoint) hvA h.1).elim
        · intro hwB
          apply SimpleGraph.between_adj.mpr
          refine ⟨?_, Or.inl ⟨hvA, hwB⟩⟩
          simp only [SimpleGraph.top_adj]
          intro hvw
          subst w
          exact (Set.disjoint_left.mp hAB.disjoint) hvA hwB
      rw [← SimpleGraph.card_neighborFinset_eq_degree, hn, hcard]
    · have hn : K.neighborFinset v = A := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset]
        constructor
        · intro hvw
          rcases (SimpleGraph.between_adj.mp hvw).2 with h | h
          · exact ((Set.disjoint_left.mp hAB.disjoint) h.1 hvB).elim
          · exact h.2
        · intro hwA
          apply SimpleGraph.between_adj.mpr
          refine ⟨?_, Or.inr ⟨hvB, hwA⟩⟩
          simp only [SimpleGraph.top_adj]
          intro hvw
          subst w
          exact (Set.disjoint_left.mp hAB.disjoint) hwA hvB
      rw [← SimpleGraph.card_neighborFinset_eq_degree, hn]
  have hKHam : K.IsHamiltonian := by
    apply SimpleGraph.dirac_theorem
    · rw [hVcard, hcard]
      omega
    · intro v
      rw [hKdegree, hVcard, hcard]
      omega
  let missing (H : SimpleGraph V) : Finset (Sym2 V) :=
    (Finset.univ : Finset (Sym2 V)).filter fun e ↦
      e ∈ K.edgeSet ∧ e ∉ H.edgeSet
  have aux : ∀ (m : ℕ) (H : SimpleGraph V),
      (missing H).card = m → G ≤ H → H ≤ K → H.IsHamiltonian := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro H hm hGH hHK
        by_cases hempty : missing H = ∅
        · have hKH : K ≤ H := by
            intro u v huv
            by_contra hnuv
            have heK : s(u, v) ∈ K.edgeSet := huv
            have heH : s(u, v) ∉ H.edgeSet := hnuv
            have : s(u, v) ∈ missing H := by
              simp [missing, heK, heH]
            simpa [hempty] using this
          have hEq : H = K := le_antisymm hHK hKH
          simpa [hEq] using hKHam
        · obtain ⟨e, heMissing⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
          induction e using Sym2.inductionOn with
          | _ u v =>
              have heParts : s(u, v) ∈ K.edgeSet ∧
                  s(u, v) ∉ H.edgeSet := by
                simpa [missing] using heMissing
              have heK : s(u, v) ∈ K.edgeSet := heParts.1
              have heH : s(u, v) ∉ H.edgeSet := heParts.2
              have huvK : K.Adj u v := by simpa using heK
              have huvH : ¬H.Adj u v := by simpa using heH
              have hcross : (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) :=
                (SimpleGraph.between_adj.mp huvK).2
              let H' : SimpleGraph V := H ⊔ SimpleGraph.edge u v
              have hHH' : H ≤ H' := le_sup_left
              have hGH' : G ≤ H' := hGH.trans hHH'
              have hH'K : H' ≤ K := by
                intro x y hxy
                rcases (SimpleGraph.sup_adj H (SimpleGraph.edge u v) x y).mp hxy with
                  hxyH | hxyE
                · exact hHK hxyH
                · rcases ((SimpleGraph.edge_adj u v x y).mp hxyE).1 with h | h
                  · simpa [h.1, h.2] using huvK
                  · simpa [h.1, h.2] using huvK.symm
              have hmissSub : missing H' ⊆ missing H := by
                intro z hz
                have hz' : z ∈ K.edgeSet ∧ z ∉ H'.edgeSet := by
                  simpa [missing] using hz
                have hzH : z ∉ H.edgeSet := by
                  intro hzH
                  exact hz'.2 (SimpleGraph.edgeSet_mono hHH' hzH)
                simp [missing, hz'.1, hzH]
              have heH' : s(u, v) ∈ H'.edgeSet := by
                apply (SimpleGraph.sup_adj H (SimpleGraph.edge u v) u v).mpr
                exact Or.inr ((SimpleGraph.edge_adj u v u v).mpr
                  ⟨Or.inl ⟨rfl, rfl⟩, huvK.ne⟩)
              have hmissStrict : missing H' ⊂ missing H := by
                apply Finset.ssubset_iff_subset_ne.mpr
                refine ⟨hmissSub, ?_⟩
                intro heq
                have : s(u, v) ∈ missing H' := heq.symm ▸ heMissing
                have hparts : s(u, v) ∈ K.edgeSet ∧
                    s(u, v) ∉ H'.edgeSet := by
                  simpa [missing] using this
                have hnot : s(u, v) ∉ H'.edgeSet := by
                  exact hparts.2
                exact hnot heH'
              have hlt : (missing H').card < m := by
                rw [← hm]
                exact Finset.card_lt_card hmissStrict
              have hH'Ham : H'.IsHamiltonian :=
                ih _ hlt H' rfl hGH' hH'K
              have hHAB : H.IsBipartiteWith (A : Set V) (B : Set V) := by
                refine ⟨hAB.disjoint, ?_⟩
                intro x y hxy
                exact (SimpleGraph.between_adj.mp (hHK hxy)).2
              rcases hcross with hcross | hcross
              · apply isHamiltonian_of_sup_edge hHAB hcover hcard
                  hcross.1 hcross.2 huvH
                · have hu := hdeg u
                  have hv := hdeg v
                  have hdu := G.degree_le_of_le (v := u) hGH
                  have hdv := G.degree_le_of_le (v := v) hGH
                  omega
                · exact hH'Ham
              · have hsup : H ⊔ SimpleGraph.edge v u = H' := by
                  simp only [H', SimpleGraph.edge_comm]
                apply isHamiltonian_of_sup_edge hHAB hcover hcard
                    hcross.2 hcross.1 (by simpa [SimpleGraph.adj_comm] using huvH)
                · have hu := hdeg u
                  have hv := hdeg v
                  have hdu := G.degree_le_of_le (v := u) hGH
                  have hdv := G.degree_le_of_le (v := v) hGH
                  omega
                · simpa [hsup] using hH'Ham
  exact aux (missing G).card G rfl le_rfl hGK

end Closure

namespace Endpoints

open SimpleGraph

private def pairComplement (a b : V) : Finset V :=
  ((Finset.univ : Finset V).erase a).erase b

private theorem pairComplement_cover {a b v : V} :
    v ∈ (pairComplement a b : Set V) ∨ v = a ∨ v = b := by
  simp only [pairComplement, Finset.coe_erase, Finset.coe_univ,
    Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
  tauto

private theorem pairComplement_not_left {a b : V} :
    a ∉ (pairComplement a b : Set V) := by
  simp [pairComplement]

private theorem pairComplement_not_right {a b : V} :
    b ∉ (pairComplement a b : Set V) := by
  simp [pairComplement]

/-- In a bipartite graph, deleting one prescribed vertex from each side
decreases the degree of every surviving vertex by at most one. -/
theorem degree_sub_one_le_degree_induce_pairComplement
    {A B : Finset V} (hAB : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcover : A ∪ B = Finset.univ) {a b : V}
    (ha : a ∈ A) (hb : b ∈ B)
    (z : (pairComplement a b : Set V)) :
    G.degree z.1 - 1 ≤
      (G.induce (pairComplement a b : Set V)).degree z := by
  let T : Finset V := ((G.neighborFinset z.1).erase a).erase b
  have hmap :
      ((G.induce (pairComplement a b : Set V)).neighborFinset z).map
          (Function.Embedding.subtype fun v ↦
            v ∈ (pairComplement a b : Set V)) = T := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, hwv⟩ := Finset.mem_map.mp hv
      subst v
      have hadj : G.Adj z.1 w.1 := SimpleGraph.induce_adj.mp
        ((G.induce (pairComplement a b : Set V)).mem_neighborFinset z w |>.mp hw)
      have hwmem : w.1 ≠ a ∧ w.1 ≠ b := by
        simpa [pairComplement] using w.2
      simp only [T, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      exact ⟨hwmem.2, hwmem.1, hadj⟩
    · intro hv
      simp only [T, Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hv
      let w : (pairComplement a b : Set V) := ⟨v, by
        simp [pairComplement, hv.1, hv.2.1]⟩
      apply Finset.mem_map.mpr
      refine ⟨w, ?_, rfl⟩
      exact (G.induce (pairComplement a b : Set V)).mem_neighborFinset z w |>.mpr
        (SimpleGraph.induce_adj.mpr hv.2.2)
  have hdegEq : (G.induce (pairComplement a b : Set V)).degree z = T.card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← Finset.card_map, hmap]
  have hzPart : z.1 ∈ A ∨ z.1 ∈ B := by
    have : z.1 ∈ A ∪ B := by simpa [hcover]
    exact Finset.mem_union.mp this
  rcases hzPart with hzA | hzB
  · have haNot : a ∉ G.neighborFinset z.1 := by
      intro haz
      have hza : G.Adj z.1 a := (G.mem_neighborFinset z.1 a).mp haz
      have haB : a ∈ B := hAB.mem_of_mem_adj hzA hza
      exact (Set.disjoint_left.mp hAB.disjoint) ha haB
    have hT : T = (G.neighborFinset z.1).erase b := by
      simp [T, Finset.erase_eq_of_notMem haNot]
    rw [hdegEq, hT]
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using
      (Finset.pred_card_le_card_erase (s := G.neighborFinset z.1) (a := b))
  · have hbNot : b ∉ G.neighborFinset z.1 := by
      intro hzb
      have hzb' : G.Adj z.1 b := (G.mem_neighborFinset z.1 b).mp hzb
      have hzA : z.1 ∈ A := hAB.mem_of_mem_adj' hb hzb'
      exact (Set.disjoint_left.mp hAB.disjoint) hzA hzB
    have hbNot' : b ∉ (G.neighborFinset z.1).erase a := by simp [hbNot]
    have hT : T = (G.neighborFinset z.1).erase a := by
      simp [T, Finset.erase_eq_of_notMem hbNot']
    rw [hdegEq, hT]
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using
      (Finset.pred_card_le_card_erase (s := G.neighborFinset z.1) (a := a))

private theorem map_left_endpoint_neighbors {a b : V} :
    (((Finset.univ : Finset (pairComplement a b : Set V)).filter
        fun z ↦ G.Adj a z.1).map
      (Function.Embedding.subtype fun v ↦
        v ∈ (pairComplement a b : Set V))) =
      (G.neighborFinset a).erase b := by
  ext v
  constructor
  · intro hv
    obtain ⟨z, hz, hzv⟩ := Finset.mem_map.mp hv
    subst v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hzmem : z.1 ≠ a ∧ z.1 ≠ b := by
      simpa [pairComplement] using z.2
    exact Finset.mem_erase.mpr ⟨hzmem.2,
      (G.mem_neighborFinset a z.1).mpr hz⟩
  · intro hv
    have hv' := Finset.mem_erase.mp hv
    have hva : v ≠ a := ((G.mem_neighborFinset a v).mp hv'.2).ne.symm
    let z : (pairComplement a b : Set V) := ⟨v, by
      simp [pairComplement, hv'.1, hva]⟩
    apply Finset.mem_map.mpr
    exact ⟨z, by simp [z, (G.mem_neighborFinset a v).mp hv'.2], rfl⟩

private theorem map_right_endpoint_neighbors {a b : V} :
    (((Finset.univ : Finset (pairComplement a b : Set V)).filter
        fun z ↦ G.Adj z.1 b).map
      (Function.Embedding.subtype fun v ↦
        v ∈ (pairComplement a b : Set V))) =
      (G.neighborFinset b).erase a := by
  ext v
  constructor
  · intro hv
    obtain ⟨z, hz, hzv⟩ := Finset.mem_map.mp hv
    subst v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hzmem : z.1 ≠ a ∧ z.1 ≠ b := by
      simpa [pairComplement] using z.2
    exact Finset.mem_erase.mpr ⟨hzmem.1,
      (G.mem_neighborFinset b z.1).mpr hz.symm⟩
  · intro hv
    have hv' := Finset.mem_erase.mp hv
    have hvb : v ≠ b := ((G.mem_neighborFinset b v).mp hv'.2).ne.symm
    let z : (pairComplement a b : Set V) := ⟨v, by
      simp [pairComplement, hv'.1, hvb]⟩
    apply Finset.mem_map.mpr
    refine ⟨z, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ((G.mem_neighborFinset b v).mp hv'.2).symm

private theorem adj_of_left_degree_ge_card
    {A B : Finset V} (hAB : G.IsBipartiteWith (A : Set V) (B : Set V))
    {x y : V} (hx : x ∈ A) (hy : y ∈ B)
    (hdeg : B.card ≤ G.degree x) : G.Adj x y := by
  by_contra hxy
  have hsub : G.neighborFinset x ⊆ B.erase y := by
    intro z hz
    have hzB : z ∈ B := hAB.mem_of_mem_adj hx
      ((G.mem_neighborFinset x z).mp hz)
    exact Finset.mem_erase.mpr ⟨fun h ↦ hxy (h ▸ (G.mem_neighborFinset x z).mp hz), hzB⟩
  have hle := Finset.card_le_card hsub
  have hypos : 0 < B.card := Finset.card_pos.mpr ⟨y, hy⟩
  rw [SimpleGraph.card_neighborFinset_eq_degree,
    Finset.card_erase_of_mem hy] at hle
  omega

/-- Dense balanced bipartite graphs are Hamilton-biconnected at the sharp
integer threshold used in DKM Lemma 3.8. -/
theorem exists_hamiltonian_path_of_balanced_bipartite
    {A B : Finset V} (hAB : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcover : A ∪ B = Finset.univ) (hcard : A.card = B.card)
    (hdeg : ∀ v : V, A.card + 2 ≤ 2 * G.degree v) :
    ∀ {a : V}, a ∈ A → ∀ {b : V}, b ∈ B →
      ∃ p : G.Walk a b, p.IsPath ∧ p.IsHamiltonian := by
  intro a ha b hb
  have hab : a ≠ b := by
    intro h
    subst b
    exact (Set.disjoint_left.mp hAB.disjoint) ha hb
  have hVcard : Fintype.card V = A.card + B.card := by
    have hABfin : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro z hzA hzB
      exact (Set.disjoint_left.mp hAB.disjoint) hzA hzB
    rw [← Finset.card_univ, ← hcover,
      Finset.card_union_of_disjoint hABfin]
  have hpartTwo : 2 ≤ A.card := by
    have hda := hdeg a
    have hupper := SimpleGraph.isBipartiteWith_degree_le hAB ha
    rw [← hcard] at hupper
    omega
  by_cases hsmall : A.card = 2
  · have hadj : ∀ {x : V}, x ∈ A → ∀ {y : V}, y ∈ B → G.Adj x y := by
      intro x hx y hy
      apply adj_of_left_degree_ge_card hAB hx hy
      have hxdeg := hdeg x
      rw [← hcard]
      omega
    have hAerase : (A.erase a).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem ha, hsmall]
      omega
    have hBerase : (B.erase b).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hb, ← hcard, hsmall]
      omega
    obtain ⟨a', ha'⟩ := hAerase
    obtain ⟨b', hb'⟩ := hBerase
    have ha'A : a' ∈ A := (Finset.mem_erase.mp ha').2
    have hb'B : b' ∈ B := (Finset.mem_erase.mp hb').2
    have ha'ne : a' ≠ a := (Finset.mem_erase.mp ha').1
    have hb'ne : b' ≠ b := (Finset.mem_erase.mp hb').1
    have haa' : a ≠ a' := ha'ne.symm
    have hbb' : b ≠ b' := hb'ne.symm
    have hab' := hadj ha hb'B
    have ha'b' := (hadj ha'A hb'B).symm
    have ha'b := hadj ha'A hb
    let p : G.Walk a b := (hab'.toWalk.concat ha'b').concat ha'b
    have hpPath : p.IsPath := by
      have ha'b'ne : a' ≠ b' := by
        intro h
        subst b'
        exact (Set.disjoint_left.mp hAB.disjoint) ha'A hb'B
      have hba' : b ≠ a' := by
        intro h
        subst b
        exact (Set.disjoint_left.mp hAB.disjoint) ha'A hb
      apply (hab'.isPath_toWalk.concat (by
        simp [SimpleGraph.Adj.support_toWalk, ha'ne, ha'b'ne]) ha'b').concat
      · simp [SimpleGraph.Adj.support_toWalk, hab.symm, hbb', hba']
    refine ⟨p, hpPath, ?_⟩
    rw [SimpleGraph.Walk.isHamiltonian_iff_isPath_and_length_eq]
    refine ⟨hpPath, ?_⟩
    have hVfour : Fintype.card V = 4 := by omega
    simp [p, hVfour]
  · have hpartThree : 3 ≤ A.card := by omega
    let s : Set V := (pairComplement a b : Set V)
    let H : SimpleGraph s := G.induce s
    let A' : Finset s := Finset.univ.filter fun z ↦ z.1 ∈ A
    let B' : Finset s := Finset.univ.filter fun z ↦ z.1 ∈ B
    let emb : s ↪ V := Function.Embedding.subtype fun v ↦ v ∈ s
    have hAmap : A'.map emb = A.erase a := by
      ext v
      constructor
      · intro hv
        obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hv
        have hzA : z.1 ∈ A := by simpa [A'] using hz
        have hzmem : z.1 ≠ a ∧ z.1 ≠ b := by
          simpa [s, pairComplement] using z.2
        have hzne : z.1 ≠ a := by
          exact hzmem.1
        exact Finset.mem_erase.mpr ⟨hzne, hzA⟩
      · intro hv
        have hv' := Finset.mem_erase.mp hv
        have hvb : v ≠ b := by
          intro h
          subst v
          exact (Set.disjoint_left.mp hAB.disjoint) hv'.2 hb
        let z : s := ⟨v, by simp [s, pairComplement, hv'.1, hvb]⟩
        exact Finset.mem_map.mpr ⟨z, by simp [A', z, hv'.2], rfl⟩
    have hBmap : B'.map emb = B.erase b := by
      ext v
      constructor
      · intro hv
        obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hv
        have hzB : z.1 ∈ B := by simpa [B'] using hz
        have hzmem : z.1 ≠ a ∧ z.1 ≠ b := by
          simpa [s, pairComplement] using z.2
        have hzne : z.1 ≠ b := by
          exact hzmem.2
        exact Finset.mem_erase.mpr ⟨hzne, hzB⟩
      · intro hv
        have hv' := Finset.mem_erase.mp hv
        have hva : v ≠ a := by
          intro h
          subst v
          exact (Set.disjoint_left.mp hAB.disjoint) ha hv'.2
        let z : s := ⟨v, by simp [s, pairComplement, hv'.1, hva]⟩
        exact Finset.mem_map.mpr ⟨z, by simp [B', z, hv'.2], rfl⟩
    have hAcard : A'.card = A.card - 1 := by
      have := congrArg Finset.card hAmap
      rw [Finset.card_map, Finset.card_erase_of_mem ha] at this
      exact this
    have hBcard : B'.card = B.card - 1 := by
      have := congrArg Finset.card hBmap
      rw [Finset.card_map, Finset.card_erase_of_mem hb] at this
      exact this
    have hAB' : H.IsBipartiteWith (A' : Set s) (B' : Set s) := by
      refine ⟨?_, ?_⟩
      · rw [Set.disjoint_left]
        intro z hzA hzB
        exact (Set.disjoint_left.mp hAB.disjoint)
          (by simpa [A'] using hzA) (by simpa [B'] using hzB)
      · intro x y hxy
        have hxyG : G.Adj x.1 y.1 := SimpleGraph.induce_adj.mp hxy
        rcases hAB.mem_of_adj hxyG with h | h
        · exact Or.inl ⟨by simpa [A'] using h.1, by simpa [B'] using h.2⟩
        · exact Or.inr ⟨by simpa [B'] using h.1, by simpa [A'] using h.2⟩
    have hcover' : A' ∪ B' = Finset.univ := by
      ext z
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      have hz : z.1 ∈ A ∪ B := by simpa [hcover]
      rcases Finset.mem_union.mp hz with hzA | hzB
      · exact Or.inl (by simp [A', hzA])
      · exact Or.inr (by simp [B', hzB])
    have hcard' : A'.card = B'.card := by omega
    have hdeg' : ∀ z : s, A'.card + 1 ≤ 2 * H.degree z := by
      intro z
      have hz := degree_sub_one_le_degree_induce_pairComplement
        hAB hcover ha hb z
      have hzdeg := hdeg z.1
      change G.degree z.1 - 1 ≤ H.degree z at hz
      omega
    have hHam : H.IsHamiltonian :=
      Closure.isHamiltonian_of_balanced_bipartite hAB' hcover' hcard'
        (by omega) hdeg'
    have hsCard : Fintype.card s = A'.card + B'.card := by
      have hdisj' : Disjoint A' B' := by
        rw [Finset.disjoint_left]
        intro z hzA hzB
        exact (Set.disjoint_left.mp hAB'.disjoint) hzA hzB
      rw [← Finset.card_univ, ← hcover',
        Finset.card_union_of_disjoint hdisj']
    have : Nontrivial s := Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [hsCard, hcard']
      omega)
    obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp (by
      rw [hsCard, hcard']
      omega : 0 < Fintype.card s)
    obtain ⟨q, hq⟩ := hHam.exists_isHamiltonianCycle x₀
    let NA : Finset s := Finset.univ.filter fun z ↦ G.Adj a z.1
    let NB : Finset s := Finset.univ.filter fun z ↦ G.Adj z.1 b
    have hNA : G.degree a - 1 ≤ NA.card := by
      have hp := Finset.pred_card_le_card_erase
        (s := G.neighborFinset a) (a := b)
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hp
      have hm := map_left_endpoint_neighbors (G := G) (a := a) (b := b)
      have hc := congrArg Finset.card hm
      rw [Finset.card_map] at hc
      exact hc.symm ▸ hp
    have hNB : G.degree b - 1 ≤ NB.card := by
      have hp := Finset.pred_card_le_card_erase
        (s := G.neighborFinset b) (a := a)
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hp
      have hm := map_right_endpoint_neighbors (G := G) (a := a) (b := b)
      have hc := congrArg Finset.card hm
      rw [Finset.card_map] at hc
      exact hc.symm ▸ hp
    have hNAB : NA ⊆ B' := by
      intro z hz
      have hza : G.Adj a z.1 := by simpa [NA] using hz
      have hzB := hAB.mem_of_mem_adj ha hza
      simp only [B', Finset.mem_filter, Finset.mem_univ, true_and]
      exact hzB
    have hNBA : NB ⊆ A' := by
      intro z hz
      have hzb : G.Adj z.1 b := by simpa [NB] using hz
      have hzA := hAB.mem_of_mem_adj' hb hzb
      simp only [A', Finset.mem_filter, Finset.mem_univ, true_and]
      exact hzA
    let imageNext : Finset s := NB.image hq.next
    have hnextCard : imageNext.card = NB.card :=
      Finset.card_image_of_injective _ hq.next_inj
    have hnextB : imageNext ⊆ B' := by
      intro z hz
      obtain ⟨w, hwNB, hwz⟩ := Finset.mem_image.mp hz
      have hwA : w ∈ A' := hNBA hwNB
      obtain ⟨d, -, hdFst, hdSnd⟩ := hq.self_next_in_darts w
      have hadj : H.Adj w (hq.next w) := by
        simpa [hdFst, hdSnd] using d.adj
      have := hAB'.mem_of_mem_adj (by simpa using hwA) hadj
      simpa [hwz] using this
    have hinter : (imageNext ∩ NA).Nonempty := by
      by_contra hempty
      have hdisj : Disjoint imageNext NA :=
        Finset.disjoint_iff_inter_eq_empty.mpr
          (Finset.not_nonempty_iff_eq_empty.mp hempty)
      have hsub : imageNext ∪ NA ⊆ B' := Finset.union_subset hnextB hNAB
      have hle := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, hnextCard] at hle
      have hda := hdeg a
      have hdb := hdeg b
      omega
    obtain ⟨z, hz⟩ := hinter
    obtain ⟨hzImage, hzNA⟩ := Finset.mem_inter.mp hz
    obtain ⟨w, hwNB, hwNext⟩ := Finset.mem_image.mp hzImage
    have hwSupport : w ∈ q.support := hq.mem_support w
    let r := q.rotate w hwSupport
    have hr : r.IsHamiltonianCycle := hq.rotate hwSupport
    have hrSnd : r.snd = z := by
      have hlen : 0 < r.length :=
        SimpleGraph.Walk.not_nil_iff_lt_length.mp hr.isCycle.not_nil
      have hnext : r.getVert 1 = hr.next w :=
        hr.getVert_succ_eq_next w (i := 0) hlen (by simp [r])
      have hrot : hr.next w = hq.next w := by
        exact SimpleGraph.Walk.IsHamiltonianCycle.rotate_next w hq hwSupport w
      exact hnext.trans (hrot.trans hwNext)
    obtain ⟨p, hp⟩ := Hamiltonicity.isHamiltonian_splice_induced_cycle
      r hr pairComplement_not_left pairComplement_not_right hab
      (fun v ↦ pairComplement_cover) (by
        rw [hrSnd]
        simpa [NA] using hzNA) (by
        simpa [NB] using hwNB)
    exact ⟨p, hp.isPath, hp⟩

end Endpoints

/-- Public namespace-level form of the endpoint-sensitive balanced bipartite
Hamilton-path theorem. -/
theorem exists_hamiltonian_path_of_balanced_bipartite
    {A B : Finset V} (hAB : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcover : A ∪ B = Finset.univ) (hcard : A.card = B.card)
    (hdeg : ∀ v : V, A.card + 2 ≤ 2 * G.degree v) :
    ∀ {a : V}, a ∈ A → ∀ {b : V}, b ∈ B →
      ∃ p : G.Walk a b, p.IsPath ∧ p.IsHamiltonian :=
  Endpoints.exists_hamiltonian_path_of_balanced_bipartite
    hAB hcover hcard hdeg

end Erdos622.BipartiteHamilton
