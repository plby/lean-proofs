import Wikipedia.CycleDoubleCoverConjecture

universe u

open scoped BigOperators symmDiff

namespace CycleDoubleCoverConjecture

open OrientedMultigraph

structure SimpleGraphCircuitDoubleCover {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) where
  circuits : List (Σ v, G.Walk v v)
  isCircuit : ∀ p ∈ circuits, p.2.IsCircuit
  coveredTwice : ∀ e ∈ G.edgeSet,
    (circuits.filter fun p ↦ e ∈ p.2.edges).length = 2

def SimpleGraphCircuitDoubleCover.IsSmall {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (C : SimpleGraphCircuitDoubleCover G) : Prop :=
  C.circuits.length ≤ Fintype.card V - 1

noncomputable def _root_.SimpleGraph.CycleDoubleCover.toCircuitDoubleCover
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (C : SimpleGraph.CycleDoubleCover G) :
    SimpleGraphCircuitDoubleCover G where
  circuits := C.cycles.map fun Z ↦ (⟨Z.vertex, Z.walk⟩ : Σ v, G.Walk v v)
  isCircuit := by
    intro p hp
    rw [List.mem_map] at hp
    rcases hp with ⟨Z, hZ, rfl⟩
    exact Z.isCycle.isCircuit
  coveredTwice := by
    intro e he
    have hfilter (L : List G.Cycle) :
        ((L.map fun Z ↦ (⟨Z.vertex, Z.walk⟩ : Σ v, G.Walk v v)).filter
            fun p ↦ e ∈ p.2.edges).length =
          (L.filter fun Z ↦ e ∈ Z.edges).length := by
      induction L with
      | nil => simp
      | cons Z L ih =>
          by_cases h : e ∈ Z.walk.edges <;>
            simp [SimpleGraph.Cycle.edges, h, ih]
    rw [hfilter]
    exact C.coveredTwice e he

@[simp]
lemma _root_.SimpleGraph.CycleDoubleCover.toCircuitDoubleCover_length
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (C : SimpleGraph.CycleDoubleCover G) :
    C.toCircuitDoubleCover.circuits.length = C.cycles.length := by
  simp [SimpleGraph.CycleDoubleCover.toCircuitDoubleCover]

theorem simpleGraph_circuitDoubleCoverConjecture
    {V : Type u} [Finite V] [DecidableEq V] (G : SimpleGraph V)
    (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    Nonempty (SimpleGraphCircuitDoubleCover G) := by
  obtain ⟨C⟩ := simpleGraph_cycleDoubleCoverConjecture G hb
  exact ⟨C.toCircuitDoubleCover⟩

theorem simpleGraph_smallCircuitDoubleCover_of_smallCycleDoubleCover
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {C : SimpleGraph.CycleDoubleCover G}
    (hsmall : C.cycles.length ≤ Fintype.card V - 1) :
    ∃ D : SimpleGraphCircuitDoubleCover G, D.IsSmall := by
  exact ⟨C.toCircuitDoubleCover, by simpa [SimpleGraphCircuitDoubleCover.IsSmall] using hsmall⟩

theorem _root_.SimpleGraph.exists_isCircuit_edges_eq_of_connected_even
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (F : Finset (Sym2 V))
    (hFedge : ∀ e ∈ F, e ∈ G.edgeSet) (hFne : F.Nonempty)
    (hFeven : ∀ v : V, Even (F.filter fun e ↦ v ∈ e).card)
    (hFconn : ∀ ⦃u v : V⦄,
      (∃ e ∈ F, u ∈ e) → (∃ e ∈ F, v ∈ e) →
        (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable u v) :
    ∃ v : V, ∃ p : G.Walk v v, p.IsCircuit ∧ p.edges.toFinset = F := by
  classical
  let H : SimpleGraph V := SimpleGraph.fromEdgeSet (F : Set (Sym2 V))
  have hHedge : H.edgeSet = (F : Set (Sym2 V)) := by
    change (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).edgeSet =
      (F : Set (Sym2 V))
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    refine sdiff_eq_left.mpr ?_
    rw [Set.disjoint_left]
    intro e heF hdiag
    exact G.not_isDiag_of_mem_edgeSet (hFedge e heF) hdiag
  have hHG : H ≤ G := by
    rw [← SimpleGraph.edgeSet_subset_edgeSet, hHedge]
    intro e he
    exact hFedge e he
  haveI : Nonempty V := by
    obtain ⟨e, heF⟩ := hFne
    revert heF
    refine Sym2.inductionOn e ?_
    intro x y _
    exact ⟨x⟩
  obtain ⟨u, v, p, hpTrail, hpMax⟩ :=
    SimpleGraph.Walk.exists_isTrail_forall_isTrail_length_le_length H
  have hp_not_nil : ¬ p.Nil := by
    obtain ⟨e, heF⟩ := hFne
    have heG : e ∈ G.edgeSet := hFedge e heF
    revert heF heG
    refine Sym2.inductionOn e ?_
    intro x y heF heG
    have hne : x ≠ y := by
      intro hxy
      exact G.not_isDiag_of_mem_edgeSet heG (by simp [hxy])
    have hxy : H.Adj x y := by
      rw [← SimpleGraph.mem_edgeSet, hHedge]
      exact heF
    have hle := hpMax x y hxy.toWalk (SimpleGraph.Walk.IsPath.of_adj hxy).isTrail
    rw [show hxy.toWalk.length = 1 by rfl] at hle
    exact fun hnil ↦ by
      have hp0 : p.length = 0 := SimpleGraph.Walk.Nil.length_eq_zero hnil
      omega
  have hclosed : u = v := by
    by_contra huv
    have hused :
        ∀ e ∈ H.incidenceSet u, e ∈ p.edges := by
      intro e heinc
      by_contra hep
      let w := H.otherVertexOfIncident heinc
      have hwu : H.Adj w u := (H.incidence_other_prop heinc).symm
      have hlong := hpMax w v (p.cons hwu) (hpTrail.cons hwu ?_)
      · rw [SimpleGraph.Walk.length_cons] at hlong
        omega
      · have heq : s(u, w) = e := Sym2.other_spec' heinc.2
        simpa [Sym2.eq_swap, heq] using hep
    have hfilter :
        p.edges.toFinset.filter (fun e ↦ u ∈ e) =
          F.filter fun e ↦ u ∈ e := by
      ext e
      constructor
      · intro he
        simp only [Finset.mem_filter, List.mem_toFinset] at he ⊢
        exact ⟨by simpa [hHedge] using p.edges_subset_edgeSet he.1, he.2⟩
      · intro he
        simp only [Finset.mem_filter, List.mem_toFinset] at he ⊢
        have heinc : e ∈ H.incidenceSet u := ⟨by simpa [hHedge] using he.1, he.2⟩
        exact ⟨hused e heinc, he.2⟩
    have hpOdd : ¬ Even (p.edges.toFinset.filter fun e ↦ u ∈ e).card := by
      intro hcard
      have hcount : Even (p.edges.countP fun e ↦ u ∈ e) := by
        rwa [← SimpleGraph.card_filter_edges_toFinset_eq_countP hpTrail u]
      exact ((hpTrail.even_countP_edges_iff u).mp hcount huv).1 rfl
    exact hpOdd (hfilter.symm ▸ hFeven u)
  subst v
  have hused_incident_of_mem_support :
      ∀ ⦃w : V⦄, w ∈ p.support → ∀ e ∈ H.incidenceSet w, e ∈ p.edges := by
    intro w hw e heinc
    by_contra hep
    let q : H.Walk w w := p.rotate w hw
    have hqTrail : q.IsTrail := by
      exact hpTrail.rotate hw
    let z := H.otherVertexOfIncident heinc
    have hzw : H.Adj z w := (H.incidence_other_prop heinc).symm
    have hnotq : s(z, w) ∉ q.edges := by
      intro hzq
      have heq : s(w, z) = e := Sym2.other_spec' heinc.2
      have heqmem : e ∈ q.edges := by
        simpa [q, Sym2.eq_swap, heq] using hzq
      exact hep ((p.rotate_edges w hw).perm.mem_iff.mp heqmem)
    have hlong := hpMax z w (q.cons hzw) (hqTrail.cons hzw hnotq)
    rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_rotate] at hlong
    omega
  have support_closed_under_adj :
      ∀ ⦃x y : V⦄, x ∈ p.support → H.Adj x y → y ∈ p.support := by
    intro x y hx hxy
    have heinc : s(x, y) ∈ H.incidenceSet x := by
      refine ⟨by simpa using hxy, ?_⟩
      exact Sym2.mem_mk_left x y
    have hused := hused_incident_of_mem_support hx (s(x, y)) heinc
    exact p.snd_mem_support_of_mem_edges hused
  have support_of_reachable :
      ∀ ⦃x y : V⦄, x ∈ p.support → H.Reachable x y → y ∈ p.support := by
    intro x y hx hxy
    rcases hxy with ⟨q⟩
    induction q with
    | nil => exact hx
    | cons h q ih =>
        exact ih (support_closed_under_adj hx h)
  have hbase :
      ∃ a : V, a ∈ p.support ∧ ∃ e ∈ F, a ∈ e := by
    have hedges_ne : p.edges ≠ [] := by
      intro hedges
      exact hp_not_nil (SimpleGraph.Walk.edges_eq_nil.mp hedges)
    obtain ⟨e, hep⟩ := List.exists_mem_of_ne_nil p.edges hedges_ne
    have heF : e ∈ F := by
      simpa [hHedge] using p.edges_subset_edgeSet hep
    revert heF hep
    refine Sym2.inductionOn e ?_
    intro a b hep heF
    exact ⟨a, p.fst_mem_support_of_mem_edges hep, s(a, b), heF,
      Sym2.mem_mk_left a b⟩
  have hFsub : F ⊆ p.edges.toFinset := by
    intro e heF
    by_contra hepFin
    have hep : e ∉ p.edges := by
      simpa using hepFin
    obtain ⟨a, haSupp, haInc⟩ := hbase
    revert heF hep
    refine Sym2.inductionOn e ?_
    intro x y heF hep
    have hxInc : ∃ e ∈ F, x ∈ e := ⟨s(x, y), heF, Sym2.mem_mk_left x y⟩
    have hreach : H.Reachable a x := hFconn haInc hxInc
    have hxSupp : x ∈ p.support := support_of_reachable haSupp hreach
    have heinc : s(x, y) ∈ H.incidenceSet x := by
      refine ⟨by simpa [hHedge] using heF, Sym2.mem_mk_left x y⟩
    exact hep (hused_incident_of_mem_support hxSupp (s(x, y)) heinc)
  have hpSub : p.edges.toFinset ⊆ F := by
    intro e he
    simpa [hHedge] using p.edges_subset_edgeSet (List.mem_toFinset.mp he)
  refine ⟨u, p.mapLe hHG, ?_, ?_⟩
  · exact ⟨hpTrail.mapLe hHG, by
      intro hnil
      apply hp_not_nil
      cases p <;> simp at hnil ⊢⟩
  · rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
    exact Finset.Subset.antisymm hpSub hFsub

lemma CubicGraph.two_mul_edge_card_eq_three_mul_vertex_card
    {V E : Type*} [Fintype V] [Fintype E] (G : CubicGraph V E) :
    2 * Fintype.card E = 3 * Fintype.card V := by
  have h := Fintype.card_congr G.incidence
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  omega

lemma CubicGraph.degree_toOrientedMultigraph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (K : CubicGraph V E) (v : V) :
    degree K.toOrientedMultigraph v = 3 := by
  let φ : Fin 3 ≃ (halfEdgesAt K.toOrientedMultigraph) v :=
  {
    toFun i :=
      ⟨(K.edgeAt v i, (K.incidence (v, i)).2), by
        change K.endAt (K.edgeAt v i) (K.incidence (v, i)).2 = v
        exact K.endAt_edgeAt_incidence v i⟩
    invFun h := (K.incidence.symm h.1).2
    left_inv i := by
      simp [CubicGraph.edgeAt]
    right_inv h := by
      rcases h with ⟨⟨e, j⟩, hv⟩
      apply Subtype.ext
      let p := K.incidence.symm (e, j)
      have hp1 : p.1 = v := hv
      have hinc : K.incidence (v, p.2) = (e, j) := by
        rw [← hp1]
        exact K.incidence.apply_symm_apply (e, j)
      simpa [p, CubicGraph.edgeAt] using hinc
  }
  have hcard := Fintype.card_congr φ
  simpa [degree] using hcard.symm

def oddVertices {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) : Finset V :=
  Finset.univ.filter fun v ↦ Odd (degree G v)

lemma not_bridgeless_of_edge_card_eq_one
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) (hE : Fintype.card E = 1) :
    ¬ Bridgeless G := by
  classical
  obtain ⟨e, heuniq⟩ := Fintype.card_eq_one_iff.mp hE
  let S : Finset V := {G.endAt e 0}
  have hcut : cut G S = {e} := by
    ext f
    have hfe : f = e := heuniq f
    constructor
    · intro _
      exact Finset.mem_singleton.mpr hfe
    · intro hf
      have hfe' : f = e := Finset.mem_singleton.mp hf
      subst f
      have hne10 : G.endAt e 1 ≠ G.endAt e 0 := fun h ↦ G.loopless e h.symm
      simp [cut, Crosses, S, hne10]
  intro hb
  have hnot := hb S
  rw [hcut] at hnot
  simp at hnot

lemma sum_degrees_eq_two_mul_edge_card
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) :
    (∑ v : V, degree G v) = 2 * Fintype.card E := by
  calc
    (∑ v : V, degree G v) =
        Fintype.card ((v : V) × (halfEdgesAt G) v) := by
      simp [degree]
    _ = Fintype.card (HalfEdge E) := by
      exact Fintype.card_congr (halfEdgeSigmaEquiv G).symm
    _ = 2 * Fintype.card E := by
      simp [HalfEdge, Nat.mul_comm]

lemma even_oddVertices_card
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) :
    Even (oddVertices G).card := by
  have hsum : Even (∑ v : V, degree G v) := by
    rw [sum_degrees_eq_two_mul_edge_card G]
    exact even_two_mul (Fintype.card E)
  simpa [oddVertices] using
    (Finset.even_sum_iff_even_card_odd (s := (Finset.univ : Finset V))
      (fun v ↦ degree G v)).mp (by simpa using hsum)

lemma CubicGraph.oddVertices_toOrientedMultigraph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (K : CubicGraph V E) :
    oddVertices K.toOrientedMultigraph = Finset.univ := by
  ext v
  simp [oddVertices, K.degree_toOrientedMultigraph v, show Odd 3 by norm_num]

lemma CubicGraph.oddVertices_card_toOrientedMultigraph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (K : CubicGraph V E) :
    (oddVertices K.toOrientedMultigraph).card = Fintype.card V := by
  rw [K.oddVertices_toOrientedMultigraph, Finset.card_univ]

lemma oddVertices_card_le_vertex_card
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) :
    (oddVertices G).card ≤ Fintype.card V := by
  rw [← Finset.card_univ]
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma oddVertices_half_add_two_le_vertex_card_sub_one_of_six
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (hlarge : 6 ≤ Fintype.card V) :
    (oddVertices G).card / 2 + 2 ≤ Fintype.card V - 1 := by
  have hqle := oddVertices_card_le_vertex_card G
  have hdiv : (oddVertices G).card / 2 ≤ Fintype.card V / 2 :=
    Nat.div_le_div_right hqle
  have hn : Fintype.card V / 2 + 2 ≤ Fintype.card V - 1 := by
    omega
  omega

def simpleGraphOddVertices {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v ↦ Odd (G.degree v)

lemma sum_halfEdge_indicator_eq_degree
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) :
    (∑ h : HalfEdge E, if vertex G h = v then (1 : F₂) else 0) =
      (degree G v : F₂) := by
  have hcard : Fintype.card (halfEdgesAt G v) =
      (Finset.univ.filter fun h : HalfEdge E ↦ vertex G h = v).card := by
    change Fintype.card {h : HalfEdge E // vertex G h = v} = _
    rw [Fintype.card_subtype]
  rw [degree, hcard]
  rw [Finset.card_eq_sum_ones]
  simp

lemma sum_univ_edgeIncidence_eq_degree
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) :
    (∑ e : E, edgeIncidence G v e) = (degree G v : F₂) := by
  calc
    (∑ e : E, edgeIncidence G v e) =
        ∑ e : E, ∑ j : Fin 2,
          if G.endAt e j = v then (1 : F₂) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Fin.sum_univ_two]
      rfl
    _ = ∑ h : HalfEdge E, if vertex G h = v then (1 : F₂) else 0 := by
      change (∑ e : E, ∑ j : Fin 2,
          if G.endAt e j = v then (1 : F₂) else 0) =
        ∑ h : E × Fin 2, if G.endAt h.1 h.2 = v then (1 : F₂) else 0
      rw [← Fintype.sum_prod_type']
    _ = (degree G v : F₂) := sum_halfEdge_indicator_eq_degree G v

lemma isEvenEdgeSet_univ_of_forall_even_degree
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (h : ∀ v : V, Even (degree G v)) :
    IsEvenEdgeSet G Finset.univ := by
  intro v
  have hv : (degree G v : F₂) = 0 := by
    rcases h v with ⟨m, hm⟩
    rw [hm]
    rw [Nat.cast_add]
    change (m : F₂) + (m : F₂) = 0
    have htwo : (2 : F₂) = 0 := by decide
    calc
      (m : F₂) + (m : F₂) = (2 : F₂) * (m : F₂) := by ring
      _ = 0 := by simp [htwo]
  simpa [sum_univ_edgeIncidence_eq_degree G v] using hv

lemma odd_iff_natCast_f2_eq_one (n : ℕ) : Odd n ↔ (n : F₂) = 1 := by
  rw [Nat.odd_iff]
  constructor
  · intro hn
    exact (ZMod.natCast_eq_natCast_iff n 1 2).mpr (by simp [Nat.ModEq, hn])
  · intro hn
    have hmod := (ZMod.natCast_eq_natCast_iff n 1 2).mp hn
    simpa [Nat.ModEq] using hmod

lemma odd_iff_of_natCast_f2_eq {m n : ℕ} (h : (m : F₂) = (n : F₂)) :
    Odd m ↔ Odd n := by
  rw [odd_iff_natCast_f2_eq_one, odd_iff_natCast_f2_eq_one, h]

lemma simpleGraph_even_oddVertices_card
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (simpleGraphOddVertices G).card := by
  have hsum : Even (∑ v : V, G.degree v) := by
    rw [G.sum_degrees_eq_twice_card_edges]
    exact even_two_mul G.edgeFinset.card
  simpa [simpleGraphOddVertices] using
    (Finset.even_sum_iff_even_card_odd (s := (Finset.univ : Finset V))
      (fun v ↦ G.degree v)).mp (by simpa using hsum)

structure OrientedPseudograph (V E : Type*) [Fintype V] [Fintype E] where
  endAt : E → Fin 2 → V

def OrientedPseudograph.edgeIncidence
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) (v : V) (e : E) : F₂ :=
  (if G.endAt e 0 = v then 1 else 0) +
    if G.endAt e 1 = v then 1 else 0

lemma OrientedPseudograph.edgeIncidence_eq_zero_of_loop
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) {e : E}
    (hloop : G.endAt e 0 = G.endAt e 1) (v : V) :
    G.edgeIncidence v e = 0 := by
  unfold OrientedPseudograph.edgeIncidence
  by_cases h0 : G.endAt e 0 = v
  · have h1 : G.endAt e 1 = v := hloop.symm.trans h0
    simp [h0, h1, show (1 : F₂) + 1 = 0 by decide]
  · have h1 : G.endAt e 1 ≠ v := by
      intro h1
      exact h0 (hloop.trans h1)
    simp [h0, h1]

def OrientedPseudograph.IsEvenEdgeSet
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) (F : Finset E) : Prop :=
  ∀ v : V, ∑ e ∈ F, G.edgeIncidence v e = 0

def OrientedPseudograph.vertex
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (h : HalfEdge E) : V :=
  G.endAt h.1 h.2

def OrientedPseudograph.halfEdgesAt
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (v : V) :=
  {h : HalfEdge E // G.vertex h = v}

instance OrientedPseudograph.halfEdgesAtFintype
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) (v : V) :
    Fintype (G.halfEdgesAt v) :=
  Subtype.fintype (fun h : HalfEdge E ↦ G.vertex h = v)

def OrientedPseudograph.degree
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) (v : V) : ℕ :=
  Fintype.card (G.halfEdgesAt v)

def OrientedPseudograph.supportGraph
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (S : Finset E) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v ↦
    ∃ e ∈ S, G.endAt e 0 = u ∧ G.endAt e 1 = v

def OrientedPseudograph.ReachableIn
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (S : Finset E) (u v : V) : Prop :=
  (G.supportGraph S).Reachable u v

def OrientedPseudograph.Connects
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (S : Finset E) : Prop :=
  (G.supportGraph S).Connected

def OrientedPseudograph.Crosses
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (S : Finset V) (e : E) : Prop :=
  (G.endAt e 0 ∈ S) ≠ (G.endAt e 1 ∈ S)

noncomputable def OrientedPseudograph.cut
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (S : Finset V) : Finset E := by
  classical
  exact Finset.univ.filter (G.Crosses S)

def OrientedPseudograph.Bridgeless
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) : Prop :=
  ∀ S : Finset V, (G.cut S).card ≠ 1

lemma OrientedPseudograph.supportGraph_adj_iff
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (S : Finset E) (u v : V) :
    (G.supportGraph S).Adj u v ↔
      u ≠ v ∧ ∃ e ∈ S,
        (G.endAt e 0 = u ∧ G.endAt e 1 = v) ∨
          (G.endAt e 0 = v ∧ G.endAt e 1 = u) := by
  simp [OrientedPseudograph.supportGraph]
  aesop

def OrientedMultigraph.toPseudograph
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) : OrientedPseudograph V E where
  endAt := G.endAt

@[simp]
lemma OrientedMultigraph.toPseudograph_endAt
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) (e : E) (j : Fin 2) :
    G.toPseudograph.endAt e j = G.endAt e j := by
  rfl

@[simp]
lemma OrientedMultigraph.toPseudograph_edgeIncidence
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (e : E) :
    G.toPseudograph.edgeIncidence v e = edgeIncidence G v e := by
  rfl

@[simp]
lemma OrientedMultigraph.toPseudograph_supportGraph
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) (S : Finset E) :
    G.toPseudograph.supportGraph S = supportGraph G S := by
  ext u v
  simp [OrientedPseudograph.supportGraph, supportGraph]

@[simp]
lemma OrientedMultigraph.toPseudograph_cut
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) (S : Finset V) :
    G.toPseudograph.cut S = cut G S := by
  ext e
  simp [OrientedPseudograph.cut, cut, OrientedPseudograph.Crosses, Crosses]

@[simp]
lemma OrientedMultigraph.toPseudograph_bridgeless
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) :
    G.toPseudograph.Bridgeless ↔ Bridgeless G := by
  simp [OrientedPseudograph.Bridgeless, Bridgeless]

lemma OrientedPseudograph.sum_halfEdge_indicator_eq_degree
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) (v : V) :
    (∑ h : HalfEdge E, if G.vertex h = v then (1 : F₂) else 0) =
      (G.degree v : F₂) := by
  have hcard : Fintype.card (G.halfEdgesAt v) =
      (Finset.univ.filter fun h : HalfEdge E ↦ G.vertex h = v).card := by
    change Fintype.card {h : HalfEdge E // G.vertex h = v} = _
    rw [Fintype.card_subtype]
  rw [OrientedPseudograph.degree, hcard]
  rw [Finset.card_eq_sum_ones]
  simp

lemma OrientedPseudograph.sum_univ_edgeIncidence_eq_degree
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) (v : V) :
    (∑ e : E, G.edgeIncidence v e) = (G.degree v : F₂) := by
  calc
    (∑ e : E, G.edgeIncidence v e) =
        ∑ e : E, ∑ j : Fin 2,
          if G.endAt e j = v then (1 : F₂) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Fin.sum_univ_two]
      rfl
    _ = ∑ h : HalfEdge E, if G.vertex h = v then (1 : F₂) else 0 := by
      change (∑ e : E, ∑ j : Fin 2,
          if G.endAt e j = v then (1 : F₂) else 0) =
        ∑ h : E × Fin 2, if G.endAt h.1 h.2 = v then (1 : F₂) else 0
      rw [← Fintype.sum_prod_type']
    _ = (G.degree v : F₂) := G.sum_halfEdge_indicator_eq_degree v

def OrientedPseudograph.oddVertices
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) : Finset V :=
  Finset.univ.filter fun v ↦ Odd (G.degree v)

def IsIncident {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) (v : V) (e : E) : Prop :=
  G.endAt e 0 = v ∨ G.endAt e 1 = v

noncomputable def incidentEdgesAt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) : Finset E := by
  classical
  exact Finset.univ.filter fun e ↦ IsIncident G v e

@[simp]
lemma mem_incidentEdgesAt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) (e : E) :
    e ∈ incidentEdgesAt G v ↔ IsIncident G v e := by
  simp [incidentEdgesAt]

noncomputable def incidentIndex
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (e : E)
    (_he : IsIncident G v e) : Fin 2 :=
  if G.endAt e 0 = v then 0 else 1

lemma incidentIndex_spec
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {e : E}
    (he : IsIncident G v e) :
    G.endAt e (incidentIndex G v e he) = v := by
  unfold incidentIndex
  by_cases h0 : G.endAt e 0 = v
  · simp [h0]
  · rcases he with he | he
    · exact (h0 he).elim
    · simp [h0, he]

noncomputable def halfEdgesAtEquivIncidentEdges
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) :
    (halfEdgesAt G v) ≃ {e : E // e ∈ incidentEdgesAt G v} where
  toFun h :=
    ⟨h.1.1, by
      rw [mem_incidentEdgesAt]
      rcases h with ⟨⟨e, j⟩, hj⟩
      dsimp [vertex] at hj
      fin_cases j
      · exact Or.inl hj
      · exact Or.inr hj⟩
  invFun e := by
    have he : IsIncident G v e.1 := (mem_incidentEdgesAt G v e.1).mp e.2
    exact ⟨(e.1, incidentIndex G v e.1 he), incidentIndex_spec G he⟩
  left_inv h := by
    rcases h with ⟨⟨e, j⟩, hj⟩
    dsimp [vertex] at hj
    fin_cases j
    · apply Subtype.ext
      have hj0 : G.endAt e 0 = v := by simpa using hj
      change (e, incidentIndex G v e (Or.inl hj0)) = (e, 0)
      simp [incidentIndex, hj0]
    · have h0 : G.endAt e 0 ≠ v := by
        intro h0
        exact G.loopless e (h0.trans hj.symm)
      apply Subtype.ext
      have hj1 : G.endAt e 1 = v := by simpa using hj
      change (e, incidentIndex G v e (Or.inr hj1)) = (e, 1)
      simp [incidentIndex, h0]
  right_inv e := by
    apply Subtype.ext
    rfl

lemma degree_eq_incidentEdgesAt_card
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) :
    degree G v = (incidentEdgesAt G v).card := by
  rw [degree]
  have hcard := Fintype.card_congr (halfEdgesAtEquivIncidentEdges G v)
  rw [hcard]
  change Fintype.card {e : E // e ∈ incidentEdgesAt G v} =
    (incidentEdgesAt G v).card
  rw [Fintype.card_subtype]
  congr 1
  ext e
  simp

lemma Finset.exists_four_distinct_of_four_le_card
    {α : Type*} {S : Finset α} (hS : 4 ≤ S.card) :
    ∃ a b c d : α,
      a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  classical
  have hSpos : 0 < S.card := by omega
  obtain ⟨a, haS⟩ := Finset.card_pos.mp hSpos
  let S₁ := S.erase a
  have hS₁card : S₁.card = S.card - 1 := by
    simp [S₁, haS]
  have hS₁ge : 3 ≤ S₁.card := by
    rw [hS₁card]
    omega
  have hS₁pos : 0 < S₁.card := by omega
  obtain ⟨b, hbS₁⟩ := Finset.card_pos.mp hS₁pos
  have hbne : b ≠ a := (Finset.mem_erase.mp hbS₁).1
  have hbS : b ∈ S := (Finset.mem_erase.mp hbS₁).2
  let S₂ := S₁.erase b
  have hS₂card : S₂.card = S₁.card - 1 := by
    simp [S₂, hbS₁]
  have hS₂ge : 2 ≤ S₂.card := by
    rw [hS₂card]
    omega
  have hS₂pos : 0 < S₂.card := by omega
  obtain ⟨c, hcS₂⟩ := Finset.card_pos.mp hS₂pos
  have hcne_b : c ≠ b := (Finset.mem_erase.mp hcS₂).1
  have hcS₁ : c ∈ S₁ := (Finset.mem_erase.mp hcS₂).2
  have hcne_a : c ≠ a := (Finset.mem_erase.mp hcS₁).1
  have hcS : c ∈ S := (Finset.mem_erase.mp hcS₁).2
  let S₃ := S₂.erase c
  have hS₃card : S₃.card = S₂.card - 1 := by
    simp [S₃, hcS₂]
  have hS₃pos : 0 < S₃.card := by
    rw [hS₃card]
    omega
  obtain ⟨d, hdS₃⟩ := Finset.card_pos.mp hS₃pos
  have hdne_c : d ≠ c := (Finset.mem_erase.mp hdS₃).1
  have hdS₂ : d ∈ S₂ := (Finset.mem_erase.mp hdS₃).2
  have hdne_b : d ≠ b := (Finset.mem_erase.mp hdS₂).1
  have hdS₁ : d ∈ S₁ := (Finset.mem_erase.mp hdS₂).2
  have hdne_a : d ≠ a := (Finset.mem_erase.mp hdS₁).1
  have hdS : d ∈ S := (Finset.mem_erase.mp hdS₁).2
  exact ⟨a, b, c, d, haS, hbS, hcS, hdS, hbne.symm,
    hcne_a.symm, hdne_a.symm, hcne_b.symm, hdne_b.symm, hdne_c.symm⟩

lemma Finset.card_le_erase_erase_add_two
    {α : Type*} [DecidableEq α] (S : Finset α) (a b : α) :
    S.card ≤ ((S.erase a).erase b).card + 2 := by
  by_cases ha : a ∈ S
  · have haCard : (S.erase a).card + 1 = S.card :=
      Finset.card_erase_add_one ha
    by_cases hb : b ∈ S.erase a
    · have hbCard : ((S.erase a).erase b).card + 1 = (S.erase a).card :=
        Finset.card_erase_add_one hb
      omega
    · have hbCard : ((S.erase a).erase b).card = (S.erase a).card :=
        congrArg Finset.card (Finset.erase_eq_of_notMem hb)
      omega
  · have haCard : (S.erase a).card = S.card :=
      congrArg Finset.card (Finset.erase_eq_of_notMem ha)
    by_cases hb : b ∈ S.erase a
    · have hbCard : ((S.erase a).erase b).card + 1 = (S.erase a).card :=
        Finset.card_erase_add_one hb
      omega
    · have hbCard : ((S.erase a).erase b).card = (S.erase a).card :=
        congrArg Finset.card (Finset.erase_eq_of_notMem hb)
      omega

lemma Finset.card_insert_insert_insert_insert
    {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset α).card = 4 := by
  simp [hab, hac, had, hbc, hbd, hcd]

lemma Finset.four_le_card_of_mem
    {α : Type*} {S : Finset α} {a b c d : α}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    4 ≤ S.card := by
  classical
  have hsub : ({a, b, c, d} : Finset α) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_insert_insert_insert hab hac had hbc hbd hcd] at hcard
  exact hcard

lemma Finset.exists_pair_not_subset_pairwise_disjoint_pairs_of_four_le_card
    {α : Type*} [DecidableEq α] {F : Finset α} (hF : 4 ≤ F.card)
    {𝒜 : Finset (Finset α)}
    (hcard : ∀ A ∈ 𝒜, A.card = 2)
    (hdisj : ∀ ⦃A B : Finset α⦄,
      A ∈ 𝒜 → B ∈ 𝒜 → A ≠ B → Disjoint A B) :
    ∃ a b : α, a ∈ F ∧ b ∈ F ∧ a ≠ b ∧
      ∀ A ∈ 𝒜, ¬ ({a, b} : Finset α) ⊆ A := by
  obtain ⟨a, b, c, _d, haF, hbF, hcF, _hdF,
    hab, hac, _had, hbc, _hbd, _hcd⟩ :=
    Finset.exists_four_distinct_of_four_le_card hF
  by_contra hno
  push Not at hno
  obtain ⟨Aab, hAab, hsubab⟩ := hno a b haF hbF hab
  obtain ⟨Aac, hAac, hsubac⟩ := hno a c haF hcF hac
  have hAab_eq : Aab = ({a, b} : Finset α) := by
    have hpair : ({a, b} : Finset α).card = 2 := Finset.card_pair hab
    exact (Finset.eq_of_subset_of_card_le hsubab
      (by rw [hcard Aab hAab, hpair])).symm
  have hAac_eq : Aac = ({a, c} : Finset α) := by
    have hpair : ({a, c} : Finset α).card = 2 := Finset.card_pair hac
    exact (Finset.eq_of_subset_of_card_le hsubac
      (by rw [hcard Aac hAac, hpair])).symm
  have hneq : Aab ≠ Aac := by
    intro h
    have hbAab : b ∈ Aab := by simp [hAab_eq]
    have hbAac : b ∈ Aac := h ▸ hbAab
    have hbPair : b ∈ ({a, c} : Finset α) := by simpa [hAac_eq] using hbAac
    rw [Finset.mem_insert, Finset.mem_singleton] at hbPair
    rcases hbPair with hba | hbc'
    · exact hab hba.symm
    · exact hbc hbc'
  have hdisjoint := hdisj hAab hAac hneq
  rw [Finset.disjoint_left] at hdisjoint
  have haAab : a ∈ Aab := by simp [hAab_eq]
  have haAac : a ∈ Aac := by simp [hAac_eq]
  exact hdisjoint haAab haAac

lemma exists_four_distinct_incident_edges_of_degree_ge_four
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} (hdeg : 4 ≤ degree G v) :
    ∃ e f g k : E,
      IsIncident G v e ∧ IsIncident G v f ∧
      IsIncident G v g ∧ IsIncident G v k ∧
      e ≠ f ∧ e ≠ g ∧ e ≠ k ∧ f ≠ g ∧ f ≠ k ∧ g ≠ k := by
  classical
  have hcard : 4 ≤ (incidentEdgesAt G v).card := by
    simpa [degree_eq_incidentEdgesAt_card G v] using hdeg
  obtain ⟨e, f, g, k, heS, hfS, hgS, hkS, hef, heg, hek, hfg, hfk, hgk⟩ :=
    Finset.exists_four_distinct_of_four_le_card hcard
  exact ⟨e, f, g, k,
    (mem_incidentEdgesAt G v e).mp heS,
    (mem_incidentEdgesAt G v f).mp hfS,
    (mem_incidentEdgesAt G v g).mp hgS,
    (mem_incidentEdgesAt G v k).mp hkS,
    hef, heg, hek, hfg, hfk, hgk⟩

lemma exists_two_remaining_incident_edges_of_degree_ge_four
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} (hdeg : 4 ≤ degree G v)
    {e f : E} (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f) :
    ∃ g k : E,
      (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
        IsIncident G v g ∧ IsIncident G v k := by
  classical
  let S := incidentEdgesAt G v
  have hcard : 4 ≤ S.card := by
    simpa [S, degree_eq_incidentEdgesAt_card G v] using hdeg
  have heS : e ∈ S := (mem_incidentEdgesAt G v e).mpr he
  have hfS : f ∈ S := (mem_incidentEdgesAt G v f).mpr hf
  have hfErase : f ∈ S.erase e := Finset.mem_erase.mpr ⟨hef.symm, hfS⟩
  have heCard : (S.erase e).card + 1 = S.card :=
    Finset.card_erase_add_one heS
  have hfCard : ((S.erase e).erase f).card + 1 = (S.erase e).card :=
    Finset.card_erase_add_one hfErase
  have htwo : 1 < ((S.erase e).erase f).card := by
    omega
  obtain ⟨g, hgRem, k, hkRem, hgk⟩ := Finset.one_lt_card.mp htwo
  have hgErase := Finset.mem_erase.mp hgRem
  have hgErase' := Finset.mem_erase.mp hgErase.2
  have hkErase := Finset.mem_erase.mp hkRem
  have hkErase' := Finset.mem_erase.mp hkErase.2
  exact ⟨g, k,
    ⟨hgErase'.1, hgErase.1⟩,
    ⟨hkErase'.1, hkErase.1⟩,
    hgk,
    (mem_incidentEdgesAt G v g).mp hgErase'.2,
    (mem_incidentEdgesAt G v k).mp hkErase'.2⟩

lemma exists_remaining_incident_edge_of_degree_ge_four_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} (hdeg : 4 ≤ degree G v)
    {p q r : E} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : IsIncident G v p) (hq : IsIncident G v q) (hr : IsIncident G v r) :
    ∃ s : E, s ≠ p ∧ s ≠ q ∧ s ≠ r ∧ IsIncident G v s := by
  classical
  let F := incidentEdgesAt G v
  have hcard : 4 ≤ F.card := by
    simpa [F, degree_eq_incidentEdgesAt_card G v] using hdeg
  have hpF : p ∈ F := (mem_incidentEdgesAt G v p).mpr hp
  have hqF : q ∈ F := (mem_incidentEdgesAt G v q).mpr hq
  have hrF : r ∈ F := (mem_incidentEdgesAt G v r).mpr hr
  have hqEraseP : q ∈ F.erase p :=
    Finset.mem_erase.mpr ⟨hpq.symm, hqF⟩
  have hrEraseP : r ∈ F.erase p :=
    Finset.mem_erase.mpr ⟨hpr.symm, hrF⟩
  have hrErasePQ : r ∈ (F.erase p).erase q :=
    Finset.mem_erase.mpr ⟨hqr.symm, hrEraseP⟩
  have hpCard : (F.erase p).card + 1 = F.card :=
    Finset.card_erase_add_one hpF
  have hqCard : ((F.erase p).erase q).card + 1 = (F.erase p).card :=
    Finset.card_erase_add_one hqEraseP
  have hrCard :
      (((F.erase p).erase q).erase r).card + 1 =
        ((F.erase p).erase q).card :=
    Finset.card_erase_add_one hrErasePQ
  have hpos : 0 < (((F.erase p).erase q).erase r).card := by
    omega
  obtain ⟨s, hsRem⟩ := Finset.card_pos.mp hpos
  have hsEraseR := Finset.mem_erase.mp hsRem
  have hsEraseQ := Finset.mem_erase.mp hsEraseR.2
  have hsEraseP := Finset.mem_erase.mp hsEraseQ.2
  exact ⟨s, hsEraseP.1, hsEraseQ.1, hsEraseR.1,
    (mem_incidentEdgesAt G v s).mp hsEraseP.2⟩

lemma incidentEdgesAt_eq_pair_of_degree_eq_two
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hdeg : degree G v = 2) (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f) :
    incidentEdgesAt G v = {e, f} := by
  have hpairSub : ({e, f} : Finset E) ⊆ incidentEdgesAt G v := by
    have he_mem : e ∈ incidentEdgesAt G v := (mem_incidentEdgesAt G v e).mpr he
    have hf_mem : f ∈ incidentEdgesAt G v := (mem_incidentEdgesAt G v f).mpr hf
    intro g hg
    rw [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with hge | hgf
    · simpa [hge] using he_mem
    · simpa [hgf] using hf_mem
  have hcard : (incidentEdgesAt G v).card = 2 := by
    simpa [degree_eq_incidentEdgesAt_card G v] using hdeg
  have hpairCard : ({e, f} : Finset E).card = 2 := Finset.card_pair hne
  have hle : (incidentEdgesAt G v).card ≤ ({e, f} : Finset E).card := by
    rw [hcard, hpairCard]
  exact (Finset.eq_of_subset_of_card_le hpairSub hle).symm

def otherEndpoint {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (e : E) : V :=
  if G.endAt e 0 = v then G.endAt e 1 else G.endAt e 0

lemma otherEndpoint_ne_of_incident
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {e : E}
    (he : IsIncident G v e) :
    otherEndpoint G v e ≠ v := by
  unfold otherEndpoint
  by_cases h0 : G.endAt e 0 = v
  · simp only [h0, ↓reduceIte]
    intro h1
    exact G.loopless e (h0.trans h1.symm)
  · rcases he with he | he
    · exact (h0 he).elim
    · simp only [h0, ↓reduceIte]
      exact h0

lemma crosses_iff_incident_otherEndpoint
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {e : E}
    (he : IsIncident G v e) (S : Finset V) :
    Crosses G S e ↔ (v ∈ S) ≠ (otherEndpoint G v e ∈ S) := by
  unfold Crosses
  by_cases h0 : G.endAt e 0 = v
  · have hother : otherEndpoint G v e = G.endAt e 1 := by
      simp [otherEndpoint, h0]
    rw [h0, hother]
  · rcases he with he | he
    · exact (h0 he).elim
    · have hother : otherEndpoint G v e = G.endAt e 0 := by
        simp [otherEndpoint, h0]
      rw [he, hother]
      constructor
      · intro h hs
        exact h hs.symm
      · intro h hs
        exact h hs.symm

lemma edgeIncidence_eq_vertex_add_otherEndpoint
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {e : E}
    (he : IsIncident G v e) (w : V) :
    edgeIncidence G w e =
      (if v = w then (1 : F₂) else 0) +
        if otherEndpoint G v e = w then (1 : F₂) else 0 := by
  unfold edgeIncidence otherEndpoint
  by_cases h0 : G.endAt e 0 = v
  · have h1ne : G.endAt e 1 ≠ v := by
      intro h1
      exact G.loopless e (h0.trans h1.symm)
    by_cases hvw : v = w
    · subst w
      simp [h0, h1ne]
    · simp [h0, hvw, eq_comm]
  · rcases he with he | he
    · exact (h0 he).elim
    · by_cases hvw : v = w
      · subst w
        simp [h0, he]
      · simp [h0, he, hvw, eq_comm]

noncomputable def incidentEdgesInto
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (S : Finset V) : Finset E := by
  classical
  exact Finset.univ.filter fun e ↦ IsIncident G v e ∧ otherEndpoint G v e ∈ S

lemma mem_incidentEdgesInto
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (S : Finset V) (e : E) :
    e ∈ incidentEdgesInto G v S ↔ IsIncident G v e ∧ otherEndpoint G v e ∈ S := by
  classical
  simp [incidentEdgesInto]

lemma incidentEdgesInto_subset_cut_of_vertex_not_mem
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V}
    (hvS : v ∉ S) :
    incidentEdgesInto G v S ⊆ cut G S := by
  intro e he
  rcases (mem_incidentEdgesInto G v S e).mp he with ⟨hev, heS⟩
  have hcross : Crosses G S e :=
    (crosses_iff_incident_otherEndpoint G hev S).mpr (by
      intro hiff
      exact hvS (hiff.mpr heS))
  simpa [cut] using hcross

lemma incidentEdgesInto_card_le_cut_card_of_vertex_not_mem
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V}
    (hvS : v ∉ S) :
    (incidentEdgesInto G v S).card ≤ (cut G S).card :=
  Finset.card_le_card (incidentEdgesInto_subset_cut_of_vertex_not_mem G hvS)

noncomputable def edgesAwayFromVertex
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) : Finset E :=
  Finset.univ \ incidentEdgesAt G v

lemma mem_edgesAwayFromVertex_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) (e : E) :
    e ∈ edgesAwayFromVertex G v ↔ ¬ IsIncident G v e := by
  classical
  simp [edgesAwayFromVertex, mem_incidentEdgesAt]

noncomputable def supportAwayFromVertex
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) : SimpleGraph V :=
  supportGraph G (edgesAwayFromVertex G v)

lemma supportAwayFromVertex_adj_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v x y : V) :
    (supportAwayFromVertex G v).Adj x y ↔
      x ≠ y ∧ ∃ e : E, ¬ IsIncident G v e ∧
        ((G.endAt e 0 = x ∧ G.endAt e 1 = y) ∨
          (G.endAt e 0 = y ∧ G.endAt e 1 = x)) := by
  rw [supportAwayFromVertex, supportGraph_adj_iff]
  constructor
  · rintro ⟨hxy, e, heAway, hend⟩
    exact ⟨hxy, e, (mem_edgesAwayFromVertex_iff G v e).mp heAway, hend⟩
  · rintro ⟨hxy, e, heAway, hend⟩
    exact ⟨hxy, e, (mem_edgesAwayFromVertex_iff G v e).mpr heAway, hend⟩

lemma supportAwayFromVertex_not_adj_left
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v x : V) :
    ¬ (supportAwayFromVertex G v).Adj v x := by
  intro h
  rcases (supportAwayFromVertex_adj_iff G v v x).mp h with
    ⟨_hvx, e, heNot, hend | hend⟩
  · exact heNot (Or.inl hend.1)
  · exact heNot (Or.inr hend.2)

lemma supportAwayFromVertex_not_adj_right
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v x : V) :
    ¬ (supportAwayFromVertex G v).Adj x v := by
  intro h
  exact supportAwayFromVertex_not_adj_left G v x h.symm

lemma supportAwayFromVertex_reachable_to_deleted_eq
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v x : V}
    (h : (supportAwayFromVertex G v).Reachable x v) :
    x = v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  have hprop :
      ∀ {a b : V}, Relation.ReflTransGen (supportAwayFromVertex G v).Adj a b →
        b = v → a = v := by
    intro a b hab
    exact Relation.ReflTransGen.trans_induction_on hab
      (fun a ↦ by intro ha; exact ha)
      (fun {a b} hadj ↦ by
        intro hb
        subst b
        exact (supportAwayFromVertex_not_adj_right G v a hadj).elim)
      (fun {_ _ _} _ _ h₁ h₂ ↦ by
        intro hc
        exact h₁ (h₂ hc))
  exact hprop h rfl

noncomputable def supportAwayComponent
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v x : V) : Finset V := by
  classical
  exact Finset.univ.filter fun y ↦ (supportAwayFromVertex G v).Reachable x y

lemma mem_supportAwayComponent
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v x y : V) :
    y ∈ supportAwayComponent G v x ↔
      (supportAwayFromVertex G v).Reachable x y := by
  simp [supportAwayComponent]

lemma self_mem_supportAwayComponent
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v x : V) :
    x ∈ supportAwayComponent G v x := by
  simp [mem_supportAwayComponent]

lemma deleted_not_mem_supportAwayComponent
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v x : V} (hxv : x ≠ v) :
    v ∉ supportAwayComponent G v x := by
  intro hv
  have hreach := (mem_supportAwayComponent G v x v).mp hv
  exact hxv (supportAwayFromVertex_reachable_to_deleted_eq G hreach)

lemma disjoint_supportAwayComponent_of_not_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v x y : V}
    (hxy : ¬ (supportAwayFromVertex G v).Reachable x y) :
    Disjoint (supportAwayComponent G v x) (supportAwayComponent G v y) := by
  rw [Finset.disjoint_left]
  intro z hzX hzY
  have hxz := (mem_supportAwayComponent G v x z).mp hzX
  have hyz := (mem_supportAwayComponent G v y z).mp hzY
  exact hxy (hxz.trans hyz.symm)

noncomputable def cutAwayFromVertex
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) (S : Finset V) : Finset E :=
  cut G S \ incidentEdgesInto G v S

lemma mem_cutAwayFromVertex_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V} (hvS : v ∉ S)
    (e : E) :
    e ∈ cutAwayFromVertex G v S ↔ Crosses G S e ∧ ¬ IsIncident G v e := by
  classical
  rw [cutAwayFromVertex, Finset.mem_sdiff]
  constructor
  · intro h
    have hcross : Crosses G S e := by
      simpa [cut] using h.1
    refine ⟨hcross, ?_⟩
    intro he
    have hside := (crosses_iff_incident_otherEndpoint G he S).mp hcross
    have hother : otherEndpoint G v e ∈ S := by
      by_contra hnot
      exact hside (propext
        ⟨fun hv ↦ (hvS hv).elim, fun ho ↦ (hnot ho).elim⟩)
    exact h.2 ((mem_incidentEdgesInto G v S e).mpr ⟨he, hother⟩)
  · rintro ⟨hcross, hnotIncident⟩
    refine ⟨by simpa [cut] using hcross, ?_⟩
    intro heInto
    exact hnotIncident ((mem_incidentEdgesInto G v S e).mp heInto).1

lemma supportAwayFromVertex_adj_same_side_of_cutAway_eq_empty
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V}
    (hvS : v ∉ S) (hcut : cutAwayFromVertex G v S = ∅)
    {x y : V} (hxy : (supportAwayFromVertex G v).Adj x y) :
    (x ∈ S) ↔ (y ∈ S) := by
  rcases (supportAwayFromVertex_adj_iff G v x y).mp hxy with
    ⟨_hxy, e, heNot, hend | hend⟩
  · by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [hx, hy]
    · have hcross : Crosses G S e := by
        simp [Crosses, hend.1, hend.2, hx, hy]
      have hmem : e ∈ cutAwayFromVertex G v S :=
        (mem_cutAwayFromVertex_iff G hvS e).mpr ⟨hcross, heNot⟩
      simp [hcut] at hmem
    · have hcross : Crosses G S e := by
        simp [Crosses, hend.1, hend.2, hx, hy]
      have hmem : e ∈ cutAwayFromVertex G v S :=
        (mem_cutAwayFromVertex_iff G hvS e).mpr ⟨hcross, heNot⟩
      simp [hcut] at hmem
  · by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [hx, hy]
    · have hcross : Crosses G S e := by
        simp [Crosses, hend.1, hend.2, hx, hy]
      have hmem : e ∈ cutAwayFromVertex G v S :=
        (mem_cutAwayFromVertex_iff G hvS e).mpr ⟨hcross, heNot⟩
      simp [hcut] at hmem
    · have hcross : Crosses G S e := by
        simp [Crosses, hend.1, hend.2, hx, hy]
      have hmem : e ∈ cutAwayFromVertex G v S :=
        (mem_cutAwayFromVertex_iff G hvS e).mpr ⟨hcross, heNot⟩
      simp [hcut] at hmem

lemma supportAwayFromVertex_reachable_same_side_of_cutAway_eq_empty
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V}
    (hvS : v ∉ S) (hcut : cutAwayFromVertex G v S = ∅)
    {x y : V} (hxy : (supportAwayFromVertex G v).Reachable x y) :
    (x ∈ S) ↔ (y ∈ S) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  exact Relation.ReflTransGen.trans_induction_on hxy
    (fun _ ↦ Iff.rfl)
    (fun {_ _} h ↦ supportAwayFromVertex_adj_same_side_of_cutAway_eq_empty
      G hvS hcut h)
    (fun {_ _ _} _ _ h₁ h₂ ↦ h₁.trans h₂)

lemma cutAwayFromVertex_nonempty_of_supportAway_reachable_crossing
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V}
    (hvS : v ∉ S) {x y : V}
    (hxy : (supportAwayFromVertex G v).Reachable x y)
    (hxS : x ∈ S) (hyS : y ∉ S) :
    (cutAwayFromVertex G v S).Nonempty := by
  by_contra hnon
  have hcut : cutAwayFromVertex G v S = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnon
  have hsame :=
    supportAwayFromVertex_reachable_same_side_of_cutAway_eq_empty
      G hvS hcut hxy
  exact hyS (hsame.mp hxS)

lemma exists_cutAwayFromVertex_edge_of_supportAway_reachable_crossing
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V}
    (hvS : v ∉ S) {x y : V}
    (hxy : (supportAwayFromVertex G v).Reachable x y)
    (hxS : x ∈ S) (hyS : y ∉ S) :
    ∃ e : E, e ∈ cutAwayFromVertex G v S ∧
      (supportAwayFromVertex G v).Reachable x (G.endAt e 0) ∧
        (supportAwayFromVertex G v).Reachable x (G.endAt e 1) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact (hyS hxS).elim
  | @head a c hac hcy ih =>
      by_cases hcS : c ∈ S
      · obtain ⟨e, heCut, hce0, hce1⟩ := ih hcS
        have hacReach : (supportAwayFromVertex G v).Reachable a c :=
          SimpleGraph.Adj.reachable hac
        exact ⟨e, heCut, hacReach.trans hce0, hacReach.trans hce1⟩
      · rcases (supportAwayFromVertex_adj_iff G v a c).mp hac with
          ⟨_hac, e, heNotIncident, hend | hend⟩
        · have hcross : Crosses G S e := by
            simp [Crosses, hend.1, hend.2, hxS, hcS]
          have heCut : e ∈ cutAwayFromVertex G v S :=
            (mem_cutAwayFromVertex_iff G hvS e).mpr ⟨hcross, heNotIncident⟩
          have hacReach : (supportAwayFromVertex G v).Reachable a c :=
            SimpleGraph.Adj.reachable hac
          exact ⟨e, heCut, by simp [hend.1],
            by simpa [hend.2] using hacReach⟩
        · have hcross : Crosses G S e := by
            simp [Crosses, hend.1, hend.2, hxS, hcS]
          have heCut : e ∈ cutAwayFromVertex G v S :=
            (mem_cutAwayFromVertex_iff G hvS e).mpr ⟨hcross, heNotIncident⟩
          have hacReach : (supportAwayFromVertex G v).Reachable a c :=
            SimpleGraph.Adj.reachable hac
          exact ⟨e, heCut, by simpa [hend.1] using hacReach,
            by simp [hend.2]⟩

lemma two_le_cutAwayFromVertex_card_of_two_supportAway_crossings
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V}
    (hvS : v ∉ S) {x x' y y' : V}
    (hxx' : (supportAwayFromVertex G v).Reachable x x')
    (hyy' : (supportAwayFromVertex G v).Reachable y y')
    (hxy : ¬ (supportAwayFromVertex G v).Reachable x y)
    (hxS : x ∈ S) (hx'S : x' ∉ S) (hyS : y ∈ S) (hy'S : y' ∉ S) :
    2 ≤ (cutAwayFromVertex G v S).card := by
  obtain ⟨a, haCut, hxa0, hxa1⟩ :=
    exists_cutAwayFromVertex_edge_of_supportAway_reachable_crossing
      G hvS hxx' hxS hx'S
  obtain ⟨b, hbCut, hyb0, _hyb1⟩ :=
    exists_cutAwayFromVertex_edge_of_supportAway_reachable_crossing
      G hvS hyy' hyS hy'S
  have hab : a ≠ b := by
    intro h
    subst b
    exact hxy (hxa0.trans hyb0.symm)
  have hpair :
      ({a, b} : Finset E) ⊆ cutAwayFromVertex G v S := by
    intro e he
    rw [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact haCut
    · exact hbCut
  have hcard := Finset.card_le_card hpair
  rw [Finset.card_pair hab] at hcard
  exact hcard

lemma cutAwayFromVertex_supportAwayComponent_eq_empty
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v x : V} (hxv : x ≠ v) :
    cutAwayFromVertex G v (supportAwayComponent G v x) = ∅ := by
  classical
  have hvS : v ∉ supportAwayComponent G v x :=
    deleted_not_mem_supportAwayComponent G hxv
  ext e
  constructor
  · intro he
    rcases (mem_cutAwayFromVertex_iff G hvS e).mp he with
      ⟨hcross, hnotIncident⟩
    have hadj :
        (supportAwayFromVertex G v).Adj (G.endAt e 0) (G.endAt e 1) := by
      rw [supportAwayFromVertex_adj_iff]
      exact ⟨G.loopless e, e, hnotIncident, .inl ⟨rfl, rfl⟩⟩
    unfold Crosses at hcross
    by_cases h0 : G.endAt e 0 ∈ supportAwayComponent G v x
    · have h1 : G.endAt e 1 ∈ supportAwayComponent G v x := by
        have hreach0 := (mem_supportAwayComponent G v x (G.endAt e 0)).mp h0
        exact (mem_supportAwayComponent G v x (G.endAt e 1)).mpr
          (hreach0.trans (SimpleGraph.Adj.reachable hadj))
      simpa using hcross (propext ⟨fun _ ↦ h1, fun _ ↦ h0⟩)
    · by_cases h1 : G.endAt e 1 ∈ supportAwayComponent G v x
      · have h0' : G.endAt e 0 ∈ supportAwayComponent G v x := by
          have hreach1 := (mem_supportAwayComponent G v x (G.endAt e 1)).mp h1
          exact (mem_supportAwayComponent G v x (G.endAt e 0)).mpr
            (hreach1.trans (SimpleGraph.Adj.reachable hadj.symm))
        simpa using h0 h0'
      · simpa using hcross (propext
          ⟨fun h ↦ (h0 h).elim, fun h ↦ (h1 h).elim⟩)
  · intro he
    simp at he

lemma cut_subset_incidentEdgesInto_of_vertex_not_mem_of_cutAway_eq_empty
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V}
    (hvS : v ∉ S) (hcutAway : cutAwayFromVertex G v S = ∅) :
    cut G S ⊆ incidentEdgesInto G v S := by
  intro e hecut
  have hcross : Crosses G S e := by
    simpa [cut] using hecut
  by_cases heIncident : IsIncident G v e
  · have hside := (crosses_iff_incident_otherEndpoint G heIncident S).mp hcross
    have hother : otherEndpoint G v e ∈ S := by
      by_contra hnot
      exact hside (propext
        ⟨fun hv ↦ (hvS hv).elim, fun ho ↦ (hnot ho).elim⟩)
    exact (mem_incidentEdgesInto G v S e).mpr ⟨heIncident, hother⟩
  · have heAway : e ∈ cutAwayFromVertex G v S :=
      (mem_cutAwayFromVertex_iff G hvS e).mpr ⟨hcross, heIncident⟩
    rw [hcutAway] at heAway
    simp at heAway

lemma cut_subset_incidentEdgesInto_supportAwayComponent
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v x : V} (hxv : x ≠ v) :
    cut G (supportAwayComponent G v x) ⊆
      incidentEdgesInto G v (supportAwayComponent G v x) := by
  exact cut_subset_incidentEdgesInto_of_vertex_not_mem_of_cutAway_eq_empty
    G (deleted_not_mem_supportAwayComponent G hxv)
      (cutAwayFromVertex_supportAwayComponent_eq_empty G hxv)

noncomputable def incidentEdgesOutside
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (S : Finset V) : Finset E := by
  classical
  exact Finset.univ.filter fun e ↦ IsIncident G v e ∧ otherEndpoint G v e ∉ S

lemma mem_incidentEdgesOutside
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (S : Finset V) (e : E) :
    e ∈ incidentEdgesOutside G v S ↔
      IsIncident G v e ∧ otherEndpoint G v e ∉ S := by
  classical
  simp [incidentEdgesOutside]

lemma disjoint_incidentEdgesInto_incidentEdgesOutside
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (S : Finset V) :
    Disjoint (incidentEdgesInto G v S) (incidentEdgesOutside G v S) := by
  classical
  rw [Finset.disjoint_left]
  intro e heIn heOut
  exact ((mem_incidentEdgesOutside G v S e).mp heOut).2
    ((mem_incidentEdgesInto G v S e).mp heIn).2

lemma incidentEdgesInto_union_incidentEdgesOutside
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) (S : Finset V) :
    incidentEdgesInto G v S ∪ incidentEdgesOutside G v S =
      incidentEdgesAt G v := by
  classical
  ext e
  by_cases he : IsIncident G v e <;>
    by_cases heS : otherEndpoint G v e ∈ S <;>
    simp [mem_incidentEdgesInto, mem_incidentEdgesOutside,
      mem_incidentEdgesAt, he, heS]

lemma incidentEdgesInto_card_add_incidentEdgesOutside_card
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (S : Finset V) :
    (incidentEdgesInto G v S).card + (incidentEdgesOutside G v S).card =
      degree G v := by
  classical
  have hdisj := disjoint_incidentEdgesInto_incidentEdgesOutside G v S
  have hcard :=
    Finset.card_union_of_disjoint hdisj
      (s := incidentEdgesInto G v S)
      (t := incidentEdgesOutside G v S)
  rw [incidentEdgesInto_union_incidentEdgesOutside G v S] at hcard
  rw [degree_eq_incidentEdgesAt_card G v]
  exact hcard.symm

abbrev SplitEdge (E : Type u) (e f : E) : Type u :=
  {g : E // g ≠ e ∧ g ≠ f} ⊕ PUnit.{u + 1}

noncomputable def splitOff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) (e f : E)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f) :
    OrientedMultigraph V (SplitEdge E e f) where
  endAt
    | Sum.inl g, j => G.endAt g.1 j
    | Sum.inr _, j => if j = 0 then otherEndpoint G v e else otherEndpoint G v f
  loopless := by
    rintro (g | _) h
    · exact G.loopless g.1 h
    · exact hnew (by simpa using h)

def splitOldEdge {E : Type u} {e f : E} (g : E) (hg : g ≠ e ∧ g ≠ f) :
    SplitEdge E e f :=
  Sum.inl ⟨g, hg⟩

def splitNewEdge {E : Type u} (e f : E) : SplitEdge E e f :=
  Sum.inr PUnit.unit

noncomputable def splitOffWithLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) (e f : E) :
    OrientedPseudograph V (SplitEdge E e f) where
  endAt
    | Sum.inl g, j => G.endAt g.1 j
    | Sum.inr _, j => if j = 0 then otherEndpoint G v e else otherEndpoint G v f

@[simp]
lemma splitOffWithLoops_endAt_old
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f g : E}
    (hg : g ≠ e ∧ g ≠ f) (j : Fin 2) :
    (splitOffWithLoops G v e f).endAt (splitOldEdge g hg) j = G.endAt g j := by
  rfl

@[simp]
lemma splitOffWithLoops_endAt_new_zero
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} :
    (splitOffWithLoops G v e f).endAt (splitNewEdge e f) 0 =
      otherEndpoint G v e := by
  simp [splitOffWithLoops, splitNewEdge]

@[simp]
lemma splitOffWithLoops_endAt_new_one
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} :
    (splitOffWithLoops G v e f).endAt (splitNewEdge e f) 1 =
      otherEndpoint G v f := by
  simp [splitOffWithLoops, splitNewEdge]

@[simp]
lemma splitOffWithLoops_toPseudograph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f) :
    (splitOff G v e f hnew).toPseudograph = splitOffWithLoops G v e f := by
  rfl

lemma splitOffWithLoops_old_isIncident_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v u : V} {e f g : E}
    (hg : g ≠ e ∧ g ≠ f) :
    (splitOffWithLoops G v e f).endAt (splitOldEdge g hg) 0 = u ∨
      (splitOffWithLoops G v e f).endAt (splitOldEdge g hg) 1 = u ↔
        IsIncident G u g := by
  constructor <;> intro h <;> simpa [IsIncident, splitOldEdge, splitOffWithLoops] using h

lemma splitOffWithLoops_new_isIncident_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v u : V} {e f : E} :
    (splitOffWithLoops G v e f).endAt (splitNewEdge e f) 0 = u ∨
      (splitOffWithLoops G v e f).endAt (splitNewEdge e f) 1 = u ↔
        otherEndpoint G v e = u ∨ otherEndpoint G v f = u := by
  constructor <;> intro h <;> simpa [splitNewEdge, splitOffWithLoops] using h

noncomputable def splitEdgePlusOneEquiv
    {E : Type u} [DecidableEq E] {e f : E} (hne : e ≠ f) :
    SplitEdge E e f ⊕ PUnit.{u + 1} ≃ E where
  toFun
    | Sum.inl (Sum.inl g) => g.1
    | Sum.inl (Sum.inr _) => e
    | Sum.inr _ => f
  invFun g :=
    if hge : g = e then
      Sum.inl (splitNewEdge e f)
    else if hgf : g = f then
      Sum.inr PUnit.unit
    else
      Sum.inl (splitOldEdge g ⟨hge, hgf⟩)
  left_inv x := by
    cases x with
    | inl x =>
        cases x with
        | inl g =>
            simp [splitOldEdge, g.2.1, g.2.2]
        | inr p =>
            cases p
            simp [splitNewEdge]
    | inr p =>
        cases p
        simp [hne.symm]
  right_inv g := by
    by_cases hge : g = e
    · simp [hge, splitNewEdge]
    · by_cases hgf : g = f
      · simp [hgf, hne.symm]
      · simp [hge, hgf, splitOldEdge]

lemma splitEdge_card_add_one
    {E : Type u} [Fintype E] [DecidableEq E] {e f : E} (hne : e ≠ f) :
    Fintype.card (SplitEdge E e f) + 1 = Fintype.card E := by
  have hcard :
      Fintype.card (SplitEdge E e f ⊕ PUnit.{u + 1}) = Fintype.card E :=
    Fintype.card_congr (splitEdgePlusOneEquiv (E := E) hne)
  simpa [Fintype.card_sum] using hcard

@[simp]
lemma splitOff_endAt_old
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f g : E}
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    (hg : g ≠ e ∧ g ≠ f) (j : Fin 2) :
    (splitOff G v e f hnew).endAt (splitOldEdge g hg) j = G.endAt g j := by
  rfl

@[simp]
lemma splitOff_endAt_new_zero
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f) :
    (splitOff G v e f hnew).endAt (splitNewEdge e f) 0 =
      otherEndpoint G v e := by
  simp [splitOff, splitNewEdge]

@[simp]
lemma splitOff_endAt_new_one
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f) :
    (splitOff G v e f hnew).endAt (splitNewEdge e f) 1 =
      otherEndpoint G v f := by
  simp [splitOff, splitNewEdge]

lemma splitOff_old_isIncident_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v u : V} {e f g : E}
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    (hg : g ≠ e ∧ g ≠ f) :
    IsIncident (splitOff G v e f hnew) u (splitOldEdge g hg) ↔
      IsIncident G u g := by
  constructor
  · intro h
    simpa [IsIncident, splitOldEdge, splitOff] using h
  · intro h
    simpa [IsIncident, splitOldEdge, splitOff] using h

lemma splitOff_new_isIncident_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v u : V} {e f : E}
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f) :
    IsIncident (splitOff G v e f hnew) u (splitNewEdge e f) ↔
      otherEndpoint G v e = u ∨ otherEndpoint G v f = u := by
  constructor
  · intro h
    simpa [IsIncident, splitNewEdge, splitOff] using h
  · intro h
    simpa [IsIncident, splitNewEdge, splitOff] using h

lemma splitOff_new_not_incident_split_vertex
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f) :
    ¬ IsIncident (splitOff G v e f hnew) v (splitNewEdge e f) := by
  rw [splitOff_new_isIncident_iff]
  rintro (heq | heq)
  · exact otherEndpoint_ne_of_incident G he heq
  · exact otherEndpoint_ne_of_incident G hf heq

def splitLiftPiece {E : Type*} [DecidableEq E] (e f : E) :
    SplitEdge E e f → Finset E
  | Sum.inl g => {g.1}
  | Sum.inr _ => {e, f}

lemma splitNewEdge_edgeIncidence_eq
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f) (w : V) :
    edgeIncidence G w e + edgeIncidence G w f =
      edgeIncidence (splitOff G v e f hnew) w (splitNewEdge e f) := by
  rw [edgeIncidence_eq_vertex_add_otherEndpoint G he w,
    edgeIncidence_eq_vertex_add_otherEndpoint G hf w]
  unfold edgeIncidence splitOff splitNewEdge
  let a : F₂ := if v = w then 1 else 0
  let b : F₂ := if otherEndpoint G v e = w then 1 else 0
  let c : F₂ := if otherEndpoint G v f = w then 1 else 0
  have hv : a + a = 0 := by
    by_cases h : v = w <;> simp [a, h, show (1 : F₂) + 1 = 0 by decide]
  have hcomm : (a + b) + (a + c) = b + c := by
    calc
      (a + b) + (a + c) = (a + a) + (b + c) := by ac_rfl
      _ = 0 + (b + c) := by rw [hv]
      _ = b + c := by simp
  change (a + b) + (a + c) =
        (if otherEndpoint G v e = w then (1 : F₂) else 0) +
      if otherEndpoint G v f = w then (1 : F₂) else 0
  rw [hcomm]

lemma splitOffWithLoops_new_edgeIncidence_eq
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (he : IsIncident G v e) (hf : IsIncident G v f) (w : V) :
    edgeIncidence G w e + edgeIncidence G w f =
      (splitOffWithLoops G v e f).edgeIncidence w (splitNewEdge e f) := by
  rw [edgeIncidence_eq_vertex_add_otherEndpoint G he w,
    edgeIncidence_eq_vertex_add_otherEndpoint G hf w]
  unfold OrientedPseudograph.edgeIncidence splitOffWithLoops splitNewEdge
  let a : F₂ := if v = w then 1 else 0
  let b : F₂ := if otherEndpoint G v e = w then 1 else 0
  let c : F₂ := if otherEndpoint G v f = w then 1 else 0
  have hv : a + a = 0 := by
    by_cases h : v = w <;> simp [a, h, show (1 : F₂) + 1 = 0 by decide]
  have hcomm : (a + b) + (a + c) = b + c := by
    calc
      (a + b) + (a + c) = (a + a) + (b + c) := by ac_rfl
      _ = 0 + (b + c) := by rw [hv]
      _ = b + c := by simp
  change (a + b) + (a + c) =
    (if otherEndpoint G v e = w then (1 : F₂) else 0) +
      if otherEndpoint G v f = w then (1 : F₂) else 0
  rw [hcomm]

def liftSplitEdgeSet {E : Type*} [DecidableEq E] (e f : E)
    (F : Finset (SplitEdge E e f)) : Finset E :=
  F.biUnion (splitLiftPiece e f)

lemma sum_splitLiftPiece_edgeIncidence
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f) (w : V)
    (x : SplitEdge E e f) :
    (∑ g ∈ splitLiftPiece e f x, edgeIncidence G w g) =
      edgeIncidence (splitOff G v e f hnew) w x := by
  cases x with
  | inl g =>
      simp [splitLiftPiece, splitOff, edgeIncidence]
      rfl
  | inr x =>
      cases x
      have hsum :
          (∑ g ∈ splitLiftPiece e f (Sum.inr PUnit.unit), edgeIncidence G w g) =
            edgeIncidence G w e + edgeIncidence G w f := by
        simp [splitLiftPiece, hne]
      rw [hsum]
      change edgeIncidence G w e + edgeIncidence G w f =
        edgeIncidence (splitOff G v e f hnew) w (splitNewEdge e f)
      exact splitNewEdge_edgeIncidence_eq G he hf hnew w

lemma sum_splitLiftPiece_pseudograph_edgeIncidence
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f) (w : V)
    (x : SplitEdge E e f) :
    (∑ g ∈ splitLiftPiece e f x, edgeIncidence G w g) =
      (splitOffWithLoops G v e f).edgeIncidence w x := by
  cases x with
  | inl g =>
      simp [splitLiftPiece, splitOffWithLoops, OrientedPseudograph.edgeIncidence,
        edgeIncidence]
      rfl
  | inr x =>
      cases x
      have hsum :
          (∑ g ∈ splitLiftPiece e f (Sum.inr PUnit.unit), edgeIncidence G w g) =
            edgeIncidence G w e + edgeIncidence G w f := by
        simp [splitLiftPiece, hne]
      rw [hsum]
      change edgeIncidence G w e + edgeIncidence G w f =
        (splitOffWithLoops G v e f).edgeIncidence w (splitNewEdge e f)
      exact splitOffWithLoops_new_edgeIncidence_eq G he hf w

lemma splitLiftPiece_disjoint
    {E : Type*} [DecidableEq E] {e f : E}
    {x y : SplitEdge E e f} (hxy : x ≠ y) :
    Disjoint (splitLiftPiece e f x) (splitLiftPiece e f y) := by
  rw [Finset.disjoint_left]
  intro z hzX hzY
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          simp only [splitLiftPiece, Finset.mem_singleton] at hzX hzY
          apply hxy
          apply congrArg Sum.inl
          exact Subtype.ext (hzX.symm.trans hzY)
      | inr y =>
          simp only [splitLiftPiece, Finset.mem_singleton] at hzX
          simp only [splitLiftPiece, Finset.mem_insert, Finset.mem_singleton] at hzY
          rcases hzY with hzY | hzY
          · exact x.2.1 (hzX.symm.trans hzY)
          · exact x.2.2 (hzX.symm.trans hzY)
  | inr x =>
      cases y with
      | inl y =>
          simp only [splitLiftPiece, Finset.mem_insert, Finset.mem_singleton] at hzX
          simp only [splitLiftPiece, Finset.mem_singleton] at hzY
          rcases hzX with hzX | hzX
          · exact y.2.1 (hzY.symm.trans hzX)
          · exact y.2.2 (hzY.symm.trans hzX)
      | inr y =>
          cases x
          cases y
          exact (hxy rfl).elim

lemma splitLiftPiece_pairwiseDisjoint
    {E : Type*} [DecidableEq E] {e f : E}
    (F : Finset (SplitEdge E e f)) :
    Set.PairwiseDisjoint (↑F) (splitLiftPiece e f) := by
  intro x _ y _ hxy
  exact splitLiftPiece_disjoint hxy

lemma sum_liftSplitEdgeSet_edgeIncidence
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    (F : Finset (SplitEdge E e f)) (w : V) :
    (∑ g ∈ liftSplitEdgeSet e f F, edgeIncidence G w g) =
      ∑ x ∈ F, edgeIncidence (splitOff G v e f hnew) w x := by
  rw [liftSplitEdgeSet, Finset.sum_biUnion (splitLiftPiece_pairwiseDisjoint F)]
  apply Finset.sum_congr rfl
  intro x _
  exact sum_splitLiftPiece_edgeIncidence G hne he hf hnew w x

lemma sum_liftSplitEdgeSet_pseudograph_edgeIncidence
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (F : Finset (SplitEdge E e f)) (w : V) :
    (∑ g ∈ liftSplitEdgeSet e f F, edgeIncidence G w g) =
      ∑ x ∈ F, (splitOffWithLoops G v e f).edgeIncidence w x := by
  rw [liftSplitEdgeSet, Finset.sum_biUnion (splitLiftPiece_pairwiseDisjoint F)]
  apply Finset.sum_congr rfl
  intro x _
  exact sum_splitLiftPiece_pseudograph_edgeIncidence G hne he hf w x

lemma liftSplitEdgeSet_even
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    {F : Finset (SplitEdge E e f)}
    (hF : IsEvenEdgeSet (splitOff G v e f hnew) F) :
    IsEvenEdgeSet G (liftSplitEdgeSet e f F) := by
  intro w
  rw [sum_liftSplitEdgeSet_edgeIncidence G hne he hf hnew F w]
  exact hF w

lemma liftSplitEdgeSet_pseudograph_even
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    {F : Finset (SplitEdge E e f)}
    (hF : (splitOffWithLoops G v e f).IsEvenEdgeSet F) :
    IsEvenEdgeSet G (liftSplitEdgeSet e f F) := by
  intro w
  rw [sum_liftSplitEdgeSet_pseudograph_edgeIncidence G hne he hf F w]
  exact hF w

lemma reachable_otherEndpoint_of_incident
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {S : Finset E} {v : V} {e : E}
    (heS : e ∈ S) (he : IsIncident G v e) :
    (ReachableIn G) S (otherEndpoint G v e) v := by
  unfold otherEndpoint
  by_cases h0 : G.endAt e 0 = v
  · simp only [h0, ↓reduceIte]
    apply SimpleGraph.Adj.reachable
    rw [supportGraph_adj_iff]
    refine ⟨?_, e, heS, .inr ⟨h0, rfl⟩⟩
    intro h
    exact G.loopless e (h0.trans h.symm)
  · rcases he with he | he
    · exact (h0 he).elim
    · simp only [h0, ↓reduceIte]
      apply SimpleGraph.Adj.reachable
      rw [supportGraph_adj_iff]
      refine ⟨?_, e, heS, .inl ⟨rfl, he⟩⟩
      intro h
      exact h0 h

lemma reachable_endpoint_to_otherEndpoint_of_incident
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {S : Finset E} {v u : V} {e : E}
    (heS : e ∈ S) (he : IsIncident G v e)
    (hu : G.endAt e 0 = u ∨ G.endAt e 1 = u) :
    (ReachableIn G) S u (otherEndpoint G v e) := by
  unfold otherEndpoint
  by_cases h0 : G.endAt e 0 = v
  · simp only [h0, ↓reduceIte]
    rcases hu with hu | hu
    · subst u
      simpa [ReachableIn, otherEndpoint, h0] using
        (reachable_otherEndpoint_of_incident G heS he).symm
    · subst u
      exact SimpleGraph.Reachable.refl _
  · rcases he with he | he
    · exact (h0 he).elim
    · simp only [h0, ↓reduceIte]
      rcases hu with hu | hu
      · subst u
        exact SimpleGraph.Reachable.refl _
      · subst u
        simpa [ReachableIn, otherEndpoint, h0, he] using
          (reachable_otherEndpoint_of_incident G heS (Or.inr he)).symm

lemma mem_liftSplitEdgeSet_old
    {E : Type*} [DecidableEq E] {e f g : E} (hg : g ≠ e ∧ g ≠ f)
    {F : Finset (SplitEdge E e f)} :
    g ∈ liftSplitEdgeSet e f F ↔ splitOldEdge g hg ∈ F := by
  constructor
  · intro h
    obtain ⟨x, hxF, hxg⟩ := Finset.mem_biUnion.mp h
    cases x with
    | inl x =>
        simp only [splitLiftPiece, Finset.mem_singleton] at hxg
        have hx : x.1 = g := hxg.symm
        subst hx
        simpa [splitOldEdge] using hxF
    | inr x =>
        simp only [splitLiftPiece, Finset.mem_insert, Finset.mem_singleton] at hxg
        rcases hxg with rfl | rfl
        · exact (hg.1 rfl).elim
        · exact (hg.2 rfl).elim
  · intro h
    apply Finset.mem_biUnion.mpr
    refine ⟨splitOldEdge g hg, h, ?_⟩
    simp [splitLiftPiece, splitOldEdge]

lemma mem_liftSplitEdgeSet_left
    {E : Type*} [DecidableEq E] {e f : E}
    {F : Finset (SplitEdge E e f)} :
    e ∈ liftSplitEdgeSet e f F ↔ splitNewEdge e f ∈ F := by
  constructor
  · intro h
    obtain ⟨x, hxF, hxe⟩ := Finset.mem_biUnion.mp h
    cases x with
    | inl x =>
        simp only [splitLiftPiece, Finset.mem_singleton] at hxe
        exact (x.2.1 hxe.symm).elim
    | inr x =>
        simpa [splitNewEdge] using hxF
  · intro h
    apply Finset.mem_biUnion.mpr
    refine ⟨splitNewEdge e f, h, ?_⟩
    simp [splitLiftPiece, splitNewEdge]

lemma mem_liftSplitEdgeSet_right
    {E : Type*} [DecidableEq E] {e f : E}
    {F : Finset (SplitEdge E e f)} :
    f ∈ liftSplitEdgeSet e f F ↔ splitNewEdge e f ∈ F := by
  constructor
  · intro h
    obtain ⟨x, hxF, hxf⟩ := Finset.mem_biUnion.mp h
    cases x with
    | inl x =>
        simp only [splitLiftPiece, Finset.mem_singleton] at hxf
        exact (x.2.2 hxf.symm).elim
    | inr x =>
        simpa [splitNewEdge] using hxF
  · intro h
    apply Finset.mem_biUnion.mpr
    refine ⟨splitNewEdge e f, h, ?_⟩
    simp [splitLiftPiece, splitNewEdge]

lemma liftSplitEdgeSet_univ
    {E : Type*} [Fintype E] [DecidableEq E] {e f : E} :
    liftSplitEdgeSet e f Finset.univ = Finset.univ := by
  ext g
  by_cases hge : g = e
  · subst g
    simp [mem_liftSplitEdgeSet_left]
  · by_cases hgf : g = f
    · subst g
      simp [mem_liftSplitEdgeSet_right]
    · have hg : g ≠ e ∧ g ≠ f := ⟨hge, hgf⟩
      simp [mem_liftSplitEdgeSet_old hg]

lemma splitOff_degree_parity
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f) (w : V) :
    (degree (splitOff G v e f hnew) w : F₂) = (degree G w : F₂) := by
  rw [← sum_univ_edgeIncidence_eq_degree G w,
    ← sum_univ_edgeIncidence_eq_degree (splitOff G v e f hnew) w]
  have hsum :=
    sum_liftSplitEdgeSet_edgeIncidence G hne he hf hnew
      (Finset.univ : Finset (SplitEdge E e f)) w
  simpa [liftSplitEdgeSet_univ] using hsum.symm

lemma splitOff_odd_degree_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f) (w : V) :
    Odd (degree (splitOff G v e f hnew) w) ↔ Odd (degree G w) := by
  exact odd_iff_of_natCast_f2_eq (splitOff_degree_parity G hne he hf hnew w)

lemma splitOff_oddVertices
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f) :
    oddVertices (splitOff G v e f hnew) = oddVertices G := by
  ext w
  simp [oddVertices, splitOff_odd_degree_iff G hne he hf hnew w]

lemma splitOffWithLoops_degree_parity
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f) (w : V) :
    ((splitOffWithLoops G v e f).degree w : F₂) = (degree G w : F₂) := by
  rw [← sum_univ_edgeIncidence_eq_degree G w,
    ← OrientedPseudograph.sum_univ_edgeIncidence_eq_degree
      (splitOffWithLoops G v e f) w]
  have hsum :=
    sum_liftSplitEdgeSet_pseudograph_edgeIncidence G hne he hf
      (Finset.univ : Finset (SplitEdge E e f)) w
  simpa [liftSplitEdgeSet_univ] using hsum.symm

lemma splitOffWithLoops_odd_degree_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f) (w : V) :
    Odd ((splitOffWithLoops G v e f).degree w) ↔ Odd (degree G w) := by
  exact odd_iff_of_natCast_f2_eq (splitOffWithLoops_degree_parity G hne he hf w)

lemma splitOffWithLoops_oddVertices
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f) :
    (splitOffWithLoops G v e f).oddVertices = oddVertices G := by
  ext w
  simp [OrientedPseudograph.oddVertices, oddVertices,
    splitOffWithLoops_odd_degree_iff G hne he hf w]

def IsAdmissibleSplit
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) (e f : E)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f) : Prop :=
  ∀ ⦃x y : V⦄, x ≠ v → y ≠ v →
    (ReachableIn G) Finset.univ x y →
      (ReachableIn (splitOff G v e f hnew)) Finset.univ x y

def IsAdmissibleSplitWithLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) (e f : E) : Prop :=
  ∀ ⦃x y : V⦄, x ≠ v → y ≠ v →
    (ReachableIn G) Finset.univ x y →
      (splitOffWithLoops G v e f).ReachableIn Finset.univ x y

lemma IsAdmissibleSplit.withLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} {e f : E}
    {hnew : otherEndpoint G v e ≠ otherEndpoint G v f}
    (h : IsAdmissibleSplit G v e f hnew) :
    IsAdmissibleSplitWithLoops G v e f := by
  intro x y hx hy hxy
  have hgraph :
      (splitOffWithLoops G v e f).supportGraph Finset.univ =
        supportGraph (splitOff G v e f hnew) Finset.univ := by
    ext a b
    simp [OrientedPseudograph.supportGraph, supportGraph, splitOffWithLoops, splitOff]
  change ((splitOffWithLoops G v e f).supportGraph Finset.univ).Reachable x y
  rw [hgraph]
  exact h hx hy hxy

lemma IsAdmissibleSplitWithLoops.toNoLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} {e f : E}
    {hnew : otherEndpoint G v e ≠ otherEndpoint G v f}
    (h : IsAdmissibleSplitWithLoops G v e f) :
    IsAdmissibleSplit G v e f hnew := by
  intro x y hx hy hxy
  have hgraph :
      supportGraph (splitOff G v e f hnew) Finset.univ =
        (splitOffWithLoops G v e f).supportGraph Finset.univ := by
    ext a b
    simp [OrientedPseudograph.supportGraph, supportGraph, splitOffWithLoops, splitOff]
  change (supportGraph (splitOff G v e f hnew) Finset.univ).Reachable x y
  rw [hgraph]
  exact h hx hy hxy

lemma splitOff_reachable_from_split_vertex_of_remaining_edge
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f g : E}
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    (hg : g ≠ e ∧ g ≠ f) (hgv : IsIncident G v g) :
    (ReachableIn (splitOff G v e f hnew)) Finset.univ v
      (otherEndpoint (splitOff G v e f hnew) v (splitOldEdge g hg)) := by
  let H := splitOff G v e f hnew
  have hinc : IsIncident H v (splitOldEdge g hg) := by
    exact (splitOff_old_isIncident_iff G hnew hg).mpr hgv
  exact (reachable_otherEndpoint_of_incident H (Finset.mem_univ _) hinc).symm

lemma splitOffWithLoops_reachable_from_split_vertex_of_remaining_edge
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f g : E}
    (hg : g ≠ e ∧ g ≠ f) (hgv : IsIncident G v g) :
    (splitOffWithLoops G v e f).ReachableIn Finset.univ v
      (otherEndpoint G v g) := by
  apply SimpleGraph.Adj.reachable
  rw [OrientedPseudograph.supportGraph_adj_iff]
  refine ⟨(otherEndpoint_ne_of_incident G hgv).symm, splitOldEdge g hg,
    Finset.mem_univ _, ?_⟩
  unfold otherEndpoint
  by_cases h0 : G.endAt g 0 = v
  · simp [h0]
  · rcases hgv with hgv | hgv
    · exact (h0 hgv).elim
    · simp [h0, hgv]

lemma splitOff_connects_of_admissible
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    (hconn : Connects G Finset.univ)
    (hadm : IsAdmissibleSplit G v e f hnew)
    (hrem : ∃ g : E, (g ≠ e ∧ g ≠ f) ∧ IsIncident G v g) :
    Connects (splitOff G v e f hnew) Finset.univ := by
  let H := splitOff G v e f hnew
  haveI : Nonempty V := hconn.nonempty
  rw [Connects]
  refine SimpleGraph.Connected.mk ?_
  intro x y
  change (ReachableIn H) Finset.univ x y
  by_cases hxv : x = v
  · subst x
    by_cases hyv : y = v
    · subst y
      exact SimpleGraph.Reachable.refl v
    · rcases hrem with ⟨g, hg, hgv⟩
      let z := otherEndpoint H v (splitOldEdge g hg)
      have hvz : (ReachableIn H) Finset.univ v z :=
        splitOff_reachable_from_split_vertex_of_remaining_edge G hnew hg hgv
      have hinc : IsIncident H v (splitOldEdge g hg) := by
        exact (splitOff_old_isIncident_iff G hnew hg).mpr hgv
      have hzv : z ≠ v := otherEndpoint_ne_of_incident H hinc
      have hzy : (ReachableIn H) Finset.univ z y :=
        hadm hzv hyv (hconn.preconnected z y)
      exact hvz.trans hzy
  · by_cases hyv : y = v
    · subst y
      rcases hrem with ⟨g, hg, hgv⟩
      let z := otherEndpoint H v (splitOldEdge g hg)
      have hvz : (ReachableIn H) Finset.univ v z :=
        splitOff_reachable_from_split_vertex_of_remaining_edge G hnew hg hgv
      have hinc : IsIncident H v (splitOldEdge g hg) := by
        exact (splitOff_old_isIncident_iff G hnew hg).mpr hgv
      have hzv : z ≠ v := otherEndpoint_ne_of_incident H hinc
      have hxz : (ReachableIn H) Finset.univ x z :=
        hadm hxv hzv (hconn.preconnected x z)
      exact hxz.trans hvz.symm
    · exact hadm hxv hyv (hconn.preconnected x y)

lemma splitOffWithLoops_connects_of_admissible
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hconn : Connects G Finset.univ)
    (hadm : IsAdmissibleSplitWithLoops G v e f)
    (hrem : ∃ g : E, (g ≠ e ∧ g ≠ f) ∧ IsIncident G v g) :
    (splitOffWithLoops G v e f).Connects Finset.univ := by
  let H := splitOffWithLoops G v e f
  haveI : Nonempty V := hconn.nonempty
  rw [OrientedPseudograph.Connects]
  refine SimpleGraph.Connected.mk ?_
  intro x y
  change H.ReachableIn Finset.univ x y
  by_cases hxv : x = v
  · subst x
    by_cases hyv : y = v
    · subst y
      exact SimpleGraph.Reachable.refl v
    · rcases hrem with ⟨g, hg, hgv⟩
      let z := otherEndpoint G v g
      have hvz : H.ReachableIn Finset.univ v z :=
        splitOffWithLoops_reachable_from_split_vertex_of_remaining_edge G hg hgv
      have hzv : z ≠ v := otherEndpoint_ne_of_incident G hgv
      have hzy : H.ReachableIn Finset.univ z y :=
        hadm hzv hyv (hconn.preconnected z y)
      exact hvz.trans hzy
  · by_cases hyv : y = v
    · subst y
      rcases hrem with ⟨g, hg, hgv⟩
      let z := otherEndpoint G v g
      have hvz : H.ReachableIn Finset.univ v z :=
        splitOffWithLoops_reachable_from_split_vertex_of_remaining_edge G hg hgv
      have hzv : z ≠ v := otherEndpoint_ne_of_incident G hgv
      have hxz : H.ReachableIn Finset.univ x z :=
        hadm hxv hzv (hconn.preconnected x z)
      exact hxz.trans hvz.symm
    · exact hadm hxv hyv (hconn.preconnected x y)

structure ReducingSplit
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) where
  left : E
  right : E
  distinct : left ≠ right
  left_incident : IsIncident G v left
  right_incident : IsIncident G v right
  endpoints_distinct : otherEndpoint G v left ≠ otherEndpoint G v right
  admissible : IsAdmissibleSplit G v left right endpoints_distinct
  remaining : ∃ g : E, (g ≠ left ∧ g ≠ right) ∧ IsIncident G v g

noncomputable abbrev ReducingSplit.graph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplit G v) :
    OrientedMultigraph V (SplitEdge E S.left S.right) :=
  splitOff G v S.left S.right S.endpoints_distinct

lemma ReducingSplit.edge_card_add_one
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplit G v) :
    Fintype.card (SplitEdge E S.left S.right) + 1 = Fintype.card E :=
  splitEdge_card_add_one S.distinct

lemma ReducingSplit.edge_card_lt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplit G v) :
    Fintype.card (SplitEdge E S.left S.right) < Fintype.card E := by
  have h := S.edge_card_add_one
  omega

lemma ReducingSplit.oddVertices_graph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplit G v) :
    oddVertices S.graph = oddVertices G :=
  splitOff_oddVertices G S.distinct S.left_incident S.right_incident
    S.endpoints_distinct

lemma ReducingSplit.connects_graph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplit G v)
    (hconn : Connects G Finset.univ) :
    Connects S.graph Finset.univ :=
  splitOff_connects_of_admissible G S.endpoints_distinct hconn
    S.admissible S.remaining

structure ReducingSplitWithLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) where
  left : E
  right : E
  distinct : left ≠ right
  left_incident : IsIncident G v left
  right_incident : IsIncident G v right
  admissible : IsAdmissibleSplitWithLoops G v left right
  remaining : ∃ g : E, (g ≠ left ∧ g ≠ right) ∧ IsIncident G v g

noncomputable abbrev ReducingSplitWithLoops.graph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v) :
    OrientedPseudograph V (SplitEdge E S.left S.right) :=
  splitOffWithLoops G v S.left S.right

def ReducingSplit.toWithLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplit G v) :
    ReducingSplitWithLoops G v where
  left := S.left
  right := S.right
  distinct := S.distinct
  left_incident := S.left_incident
  right_incident := S.right_incident
  admissible := S.admissible.withLoops
  remaining := S.remaining

def ReducingSplitWithLoops.toNoLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v)
    (hnew : otherEndpoint G v S.left ≠ otherEndpoint G v S.right) :
    ReducingSplit G v where
  left := S.left
  right := S.right
  distinct := S.distinct
  left_incident := S.left_incident
  right_incident := S.right_incident
  endpoints_distinct := hnew
  admissible := S.admissible.toNoLoops
  remaining := S.remaining

lemma ReducingSplitWithLoops.edge_card_add_one
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v) :
    Fintype.card (SplitEdge E S.left S.right) + 1 = Fintype.card E :=
  splitEdge_card_add_one S.distinct

lemma ReducingSplitWithLoops.edge_card_lt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v) :
    Fintype.card (SplitEdge E S.left S.right) < Fintype.card E := by
  have h := S.edge_card_add_one
  omega

lemma ReducingSplitWithLoops.oddVertices_graph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v) :
    S.graph.oddVertices = oddVertices G :=
  splitOffWithLoops_oddVertices G S.distinct S.left_incident S.right_incident

lemma ReducingSplitWithLoops.connects_graph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v)
    (hconn : Connects G Finset.univ) :
    S.graph.Connects Finset.univ :=
  splitOffWithLoops_connects_of_admissible G hconn S.admissible S.remaining

structure SuppressingSplit
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) where
  left : E
  right : E
  degree_two : degree G v = 2
  distinct : left ≠ right
  left_incident : IsIncident G v left
  right_incident : IsIncident G v right
  endpoints_distinct : otherEndpoint G v left ≠ otherEndpoint G v right
  connects_graph :
    Connects (splitOff G v left right endpoints_distinct) Finset.univ
  bridgeless_graph :
    Bridgeless (splitOff G v left right endpoints_distinct)

structure SuppressingSplitWithLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) where
  left : E
  right : E
  degree_two : degree G v = 2
  distinct : left ≠ right
  left_incident : IsIncident G v left
  right_incident : IsIncident G v right
  connects_graph :
    (splitOffWithLoops G v left right).Connects Finset.univ
  bridgeless_graph :
    (splitOffWithLoops G v left right).Bridgeless

noncomputable abbrev SuppressingSplit.graph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplit G v) :
    OrientedMultigraph V (SplitEdge E S.left S.right) :=
  splitOff G v S.left S.right S.endpoints_distinct

noncomputable abbrev SuppressingSplitWithLoops.graph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplitWithLoops G v) :
    OrientedPseudograph V (SplitEdge E S.left S.right) :=
  splitOffWithLoops G v S.left S.right

lemma SuppressingSplit.incidentEdgesAt_eq
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplit G v) :
    incidentEdgesAt G v = {S.left, S.right} :=
  incidentEdgesAt_eq_pair_of_degree_eq_two G S.degree_two S.distinct
    S.left_incident S.right_incident

lemma SuppressingSplitWithLoops.incidentEdgesAt_eq
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplitWithLoops G v) :
    incidentEdgesAt G v = {S.left, S.right} :=
  incidentEdgesAt_eq_pair_of_degree_eq_two G S.degree_two S.distinct
    S.left_incident S.right_incident

lemma SuppressingSplit.edge_card_add_one
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplit G v) :
    Fintype.card (SplitEdge E S.left S.right) + 1 = Fintype.card E :=
  splitEdge_card_add_one S.distinct

lemma SuppressingSplitWithLoops.edge_card_add_one
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplitWithLoops G v) :
    Fintype.card (SplitEdge E S.left S.right) + 1 = Fintype.card E :=
  splitEdge_card_add_one S.distinct

lemma SuppressingSplit.edge_card_lt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplit G v) :
    Fintype.card (SplitEdge E S.left S.right) < Fintype.card E := by
  have h := S.edge_card_add_one
  omega

lemma SuppressingSplitWithLoops.edge_card_lt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplitWithLoops G v) :
    Fintype.card (SplitEdge E S.left S.right) < Fintype.card E := by
  have h := S.edge_card_add_one
  omega

lemma SuppressingSplit.oddVertices_graph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplit G v) :
    oddVertices S.graph = oddVertices G :=
  splitOff_oddVertices G S.distinct S.left_incident S.right_incident
    S.endpoints_distinct

lemma SuppressingSplitWithLoops.oddVertices_graph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplitWithLoops G v) :
    S.graph.oddVertices = oddVertices G :=
  splitOffWithLoops_oddVertices G S.distinct S.left_incident S.right_incident

lemma split_adj_lift_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    {F : Finset (SplitEdge E e f)} {a b : V}
    (hab : ((supportGraph (splitOff G v e f hnew)) F).Adj a b) :
    (ReachableIn G) (liftSplitEdgeSet e f F) a b := by
  rw [supportGraph_adj_iff] at hab
  rcases hab with ⟨habne, x, hxF, hends⟩
  cases x with
  | inl x =>
      have hxLift : x.1 ∈ liftSplitEdgeSet e f F :=
        (mem_liftSplitEdgeSet_old x.2).mpr hxF
      apply SimpleGraph.Adj.reachable
      rw [supportGraph_adj_iff]
      rcases hends with hends | hends
      · exact ⟨habne, x.1, hxLift, .inl hends⟩
      · exact ⟨habne, x.1, hxLift, .inr hends⟩
  | inr x =>
      cases x
      have hnewF : splitNewEdge e f ∈ F := hxF
      have heLift : e ∈ liftSplitEdgeSet e f F :=
        mem_liftSplitEdgeSet_left.mpr hnewF
      have hfLift : f ∈ liftSplitEdgeSet e f F :=
        mem_liftSplitEdgeSet_right.mpr hnewF
      have hre : (ReachableIn G) (liftSplitEdgeSet e f F)
          (otherEndpoint G v e) v :=
        reachable_otherEndpoint_of_incident G heLift he
      have hrf : (ReachableIn G) (liftSplitEdgeSet e f F)
          (otherEndpoint G v f) v :=
        reachable_otherEndpoint_of_incident G hfLift hf
      rcases hends with hends | hends
      · change otherEndpoint G v e = a ∧ otherEndpoint G v f = b at hends
        rcases hends with ⟨rfl, rfl⟩
        exact hre.trans hrf.symm
      · change otherEndpoint G v e = b ∧ otherEndpoint G v f = a at hends
        rcases hends with ⟨rfl, rfl⟩
        exact hrf.trans hre.symm

lemma split_reachable_lift_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    {F : Finset (SplitEdge E e f)} {a b : V}
    (hab : (ReachableIn (splitOff G v e f hnew)) F a b) :
    (ReachableIn G) (liftSplitEdgeSet e f F) a b := by
  rw [ReachableIn, SimpleGraph.reachable_iff_reflTransGen] at hab ⊢
  exact Relation.ReflTransGen.trans_induction_on hab
    (fun _ ↦ Relation.ReflTransGen.refl)
    (fun h ↦ by
      have hr := split_adj_lift_reachable G he hf hnew h
      rwa [ReachableIn, SimpleGraph.reachable_iff_reflTransGen] at hr)
    (fun _ _ ih₁ ih₂ ↦ ih₁.trans ih₂)

lemma splitOffWithLoops_adj_lift_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (he : IsIncident G v e) (hf : IsIncident G v f)
    {F : Finset (SplitEdge E e f)} {a b : V}
    (hab : ((splitOffWithLoops G v e f).supportGraph F).Adj a b) :
    (ReachableIn G) (liftSplitEdgeSet e f F) a b := by
  rw [OrientedPseudograph.supportGraph_adj_iff] at hab
  rcases hab with ⟨habne, x, hxF, hends⟩
  cases x with
  | inl x =>
      have hxLift : x.1 ∈ liftSplitEdgeSet e f F :=
        (mem_liftSplitEdgeSet_old x.2).mpr hxF
      apply SimpleGraph.Adj.reachable
      rw [supportGraph_adj_iff]
      rcases hends with hends | hends
      · exact ⟨habne, x.1, hxLift, .inl hends⟩
      · exact ⟨habne, x.1, hxLift, .inr hends⟩
  | inr x =>
      cases x
      have hnewF : splitNewEdge e f ∈ F := hxF
      have heLift : e ∈ liftSplitEdgeSet e f F :=
        mem_liftSplitEdgeSet_left.mpr hnewF
      have hfLift : f ∈ liftSplitEdgeSet e f F :=
        mem_liftSplitEdgeSet_right.mpr hnewF
      have hre : (ReachableIn G) (liftSplitEdgeSet e f F)
          (otherEndpoint G v e) v :=
        reachable_otherEndpoint_of_incident G heLift he
      have hrf : (ReachableIn G) (liftSplitEdgeSet e f F)
          (otherEndpoint G v f) v :=
        reachable_otherEndpoint_of_incident G hfLift hf
      rcases hends with hends | hends
      · change otherEndpoint G v e = a ∧ otherEndpoint G v f = b at hends
        rcases hends with ⟨rfl, rfl⟩
        exact hre.trans hrf.symm
      · change otherEndpoint G v e = b ∧ otherEndpoint G v f = a at hends
        rcases hends with ⟨rfl, rfl⟩
        exact hrf.trans hre.symm

lemma splitOffWithLoops_reachable_lift_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (he : IsIncident G v e) (hf : IsIncident G v f)
    {F : Finset (SplitEdge E e f)} {a b : V}
    (hab : (splitOffWithLoops G v e f).ReachableIn F a b) :
    (ReachableIn G) (liftSplitEdgeSet e f F) a b := by
  rw [OrientedPseudograph.ReachableIn, SimpleGraph.reachable_iff_reflTransGen] at hab
  rw [ReachableIn, SimpleGraph.reachable_iff_reflTransGen]
  exact Relation.ReflTransGen.trans_induction_on hab
    (fun _ ↦ Relation.ReflTransGen.refl)
    (fun h ↦ by
      have hr := splitOffWithLoops_adj_lift_reachable G he hf h
      rwa [ReachableIn, SimpleGraph.reachable_iff_reflTransGen] at hr)
    (fun _ _ ih₁ ih₂ ↦ ih₁.trans ih₂)

lemma list_filter_liftSplitEdgeSet_old_length
    {E : Type*} [DecidableEq E] {e f g : E} (hg : g ≠ e ∧ g ≠ f)
    (L : List (Finset (SplitEdge E e f))) :
    ((L.map (liftSplitEdgeSet e f)).filter fun F ↦ g ∈ F).length =
      (L.filter fun F ↦ splitOldEdge g hg ∈ F).length := by
  induction L with
  | nil => simp
  | cons F L ih =>
      by_cases h : splitOldEdge g hg ∈ F <;>
        simp [mem_liftSplitEdgeSet_old hg, h, ih]

lemma list_filter_liftSplitEdgeSet_left_length
    {E : Type*} [DecidableEq E] {e f : E}
    (L : List (Finset (SplitEdge E e f))) :
    ((L.map (liftSplitEdgeSet e f)).filter fun F ↦ e ∈ F).length =
      (L.filter fun F ↦ splitNewEdge e f ∈ F).length := by
  induction L with
  | nil => simp
  | cons F L ih =>
      by_cases h : splitNewEdge e f ∈ F <;>
        simp [mem_liftSplitEdgeSet_left, h, ih]

lemma list_filter_liftSplitEdgeSet_right_length
    {E : Type*} [DecidableEq E] {e f : E}
    (L : List (Finset (SplitEdge E e f))) :
    ((L.map (liftSplitEdgeSet e f)).filter fun F ↦ f ∈ F).length =
      (L.filter fun F ↦ splitNewEdge e f ∈ F).length := by
  induction L with
  | nil => simp
  | cons F L ih =>
      by_cases h : splitNewEdge e f ∈ F <;>
        simp [mem_liftSplitEdgeSet_right, h, ih]

lemma CubicGraph.two_mul_cotree_card_of_spanningTree
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (K : CubicGraph V E) {T : Finset E}
    (hT : IsSpanningTree K.toOrientedMultigraph T) :
    2 * (Finset.univ \ T).card = Fintype.card V + 2 := by
  have hE := K.two_mul_edge_card_eq_three_mul_vertex_card
  have hTcard := hT.2
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ T)]
  simp only [Finset.card_univ]
  omega

lemma degree_eq_two_add_odd_indicator_of_eq_two_or_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V}
    (hdeg : degree G v = 2 ∨ degree G v = 3) :
    degree G v = 2 + if Odd (degree G v) then 1 else 0 := by
  rcases hdeg with hdeg | hdeg <;> rw [hdeg] <;> norm_num

open scoped Classical in
lemma sum_degrees_eq_two_mul_vertex_card_add_oddVertices_card_of_degrees_two_or_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E)
    (hdeg : ∀ v : V, degree G v = 2 ∨ degree G v = 3) :
    (∑ v : V, degree G v) =
      2 * Fintype.card V + (oddVertices G).card := by
  classical
  calc
    (∑ v : V, degree G v) =
        ∑ v : V, (2 + if Odd (degree G v) then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro v _
          exact degree_eq_two_add_odd_indicator_of_eq_two_or_three G (hdeg v)
    _ = (∑ _ : V, 2) + ∑ v : V, (if Odd (degree G v) then 1 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = 2 * Fintype.card V + (oddVertices G).card := by
          have hconst : (∑ _ : V, 2) = 2 * Fintype.card V := by
            simp [Nat.mul_comm]
          have hodd :
              (∑ v : V, (if Odd (degree G v) then 1 else 0)) =
                (oddVertices G).card := by
            rw [Finset.card_eq_sum_ones]
            simp [oddVertices]
          rw [hconst, hodd]

lemma two_mul_cotree_card_eq_oddVertices_card_add_two_of_degrees_two_or_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {T : Finset E}
    (hT : IsSpanningTree G T)
    (hdeg : ∀ v : V, degree G v = 2 ∨ degree G v = 3) :
    2 * (Finset.univ \ T).card = (oddVertices G).card + 2 := by
  have hsum :=
    sum_degrees_eq_two_mul_vertex_card_add_oddVertices_card_of_degrees_two_or_three
      G hdeg
  have hhand := sum_degrees_eq_two_mul_edge_card G
  have hE :
      2 * Fintype.card E = 2 * Fintype.card V + (oddVertices G).card := by
    omega
  have hTcard := hT.2
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ]
  omega

lemma not_reachableIn_erase_of_mem_spanningTree {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq E] (G : OrientedMultigraph V E) [Nonempty V]
    {T : Finset E} (hT : IsSpanningTree G T) {e : E} (he : e ∈ T) :
    ¬ (ReachableIn G) (T.erase e) (G.endAt e 0) (G.endAt e 1) := by
  intro hecyc
  have hc : (Connects G) (T.erase e) := by
    rw [Connects, SimpleGraph.connected_iff]
    exact ⟨fun u v ↦ (reachableIn_erase_of_cyclic G) ⟨he, hecyc⟩
      (hT.1.1 u v), hT.1.2⟩
  obtain ⟨U, hUsub, hU⟩ := (exists_isSpanningTree_subset_of_connects G) _ hc
  have hcard' : U.card + 1 = T.card + 1 := hU.2.trans hT.2.symm
  have hcard : U.card = T.card := Nat.add_right_cancel hcard'
  have hle := Finset.card_le_card hUsub
  have hp : 0 < T.card := Finset.card_pos.mpr ⟨e, he⟩
  rw [hcard, Finset.card_erase_of_mem he] at hle
  omega

def IncidentVertex {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) (F : Finset E) (v : V) : Prop :=
  ∃ e ∈ F, G.endAt e 0 = v ∨ G.endAt e 1 = v

def EdgeSupportConnected {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) (F : Finset E) : Prop :=
  ∀ ⦃u v : V⦄, IncidentVertex G F u → IncidentVertex G F v →
    (ReachableIn G) F u v

lemma edgeSupportConnected_of_connects {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) {F : Finset E} (hF : Connects G F) :
    EdgeSupportConnected G F := by
  intro u v _ _
  exact hF.preconnected u v

lemma endpoint_reachable_of_edge_mem {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) {F : Finset E} {e : E} (he : e ∈ F) :
    (ReachableIn G) F (G.endAt e 0) (G.endAt e 1) := by
  apply SimpleGraph.Adj.reachable
  rw [supportGraph_adj_iff]
  exact ⟨G.loopless e, e, he, .inl ⟨rfl, rfl⟩⟩

def OrientedPseudograph.IncidentVertex
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (F : Finset E) (v : V) : Prop :=
  ∃ e ∈ F, G.endAt e 0 = v ∨ G.endAt e 1 = v

def OrientedPseudograph.EdgeSupportConnected
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (F : Finset E) : Prop :=
  ∀ ⦃u v : V⦄, G.IncidentVertex F u → G.IncidentVertex F v →
    G.ReachableIn F u v

lemma OrientedPseudograph.edgeSupportConnected_of_connects
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) {F : Finset E} (hF : G.Connects F) :
    G.EdgeSupportConnected F := by
  intro u v _ _
  exact hF.preconnected u v

lemma OrientedPseudograph.endpoint_reachable_of_edge_mem
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) {F : Finset E} {e : E} (he : e ∈ F) :
    G.ReachableIn F (G.endAt e 0) (G.endAt e 1) := by
  by_cases hloop : G.endAt e 0 = G.endAt e 1
  · simp [hloop, OrientedPseudograph.ReachableIn]
  · apply SimpleGraph.Adj.reachable
    rw [OrientedPseudograph.supportGraph_adj_iff]
    exact ⟨hloop, e, he, .inl ⟨rfl, rfl⟩⟩

lemma OrientedPseudograph.reachableIn_mono
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) {S T : Finset E} (hST : S ⊆ T)
    {u v : V} (h : G.ReachableIn S u v) : G.ReachableIn T u v := by
  apply h.mono
  intro x y hxy
  rw [OrientedPseudograph.supportGraph_adj_iff] at hxy ⊢
  aesop

structure OrientedPseudograph.Circuit
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) where
  edges : Finset E
  nonempty : edges.Nonempty
  even : G.IsEvenEdgeSet edges
  connected : G.EdgeSupportConnected edges

structure OrientedPseudograph.CircuitDoubleCover
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) where
  circuits : List G.Circuit
  coveredTwice : ∀ e : E, (circuits.filter fun C ↦ e ∈ C.edges).length = 2

noncomputable def OrientedPseudograph.loopCircuit
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) (e : E)
    (hloop : G.endAt e 0 = G.endAt e 1) : G.Circuit where
  edges := {e}
  nonempty := by simp
  even := by
    intro v
    rw [Finset.sum_singleton]
    unfold OrientedPseudograph.edgeIncidence
    by_cases h0 : G.endAt e 0 = v
    · have h1 : G.endAt e 1 = v := hloop.symm.trans h0
      simp [h0, h1, show (1 : F₂) + 1 = 0 by decide]
    · have h1 : G.endAt e 1 ≠ v := by
        intro h1
        exact h0 (hloop.trans h1)
      simp [h0, h1]
  connected := by
    intro u w hu hw
    rcases hu with ⟨g, hg, hgu⟩
    rcases hw with ⟨k, hk, hkw⟩
    have hge : g = e := Finset.mem_singleton.mp hg
    have hke : k = e := Finset.mem_singleton.mp hk
    subst g
    subst k
    have hu0 : G.endAt e 0 = u := by
      rcases hgu with hgu | hgu
      · exact hgu
      · exact hloop.trans hgu
    have hw0 : G.endAt e 0 = w := by
      rcases hkw with hkw | hkw
      · exact hkw
      · exact hloop.trans hkw
    change G.ReachableIn {e} u w
    rw [← hu0, ← hw0]
    exact SimpleGraph.Reachable.refl (G.endAt e 0)

@[simp]
lemma OrientedPseudograph.mem_loopCircuit_edges
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) (e f : E)
    (hloop : G.endAt e 0 = G.endAt e 1) :
    f ∈ (G.loopCircuit e hloop).edges ↔ f = e := by
  simp [OrientedPseudograph.loopCircuit]

def OrientedPseudograph.LoopEdge
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) :=
  {e : E // G.endAt e 0 = G.endAt e 1}

noncomputable instance OrientedPseudograph.loopEdgeFintype
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) : Fintype G.LoopEdge :=
  Subtype.fintype fun e : E ↦ G.endAt e 0 = G.endAt e 1

instance OrientedPseudograph.loopEdgeDecidableEq
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : OrientedPseudograph V E) : DecidableEq G.LoopEdge :=
  fun e f ↦
    if h : e.1 = f.1 then
      isTrue (Subtype.ext h)
    else
      isFalse fun hef ↦ h (congrArg Subtype.val hef)

noncomputable def OrientedPseudograph.loopCircuitListFrom
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) : List G.LoopEdge → List G.Circuit
  | [] => []
  | e :: L => G.loopCircuit e.1 e.2 :: G.loopCircuit e.1 e.2 ::
      G.loopCircuitListFrom L

lemma OrientedPseudograph.loopCircuitListFrom_filter_length
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) {L : List G.LoopEdge}
    (hL : L.Nodup) (e : G.LoopEdge) :
    ((G.loopCircuitListFrom L).filter fun C ↦ e.1 ∈ C.edges).length =
      if e ∈ L then 2 else 0 := by
  induction L generalizing e with
  | nil =>
      simp [OrientedPseudograph.loopCircuitListFrom]
  | cons x L ih =>
      rw [List.nodup_cons] at hL
      rcases hL with ⟨hxL, hnodup⟩
      by_cases hex : e = x
      · subst e
        have hnot : x ∉ L := hxL
        have htail :
            ((G.loopCircuitListFrom L).filter fun C ↦ x.1 ∈ C.edges).length = 0 := by
          simpa [hnot] using ih hnodup x
        simp [OrientedPseudograph.loopCircuitListFrom, htail]
      · have hval : e.1 ≠ x.1 := by
          intro h
          exact hex (Subtype.ext h)
        have htail := ih hnodup e
        simp [OrientedPseudograph.loopCircuitListFrom, hex, hval, htail]

noncomputable def OrientedPseudograph.loopCircuitList
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) : List G.Circuit :=
  G.loopCircuitListFrom Finset.univ.toList

@[simp]
lemma OrientedPseudograph.loopCircuitListFrom_length
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) (L : List G.LoopEdge) :
    (G.loopCircuitListFrom L).length = 2 * L.length := by
  induction L with
  | nil =>
      simp [OrientedPseudograph.loopCircuitListFrom]
  | cons e L ih =>
      simp [OrientedPseudograph.loopCircuitListFrom, ih]
      omega

@[simp]
lemma OrientedPseudograph.loopCircuitList_length
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) :
    G.loopCircuitList.length = 2 * Fintype.card G.LoopEdge := by
  rw [OrientedPseudograph.loopCircuitList,
    OrientedPseudograph.loopCircuitListFrom_length, Finset.length_toList]
  simp

lemma OrientedPseudograph.loopCircuitList_filter_length_of_loop
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) (e : G.LoopEdge) :
    (G.loopCircuitList.filter fun C ↦ e.1 ∈ C.edges).length = 2 := by
  rw [OrientedPseudograph.loopCircuitList,
    G.loopCircuitListFrom_filter_length (Finset.nodup_toList _) e]
  simp

lemma OrientedPseudograph.loopCircuitList_filter_length_of_nonloop
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) {e : E}
    (hno : G.endAt e 0 ≠ G.endAt e 1) :
    (G.loopCircuitList.filter fun C ↦ e ∈ C.edges).length = 0 := by
  rw [OrientedPseudograph.loopCircuitList]
  induction (Finset.univ.toList : List G.LoopEdge) with
  | nil =>
      simp [OrientedPseudograph.loopCircuitListFrom]
  | cons x L ih =>
      have hval : e ≠ x.1 := by
        intro h
        exact hno (by simpa [h] using x.2)
      simp [OrientedPseudograph.loopCircuitListFrom, hval, ih]

def OrientedPseudograph.NonloopEdge
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) :=
  {e : E // G.endAt e 0 ≠ G.endAt e 1}

noncomputable instance OrientedPseudograph.nonloopEdgeFintype
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) : Fintype G.NonloopEdge :=
  Subtype.fintype fun e : E ↦ G.endAt e 0 ≠ G.endAt e 1

instance OrientedPseudograph.nonloopEdgeDecidableEq
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : OrientedPseudograph V E) : DecidableEq G.NonloopEdge :=
  fun e f ↦
    if h : e.1 = f.1 then
      isTrue (Subtype.ext h)
    else
      isFalse fun hef ↦ h (congrArg Subtype.val hef)

def OrientedPseudograph.nonloopEdgeEmbedding
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) : G.NonloopEdge ↪ E where
  toFun e := e.1
  inj' := fun _ _ h ↦ Subtype.ext h

noncomputable def OrientedPseudograph.nonloopSubgraph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) :
    OrientedMultigraph V G.NonloopEdge where
  endAt e j := G.endAt e.1 j
  loopless e := e.2

@[simp]
lemma OrientedPseudograph.nonloopSubgraph_endAt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) (e : G.NonloopEdge) (j : Fin 2) :
    G.nonloopSubgraph.endAt e j = G.endAt e.1 j := by
  rfl

@[simp]
lemma OrientedPseudograph.nonloopSubgraph_edgeIncidence
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) (v : V) (e : G.NonloopEdge) :
    OrientedMultigraph.edgeIncidence G.nonloopSubgraph v e =
      G.edgeIncidence v e.1 := by
  rfl

lemma OrientedPseudograph.nonloopSubgraph_degree_parity
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) (v : V) :
    (_root_.CycleDoubleCoverConjecture.degree G.nonloopSubgraph v : F₂) =
      (G.degree v : F₂) := by
  have hdecomp := Fintype.sum_subtype_add_sum_subtype
    (p := fun e : E ↦ G.endAt e 0 ≠ G.endAt e 1)
    (f := fun e : E ↦ G.edgeIncidence v e)
  have hloop :
      (∑ e : {e : E // ¬G.endAt e 0 ≠ G.endAt e 1},
        G.edgeIncidence v e.1) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    exact G.edgeIncidence_eq_zero_of_loop (not_not.mp e.2) v
  have hnonloop :
      (∑ e : G.NonloopEdge, G.edgeIncidence v e.1) =
        ∑ e : E, G.edgeIncidence v e := by
    rw [← hdecomp]
    rw [hloop, add_zero]
    rfl
  calc
    (_root_.CycleDoubleCoverConjecture.degree G.nonloopSubgraph v : F₂) =
        ∑ e : G.NonloopEdge,
          OrientedMultigraph.edgeIncidence G.nonloopSubgraph v e := by
      exact (_root_.CycleDoubleCoverConjecture.sum_univ_edgeIncidence_eq_degree
        G.nonloopSubgraph v).symm
    _ = ∑ e : G.NonloopEdge, G.edgeIncidence v e.1 := by
      simp
    _ = ∑ e : E, G.edgeIncidence v e := hnonloop
    _ = (G.degree v : F₂) := G.sum_univ_edgeIncidence_eq_degree v

lemma OrientedPseudograph.oddVertices_nonloopSubgraph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) :
    _root_.CycleDoubleCoverConjecture.oddVertices G.nonloopSubgraph =
      G.oddVertices := by
  ext v
  have hodd := odd_iff_of_natCast_f2_eq
    (G.nonloopSubgraph_degree_parity v)
  simp [_root_.CycleDoubleCoverConjecture.oddVertices,
    OrientedPseudograph.oddVertices, hodd]

noncomputable def OrientedPseudograph.nonloopEdgesIn
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (S : Finset E) : Finset G.NonloopEdge := by
  classical
  exact Finset.univ.filter fun e : G.NonloopEdge ↦ e.1 ∈ S

@[simp]
lemma OrientedPseudograph.mem_nonloopEdgesIn
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (S : Finset E) (e : G.NonloopEdge) :
    e ∈ G.nonloopEdgesIn S ↔ e.1 ∈ S := by
  classical
  simp [OrientedPseudograph.nonloopEdgesIn]

@[simp]
lemma OrientedPseudograph.nonloopEdgesIn_univ
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) :
    G.nonloopEdgesIn Finset.univ = Finset.univ := by
  ext e
  simp

lemma OrientedPseudograph.supportGraph_nonloopSubgraph_nonloopEdgesIn
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) (S : Finset E) :
    _root_.CycleDoubleCoverConjecture.supportGraph G.nonloopSubgraph
        (G.nonloopEdgesIn S) =
      G.supportGraph S := by
  ext u v
  constructor
  · intro h
    rw [_root_.CycleDoubleCoverConjecture.supportGraph_adj_iff] at h
    rw [OrientedPseudograph.supportGraph_adj_iff]
    rcases h with ⟨huv, e, heS, hends⟩
    refine ⟨huv, e.1, (G.mem_nonloopEdgesIn S e).mp heS, ?_⟩
    simpa using hends
  · intro h
    rw [OrientedPseudograph.supportGraph_adj_iff] at h
    rw [_root_.CycleDoubleCoverConjecture.supportGraph_adj_iff]
    rcases h with ⟨huv, e, heS, hends⟩
    have hnonloop : G.endAt e 0 ≠ G.endAt e 1 := by
      intro hloop
      rcases hends with hends | hends
      · exact huv (hends.1.symm.trans (hloop.trans hends.2))
      · exact huv (hends.2.symm.trans (hloop.symm.trans hends.1))
    refine ⟨huv, ⟨e, hnonloop⟩, ?_, ?_⟩
    · exact (G.mem_nonloopEdgesIn S ⟨e, hnonloop⟩).mpr heS
    · simpa using hends

lemma OrientedPseudograph.reachableIn_nonloopSubgraph_nonloopEdgesIn_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) (S : Finset E) (u v : V) :
    _root_.CycleDoubleCoverConjecture.ReachableIn G.nonloopSubgraph
        (G.nonloopEdgesIn S) u v ↔
      G.ReachableIn S u v := by
  rw [_root_.CycleDoubleCoverConjecture.ReachableIn,
    OrientedPseudograph.ReachableIn,
    OrientedPseudograph.supportGraph_nonloopSubgraph_nonloopEdgesIn]

lemma OrientedPseudograph.supportGraph_nonloopSubgraph_univ
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) :
    _root_.CycleDoubleCoverConjecture.supportGraph G.nonloopSubgraph Finset.univ =
      G.supportGraph Finset.univ := by
  rw [← G.nonloopEdgesIn_univ]
  exact G.supportGraph_nonloopSubgraph_nonloopEdgesIn Finset.univ

lemma OrientedPseudograph.connects_nonloopSubgraph_nonloopEdgesIn_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) (S : Finset E) :
    _root_.CycleDoubleCoverConjecture.Connects G.nonloopSubgraph
        (G.nonloopEdgesIn S) ↔
      G.Connects S := by
  rw [_root_.CycleDoubleCoverConjecture.Connects, OrientedPseudograph.Connects,
    OrientedPseudograph.supportGraph_nonloopSubgraph_nonloopEdgesIn]

lemma OrientedPseudograph.connects_nonloopSubgraph_univ_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) :
    _root_.CycleDoubleCoverConjecture.Connects G.nonloopSubgraph Finset.univ ↔
      G.Connects Finset.univ := by
  rw [← G.nonloopEdgesIn_univ]
  exact G.connects_nonloopSubgraph_nonloopEdgesIn_iff Finset.univ

lemma OrientedPseudograph.cut_nonloopSubgraph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) (S : Finset V) :
    _root_.CycleDoubleCoverConjecture.OrientedMultigraph.cut G.nonloopSubgraph S =
      G.nonloopEdgesIn (G.cut S) := by
  classical
  ext e
  simp [_root_.CycleDoubleCoverConjecture.OrientedMultigraph.cut,
    OrientedPseudograph.cut,
    _root_.CycleDoubleCoverConjecture.OrientedMultigraph.Crosses,
    OrientedPseudograph.Crosses]

lemma OrientedPseudograph.mem_cut_nonloop
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) {S : Finset V} {e : E}
    (he : e ∈ G.cut S) :
    G.endAt e 0 ≠ G.endAt e 1 := by
  intro hloop
  have hcross : G.Crosses S e := by
    simpa [OrientedPseudograph.cut] using he
  exact hcross (by rw [hloop])

lemma OrientedPseudograph.map_nonloopEdgesIn_cut
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (S : Finset V) :
    (G.nonloopEdgesIn (G.cut S)).map G.nonloopEdgeEmbedding = G.cut S := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_map.mp he with ⟨f, hf, rfl⟩
    exact (G.mem_nonloopEdgesIn (G.cut S) f).mp hf
  · intro he
    exact Finset.mem_map_of_mem G.nonloopEdgeEmbedding
      ((G.mem_nonloopEdgesIn (G.cut S) ⟨e, G.mem_cut_nonloop he⟩).mpr he)

lemma OrientedPseudograph.card_nonloopEdgesIn_cut
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (S : Finset V) :
    (G.nonloopEdgesIn (G.cut S)).card = (G.cut S).card := by
  have hmap := congrArg Finset.card (G.map_nonloopEdgesIn_cut S)
  simpa using hmap

lemma OrientedPseudograph.bridgeless_nonloopSubgraph_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) :
    _root_.CycleDoubleCoverConjecture.OrientedMultigraph.Bridgeless
        G.nonloopSubgraph ↔ G.Bridgeless := by
  constructor
  · intro hb S hcard
    have hcard' :
        (_root_.CycleDoubleCoverConjecture.OrientedMultigraph.cut
            G.nonloopSubgraph S).card = 1 := by
      rw [G.cut_nonloopSubgraph S, G.card_nonloopEdgesIn_cut S, hcard]
    exact hb S hcard'
  · intro hb S hcard
    rw [G.cut_nonloopSubgraph S, G.card_nonloopEdgesIn_cut S] at hcard
    exact hb S hcard

lemma splitOffWithLoops_loopEdge_val_eq_new
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (x : (splitOffWithLoops G v e f).LoopEdge) :
    x.1 = splitNewEdge e f := by
  rcases x with ⟨x, hx⟩
  cases x with
  | inl g =>
      exfalso
      exact G.loopless g.1 (by simpa [splitOffWithLoops] using hx)
  | inr u =>
      cases u
      rfl

instance splitOffWithLoops_loopEdge_subsingleton
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} :
    Subsingleton (splitOffWithLoops G v e f).LoopEdge where
  allEq x y := by
    apply Subtype.ext
    rw [splitOffWithLoops_loopEdge_val_eq_new G x,
      splitOffWithLoops_loopEdge_val_eq_new G y]

lemma splitOffWithLoops_loopEdge_card_le_one
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} :
    Fintype.card (splitOffWithLoops G v e f).LoopEdge ≤ 1 := by
  exact Fintype.card_le_one_iff_subsingleton.mpr
    (splitOffWithLoops_loopEdge_subsingleton G)

lemma splitOffWithLoops_nonloopEdge_card_lt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f) :
    Fintype.card (splitOffWithLoops G v e f).NonloopEdge < Fintype.card E := by
  have hle :
      Fintype.card (splitOffWithLoops G v e f).NonloopEdge ≤
        Fintype.card (SplitEdge E e f) :=
    Fintype.card_subtype_le fun x : SplitEdge E e f ↦
      (splitOffWithLoops G v e f).endAt x 0 ≠
        (splitOffWithLoops G v e f).endAt x 1
  exact lt_of_le_of_lt hle (by
    have h := splitEdge_card_add_one hne
    omega)

lemma ReducingSplitWithLoops.nonloop_edge_card_lt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v) :
    Fintype.card S.graph.NonloopEdge < Fintype.card E :=
  splitOffWithLoops_nonloopEdge_card_lt G S.distinct

lemma SuppressingSplitWithLoops.nonloop_edge_card_lt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplitWithLoops G v) :
    Fintype.card S.graph.NonloopEdge < Fintype.card E :=
  splitOffWithLoops_nonloopEdge_card_lt G S.distinct

structure Circuit {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) where
  edges : Finset E
  nonempty : edges.Nonempty
  even : IsEvenEdgeSet G edges
  connected : EdgeSupportConnected G edges

structure CircuitDoubleCover {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : OrientedMultigraph V E) where
  circuits : List (Circuit G)
  coveredTwice : ∀ e : E, (circuits.filter fun C ↦ e ∈ C.edges).length = 2

lemma simpleGraphAsGraph_toOrientedMultigraph_connects
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hconn : G.Connected) :
    Connects ((simpleGraphAsGraph G).toOrientedMultigraph
      (simpleGraphAsGraph_loopless G)) Finset.univ := by
  classical
  let H := simpleGraphAsGraph G
  let O := H.toOrientedMultigraph (simpleGraphAsGraph_loopless G)
  haveI : Nonempty H.Vertex := by
    letI : Nonempty V := hconn.nonempty
    exact ⟨⟨Classical.choice inferInstance, Set.mem_univ _⟩⟩
  rw [Connects]
  refine SimpleGraph.Connected.mk ?_
  intro x y
  have hxy : G.Reachable x.1 y.1 := hconn x.1 y.1
  have hstep {a b : V} (hab : G.Adj a b) :
      ((supportGraph O) Finset.univ).Reachable
        (⟨a, Set.mem_univ a⟩ : H.Vertex)
        (⟨b, Set.mem_univ b⟩ : H.Vertex) := by
    apply SimpleGraph.Adj.reachable
    rw [supportGraph_adj_iff]
    let e : H.Edge := ⟨s(a, b), by
      simpa [H, simpleGraphAsGraph, SimpleGraph.mem_edgeSet] using hab⟩
    have hlink :
        H.IsLink e.1 (O.endAt e 0).1 (O.endAt e 1).1 := by
      simpa [O, H, e] using H.toOrientedMultigraph_isLink
        (simpleGraphAsGraph_loopless G) e
    have hlink_ab : H.IsLink e.1 a b := by
      change e.1 ∈ G.edgeSet ∧ e.1 = s(a, b)
      exact ⟨e.2, rfl⟩
    have hend := hlink_ab.eq_and_eq_or_eq_and_eq hlink
    refine ⟨by
      intro h
      exact hab.ne (congrArg Subtype.val h), e, Finset.mem_univ _, ?_⟩
    rcases hend with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact Or.inl ⟨Subtype.ext h0.symm, Subtype.ext h1.symm⟩
    · exact Or.inr ⟨Subtype.ext h1.symm, Subtype.ext h0.symm⟩
  have hsub :
      ((supportGraph O) Finset.univ).Reachable
        (⟨x.1, Set.mem_univ x.1⟩ : H.Vertex)
        (⟨y.1, Set.mem_univ y.1⟩ : H.Vertex) :=
    reachable_map_of_adj_reachable
      (fun a : V => (⟨a, Set.mem_univ a⟩ : H.Vertex))
      (fun {a b} hab => hstep hab) hxy
  simpa [H] using hsub

lemma mem_simpleGraphEdgeValSet_iff
    {V : Type*} (G : SimpleGraph V)
    (F : Finset (simpleGraphAsGraph G).Edge) {e : Sym2 V}
    (he : e ∈ G.edgeSet) :
    e ∈ simpleGraphEdgeValSet G F ↔
      (⟨e, he⟩ : (simpleGraphAsGraph G).Edge) ∈ F := by
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨f, hf, hval⟩
    have hf_eq : f = ⟨e, he⟩ := by
      apply Subtype.ext
      simpa [simpleGraphAsGraphEdgeEmbedding] using hval
    simpa [hf_eq] using hf
  · intro h
    exact Finset.mem_map.mpr ⟨⟨e, he⟩, h, rfl⟩

lemma simpleGraphEdgeValSet_univ
    {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    simpleGraphEdgeValSet G
      (Finset.univ : Finset (simpleGraphAsGraph G).Edge) =
        G.edgeFinset := by
  ext e
  constructor
  · intro he
    exact SimpleGraph.mem_edgeFinset.mpr
      (simpleGraphEdgeValSet_subset_edgeSet G _ e he)
  · intro he
    exact (mem_simpleGraphEdgeValSet_iff G _ (SimpleGraph.mem_edgeFinset.mp he)).mpr
      (Finset.mem_univ _)

lemma simpleGraphAsGraph_toOrientedMultigraph_degree_parity
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] :
    (degree ((simpleGraphAsGraph G).toOrientedMultigraph
      (simpleGraphAsGraph_loopless G))
        (⟨v, Set.mem_univ v⟩ : (simpleGraphAsGraph G).Vertex) : F₂) =
      (G.degree v : F₂) := by
  classical
  haveI : Fintype G.edgeSet :=
    @Subtype.fintype (Sym2 V) (fun e ↦ e ∈ G.edgeSet)
      (Classical.decPred _) inferInstance
  let H := simpleGraphAsGraph G
  let O := H.toOrientedMultigraph (simpleGraphAsGraph_loopless G)
  have hfilter :
      ((simpleGraphEdgeValSet G (Finset.univ : Finset H.Edge)).filter
          fun e ↦ v ∈ e).card = G.degree v := by
    rw [simpleGraphEdgeValSet_univ G]
    rw [← G.incidenceFinset_eq_filter (v := v)]
    exact G.card_incidenceFinset_eq_degree (v := v)
  calc
    (degree O (⟨v, Set.mem_univ v⟩ : H.Vertex) : F₂) =
        ∑ e : H.Edge, edgeIncidence O (⟨v, Set.mem_univ v⟩ : H.Vertex) e := by
          rw [sum_univ_edgeIncidence_eq_degree]
    _ = ∑ e : H.Edge, H.edgeIncidence (⟨v, Set.mem_univ v⟩ : H.Vertex) e := by
          apply Finset.sum_congr rfl
          intro e _
          exact H.toOrientedMultigraph_edgeIncidence
            (simpleGraphAsGraph_loopless G)
            (⟨v, Set.mem_univ v⟩ : H.Vertex) e
    _ = (∑ e ∈ (Finset.univ : Finset H.Edge),
          H.edgeIncidence (⟨v, Set.mem_univ v⟩ : H.Vertex) e) := by
          simp
    _ = (((simpleGraphEdgeValSet G
          (Finset.univ : Finset H.Edge)).filter fun e ↦ v ∈ e).card : F₂) := by
          rw [simpleGraphAsGraph_sum_edgeIncidence_eq_card_filter]
    _ = (G.degree v : F₂) := by
          simp [hfilter]

lemma simpleGraph_not_reachable_delete_leaf_edge
    {V : Type*} (G : SimpleGraph V)
    {v u : V} [Fintype (G.neighborSet v)]
    (hdeg : G.degree v = 1) (huv : G.Adj v u) :
    ¬ (G.deleteEdges ({s(v, u)} : Set (Sym2 V))).Reachable v u := by
  classical
  intro hreach
  obtain ⟨w, hvw, huniq⟩ :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  have huw : u = w := huniq u huv
  rcases hreach with ⟨p⟩
  cases p with
  | nil =>
      exact huv.ne rfl
  | cons hfirst p =>
      rcases SimpleGraph.deleteEdges_adj.mp hfirst with ⟨hG, hnot⟩
      have hxw := huniq _ hG
      exact hnot (by
        simp [huw, hxw])

lemma simpleGraph_degree_ne_one_of_forall_not_isBridge
    {V : Type*} (G : SimpleGraph V)
    (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) (v : V)
    [Fintype (G.neighborSet v)] :
    G.degree v ≠ 1 := by
  intro hdeg
  obtain ⟨u, huv, _⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  have hbridge : G.IsBridge s(v, u) := by
    rw [SimpleGraph.isBridge_iff]
    exact simpleGraph_not_reachable_delete_leaf_edge G hdeg huv
  exact (hb s(v, u) (by simpa using huv)) hbridge

lemma simpleGraphAsGraph_incidentVertex_of_edgeValSet
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {F : Finset (simpleGraphAsGraph G).Edge} {u : V}
    (hu : ∃ e ∈ simpleGraphEdgeValSet G F, u ∈ e) :
    IncidentVertex
      ((simpleGraphAsGraph G).toOrientedMultigraph
        (simpleGraphAsGraph_loopless G))
      F (⟨u, Set.mem_univ u⟩ : (simpleGraphAsGraph G).Vertex) := by
  classical
  let H := simpleGraphAsGraph G
  let O := H.toOrientedMultigraph (simpleGraphAsGraph_loopless G)
  rcases hu with ⟨e, heF, hue⟩
  rcases Finset.mem_map.mp heF with ⟨f, hf, hval⟩
  have huef : u ∈ f.1 := by
    rw [← hval] at hue
    simpa [simpleGraphAsGraphEdgeEmbedding] using hue
  have hinc : H.IsNonloopAt f.1 u :=
    (simpleGraphAsGraph_isNonloopAt G f.2 u).mpr huef
  have hlink :
      H.IsLink f.1 (O.endAt f 0).1 (O.endAt f 1).1 := by
    simpa [O, H] using H.toOrientedMultigraph_isLink
      (simpleGraphAsGraph_loopless G) f
  refine ⟨f, hf, ?_⟩
  rcases hinc.inc.eq_or_eq_of_isLink hlink with h0 | h1
  · exact Or.inl (Subtype.ext h0.symm)
  · exact Or.inr (Subtype.ext h1.symm)

lemma simpleGraph_fromEdgeSet_reachable_of_toOrientedMultigraph_reachable
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {F : Finset (simpleGraphAsGraph G).Edge}
    {u v : (simpleGraphAsGraph G).Vertex}
    (h : (ReachableIn
      ((simpleGraphAsGraph G).toOrientedMultigraph
        (simpleGraphAsGraph_loopless G))) F u v) :
    (SimpleGraph.fromEdgeSet (simpleGraphEdgeValSet G F : Set (Sym2 V))).Reachable
      u.1 v.1 := by
  classical
  let H := simpleGraphAsGraph G
  let O := H.toOrientedMultigraph (simpleGraphAsGraph_loopless G)
  have hstep {x y : H.Vertex}
      (hxy : ((supportGraph O) F).Adj x y) :
      (SimpleGraph.fromEdgeSet (simpleGraphEdgeValSet G F : Set (Sym2 V))).Reachable
        x.1 y.1 := by
    apply SimpleGraph.Adj.reachable
    rw [supportGraph_adj_iff] at hxy
    rcases hxy with ⟨hxy_ne, e, heF, hend⟩
    rw [SimpleGraph.fromEdgeSet_adj]
    have hlink :
        H.IsLink e.1 (O.endAt e 0).1 (O.endAt e 1).1 := by
      simpa [O, H] using H.toOrientedMultigraph_isLink
        (simpleGraphAsGraph_loopless G) e
    have heVal : e.1 ∈ simpleGraphEdgeValSet G F :=
      Finset.mem_map_of_mem (simpleGraphAsGraphEdgeEmbedding G) heF
    refine ⟨?_, fun hval => hxy_ne (Subtype.ext hval)⟩
    rcases hend with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have heq : e.1 = s(x.1, y.1) := by
        simpa [h0, h1] using hlink.2
      simpa [heq] using heVal
    · have heq : e.1 = s(y.1, x.1) := by
        simpa [h0, h1] using hlink.2
      simpa [heq, Sym2.eq_swap] using heVal
  exact reachable_map_of_adj_reachable
    (fun x : H.Vertex => x.1) (fun {x y} hxy => hstep hxy) h

theorem Circuit.exists_simpleGraphCircuit
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (C : Circuit ((simpleGraphAsGraph G).toOrientedMultigraph
      (simpleGraphAsGraph_loopless G))) :
    ∃ p : Σ v, G.Walk v v,
      p.2.IsCircuit ∧ p.2.edges.toFinset = simpleGraphEdgeValSet G C.edges := by
  classical
  let H := simpleGraphAsGraph G
  let O := H.toOrientedMultigraph (simpleGraphAsGraph_loopless G)
  have hGraphEven : H.IsEvenEdgeSet C.edges := by
    intro v
    calc
      ∑ e ∈ C.edges, H.edgeIncidence v e =
          ∑ e ∈ C.edges, edgeIncidence O v e := by
            apply Finset.sum_congr rfl
            intro e _
            exact (H.toOrientedMultigraph_edgeIncidence
              (simpleGraphAsGraph_loopless G) v e).symm
      _ = 0 := C.even v
  obtain ⟨v, p, hp, hpEdges⟩ :=
    SimpleGraph.exists_isCircuit_edges_eq_of_connected_even G
      (simpleGraphEdgeValSet G C.edges)
      (simpleGraphEdgeValSet_subset_edgeSet G C.edges)
      (simpleGraphEdgeValSet_nonempty G C.nonempty)
      ((simpleGraphAsGraph_isEvenEdgeSet_iff G C.edges).mp hGraphEven)
      (by
        intro u v hu hv
        exact simpleGraph_fromEdgeSet_reachable_of_toOrientedMultigraph_reachable G
          (C.connected
            (simpleGraphAsGraph_incidentVertex_of_edgeValSet G hu)
            (simpleGraphAsGraph_incidentVertex_of_edgeValSet G hv)))
  exact ⟨⟨v, p⟩, hp, hpEdges⟩

noncomputable def Circuit.toSimpleGraphCircuit
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (C : Circuit ((simpleGraphAsGraph G).toOrientedMultigraph
      (simpleGraphAsGraph_loopless G))) :
    Σ v, G.Walk v v :=
  Classical.choose (Circuit.exists_simpleGraphCircuit G C)

lemma Circuit.toSimpleGraphCircuit_isCircuit
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (C : Circuit ((simpleGraphAsGraph G).toOrientedMultigraph
      (simpleGraphAsGraph_loopless G))) :
    (Circuit.toSimpleGraphCircuit G C).2.IsCircuit :=
  (Classical.choose_spec (Circuit.exists_simpleGraphCircuit G C)).1

lemma Circuit.toSimpleGraphCircuit_edges_toFinset
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (C : Circuit ((simpleGraphAsGraph G).toOrientedMultigraph
      (simpleGraphAsGraph_loopless G))) :
    (Circuit.toSimpleGraphCircuit G C).2.edges.toFinset =
      simpleGraphEdgeValSet G C.edges :=
  (Classical.choose_spec (Circuit.exists_simpleGraphCircuit G C)).2

lemma Circuit.toSimpleGraphCircuit_mem_edges_iff
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (C : Circuit ((simpleGraphAsGraph G).toOrientedMultigraph
      (simpleGraphAsGraph_loopless G))) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    e ∈ (Circuit.toSimpleGraphCircuit G C).2.edges ↔
      (⟨e, he⟩ : (simpleGraphAsGraph G).Edge) ∈ C.edges := by
  have hfin := Circuit.toSimpleGraphCircuit_edges_toFinset G C
  rw [← List.mem_toFinset, hfin]
  exact mem_simpleGraphEdgeValSet_iff G C.edges he

noncomputable def CircuitDoubleCover.toSimpleGraphCircuitDoubleCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (M : CircuitDoubleCover ((simpleGraphAsGraph G).toOrientedMultigraph
      (simpleGraphAsGraph_loopless G))) :
    SimpleGraphCircuitDoubleCover G where
  circuits := M.circuits.map (Circuit.toSimpleGraphCircuit G)
  isCircuit := by
    intro p hp
    rw [List.mem_map] at hp
    rcases hp with ⟨C, _, rfl⟩
    exact Circuit.toSimpleGraphCircuit_isCircuit G C
  coveredTwice := by
    intro e he
    have hfilter (L : List (Circuit ((simpleGraphAsGraph G).toOrientedMultigraph
        (simpleGraphAsGraph_loopless G)))) :
        ((L.map (Circuit.toSimpleGraphCircuit G)).filter fun p ↦
            e ∈ p.2.edges).length =
          (L.filter fun C ↦
            (⟨e, he⟩ : (simpleGraphAsGraph G).Edge) ∈ C.edges).length := by
      induction L with
      | nil => simp
      | cons C L ih =>
          by_cases hC : (⟨e, he⟩ : (simpleGraphAsGraph G).Edge) ∈ C.edges
          · have hp : e ∈ (Circuit.toSimpleGraphCircuit G C).2.edges :=
              (Circuit.toSimpleGraphCircuit_mem_edges_iff G C he).mpr hC
            simp [hC, hp, ih]
          · have hp : e ∉ (Circuit.toSimpleGraphCircuit G C).2.edges := by
              intro hp
              exact hC ((Circuit.toSimpleGraphCircuit_mem_edges_iff G C he).mp hp)
            simp [hC, hp, ih]
    rw [hfilter]
    exact M.coveredTwice ⟨e, he⟩

@[simp]
lemma CircuitDoubleCover.toSimpleGraphCircuitDoubleCover_length
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (M : CircuitDoubleCover ((simpleGraphAsGraph G).toOrientedMultigraph
      (simpleGraphAsGraph_loopless G))) :
    (CircuitDoubleCover.toSimpleGraphCircuitDoubleCover G M).circuits.length =
      M.circuits.length := by
  simp [CircuitDoubleCover.toSimpleGraphCircuitDoubleCover]

lemma OrientedPseudograph.nonloop_reachable_lift
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) {F : Finset G.NonloopEdge} {u v : V}
    (h : _root_.CycleDoubleCoverConjecture.ReachableIn G.nonloopSubgraph F u v) :
    G.ReachableIn (F.map G.nonloopEdgeEmbedding) u v := by
  rw [_root_.CycleDoubleCoverConjecture.ReachableIn,
    SimpleGraph.reachable_iff_reflTransGen] at h
  rw [OrientedPseudograph.ReachableIn, SimpleGraph.reachable_iff_reflTransGen]
  exact Relation.ReflTransGen.trans_induction_on h
    (fun _ ↦ Relation.ReflTransGen.refl)
    (fun hab ↦ by
      apply Relation.ReflTransGen.single
      rw [_root_.CycleDoubleCoverConjecture.supportGraph_adj_iff] at hab
      rw [OrientedPseudograph.supportGraph_adj_iff]
      rcases hab with ⟨hne, e, heF, hends⟩
      exact ⟨hne, e.1, Finset.mem_map_of_mem G.nonloopEdgeEmbedding heF, by simpa using hends⟩)
    (fun _ _ ih₁ ih₂ ↦ ih₁.trans ih₂)

lemma OrientedPseudograph.incidentVertex_of_nonloop_map
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedPseudograph V E) {F : Finset G.NonloopEdge} {u : V}
    (hu : G.IncidentVertex (F.map G.nonloopEdgeEmbedding) u) :
    _root_.CycleDoubleCoverConjecture.IncidentVertex G.nonloopSubgraph F u := by
  rcases hu with ⟨e, he, heu⟩
  rcases Finset.mem_map.mp he with ⟨f, hfF, rfl⟩
  exact ⟨f, hfF, by simpa [OrientedPseudograph.nonloopEdgeEmbedding] using heu⟩

noncomputable def OrientedPseudograph.Circuit.ofNonloop
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E)
    (C : _root_.CycleDoubleCoverConjecture.Circuit G.nonloopSubgraph) :
    G.Circuit where
  edges := C.edges.map G.nonloopEdgeEmbedding
  nonempty := by
    rcases C.nonempty with ⟨e, he⟩
    exact ⟨G.nonloopEdgeEmbedding e, Finset.mem_map_of_mem G.nonloopEdgeEmbedding he⟩
  even := by
    intro v
    calc
      ∑ e ∈ C.edges.map G.nonloopEdgeEmbedding, G.edgeIncidence v e =
          ∑ e ∈ C.edges, G.edgeIncidence v (G.nonloopEdgeEmbedding e) := by
        rw [Finset.sum_map]
      _ = ∑ e ∈ C.edges, OrientedMultigraph.edgeIncidence G.nonloopSubgraph v e := by
        apply Finset.sum_congr rfl
        intro e _
        simp [OrientedPseudograph.nonloopEdgeEmbedding]
      _ = 0 := C.even v
  connected := by
    intro u v hu hv
    exact G.nonloop_reachable_lift
      (C.connected (G.incidentVertex_of_nonloop_map hu)
        (G.incidentVertex_of_nonloop_map hv))

lemma OrientedPseudograph.mem_ofNonloop_edges_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E)
    (C : _root_.CycleDoubleCoverConjecture.Circuit G.nonloopSubgraph)
    (e : G.NonloopEdge) :
    e.1 ∈ (OrientedPseudograph.Circuit.ofNonloop G C).edges ↔ e ∈ C.edges := by
  simp [OrientedPseudograph.Circuit.ofNonloop, OrientedPseudograph.nonloopEdgeEmbedding]

lemma OrientedPseudograph.not_mem_ofNonloop_edges_of_loop
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E)
    (C : _root_.CycleDoubleCoverConjecture.Circuit G.nonloopSubgraph)
    {e : E} (hloop : G.endAt e 0 = G.endAt e 1) :
    e ∉ (OrientedPseudograph.Circuit.ofNonloop G C).edges := by
  intro he
  rcases Finset.mem_map.mp he with ⟨f, _hf, hfe⟩
  have hfe' : f.1 = e := by
    simpa [OrientedPseudograph.nonloopEdgeEmbedding] using hfe
  exact f.2 (by simpa [hfe'] using hloop)

lemma OrientedPseudograph.list_filter_ofNonloop_length
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) (e : G.NonloopEdge)
    (L : List (_root_.CycleDoubleCoverConjecture.Circuit G.nonloopSubgraph)) :
    ((L.map (OrientedPseudograph.Circuit.ofNonloop G)).filter
        fun C ↦ e.1 ∈ C.edges).length =
      (L.filter fun C ↦ decide (e ∈ C.edges)).length := by
  induction L with
  | nil => simp
  | cons C L ih =>
      by_cases h : e ∈ C.edges <;>
        simp [OrientedPseudograph.mem_ofNonloop_edges_iff, h, ih]

lemma OrientedPseudograph.list_filter_ofNonloop_length_of_loop
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) {e : E}
    (hloop : G.endAt e 0 = G.endAt e 1)
    (L : List (_root_.CycleDoubleCoverConjecture.Circuit G.nonloopSubgraph)) :
    ((L.map (OrientedPseudograph.Circuit.ofNonloop G)).filter
        fun C ↦ e ∈ C.edges).length = 0 := by
  induction L with
  | nil => simp
  | cons C L ih =>
      have hnot := G.not_mem_ofNonloop_edges_of_loop C hloop
      simp [hnot, ih]

noncomputable def OrientedPseudograph.Circuit.withLoop
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) (C : G.Circuit) {l : E}
    (hloop : G.endAt l 0 = G.endAt l 1)
    (hinc : G.IncidentVertex C.edges (G.endAt l 0)) : G.Circuit where
  edges := insert l C.edges
  nonempty := ⟨l, Finset.mem_insert_self l C.edges⟩
  even := by
    intro v
    by_cases hlC : l ∈ C.edges
    · have hinsert : insert l C.edges = C.edges := Finset.insert_eq_of_mem hlC
      simpa [hinsert] using C.even v
    · rw [Finset.sum_insert hlC]
      rw [G.edgeIncidence_eq_zero_of_loop hloop v, zero_add]
      exact C.even v
  connected := by
    intro u w hu hw
    have hcases :
        ∀ {x : V}, G.IncidentVertex (insert l C.edges) x →
          G.IncidentVertex C.edges x ∨ x = G.endAt l 0 := by
      intro x hx
      rcases hx with ⟨e, he, hex⟩
      rw [Finset.mem_insert] at he
      rcases he with rfl | heC
      · right
        rcases hex with hex | hex
        · exact hex.symm
        · exact (hloop.trans hex).symm
      · exact .inl ⟨e, heC, hex⟩
    rcases hcases hu with huC | rfl
    · rcases hcases hw with hwC | rfl
      · exact G.reachableIn_mono (Finset.subset_insert l C.edges)
          (C.connected huC hwC)
      · exact (G.reachableIn_mono (Finset.subset_insert l C.edges)
          (C.connected hinc huC)).symm
    · rcases hcases hw with hwC | rfl
      · exact G.reachableIn_mono (Finset.subset_insert l C.edges)
          (C.connected hinc hwC)
      · exact SimpleGraph.Reachable.refl (G.endAt l 0)

@[simp]
lemma OrientedPseudograph.mem_withLoop_edges
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) (C : G.Circuit) {l e : E}
    (hloop : G.endAt l 0 = G.endAt l 1)
    (hinc : G.IncidentVertex C.edges (G.endAt l 0)) :
    e ∈ (C.withLoop G hloop hinc).edges ↔ e = l ∨ e ∈ C.edges := by
  simp [OrientedPseudograph.Circuit.withLoop]

noncomputable def OrientedPseudograph.Circuit.ofNonloopAbsorbingLoop
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) {l : E}
    (hloop : G.endAt l 0 = G.endAt l 1) (a : G.NonloopEdge)
    (ha : G.endAt a.1 0 = G.endAt l 0 ∨ G.endAt a.1 1 = G.endAt l 0)
    (C : _root_.CycleDoubleCoverConjecture.Circuit G.nonloopSubgraph) :
    G.Circuit :=
  if haC : a ∈ C.edges then
    (OrientedPseudograph.Circuit.ofNonloop G C).withLoop G hloop
      ⟨a.1, (G.mem_ofNonloop_edges_iff C a).mpr haC, ha⟩
  else
    OrientedPseudograph.Circuit.ofNonloop G C

lemma OrientedPseudograph.mem_ofNonloopAbsorbingLoop_nonloop_edges_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) {l : E}
    (hloop : G.endAt l 0 = G.endAt l 1) (a b : G.NonloopEdge)
    (ha : G.endAt a.1 0 = G.endAt l 0 ∨ G.endAt a.1 1 = G.endAt l 0)
    (C : _root_.CycleDoubleCoverConjecture.Circuit G.nonloopSubgraph) :
    b.1 ∈ (OrientedPseudograph.Circuit.ofNonloopAbsorbingLoop G hloop a ha C).edges ↔
      b ∈ C.edges := by
  have hbl : b.1 ≠ l := by
    intro h
    exact b.2 (by simpa [h] using hloop)
  by_cases haC : a ∈ C.edges
  · simp [OrientedPseudograph.Circuit.ofNonloopAbsorbingLoop, haC,
      OrientedPseudograph.mem_ofNonloop_edges_iff, hbl]
  · simp [OrientedPseudograph.Circuit.ofNonloopAbsorbingLoop, haC,
      OrientedPseudograph.mem_ofNonloop_edges_iff]

lemma OrientedPseudograph.mem_ofNonloopAbsorbingLoop_loop_edges_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) {l : E}
    (hloop : G.endAt l 0 = G.endAt l 1) (a : G.NonloopEdge)
    (ha : G.endAt a.1 0 = G.endAt l 0 ∨ G.endAt a.1 1 = G.endAt l 0)
    (C : _root_.CycleDoubleCoverConjecture.Circuit G.nonloopSubgraph) :
    l ∈ (OrientedPseudograph.Circuit.ofNonloopAbsorbingLoop G hloop a ha C).edges ↔
      a ∈ C.edges := by
  by_cases haC : a ∈ C.edges
  · simp [OrientedPseudograph.Circuit.ofNonloopAbsorbingLoop, haC]
  · have hlnot :
        l ∉ (OrientedPseudograph.Circuit.ofNonloop G C).edges :=
      G.not_mem_ofNonloop_edges_of_loop C hloop
    simp [OrientedPseudograph.Circuit.ofNonloopAbsorbingLoop, haC, hlnot]

lemma OrientedPseudograph.list_filter_ofNonloopAbsorbingLoop_nonloop_length
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) {l : E}
    (hloop : G.endAt l 0 = G.endAt l 1) (a b : G.NonloopEdge)
    (ha : G.endAt a.1 0 = G.endAt l 0 ∨ G.endAt a.1 1 = G.endAt l 0)
    (L : List (_root_.CycleDoubleCoverConjecture.Circuit G.nonloopSubgraph)) :
    ((L.map (OrientedPseudograph.Circuit.ofNonloopAbsorbingLoop G hloop a ha)).filter
        fun C ↦ b.1 ∈ C.edges).length =
      (L.filter fun C ↦ b ∈ C.edges).length := by
  induction L with
  | nil => simp
  | cons C L ih =>
      by_cases hbC : b ∈ C.edges <;>
        simp [OrientedPseudograph.mem_ofNonloopAbsorbingLoop_nonloop_edges_iff,
          hbC, ih]

lemma OrientedPseudograph.list_filter_ofNonloopAbsorbingLoop_loop_length
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) {l : E}
    (hloop : G.endAt l 0 = G.endAt l 1) (a : G.NonloopEdge)
    (ha : G.endAt a.1 0 = G.endAt l 0 ∨ G.endAt a.1 1 = G.endAt l 0)
    (L : List (_root_.CycleDoubleCoverConjecture.Circuit G.nonloopSubgraph)) :
    ((L.map (OrientedPseudograph.Circuit.ofNonloopAbsorbingLoop G hloop a ha)).filter
        fun C ↦ l ∈ C.edges).length =
      (L.filter fun C ↦ a ∈ C.edges).length := by
  induction L with
  | nil => simp
  | cons C L ih =>
      by_cases haC : a ∈ C.edges <;>
        simp [OrientedPseudograph.mem_ofNonloopAbsorbingLoop_loop_edges_iff,
          haC, ih]

noncomputable def OrientedPseudograph.CircuitDoubleCover.ofNonloopAbsorbingLoop
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) {l : E}
    (hloop : G.endAt l 0 = G.endAt l 1)
    (honly : ∀ e : E, G.endAt e 0 = G.endAt e 1 → e = l)
    (a : G.NonloopEdge)
    (ha : G.endAt a.1 0 = G.endAt l 0 ∨ G.endAt a.1 1 = G.endAt l 0)
    (M : _root_.CycleDoubleCoverConjecture.CircuitDoubleCover G.nonloopSubgraph) :
    G.CircuitDoubleCover where
  circuits := M.circuits.map
    (OrientedPseudograph.Circuit.ofNonloopAbsorbingLoop G hloop a ha)
  coveredTwice := by
    intro e
    by_cases heLoop : G.endAt e 0 = G.endAt e 1
    · have hel : e = l := honly e heLoop
      subst e
      have hfilter :=
        G.list_filter_ofNonloopAbsorbingLoop_loop_length hloop a ha M.circuits
      exact hfilter.trans (M.coveredTwice a)
    · let e' : G.NonloopEdge := ⟨e, heLoop⟩
      have hfilter :=
        G.list_filter_ofNonloopAbsorbingLoop_nonloop_length hloop a e' ha
          M.circuits
      simpa [e'] using hfilter.trans (M.coveredTwice e')

@[simp]
lemma OrientedPseudograph.CircuitDoubleCover.ofNonloopAbsorbingLoop_length
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) {l : E}
    (hloop : G.endAt l 0 = G.endAt l 1)
    (honly : ∀ e : E, G.endAt e 0 = G.endAt e 1 → e = l)
    (a : G.NonloopEdge)
    (ha : G.endAt a.1 0 = G.endAt l 0 ∨ G.endAt a.1 1 = G.endAt l 0)
    (M : _root_.CycleDoubleCoverConjecture.CircuitDoubleCover G.nonloopSubgraph) :
    (OrientedPseudograph.CircuitDoubleCover.ofNonloopAbsorbingLoop
      G hloop honly a ha M).circuits.length = M.circuits.length := by
  simp [OrientedPseudograph.CircuitDoubleCover.ofNonloopAbsorbingLoop]

theorem OrientedPseudograph.exists_circuitDoubleCover_length_le_of_nonloopSubgraph_absorb_loop
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) {l : E}
    (hloop : G.endAt l 0 = G.endAt l 1)
    (honly : ∀ e : E, G.endAt e 0 = G.endAt e 1 → e = l)
    (a : G.NonloopEdge)
    (ha : G.endAt a.1 0 = G.endAt l 0 ∨ G.endAt a.1 1 = G.endAt l 0)
    {k : ℕ}
    (h : ∃ M : _root_.CycleDoubleCoverConjecture.CircuitDoubleCover G.nonloopSubgraph,
      M.circuits.length ≤ k) :
    ∃ M : G.CircuitDoubleCover, M.circuits.length ≤ k := by
  rcases h with ⟨M, hM⟩
  exact ⟨OrientedPseudograph.CircuitDoubleCover.ofNonloopAbsorbingLoop
    G hloop honly a ha M, by simpa using hM⟩

lemma OrientedPseudograph.exists_crossing_edge_on_walk
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) {T : Finset E} {S : Finset V}
    {x y : V} (p : (G.supportGraph T).Walk x y)
    (hx : x ∈ S) (hy : y ∉ S) :
    ∃ e ∈ T, G.Crosses S e := by
  induction p with
  | nil =>
      exact (hy hx).elim
  | @cons x z y hxz p ih =>
      by_cases hz : z ∈ S
      · exact ih hz hy
      · rw [OrientedPseudograph.supportGraph_adj_iff] at hxz
        rcases hxz with ⟨_, e, heT, hend⟩
        refine ⟨e, heT, ?_⟩
        rcases hend with hend | hend
        · simp [OrientedPseudograph.Crosses, hend, hx, hz]
        · simp [OrientedPseudograph.Crosses, hend, hx, hz]

lemma OrientedPseudograph.cut_nonempty_of_connects
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (hconn : G.Connects Finset.univ)
    {S : Finset V} (hSnonempty : S.Nonempty) (hSproper : S ≠ Finset.univ) :
    (G.cut S).Nonempty := by
  classical
  obtain ⟨x, hxS⟩ := hSnonempty
  have hnotSubset : ¬ Finset.univ ⊆ S := by
    intro hsub
    apply hSproper
    exact Finset.eq_univ_iff_forall.mpr fun y ↦ hsub (Finset.mem_univ y)
  obtain ⟨y, _, hyS⟩ := Finset.not_subset.mp hnotSubset
  obtain ⟨p⟩ := hconn.preconnected x y
  obtain ⟨e, _heT, heCross⟩ :=
    G.exists_crossing_edge_on_walk (T := Finset.univ) p hxS hyS
  exact ⟨e, by simpa [OrientedPseudograph.cut] using heCross⟩

lemma OrientedPseudograph.exists_nonloopEdge_incident_of_connects_of_vertex_ne
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (hconn : G.Connects Finset.univ)
    {u w : V} (hwu : w ≠ u) :
    ∃ a : G.NonloopEdge, G.endAt a.1 0 = u ∨ G.endAt a.1 1 = u := by
  classical
  have hcutNonempty : (G.cut ({u} : Finset V)).Nonempty := by
    apply G.cut_nonempty_of_connects hconn
    · exact Finset.singleton_nonempty u
    · intro h
      have hw : w ∈ ({u} : Finset V) := by
        rw [h]
        exact Finset.mem_univ w
      exact hwu (Finset.mem_singleton.mp hw)
  obtain ⟨e, heCut⟩ := hcutNonempty
  have hcross : G.Crosses ({u} : Finset V) e := by
    simpa [OrientedPseudograph.cut] using heCut
  have hnonloop : G.endAt e 0 ≠ G.endAt e 1 := by
    intro h
    exact hcross (by rw [h])
  have hinc : G.endAt e 0 = u ∨ G.endAt e 1 = u := by
    unfold OrientedPseudograph.Crosses at hcross
    by_cases h0 : G.endAt e 0 = u
    · exact .inl h0
    · by_cases h1 : G.endAt e 1 = u
      · exact .inr h1
      · have hsame : (G.endAt e 0 ∈ ({u} : Finset V)) =
            (G.endAt e 1 ∈ ({u} : Finset V)) := by
          simp [h0, h1]
        exact (hcross hsame).elim
  exact ⟨⟨e, hnonloop⟩, hinc⟩

noncomputable def OrientedPseudograph.CircuitDoubleCover.ofNonloopOfNoLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E)
    (hno : ∀ e : E, G.endAt e 0 ≠ G.endAt e 1)
    (M : _root_.CycleDoubleCoverConjecture.CircuitDoubleCover G.nonloopSubgraph) :
    G.CircuitDoubleCover where
  circuits := M.circuits.map (OrientedPseudograph.Circuit.ofNonloop G)
  coveredTwice := by
    intro e
    let e' : G.NonloopEdge := ⟨e, hno e⟩
    have hfilter := G.list_filter_ofNonloop_length e' M.circuits
    simpa [e'] using hfilter.trans (M.coveredTwice e')

@[simp]
lemma OrientedPseudograph.CircuitDoubleCover.ofNonloopOfNoLoops_length
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E)
    (hno : ∀ e : E, G.endAt e 0 ≠ G.endAt e 1)
    (M : _root_.CycleDoubleCoverConjecture.CircuitDoubleCover G.nonloopSubgraph) :
    (OrientedPseudograph.CircuitDoubleCover.ofNonloopOfNoLoops G hno M).circuits.length =
      M.circuits.length := by
  simp [OrientedPseudograph.CircuitDoubleCover.ofNonloopOfNoLoops]

noncomputable def OrientedPseudograph.CircuitDoubleCover.ofNonloopAndLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E)
    (M : _root_.CycleDoubleCoverConjecture.CircuitDoubleCover G.nonloopSubgraph) :
    G.CircuitDoubleCover where
  circuits := M.circuits.map (OrientedPseudograph.Circuit.ofNonloop G) ++
    G.loopCircuitList
  coveredTwice := by
    intro e
    rw [List.filter_append, List.length_append]
    by_cases hloop : G.endAt e 0 = G.endAt e 1
    · have hnonloop :=
        G.list_filter_ofNonloop_length_of_loop hloop M.circuits
      have hloopCount :=
        G.loopCircuitList_filter_length_of_loop ⟨e, hloop⟩
      have hloopCount' :
          (G.loopCircuitList.filter fun C ↦ e ∈ C.edges).length = 2 := by
        simpa using hloopCount
      rw [hnonloop, hloopCount']
    · let e' : G.NonloopEdge := ⟨e, hloop⟩
      have hnonloop :
          ((M.circuits.map (OrientedPseudograph.Circuit.ofNonloop G)).filter
              fun C ↦ e ∈ C.edges).length = 2 := by
        have hfilter := G.list_filter_ofNonloop_length e' M.circuits
        simpa [e'] using hfilter.trans (M.coveredTwice e')
      have hloopCount := G.loopCircuitList_filter_length_of_nonloop hloop
      rw [hnonloop, hloopCount]

@[simp]
lemma OrientedPseudograph.CircuitDoubleCover.ofNonloopAndLoops_length
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E)
    (M : _root_.CycleDoubleCoverConjecture.CircuitDoubleCover G.nonloopSubgraph) :
    (OrientedPseudograph.CircuitDoubleCover.ofNonloopAndLoops G M).circuits.length =
      M.circuits.length + G.loopCircuitList.length := by
  simp [OrientedPseudograph.CircuitDoubleCover.ofNonloopAndLoops]

theorem OrientedPseudograph.exists_circuitDoubleCover_of_nonloopSubgraph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E)
    (h : Nonempty (_root_.CycleDoubleCoverConjecture.CircuitDoubleCover G.nonloopSubgraph)) :
    Nonempty G.CircuitDoubleCover := by
  obtain ⟨M⟩ := h
  exact ⟨OrientedPseudograph.CircuitDoubleCover.ofNonloopAndLoops G M⟩

theorem OrientedPseudograph.exists_circuitDoubleCover_length_le_of_nonloopSubgraph
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) {k : ℕ}
    (h : ∃ M : _root_.CycleDoubleCoverConjecture.CircuitDoubleCover G.nonloopSubgraph,
      M.circuits.length + G.loopCircuitList.length ≤ k) :
    ∃ M : G.CircuitDoubleCover, M.circuits.length ≤ k := by
  rcases h with ⟨M, hM⟩
  exact ⟨OrientedPseudograph.CircuitDoubleCover.ofNonloopAndLoops G M, by simpa using hM⟩

theorem OrientedPseudograph.exists_circuitDoubleCover_length_le_of_nonloopSubgraph_noLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E)
    (hno : ∀ e : E, G.endAt e 0 ≠ G.endAt e 1) {k : ℕ}
    (h : ∃ M : _root_.CycleDoubleCoverConjecture.CircuitDoubleCover G.nonloopSubgraph,
      M.circuits.length ≤ k) :
    ∃ M : G.CircuitDoubleCover, M.circuits.length ≤ k := by
  rcases h with ⟨M, hM⟩
  exact ⟨OrientedPseudograph.CircuitDoubleCover.ofNonloopOfNoLoops G hno M,
    by simpa using hM⟩

def CircuitDoubleCover.empty {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [IsEmpty E] (G : OrientedMultigraph V E) :
    CircuitDoubleCover G where
  circuits := []
  coveredTwice := by
    intro e
    exact isEmptyElim e

theorem exists_circuitDoubleCover_length_zero_of_isEmpty_edges
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [IsEmpty E] (G : OrientedMultigraph V E) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ 0 := by
  exact ⟨CircuitDoubleCover.empty G, by simp [CircuitDoubleCover.empty]⟩

theorem exists_circuitDoubleCover_length_zero_of_edge_card_eq_zero
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (hE : Fintype.card E = 0) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ 0 := by
  haveI : IsEmpty E := Fintype.card_eq_zero_iff.mp hE
  exact exists_circuitDoubleCover_length_zero_of_isEmpty_edges G

theorem exists_circuitDoubleCover_oddVertices_bound_of_edge_card_eq_zero
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (hE : Fintype.card E = 0) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  rcases exists_circuitDoubleCover_length_zero_of_edge_card_eq_zero G hE with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  omega

theorem exists_circuitDoubleCover_vertex_bound_of_edge_card_eq_zero
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (hE : Fintype.card E = 0) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  rcases exists_circuitDoubleCover_length_zero_of_edge_card_eq_zero G hE with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  omega

noncomputable def Circuit.whole {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [Nonempty E] (G : OrientedMultigraph V E)
    (heven : IsEvenEdgeSet G Finset.univ) (hconn : Connects G Finset.univ) :
    Circuit G where
  edges := Finset.univ
  nonempty := ⟨Classical.arbitrary E, Finset.mem_univ _⟩
  even := heven
  connected := edgeSupportConnected_of_connects G hconn

theorem exists_circuitDoubleCover_length_le_two_of_univ_even_connected
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [Nonempty E] (G : OrientedMultigraph V E)
    (heven : IsEvenEdgeSet G Finset.univ) (hconn : Connects G Finset.univ) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ 2 := by
  let C := Circuit.whole G heven hconn
  refine ⟨{ circuits := [C, C], coveredTwice := ?_ }, ?_⟩
  · intro e
    simp [C, Circuit.whole]
  · simp

lemma forall_even_degree_of_oddVertices_eq_empty
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (hodd : oddVertices G = ∅) :
    ∀ v : V, Even (degree G v) := by
  intro v
  by_contra hEven
  have hOdd : Odd (degree G v) := Nat.not_even_iff_odd.mp hEven
  have hv : v ∈ oddVertices G := by
    simp [oddVertices, hOdd]
  rw [hodd] at hv
  simp at hv

theorem exists_circuitDoubleCover_length_le_two_of_oddVertices_eq_empty
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [Nonempty E] (G : OrientedMultigraph V E)
    (hodd : oddVertices G = ∅) (hconn : Connects G Finset.univ) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ 2 := by
  exact exists_circuitDoubleCover_length_le_two_of_univ_even_connected G
    (isEvenEdgeSet_univ_of_forall_even_degree G
      (forall_even_degree_of_oddVertices_eq_empty G hodd))
    hconn

theorem exists_circuitDoubleCover_oddVertices_bound_of_oddVertices_eq_empty
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hodd : oddVertices G = ∅) (hconn : Connects G Finset.univ) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  by_cases hE : Fintype.card E = 0
  · exact exists_circuitDoubleCover_oddVertices_bound_of_edge_card_eq_zero G hE
  · haveI : Nonempty E := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hE)
    obtain ⟨M, hM⟩ :=
      exists_circuitDoubleCover_length_le_two_of_oddVertices_eq_empty G hodd hconn
    refine ⟨M, ?_⟩
    have hcard : (oddVertices G).card = 0 := by
      simp [hodd]
    omega

theorem exists_circuitDoubleCover_vertex_bound_of_oddVertices_eq_empty
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hodd : oddVertices G = ∅) (hconn : Connects G Finset.univ)
    (hlarge : 3 ≤ Fintype.card V) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  by_cases hE : Fintype.card E = 0
  · exact exists_circuitDoubleCover_vertex_bound_of_edge_card_eq_zero G hE
  · haveI : Nonempty E := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hE)
    obtain ⟨M, hM⟩ :=
      exists_circuitDoubleCover_length_le_two_of_oddVertices_eq_empty G hodd hconn
    refine ⟨M, ?_⟩
    omega

theorem exists_circuitDoubleCover_length_le_vertex_card_sub_one_of_oddVertices_bound
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (hlarge : 6 ≤ Fintype.card V)
    (h : ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  rcases h with ⟨M, hM⟩
  exact ⟨M, hM.trans (oddVertices_half_add_two_le_vertex_card_sub_one_of_six G hlarge)⟩

lemma liftSplitEdgeSet_nonempty
    {E : Type*} [DecidableEq E] {e f : E} {F : Finset (SplitEdge E e f)}
    (hF : F.Nonempty) :
    (liftSplitEdgeSet e f F).Nonempty := by
  rcases hF with ⟨x, hxF⟩
  cases x with
  | inl x =>
      exact ⟨x.1, Finset.mem_biUnion.mpr
        ⟨Sum.inl x, hxF, by simp [splitLiftPiece]⟩⟩
  | inr x =>
      exact ⟨e, Finset.mem_biUnion.mpr
        ⟨Sum.inr x, hxF, by simp [splitLiftPiece]⟩⟩

lemma lift_incident_proxy
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    {F : Finset (SplitEdge E e f)} {u : V}
    (hu : IncidentVertex G (liftSplitEdgeSet e f F) u) :
    ∃ u', IncidentVertex (splitOff G v e f hnew) F u' ∧
      (ReachableIn G) (liftSplitEdgeSet e f F) u u' := by
  rcases hu with ⟨g, hgLift, hgu⟩
  by_cases hge : g = e
  · subst g
    have hnewF : splitNewEdge e f ∈ F := mem_liftSplitEdgeSet_left.mp hgLift
    refine ⟨otherEndpoint G v e, ?_, ?_⟩
    · refine ⟨splitNewEdge e f, hnewF, ?_⟩
      left
      simp [splitOff, splitNewEdge]
    · exact reachable_endpoint_to_otherEndpoint_of_incident G hgLift he hgu
  · by_cases hgf : g = f
    · subst g
      have hnewF : splitNewEdge e f ∈ F := mem_liftSplitEdgeSet_right.mp hgLift
      refine ⟨otherEndpoint G v f, ?_, ?_⟩
      · refine ⟨splitNewEdge e f, hnewF, ?_⟩
        right
        simp [splitOff, splitNewEdge]
      · exact reachable_endpoint_to_otherEndpoint_of_incident G hgLift hf hgu
    · let hgOld : g ≠ e ∧ g ≠ f := ⟨hge, hgf⟩
      have hgF : splitOldEdge g hgOld ∈ F :=
        (mem_liftSplitEdgeSet_old hgOld).mp hgLift
      refine ⟨u, ?_, SimpleGraph.Reachable.refl _⟩
      refine ⟨splitOldEdge g hgOld, hgF, ?_⟩
      simpa [splitOldEdge, splitOff] using hgu

lemma liftSplitEdgeSet_connected
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    {F : Finset (SplitEdge E e f)}
    (hF : EdgeSupportConnected (splitOff G v e f hnew) F) :
    EdgeSupportConnected G (liftSplitEdgeSet e f F) := by
  intro u w hu hw
  obtain ⟨u', hu', hru⟩ := lift_incident_proxy G he hf hnew hu
  obtain ⟨w', hw', hrw⟩ := lift_incident_proxy G he hf hnew hw
  exact hru.trans ((split_reachable_lift_reachable G he hf hnew (hF hu' hw')).trans hrw.symm)

lemma lift_pseudograph_incident_proxy
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (he : IsIncident G v e) (hf : IsIncident G v f)
    {F : Finset (SplitEdge E e f)} {u : V}
    (hu : IncidentVertex G (liftSplitEdgeSet e f F) u) :
    ∃ u', (splitOffWithLoops G v e f).IncidentVertex F u' ∧
      (ReachableIn G) (liftSplitEdgeSet e f F) u u' := by
  rcases hu with ⟨g, hgLift, hgu⟩
  by_cases hge : g = e
  · subst g
    have hnewF : splitNewEdge e f ∈ F := mem_liftSplitEdgeSet_left.mp hgLift
    refine ⟨otherEndpoint G v e, ?_, ?_⟩
    · refine ⟨splitNewEdge e f, hnewF, ?_⟩
      left
      simp [splitOffWithLoops, splitNewEdge]
    · exact reachable_endpoint_to_otherEndpoint_of_incident G hgLift he hgu
  · by_cases hgf : g = f
    · subst g
      have hnewF : splitNewEdge e f ∈ F := mem_liftSplitEdgeSet_right.mp hgLift
      refine ⟨otherEndpoint G v f, ?_, ?_⟩
      · refine ⟨splitNewEdge e f, hnewF, ?_⟩
        right
        simp [splitOffWithLoops, splitNewEdge]
      · exact reachable_endpoint_to_otherEndpoint_of_incident G hgLift hf hgu
    · let hgOld : g ≠ e ∧ g ≠ f := ⟨hge, hgf⟩
      have hgF : splitOldEdge g hgOld ∈ F :=
        (mem_liftSplitEdgeSet_old hgOld).mp hgLift
      refine ⟨u, ?_, SimpleGraph.Reachable.refl _⟩
      refine ⟨splitOldEdge g hgOld, hgF, ?_⟩
      simpa [splitOldEdge, splitOffWithLoops] using hgu

lemma liftSplitEdgeSet_pseudograph_connected
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (he : IsIncident G v e) (hf : IsIncident G v f)
    {F : Finset (SplitEdge E e f)}
    (hF : (splitOffWithLoops G v e f).EdgeSupportConnected F) :
    EdgeSupportConnected G (liftSplitEdgeSet e f F) := by
  intro u w hu hw
  obtain ⟨u', hu', hru⟩ := lift_pseudograph_incident_proxy G he hf hu
  obtain ⟨w', hw', hrw⟩ := lift_pseudograph_incident_proxy G he hf hw
  exact hru.trans
    ((splitOffWithLoops_reachable_lift_reachable G he hf (hF hu' hw')).trans hrw.symm)

noncomputable def pseudographCircuit_liftSplit
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (C : OrientedPseudograph.Circuit (splitOffWithLoops G v e f)) :
    _root_.CycleDoubleCoverConjecture.Circuit G where
  edges := liftSplitEdgeSet e f C.edges
  nonempty := liftSplitEdgeSet_nonempty C.nonempty
  even := liftSplitEdgeSet_pseudograph_even G hne he hf C.even
  connected := liftSplitEdgeSet_pseudograph_connected G he hf C.connected

noncomputable def Circuit.liftSplit
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    (C : Circuit (splitOff G v e f hnew)) : Circuit G where
  edges := liftSplitEdgeSet e f C.edges
  nonempty := liftSplitEdgeSet_nonempty C.nonempty
  even := liftSplitEdgeSet_even G hne he hf hnew C.even
  connected := liftSplitEdgeSet_connected G he hf hnew C.connected

noncomputable def CircuitDoubleCover.liftSplit
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    (M : CircuitDoubleCover (splitOff G v e f hnew)) : CircuitDoubleCover G where
  circuits := M.circuits.map (Circuit.liftSplit G hne he hf hnew)
  coveredTwice := by
    intro g
    by_cases hge : g = e
    · subst g
      have hfilter (L : List (Circuit (splitOff G v e f hnew))) :
          ((L.map (Circuit.liftSplit G hne he hf hnew)).filter
              fun C ↦ e ∈ C.edges).length =
            (L.filter fun C ↦ splitNewEdge e f ∈ C.edges).length := by
        induction L with
        | nil => simp
        | cons C L ih =>
            by_cases h : splitNewEdge e f ∈ C.edges <;>
              simp [Circuit.liftSplit, mem_liftSplitEdgeSet_left, h, ih]
      rw [hfilter]
      exact M.coveredTwice (splitNewEdge e f)
    · by_cases hgf : g = f
      · subst g
        have hfilter (L : List (Circuit (splitOff G v e f hnew))) :
            ((L.map (Circuit.liftSplit G hne he hf hnew)).filter
                fun C ↦ f ∈ C.edges).length =
              (L.filter fun C ↦ splitNewEdge e f ∈ C.edges).length := by
          induction L with
          | nil => simp
          | cons C L ih =>
              by_cases h : splitNewEdge e f ∈ C.edges <;>
                simp [Circuit.liftSplit, mem_liftSplitEdgeSet_right, h, ih]
        rw [hfilter]
        exact M.coveredTwice (splitNewEdge e f)
      · let hgOld : g ≠ e ∧ g ≠ f := ⟨hge, hgf⟩
        have hfilter (L : List (Circuit (splitOff G v e f hnew))) :
            ((L.map (Circuit.liftSplit G hne he hf hnew)).filter
                fun C ↦ g ∈ C.edges).length =
              (L.filter fun C ↦ splitOldEdge g hgOld ∈ C.edges).length := by
          induction L with
          | nil => simp
          | cons C L ih =>
              by_cases h : splitOldEdge g hgOld ∈ C.edges <;>
                simp [Circuit.liftSplit, mem_liftSplitEdgeSet_old hgOld, h, ih]
        rw [hfilter]
        exact M.coveredTwice (splitOldEdge g hgOld)

noncomputable def pseudographCircuitDoubleCover_liftSplit
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (M : OrientedPseudograph.CircuitDoubleCover (splitOffWithLoops G v e f)) :
    _root_.CycleDoubleCoverConjecture.CircuitDoubleCover G where
  circuits := M.circuits.map (pseudographCircuit_liftSplit G hne he hf)
  coveredTwice := by
    intro g
    by_cases hge : g = e
    · subst g
      have hfilter (L : List (OrientedPseudograph.Circuit (splitOffWithLoops G v e f))) :
          ((L.map (pseudographCircuit_liftSplit G hne he hf)).filter
              fun C ↦ e ∈ C.edges).length =
            (L.filter fun C ↦ splitNewEdge e f ∈ C.edges).length := by
        induction L with
        | nil => simp
        | cons C L ih =>
            by_cases h : splitNewEdge e f ∈ C.edges <;>
              simp [pseudographCircuit_liftSplit, mem_liftSplitEdgeSet_left, h, ih]
      rw [hfilter]
      exact M.coveredTwice (splitNewEdge e f)
    · by_cases hgf : g = f
      · subst g
        have hfilter (L : List (OrientedPseudograph.Circuit (splitOffWithLoops G v e f))) :
            ((L.map (pseudographCircuit_liftSplit G hne he hf)).filter
                fun C ↦ f ∈ C.edges).length =
              (L.filter fun C ↦ splitNewEdge e f ∈ C.edges).length := by
          induction L with
          | nil => simp
          | cons C L ih =>
              by_cases h : splitNewEdge e f ∈ C.edges <;>
                simp [pseudographCircuit_liftSplit, mem_liftSplitEdgeSet_right, h, ih]
        rw [hfilter]
        exact M.coveredTwice (splitNewEdge e f)
      · let hgOld : g ≠ e ∧ g ≠ f := ⟨hge, hgf⟩
        have hfilter (L : List (OrientedPseudograph.Circuit (splitOffWithLoops G v e f))) :
            ((L.map (pseudographCircuit_liftSplit G hne he hf)).filter
                fun C ↦ g ∈ C.edges).length =
              (L.filter fun C ↦ splitOldEdge g hgOld ∈ C.edges).length := by
          induction L with
          | nil => simp
          | cons C L ih =>
              by_cases h : splitOldEdge g hgOld ∈ C.edges <;>
                simp [pseudographCircuit_liftSplit, mem_liftSplitEdgeSet_old hgOld, h, ih]
        rw [hfilter]
        exact M.coveredTwice (splitOldEdge g hgOld)

@[simp]
lemma CircuitDoubleCover.liftSplit_length
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    (M : CircuitDoubleCover (splitOff G v e f hnew)) :
    (M.liftSplit G hne he hf hnew).circuits.length = M.circuits.length := by
  simp [CircuitDoubleCover.liftSplit]

@[simp]
lemma pseudographCircuitDoubleCover_liftSplit_length
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (M : OrientedPseudograph.CircuitDoubleCover (splitOffWithLoops G v e f)) :
    (pseudographCircuitDoubleCover_liftSplit G hne he hf M).circuits.length =
      M.circuits.length := by
  simp [pseudographCircuitDoubleCover_liftSplit]

theorem exists_circuitDoubleCover_length_le_of_splitOff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f) {k : ℕ}
    (h : ∃ M : CircuitDoubleCover (splitOff G v e f hnew), M.circuits.length ≤ k) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ k := by
  rcases h with ⟨M, hM⟩
  exact ⟨M.liftSplit G hne he hf hnew, by simpa using hM⟩

theorem exists_circuitDoubleCover_length_le_of_splitOffWithLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f) {k : ℕ}
    (h : ∃ M : OrientedPseudograph.CircuitDoubleCover (splitOffWithLoops G v e f),
      M.circuits.length ≤ k) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ k := by
  rcases h with ⟨M, hM⟩
  exact ⟨pseudographCircuitDoubleCover_liftSplit G hne he hf M, by simpa using hM⟩

theorem exists_circuitDoubleCover_oddVertices_bound_of_splitOff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    (h : ∃ M : CircuitDoubleCover (splitOff G v e f hnew),
      M.circuits.length ≤ (oddVertices (splitOff G v e f hnew)).card / 2 + 2) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  have h' : ∃ M : CircuitDoubleCover (splitOff G v e f hnew),
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
    rcases h with ⟨M, hM⟩
    have hodd := splitOff_oddVertices G hne he hf hnew
    exact ⟨M, by simpa [hodd] using hM⟩
  exact exists_circuitDoubleCover_length_le_of_splitOff G hne he hf hnew h'

theorem exists_circuitDoubleCover_oddVertices_bound_of_splitOffWithLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (h : ∃ M : OrientedPseudograph.CircuitDoubleCover (splitOffWithLoops G v e f),
      M.circuits.length ≤ (splitOffWithLoops G v e f).oddVertices.card / 2 + 2) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  have h' : ∃ M : OrientedPseudograph.CircuitDoubleCover (splitOffWithLoops G v e f),
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
    rcases h with ⟨M, hM⟩
    have hodd := splitOffWithLoops_oddVertices G hne he hf
    exact ⟨M, by simpa [hodd] using hM⟩
  exact exists_circuitDoubleCover_length_le_of_splitOffWithLoops G hne he hf h'

theorem exists_circuitDoubleCover_vertex_bound_of_splitOff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : otherEndpoint G v e ≠ otherEndpoint G v f)
    (h : ∃ M : CircuitDoubleCover (splitOff G v e f hnew),
      M.circuits.length ≤ Fintype.card V - 1) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  exact exists_circuitDoubleCover_length_le_of_splitOff G hne he hf hnew h

theorem exists_circuitDoubleCover_vertex_bound_of_splitOffWithLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (hne : e ≠ f)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (h : ∃ M : OrientedPseudograph.CircuitDoubleCover (splitOffWithLoops G v e f),
      M.circuits.length ≤ Fintype.card V - 1) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  exact exists_circuitDoubleCover_length_le_of_splitOffWithLoops G hne he hf h

theorem ReducingSplit.lift_oddVertices_bound
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplit G v)
    (h : ∃ M : CircuitDoubleCover S.graph,
      M.circuits.length ≤ (oddVertices S.graph).card / 2 + 2) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  exact exists_circuitDoubleCover_oddVertices_bound_of_splitOff G
    S.distinct S.left_incident S.right_incident S.endpoints_distinct h

theorem ReducingSplitWithLoops.lift_oddVertices_bound
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v)
    (h : ∃ M : OrientedPseudograph.CircuitDoubleCover S.graph,
      M.circuits.length ≤ S.graph.oddVertices.card / 2 + 2) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  exact exists_circuitDoubleCover_oddVertices_bound_of_splitOffWithLoops G
    S.distinct S.left_incident S.right_incident h

theorem ReducingSplit.lift_vertex_bound
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplit G v)
    (h : ∃ M : CircuitDoubleCover S.graph,
      M.circuits.length ≤ Fintype.card V - 1) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  exact exists_circuitDoubleCover_vertex_bound_of_splitOff G
    S.distinct S.left_incident S.right_incident S.endpoints_distinct h

theorem ReducingSplitWithLoops.lift_vertex_bound
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v)
    (h : ∃ M : OrientedPseudograph.CircuitDoubleCover S.graph,
      M.circuits.length ≤ Fintype.card V - 1) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  exact exists_circuitDoubleCover_vertex_bound_of_splitOffWithLoops G
    S.distinct S.left_incident S.right_incident h

theorem SuppressingSplit.lift_oddVertices_bound
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplit G v)
    (h : ∃ M : CircuitDoubleCover S.graph,
      M.circuits.length ≤ (oddVertices S.graph).card / 2 + 2) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  exact exists_circuitDoubleCover_oddVertices_bound_of_splitOff G
    S.distinct S.left_incident S.right_incident S.endpoints_distinct h

theorem SuppressingSplit.lift_vertex_bound
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplit G v)
    (h : ∃ M : CircuitDoubleCover S.graph,
      M.circuits.length ≤ Fintype.card V - 1) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  exact exists_circuitDoubleCover_vertex_bound_of_splitOff G
    S.distinct S.left_incident S.right_incident S.endpoints_distinct h

theorem SuppressingSplitWithLoops.lift_oddVertices_bound
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplitWithLoops G v)
    (h : ∃ M : OrientedPseudograph.CircuitDoubleCover S.graph,
      M.circuits.length ≤ S.graph.oddVertices.card / 2 + 2) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  exact exists_circuitDoubleCover_oddVertices_bound_of_splitOffWithLoops G
    S.distinct S.left_incident S.right_incident h

theorem SuppressingSplitWithLoops.lift_vertex_bound
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplitWithLoops G v)
    (h : ∃ M : OrientedPseudograph.CircuitDoubleCover S.graph,
      M.circuits.length ≤ Fintype.card V - 1) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  exact exists_circuitDoubleCover_vertex_bound_of_splitOffWithLoops G
    S.distinct S.left_incident S.right_incident h

theorem ReducingSplit.oddVertices_bound_of_induction
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplit G v)
    (hconn : Connects G Finset.univ) (hb : Bridgeless S.graph)
    (hIH : ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' < Fintype.card E →
      (H : OrientedMultigraph V E') → Connects H Finset.univ → Bridgeless H →
        ∃ M : CircuitDoubleCover H,
          M.circuits.length ≤ (oddVertices H).card / 2 + 2) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  have hsplit :
      ∃ M : CircuitDoubleCover S.graph,
        M.circuits.length ≤ (oddVertices S.graph).card / 2 + 2 :=
    hIH (E' := SplitEdge E S.left S.right) S.edge_card_lt
      S.graph (S.connects_graph hconn) hb
  exact S.lift_oddVertices_bound hsplit

theorem ReducingSplitWithLoops.nonloopSubgraph_oddVertices_bound_of_induction
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v)
    (hconn : Connects G Finset.univ) (hb : S.graph.Bridgeless)
    (hIH : ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' < Fintype.card E →
      (H : OrientedMultigraph V E') → Connects H Finset.univ → Bridgeless H →
        ∃ M : CircuitDoubleCover H,
          M.circuits.length ≤ (oddVertices H).card / 2 + 2) :
    ∃ M : CircuitDoubleCover S.graph.nonloopSubgraph,
      M.circuits.length ≤ (oddVertices S.graph.nonloopSubgraph).card / 2 + 2 := by
  have hconnGraph : S.graph.Connects Finset.univ := S.connects_graph hconn
  have hconnCore : Connects S.graph.nonloopSubgraph Finset.univ :=
    (S.graph.connects_nonloopSubgraph_univ_iff).mpr hconnGraph
  have hbCore : Bridgeless S.graph.nonloopSubgraph :=
    (S.graph.bridgeless_nonloopSubgraph_iff).mpr hb
  exact hIH (E' := S.graph.NonloopEdge) S.nonloop_edge_card_lt
    S.graph.nonloopSubgraph hconnCore hbCore

theorem ReducingSplitWithLoops.pseudograph_cover_bound_of_induction
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v)
    (hconn : Connects G Finset.univ) (hb : S.graph.Bridgeless)
    (hIH : ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' < Fintype.card E →
      (H : OrientedMultigraph V E') → Connects H Finset.univ → Bridgeless H →
        ∃ M : CircuitDoubleCover H,
          M.circuits.length ≤ (oddVertices H).card / 2 + 2) :
    ∃ M : S.graph.CircuitDoubleCover,
      M.circuits.length ≤
        (oddVertices S.graph.nonloopSubgraph).card / 2 + 2 +
          S.graph.loopCircuitList.length := by
  obtain ⟨M, hM⟩ := S.nonloopSubgraph_oddVertices_bound_of_induction hconn hb hIH
  apply S.graph.exists_circuitDoubleCover_length_le_of_nonloopSubgraph
  exact ⟨M, by omega⟩

theorem ReducingSplitWithLoops.pseudograph_cover_bound_of_induction_with_one_loop_cost
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v)
    (hconn : Connects G Finset.univ) (hb : S.graph.Bridgeless)
    (hIH : ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' < Fintype.card E →
      (H : OrientedMultigraph V E') → Connects H Finset.univ → Bridgeless H →
        ∃ M : CircuitDoubleCover H,
          M.circuits.length ≤ (oddVertices H).card / 2 + 2) :
    ∃ M : S.graph.CircuitDoubleCover,
      M.circuits.length ≤ (oddVertices S.graph.nonloopSubgraph).card / 2 + 4 := by
  obtain ⟨M, hM⟩ := S.pseudograph_cover_bound_of_induction hconn hb hIH
  refine ⟨M, ?_⟩
  have hloopCard : Fintype.card S.graph.LoopEdge ≤ 1 :=
    splitOffWithLoops_loopEdge_card_le_one G
  have hloopLen : S.graph.loopCircuitList.length ≤ 2 := by
    rw [OrientedPseudograph.loopCircuitList_length]
    omega
  omega

theorem ReducingSplitWithLoops.pseudograph_cover_bound_of_induction_with_one_loop_cost_oddVertices
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v)
    (hconn : Connects G Finset.univ) (hb : S.graph.Bridgeless)
    (hIH : ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' < Fintype.card E →
      (H : OrientedMultigraph V E') → Connects H Finset.univ → Bridgeless H →
        ∃ M : CircuitDoubleCover H,
          M.circuits.length ≤ (oddVertices H).card / 2 + 2) :
    ∃ M : S.graph.CircuitDoubleCover,
      M.circuits.length ≤ S.graph.oddVertices.card / 2 + 4 := by
  obtain ⟨M, hM⟩ :=
    S.pseudograph_cover_bound_of_induction_with_one_loop_cost hconn hb hIH
  refine ⟨M, ?_⟩
  have hodd := S.graph.oddVertices_nonloopSubgraph
  simpa [hodd] using hM

theorem ReducingSplitWithLoops.lift_oddVertices_bound_with_one_loop_cost_of_induction
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v)
    (hconn : Connects G Finset.univ) (hb : S.graph.Bridgeless)
    (hIH : ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' < Fintype.card E →
      (H : OrientedMultigraph V E') → Connects H Finset.univ → Bridgeless H →
        ∃ M : CircuitDoubleCover H,
          M.circuits.length ≤ (oddVertices H).card / 2 + 2) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 4 := by
  obtain ⟨M, hM⟩ :=
    S.pseudograph_cover_bound_of_induction_with_one_loop_cost_oddVertices
      hconn hb hIH
  have h' : ∃ M : OrientedPseudograph.CircuitDoubleCover S.graph,
      M.circuits.length ≤ (oddVertices G).card / 2 + 4 := by
    refine ⟨M, ?_⟩
    have hodd := S.oddVertices_graph
    simpa [hodd] using hM
  exact exists_circuitDoubleCover_length_le_of_splitOffWithLoops G
    S.distinct S.left_incident S.right_incident h'

theorem ReducingSplitWithLoops.pseudograph_oddVertices_bound_of_induction_absorb_loop
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v)
    (hconn : Connects G Finset.univ) (hb : S.graph.Bridgeless)
    (hIH : ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' < Fintype.card E →
      (H : OrientedMultigraph V E') → Connects H Finset.univ → Bridgeless H →
        ∃ M : CircuitDoubleCover H,
          M.circuits.length ≤ (oddVertices H).card / 2 + 2) :
    ∃ M : S.graph.CircuitDoubleCover,
      M.circuits.length ≤ S.graph.oddVertices.card / 2 + 2 := by
  have hconnGraph : S.graph.Connects Finset.univ := S.connects_graph hconn
  have hcore :
      ∃ M : CircuitDoubleCover S.graph.nonloopSubgraph,
        M.circuits.length ≤ S.graph.oddVertices.card / 2 + 2 := by
    obtain ⟨M, hM⟩ := S.nonloopSubgraph_oddVertices_bound_of_induction hconn hb hIH
    refine ⟨M, ?_⟩
    have hodd := S.graph.oddVertices_nonloopSubgraph
    simpa [hodd] using hM
  by_cases hno : ∀ e : SplitEdge E S.left S.right,
      S.graph.endAt e 0 ≠ S.graph.endAt e 1
  · exact S.graph.exists_circuitDoubleCover_length_le_of_nonloopSubgraph_noLoops
      hno hcore
  · push Not at hno
    rcases hno with ⟨l, hloop⟩
    have hlNew : l = splitNewEdge S.left S.right := by
      simpa [ReducingSplitWithLoops.graph] using
        splitOffWithLoops_loopEdge_val_eq_new G
          (v := v) (e := S.left) (f := S.right) ⟨l, hloop⟩
    have honly : ∀ e : SplitEdge E S.left S.right,
        S.graph.endAt e 0 = S.graph.endAt e 1 → e = l := by
      intro e he
      have heNew : e = splitNewEdge S.left S.right := by
        simpa [ReducingSplitWithLoops.graph] using
          splitOffWithLoops_loopEdge_val_eq_new G
            (v := v) (e := S.left) (f := S.right) ⟨e, he⟩
      exact heNew.trans hlNew.symm
    have hvne : v ≠ S.graph.endAt l 0 := by
      rw [hlNew]
      simp only [ReducingSplitWithLoops.graph, Fin.isValue,
        splitOffWithLoops_endAt_new_zero, ne_eq]
      exact fun h ↦ (otherEndpoint_ne_of_incident G S.left_incident) h.symm
    obtain ⟨a, ha⟩ :=
      S.graph.exists_nonloopEdge_incident_of_connects_of_vertex_ne
        hconnGraph hvne
    exact S.graph.exists_circuitDoubleCover_length_le_of_nonloopSubgraph_absorb_loop
      hloop honly a ha hcore

theorem ReducingSplitWithLoops.oddVertices_bound_of_induction_absorb_loop
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : ReducingSplitWithLoops G v)
    (hconn : Connects G Finset.univ) (hb : S.graph.Bridgeless)
    (hIH : ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' < Fintype.card E →
      (H : OrientedMultigraph V E') → Connects H Finset.univ → Bridgeless H →
        ∃ M : CircuitDoubleCover H,
          M.circuits.length ≤ (oddVertices H).card / 2 + 2) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  obtain ⟨M, hM⟩ :=
    S.pseudograph_oddVertices_bound_of_induction_absorb_loop hconn hb hIH
  have h' : ∃ M : OrientedPseudograph.CircuitDoubleCover S.graph,
      M.circuits.length ≤ S.graph.oddVertices.card / 2 + 2 :=
    ⟨M, hM⟩
  exact S.lift_oddVertices_bound h'

theorem SuppressingSplit.oddVertices_bound_of_induction
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplit G v)
    (hIH : ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' < Fintype.card E →
      (H : OrientedMultigraph V E') → Connects H Finset.univ → Bridgeless H →
        ∃ M : CircuitDoubleCover H,
          M.circuits.length ≤ (oddVertices H).card / 2 + 2) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  have hsplit :
      ∃ M : CircuitDoubleCover S.graph,
        M.circuits.length ≤ (oddVertices S.graph).card / 2 + 2 :=
    hIH (E' := SplitEdge E S.left S.right) S.edge_card_lt
      S.graph S.connects_graph S.bridgeless_graph
  exact S.lift_oddVertices_bound hsplit

theorem SuppressingSplit.vertex_bound_of_induction
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplit G v)
    (hIH : ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' < Fintype.card E →
      (H : OrientedMultigraph V E') → Connects H Finset.univ → Bridgeless H →
        ∃ M : CircuitDoubleCover H, M.circuits.length ≤ Fintype.card V - 1) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  have hsplit :
      ∃ M : CircuitDoubleCover S.graph,
        M.circuits.length ≤ Fintype.card V - 1 :=
    hIH (E' := SplitEdge E S.left S.right) S.edge_card_lt
      S.graph S.connects_graph S.bridgeless_graph
  exact S.lift_vertex_bound hsplit

theorem SuppressingSplitWithLoops.nonloopSubgraph_oddVertices_bound_of_induction
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplitWithLoops G v)
    (hIH : ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' < Fintype.card E →
      (H : OrientedMultigraph V E') → Connects H Finset.univ → Bridgeless H →
        ∃ M : CircuitDoubleCover H,
          M.circuits.length ≤ (oddVertices H).card / 2 + 2) :
    ∃ M : CircuitDoubleCover S.graph.nonloopSubgraph,
      M.circuits.length ≤ (oddVertices S.graph.nonloopSubgraph).card / 2 + 2 := by
  have hconnCore : Connects S.graph.nonloopSubgraph Finset.univ :=
    (S.graph.connects_nonloopSubgraph_univ_iff).mpr S.connects_graph
  have hbCore : Bridgeless S.graph.nonloopSubgraph :=
    (S.graph.bridgeless_nonloopSubgraph_iff).mpr S.bridgeless_graph
  exact hIH (E' := S.graph.NonloopEdge) S.nonloop_edge_card_lt
    S.graph.nonloopSubgraph hconnCore hbCore

theorem SuppressingSplitWithLoops.pseudograph_cover_bound_of_induction
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplitWithLoops G v)
    (hIH : ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' < Fintype.card E →
      (H : OrientedMultigraph V E') → Connects H Finset.univ → Bridgeless H →
        ∃ M : CircuitDoubleCover H,
          M.circuits.length ≤ (oddVertices H).card / 2 + 2) :
    ∃ M : S.graph.CircuitDoubleCover,
      M.circuits.length ≤
        (oddVertices S.graph.nonloopSubgraph).card / 2 + 2 +
          S.graph.loopCircuitList.length := by
  obtain ⟨M, hM⟩ := S.nonloopSubgraph_oddVertices_bound_of_induction hIH
  apply S.graph.exists_circuitDoubleCover_length_le_of_nonloopSubgraph
  exact ⟨M, by omega⟩

theorem SuppressingSplitWithLoops.pseudograph_cover_bound_of_induction_with_one_loop_cost
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplitWithLoops G v)
    (hIH : ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' < Fintype.card E →
      (H : OrientedMultigraph V E') → Connects H Finset.univ → Bridgeless H →
        ∃ M : CircuitDoubleCover H,
          M.circuits.length ≤ (oddVertices H).card / 2 + 2) :
    ∃ M : S.graph.CircuitDoubleCover,
      M.circuits.length ≤ (oddVertices S.graph.nonloopSubgraph).card / 2 + 4 := by
  obtain ⟨M, hM⟩ := S.pseudograph_cover_bound_of_induction hIH
  refine ⟨M, ?_⟩
  have hloopCard : Fintype.card S.graph.LoopEdge ≤ 1 :=
    splitOffWithLoops_loopEdge_card_le_one G
  have hloopLen : S.graph.loopCircuitList.length ≤ 2 := by
    rw [OrientedPseudograph.loopCircuitList_length]
    omega
  omega

theorem SuppressingSplitWithLoops.lift_oddVertices_bound_with_one_loop_cost_of_induction
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} (S : SuppressingSplitWithLoops G v)
    (hIH : ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' < Fintype.card E →
      (H : OrientedMultigraph V E') → Connects H Finset.univ → Bridgeless H →
        ∃ M : CircuitDoubleCover H,
          M.circuits.length ≤ (oddVertices H).card / 2 + 2) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 4 := by
  obtain ⟨M, hM⟩ :=
    S.pseudograph_cover_bound_of_induction_with_one_loop_cost hIH
  have h' : ∃ M : OrientedPseudograph.CircuitDoubleCover S.graph,
      M.circuits.length ≤ (oddVertices G).card / 2 + 4 := by
    refine ⟨M, ?_⟩
    have hodd := S.oddVertices_graph
    simpa [hodd, S.graph.oddVertices_nonloopSubgraph] using hM
  exact exists_circuitDoubleCover_length_le_of_splitOffWithLoops G
    S.distinct S.left_incident S.right_incident h'

lemma exists_length_minimal_circuitDoubleCover {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (h : Nonempty (CircuitDoubleCover G)) :
    ∃ C : CircuitDoubleCover G,
      ∀ D : CircuitDoubleCover G, C.circuits.length ≤ D.circuits.length := by
  classical
  let P : ℕ → Prop := fun n ↦ ∃ C : CircuitDoubleCover G, C.circuits.length = n
  have hP : ∃ n, P n := by
    obtain ⟨C⟩ := h
    exact ⟨C.circuits.length, C, rfl⟩
  obtain ⟨C, hC⟩ := Nat.find_spec hP
  refine ⟨C, ?_⟩
  intro D
  have hmin : Nat.find hP ≤ D.circuits.length :=
    Nat.find_min' hP ⟨D, rfl⟩
  simpa [hC] using hmin

noncomputable def CircuitDoubleCover.ofPerm {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (C : CircuitDoubleCover G)
    {L : List (Circuit G)} (hperm : List.Perm L C.circuits) :
    CircuitDoubleCover G where
  circuits := L
  coveredTwice := by
    intro e
    have hfilter := List.Perm.filter (fun Z : Circuit G ↦ e ∈ Z.edges) hperm
    exact hfilter.length_eq.trans (C.coveredTwice e)

@[simp]
lemma CircuitDoubleCover.ofPerm_length {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (C : CircuitDoubleCover G)
    {L : List (Circuit G)} (hperm : List.Perm L C.circuits) :
    (CircuitDoubleCover.ofPerm G C hperm).circuits.length = C.circuits.length :=
  hperm.length_eq

lemma incidentVertex_union {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : OrientedMultigraph V E) (A B : Finset E) (v : V) :
    IncidentVertex G (A ∪ B) v ↔
      IncidentVertex G A v ∨ IncidentVertex G B v := by
  constructor
  · rintro ⟨e, he, hend⟩
    rcases Finset.mem_union.mp he with heA | heB
    · exact .inl ⟨e, heA, hend⟩
    · exact .inr ⟨e, heB, hend⟩
  · rintro (⟨e, heA, hend⟩ | ⟨e, heB, hend⟩)
    · exact ⟨e, Finset.mem_union_left B heA, hend⟩
    · exact ⟨e, Finset.mem_union_right A heB, hend⟩

lemma incidentVertex_of_reachableIn {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) {F : Finset E} {u v : V}
    (hu : IncidentVertex G F u) (h : (ReachableIn G) F u v) :
    IncidentVertex G F v := by
  rcases h with ⟨p⟩
  induction p with
  | nil =>
      exact hu
  | @cons x y z hxy p ih =>
      apply ih
      rw [supportGraph_adj_iff] at hxy
      rcases hxy with ⟨_, e, heF, hend⟩
      rcases hend with hend | hend
      · exact ⟨e, heF, .inr hend.2⟩
      · exact ⟨e, heF, .inl hend.1⟩

def Circuit.unionOfTouching {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : OrientedMultigraph V E)
    (C D : Circuit G) (hdisj : Disjoint C.edges D.edges) {w : V}
    (hwC : IncidentVertex G C.edges w) (hwD : IncidentVertex G D.edges w) :
    Circuit G where
  edges := C.edges ∪ D.edges
  nonempty := C.nonempty.mono (Finset.subset_union_left (s₂ := D.edges))
  even := by
    intro v
    rw [Finset.sum_union hdisj]
    rw [C.even v, D.even v]
    rfl
  connected := by
    intro u v hu hv
    rw [incidentVertex_union] at hu hv
    rcases hu with huC | huD <;> rcases hv with hvC | hvD
    · exact (reachableIn_mono G (Finset.subset_union_left) (C.connected huC hvC))
    · exact (reachableIn_mono G (Finset.subset_union_left) (C.connected huC hwC)).trans
        (reachableIn_mono G (Finset.subset_union_right) (D.connected hwD hvD))
    · exact (reachableIn_mono G (Finset.subset_union_right) (D.connected huD hwD)).trans
        (reachableIn_mono G (Finset.subset_union_left) (C.connected hwC hvC))
    · exact (reachableIn_mono G (Finset.subset_union_right) (D.connected huD hvD))

noncomputable def CircuitDoubleCover.mergeTouchingCons {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (C D : Circuit G) (L : List (Circuit G))
    (hcover : ∀ e : E, ((C :: D :: L).filter fun Z ↦ e ∈ Z.edges).length = 2)
    (hdisj : Disjoint C.edges D.edges) {w : V}
    (hwC : IncidentVertex G C.edges w) (hwD : IncidentVertex G D.edges w) :
    CircuitDoubleCover G where
  circuits := Circuit.unionOfTouching G C D hdisj hwC hwD :: L
  coveredTwice := by
    intro e
    have hnotBoth : ¬ (e ∈ C.edges ∧ e ∈ D.edges) := by
      intro h
      exact (Finset.disjoint_left.mp hdisj) h.1 h.2
    by_cases hC : e ∈ C.edges
    · have hD : e ∉ D.edges := fun h ↦ hnotBoth ⟨hC, h⟩
      simpa [Circuit.unionOfTouching, hC, hD] using hcover e
    · by_cases hD : e ∈ D.edges
      · simpa [Circuit.unionOfTouching, hC, hD] using hcover e
      · simpa [Circuit.unionOfTouching, hC, hD] using hcover e

@[simp]
lemma CircuitDoubleCover.mergeTouchingCons_length {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (C D : Circuit G) (L : List (Circuit G))
    (hcover : ∀ e : E, ((C :: D :: L).filter fun Z ↦ e ∈ Z.edges).length = 2)
    (hdisj : Disjoint C.edges D.edges) {w : V}
    (hwC : IncidentVertex G C.edges w) (hwD : IncidentVertex G D.edges w) :
    (CircuitDoubleCover.mergeTouchingCons G C D L hcover hdisj hwC hwD).circuits.length =
      L.length + 1 := by
  simp [CircuitDoubleCover.mergeTouchingCons]

lemma CircuitDoubleCover.not_mergeable_head_of_length_minimal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (M : CircuitDoubleCover G)
    (hmin : ∀ N : CircuitDoubleCover G, M.circuits.length ≤ N.circuits.length)
    {C D : Circuit G} {L : List (Circuit G)} (hM : M.circuits = C :: D :: L)
    (hdisj : Disjoint C.edges D.edges) {w : V}
    (hwC : IncidentVertex G C.edges w) (hwD : IncidentVertex G D.edges w) :
    False := by
  have hcover :
      ∀ e : E, ((C :: D :: L).filter fun Z ↦ e ∈ Z.edges).length = 2 := by
    intro e
    simpa [hM] using M.coveredTwice e
  let N := CircuitDoubleCover.mergeTouchingCons G C D L hcover hdisj hwC hwD
  have hN : N.circuits.length = L.length + 1 := by
    simp [N]
  have hMlen : M.circuits.length = L.length + 2 := by
    simp [hM]
  have := hmin N
  omega

lemma CircuitDoubleCover.not_mergeable_of_perm_to_head {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (M : CircuitDoubleCover G)
    (hmin : ∀ N : CircuitDoubleCover G, M.circuits.length ≤ N.circuits.length)
    {C D : Circuit G} {L : List (Circuit G)}
    (hperm : List.Perm (C :: D :: L) M.circuits)
    (hdisj : Disjoint C.edges D.edges) {w : V}
    (hwC : IncidentVertex G C.edges w) (hwD : IncidentVertex G D.edges w) :
    False := by
  let M' := CircuitDoubleCover.ofPerm G M hperm
  have hmin' : ∀ N : CircuitDoubleCover G, M'.circuits.length ≤ N.circuits.length := by
    intro N
    rw [CircuitDoubleCover.ofPerm_length]
    exact hmin N
  exact CircuitDoubleCover.not_mergeable_head_of_length_minimal G M' hmin'
    rfl hdisj hwC hwD

noncomputable def restrictedCut {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) (F : Finset E) (S : Finset V) :
    Finset E := by
  classical
  exact F.filter ((Crosses G) S)

@[simp]
lemma mem_restrictedCut {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) {F : Finset E} {S : Finset V} {e : E} :
    e ∈ restrictedCut G F S ↔ e ∈ F ∧ Crosses G S e := by
  simp [restrictedCut]

lemma sum_vertex_indicator_eq_mem {V : Type*} [DecidableEq V]
    (S : Finset V) (a : V) :
    ∑ v ∈ S, (if a = v then (1 : F₂) else 0) =
      if a ∈ S then (1 : F₂) else 0 := by
  by_cases ha : a ∈ S
  · rw [if_pos ha]
    simpa using Finset.sum_eq_single_of_mem (s := S)
      (f := fun v ↦ if a = v then (1 : F₂) else 0) a ha
      (fun _ _ hb ↦ by
        rw [if_neg]
        intro h
        exact hb h.symm)
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro b hb
    have hne : a ≠ b := by
      intro hab
      exact ha (by simpa [hab] using hb)
    simp [hne]

lemma sum_edgeIncidence_over_set_eq_endpoint_members {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq V] (G : OrientedMultigraph V E)
    (S : Finset V) (e : E) :
    ∑ v ∈ S, edgeIncidence G v e =
      (if G.endAt e 0 ∈ S then (1 : F₂) else 0) +
        if G.endAt e 1 ∈ S then (1 : F₂) else 0 := by
  change (∑ v ∈ S,
    ((if G.endAt e 0 = v then (1 : F₂) else 0) +
      if G.endAt e 1 = v then (1 : F₂) else 0)) = _
  rw [Finset.sum_add_distrib]
  rw [sum_vertex_indicator_eq_mem, sum_vertex_indicator_eq_mem]

lemma sum_edgeIncidence_over_set_eq_one_of_crosses {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] (G : OrientedMultigraph V E)
    (S : Finset V) {e : E} (he : Crosses G S e) :
    ∑ v ∈ S, edgeIncidence G v e = 1 := by
  rw [sum_edgeIncidence_over_set_eq_endpoint_members]
  unfold Crosses at he
  by_cases h0 : G.endAt e 0 ∈ S <;>
    by_cases h1 : G.endAt e 1 ∈ S <;>
      simp [h0, h1] at he ⊢

lemma sum_edgeIncidence_over_set_eq_zero_of_not_crosses {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] (G : OrientedMultigraph V E)
    (S : Finset V) {e : E} (he : ¬ Crosses G S e) :
    ∑ v ∈ S, edgeIncidence G v e = 0 := by
  rw [sum_edgeIncidence_over_set_eq_endpoint_members]
  unfold Crosses at he
  have htwo : (1 : F₂) + 1 = 0 := by decide
  by_cases h0 : G.endAt e 0 ∈ S
  · by_cases h1 : G.endAt e 1 ∈ S
    · simp [h0, h1, htwo]
    · exact (he (by simp [h0, h1])).elim
  · by_cases h1 : G.endAt e 1 ∈ S
    · exact (he (by simp [h0, h1])).elim
    · simp [h0, h1]

lemma exists_crossing_edge_on_walk {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) {T : Finset E} {S : Finset V}
    {x y : V} (p : ((supportGraph G) T).Walk x y)
    (hx : x ∈ S) (hy : y ∉ S) :
    ∃ e ∈ T, (symEdge G) e ∈ p.edges ∧ Crosses G S e := by
  induction p with
  | nil =>
      exact (hy hx).elim
  | @cons x z y hxz p ih =>
      by_cases hz : z ∈ S
      · obtain ⟨e, heT, hePath, heCross⟩ := ih hz hy
        exact ⟨e, heT, by simp [hePath], heCross⟩
      · rw [supportGraph_adj_iff] at hxz
        rcases hxz with ⟨_, e, heT, hend⟩
        refine ⟨e, heT, ?_, ?_⟩
        · rcases hend with hend | hend
          · simp [symEdge, hend]
          · simp [symEdge, hend, Sym2.eq_swap]
        · rcases hend with hend | hend
          · simp [Crosses, hend, hx, hz]
          · simp [Crosses, hend, hx, hz]

lemma cut_nonempty_of_connects {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) (hconn : Connects G Finset.univ)
    {S : Finset V} (hSnonempty : S.Nonempty) (hSproper : S ≠ Finset.univ) :
    (cut G S).Nonempty := by
  classical
  obtain ⟨x, hxS⟩ := hSnonempty
  have hnotSubset : ¬ Finset.univ ⊆ S := by
    intro hsub
    apply hSproper
    exact Finset.eq_univ_iff_forall.mpr fun y ↦ hsub (Finset.mem_univ y)
  obtain ⟨y, _, hyS⟩ := Finset.not_subset.mp hnotSubset
  obtain ⟨p⟩ := hconn.preconnected x y
  obtain ⟨e, _heT, _hePath, heCross⟩ :=
    exists_crossing_edge_on_walk G (T := Finset.univ) p hxS hyS
  exact ⟨e, by simpa [cut] using heCross⟩

lemma two_le_cut_card_of_connects_bridgeless {V E : Type*}
    [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) (hconn : Connects G Finset.univ)
    (hb : Bridgeless G) {S : Finset V}
    (hSnonempty : S.Nonempty) (hSproper : S ≠ Finset.univ) :
    2 ≤ (cut G S).card := by
  have hpos : 0 < (cut G S).card :=
    Finset.card_pos.mpr (cut_nonempty_of_connects G hconn hSnonempty hSproper)
  have hne : (cut G S).card ≠ 1 := hb S
  omega

lemma two_le_incidentEdgesInto_card_supportAwayComponent
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v x : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G) (hxv : x ≠ v) :
    2 ≤ (incidentEdgesInto G v (supportAwayComponent G v x)).card := by
  let S := supportAwayComponent G v x
  have hnonempty : S.Nonempty := ⟨x, self_mem_supportAwayComponent G v x⟩
  have hvS : v ∉ S := deleted_not_mem_supportAwayComponent G hxv
  have hproper : S ≠ Finset.univ := by
    intro hS
    exact hvS (by rw [hS]; exact Finset.mem_univ v)
  have hcutLower : 2 ≤ (cut G S).card :=
    two_le_cut_card_of_connects_bridgeless G hconn hb hnonempty hproper
  have hsub :
      cut G S ⊆ incidentEdgesInto G v S :=
    cut_subset_incidentEdgesInto_supportAwayComponent G hxv
  have hle : (cut G S).card ≤ (incidentEdgesInto G v S).card :=
    Finset.card_le_card hsub
  exact hcutLower.trans hle

lemma exists_other_incident_edge_into_supportAwayComponent
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    {e : E} (he : IsIncident G v e) :
    ∃ f : E, f ≠ e ∧ IsIncident G v f ∧
      otherEndpoint G v f ∈
        supportAwayComponent G v (otherEndpoint G v e) := by
  let C := supportAwayComponent G v (otherEndpoint G v e)
  have hxv : otherEndpoint G v e ≠ v := otherEndpoint_ne_of_incident G he
  have htwo : 2 ≤ (incidentEdgesInto G v C).card :=
    two_le_incidentEdgesInto_card_supportAwayComponent G hconn hb hxv
  have heC : e ∈ incidentEdgesInto G v C := by
    exact (mem_incidentEdgesInto G v C e).mpr
      ⟨he, self_mem_supportAwayComponent G v (otherEndpoint G v e)⟩
  have hpos : 0 < ((incidentEdgesInto G v C).erase e).card := by
    have hcard := Finset.card_erase_add_one heC
    omega
  obtain ⟨f, hfErase⟩ := Finset.card_pos.mp hpos
  have hf := Finset.mem_erase.mp hfErase
  rcases (mem_incidentEdgesInto G v C f).mp hf.2 with ⟨hfv, hfC⟩
  exact ⟨f, hf.1, hfv, hfC⟩

lemma exists_incident_endpoint_supportAway_reaches
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v y : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G) (hyv : y ≠ v) :
    ∃ e : E, IsIncident G v e ∧
      (supportAwayFromVertex G v).Reachable (otherEndpoint G v e) y := by
  let C := supportAwayComponent G v y
  have htwo : 2 ≤ (incidentEdgesInto G v C).card :=
    two_le_incidentEdgesInto_card_supportAwayComponent G hconn hb hyv
  have hpos : 0 < (incidentEdgesInto G v C).card := by
    omega
  obtain ⟨e, heC⟩ := Finset.card_pos.mp hpos
  rcases (mem_incidentEdgesInto G v C e).mp heC with ⟨he, heEndpoint⟩
  have hyEndpoint :
      (supportAwayFromVertex G v).Reachable y (otherEndpoint G v e) :=
    (mem_supportAwayComponent G v y (otherEndpoint G v e)).mp heEndpoint
  exact ⟨e, he, hyEndpoint.symm⟩

lemma cut_compl {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (S : Finset V) :
    cut G (Finset.univ \ S) = cut G S := by
  classical
  ext e
  simp [cut, Crosses]
  tauto

lemma mem_cut_univ_sdiff_singleton_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (e : E) :
    e ∈ cut G (Finset.univ \ ({v} : Finset V)) ↔ IsIncident G v e := by
  classical
  by_cases h0 : G.endAt e 0 = v
  · by_cases h1 : G.endAt e 1 = v
    · exact (G.loopless e (h0.trans h1.symm)).elim
    · have h1' : v ≠ G.endAt e 1 := fun h ↦ h1 h.symm
      simp [cut, Crosses, IsIncident, h0, h1]
  · by_cases h1 : G.endAt e 1 = v
    · have h0' : v ≠ G.endAt e 0 := fun h ↦ h0 h.symm
      simp [cut, Crosses, IsIncident, h0, h1]
    · have h0' : v ≠ G.endAt e 0 := fun h ↦ h0 h.symm
      have h1' : v ≠ G.endAt e 1 := fun h ↦ h1 h.symm
      simp [cut, Crosses, IsIncident, h0, h1]

lemma cut_univ_sdiff_singleton_eq_incidentEdgesAt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) :
    cut G (Finset.univ \ ({v} : Finset V)) = incidentEdgesAt G v := by
  ext e
  rw [mem_cut_univ_sdiff_singleton_iff G v e, mem_incidentEdgesAt]

lemma cut_card_univ_sdiff_singleton_eq_degree
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) :
    (cut G (Finset.univ \ ({v} : Finset V))).card = degree G v := by
  classical
  rw [cut_univ_sdiff_singleton_eq_incidentEdgesAt, degree_eq_incidentEdgesAt_card]

lemma cut_card_singleton_eq_degree
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) :
    (cut G ({v} : Finset V)).card = degree G v := by
  rw [← cut_compl G ({v} : Finset V), cut_card_univ_sdiff_singleton_eq_degree]

lemma degree_ne_one_of_bridgeless
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} (hb : Bridgeless G) (v : V) :
    degree G v ≠ 1 := by
  intro hdeg
  have hcut : (cut G ({v} : Finset V)).card = 1 := by
    rw [cut_card_singleton_eq_degree, hdeg]
  exact hb ({v} : Finset V) hcut

open scoped Classical in
lemma cut_card_eq_sum_crosses_indicator {V E : Type*} [Fintype V]
    [Fintype E] (G : OrientedMultigraph V E) (S : Finset V) :
    (cut G S).card =
      ∑ e : E, if Crosses G S e then 1 else 0 := by
  rw [Finset.card_eq_sum_ones]
  simp [cut]

open scoped Classical in
lemma cut_crosses_indicator_inter_union_le {V E : Type*} [Fintype V]
    [DecidableEq V]
    [Fintype E] (G : OrientedMultigraph V E) (A B : Finset V) (e : E) :
    (if Crosses G (A ∩ B) e then 1 else 0) +
        (if Crosses G (A ∪ B) e then 1 else 0) ≤
      (if Crosses G A e then 1 else 0) +
        (if Crosses G B e then 1 else 0) := by
  unfold Crosses
  by_cases h0A : G.endAt e 0 ∈ A <;>
    by_cases h1A : G.endAt e 1 ∈ A <;>
    by_cases h0B : G.endAt e 0 ∈ B <;>
    by_cases h1B : G.endAt e 1 ∈ B <;>
    simp [h0A, h1A, h0B, h1B]

open scoped Classical in
lemma cut_card_inter_add_cut_card_union_le {V E : Type*} [Fintype V]
    [DecidableEq V]
    [Fintype E] (G : OrientedMultigraph V E) (A B : Finset V) :
    (cut G (A ∩ B)).card + (cut G (A ∪ B)).card ≤
      (cut G A).card + (cut G B).card := by
  rw [cut_card_eq_sum_crosses_indicator G (A ∩ B)]
  rw [cut_card_eq_sum_crosses_indicator G (A ∪ B)]
  rw [cut_card_eq_sum_crosses_indicator G A]
  rw [cut_card_eq_sum_crosses_indicator G B]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun e _ ↦
    cut_crosses_indicator_inter_union_le G A B e

def CrossesBetweenDiffs {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) (A B : Finset V) (e : E) : Prop :=
  (G.endAt e 0 ∈ A ∧ G.endAt e 0 ∉ B ∧
      G.endAt e 1 ∈ B ∧ G.endAt e 1 ∉ A) ∨
    (G.endAt e 0 ∈ B ∧ G.endAt e 0 ∉ A ∧
      G.endAt e 1 ∈ A ∧ G.endAt e 1 ∉ B)

noncomputable def edgesBetweenDiffs {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) (A B : Finset V) : Finset E := by
  classical
  exact Finset.univ.filter (CrossesBetweenDiffs G A B)

open scoped Classical in
lemma cut_crosses_indicator_add_eq_inter_union_add_two_betweenDiffs
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (A B : Finset V) (e : E) :
    (if Crosses G A e then 1 else 0) +
        (if Crosses G B e then 1 else 0) =
      (if Crosses G (A ∩ B) e then 1 else 0) +
        (if Crosses G (A ∪ B) e then 1 else 0) +
          2 * if CrossesBetweenDiffs G A B e then 1 else 0 := by
  unfold Crosses CrossesBetweenDiffs
  by_cases h0A : G.endAt e 0 ∈ A <;>
    by_cases h1A : G.endAt e 1 ∈ A <;>
    by_cases h0B : G.endAt e 0 ∈ B <;>
    by_cases h1B : G.endAt e 1 ∈ B <;>
    simp [h0A, h1A, h0B, h1B]

open scoped Classical in
lemma cut_card_add_cut_card_eq_inter_union_add_two_edgesBetweenDiffs
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (A B : Finset V) :
    (cut G A).card + (cut G B).card =
      (cut G (A ∩ B)).card + (cut G (A ∪ B)).card +
        2 * (edgesBetweenDiffs G A B).card := by
  have hbetween :
      (∑ e : E, 2 * (if CrossesBetweenDiffs G A B e then 1 else 0)) =
        2 * (edgesBetweenDiffs G A B).card := by
    have hcard :
        (∑ e : E, if CrossesBetweenDiffs G A B e then 1 else 0) =
          (edgesBetweenDiffs G A B).card := by
      rw [Finset.card_eq_sum_ones]
      simp [edgesBetweenDiffs]
    rw [← hcard, Finset.mul_sum]
  calc
    (cut G A).card + (cut G B).card =
        (∑ e : E, if Crosses G A e then 1 else 0) +
          ∑ e : E, if Crosses G B e then 1 else 0 := by
          rw [cut_card_eq_sum_crosses_indicator,
            cut_card_eq_sum_crosses_indicator]
    _ = ∑ e : E,
          ((if Crosses G A e then 1 else 0) +
            if Crosses G B e then 1 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ e : E,
          ((if Crosses G (A ∩ B) e then 1 else 0) +
            (if Crosses G (A ∪ B) e then 1 else 0) +
              2 * if CrossesBetweenDiffs G A B e then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [cut_crosses_indicator_add_eq_inter_union_add_two_betweenDiffs]
    _ = (∑ e : E, if Crosses G (A ∩ B) e then 1 else 0) +
          (∑ e : E, if Crosses G (A ∪ B) e then 1 else 0) +
            ∑ e : E, 2 * (if CrossesBetweenDiffs G A B e then 1 else 0) := by
          simp [Finset.sum_add_distrib, add_assoc, add_comm]
    _ = (cut G (A ∩ B)).card + (cut G (A ∪ B)).card +
          2 * (edgesBetweenDiffs G A B).card := by
          rw [← cut_card_eq_sum_crosses_indicator,
            ← cut_card_eq_sum_crosses_indicator, hbetween]

open scoped Classical in
lemma OrientedPseudograph.cut_reachableComponent_eq_empty
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedPseudograph V E) (x : V) :
    G.cut (Finset.univ.filter fun y ↦ G.ReachableIn Finset.univ x y) = ∅ := by
  classical
  let S : Finset V := Finset.univ.filter fun y ↦ G.ReachableIn Finset.univ x y
  ext e
  constructor
  · intro he
    have hcross : G.Crosses S e := by
      simpa [OrientedPseudograph.cut, S] using he
    have h01 : G.ReachableIn Finset.univ (G.endAt e 0) (G.endAt e 1) :=
      G.endpoint_reachable_of_edge_mem (Finset.mem_univ e)
    unfold OrientedPseudograph.Crosses at hcross
    by_cases h0 : G.endAt e 0 ∈ S
    · have h1 : G.endAt e 1 ∈ S := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp h0).2.trans h01⟩
      exact (hcross (propext ⟨fun _ ↦ h1, fun _ ↦ h0⟩)).elim
    · by_cases h1 : G.endAt e 1 ∈ S
      · have h0' : G.endAt e 0 ∈ S := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (Finset.mem_filter.mp h1).2.trans h01.symm⟩
        exact (h0 h0').elim
      · exact (hcross (propext ⟨fun h ↦ (h0 h).elim, fun h ↦ (h1 h).elim⟩)).elim
  · intro he
    simp at he

def IsFleischnerAdmissibleSplitWithLoops
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) (e f : E) : Prop :=
  ∀ S : Finset V,
    (∃ x ∈ S, x ≠ v) →
    (∃ y : V, y ∉ S ∧ y ≠ v) →
      2 ≤ ((splitOffWithLoops G v e f).cut S).card

lemma IsFleischnerAdmissibleSplitWithLoops.to_admissible
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} {e f : E}
    (h : IsFleischnerAdmissibleSplitWithLoops G v e f) :
    IsAdmissibleSplitWithLoops G v e f := by
  classical
  intro x y hxv hyv _hxy
  by_contra hnot
  let H := splitOffWithLoops G v e f
  let S : Finset V := Finset.univ.filter fun z ↦ H.ReachableIn Finset.univ x z
  have hxS : x ∈ S := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      SimpleGraph.Reachable.refl x⟩
  have hyS : y ∉ S := by
    intro hy
    exact hnot (Finset.mem_filter.mp hy).2
  have htwo := h S ⟨x, hxS, hxv⟩ ⟨y, hyS, hyv⟩
  have hcut := H.cut_reachableComponent_eq_empty x
  rw [hcut] at htwo
  simp at htwo

lemma splitOffWithLoops_old_mem_cut_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f g : E}
    (hg : g ≠ e ∧ g ≠ f) (S : Finset V) :
    splitOldEdge g hg ∈ (splitOffWithLoops G v e f).cut S ↔
      g ∈ cut G S := by
  classical
  simp [OrientedPseudograph.cut, cut, OrientedPseudograph.Crosses,
    Crosses, splitOldEdge, splitOffWithLoops]

lemma splitOffWithLoops_new_mem_cut_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (S : Finset V) :
    splitNewEdge e f ∈ (splitOffWithLoops G v e f).cut S ↔
      (otherEndpoint G v e ∈ S) ≠ (otherEndpoint G v f ∈ S) := by
  classical
  simp [OrientedPseudograph.cut, OrientedPseudograph.Crosses,
    splitNewEdge, splitOffWithLoops]

lemma splitOldEdge_ne_splitNewEdge {E : Type*} {e f g : E}
    (hg : g ≠ e ∧ g ≠ f) :
    splitOldEdge g hg ≠ splitNewEdge e f := by
  intro h
  cases h

lemma splitOffWithLoops_original_cut_erase_erase_card_le_cut
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (S : Finset V) :
    (((cut G S).erase e).erase f).card ≤
      ((splitOffWithLoops G v e f).cut S).card := by
  classical
  let H := splitOffWithLoops G v e f
  let A := {g : E // g ∈ ((cut G S).erase e).erase f}
  let B := {x : SplitEdge E e f // x ∈ H.cut S}
  let φ : A → B := fun g ↦
    let hgf : g.1 ≠ f := (Finset.mem_erase.mp g.2).1
    let hge : g.1 ≠ e := (Finset.mem_erase.mp (Finset.mem_erase.mp g.2).2).1
    let hgcut : g.1 ∈ cut G S := (Finset.mem_erase.mp
      (Finset.mem_erase.mp g.2).2).2
    ⟨splitOldEdge g.1 ⟨hge, hgf⟩,
      (splitOffWithLoops_old_mem_cut_iff G ⟨hge, hgf⟩ S).2 hgcut⟩
  have hφinj : Function.Injective φ := by
    intro a b hab
    have habval : a.1 = b.1 := by
      have hval := congrArg Subtype.val hab
      simpa only [φ, splitOldEdge] using congrArg
        (fun x : SplitEdge E e f =>
          match x with
          | Sum.inl y => y.1
          | Sum.inr _ => a.1) hval
    exact Subtype.ext habval
  have hcard : Fintype.card A ≤ Fintype.card B :=
    Fintype.card_le_of_injective φ hφinj
  have hAcard : Fintype.card A = (((cut G S).erase e).erase f).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext g
    simp
  have hBcard : Fintype.card B = (H.cut S).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp
  rw [hAcard, hBcard] at hcard
  simpa [H] using hcard

lemma splitOffWithLoops_original_cut_erase_erase_card_le_cut_erase_new
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (S : Finset V) :
    (((cut G S).erase e).erase f).card ≤
      (((splitOffWithLoops G v e f).cut S).erase (splitNewEdge e f)).card := by
  classical
  let H := splitOffWithLoops G v e f
  let A := {g : E // g ∈ ((cut G S).erase e).erase f}
  let B := {x : SplitEdge E e f // x ∈ (H.cut S).erase (splitNewEdge e f)}
  let φ : A → B := fun g ↦
    let hgf : g.1 ≠ f := (Finset.mem_erase.mp g.2).1
    let hge : g.1 ≠ e := (Finset.mem_erase.mp (Finset.mem_erase.mp g.2).2).1
    let hgcut : g.1 ∈ cut G S := (Finset.mem_erase.mp
      (Finset.mem_erase.mp g.2).2).2
    let hold : splitOldEdge g.1 ⟨hge, hgf⟩ ∈ H.cut S :=
      (splitOffWithLoops_old_mem_cut_iff G ⟨hge, hgf⟩ S).2 hgcut
    ⟨splitOldEdge g.1 ⟨hge, hgf⟩,
      Finset.mem_erase.mpr ⟨splitOldEdge_ne_splitNewEdge ⟨hge, hgf⟩, hold⟩⟩
  have hφinj : Function.Injective φ := by
    intro a b hab
    have habval : a.1 = b.1 := by
      have hval := congrArg Subtype.val hab
      simpa only [φ, splitOldEdge] using congrArg
        (fun x : SplitEdge E e f =>
          match x with
          | Sum.inl y => y.1
          | Sum.inr _ => a.1) hval
    exact Subtype.ext habval
  have hcard : Fintype.card A ≤ Fintype.card B :=
    Fintype.card_le_of_injective φ hφinj
  have hAcard : Fintype.card A = (((cut G S).erase e).erase f).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext g
    simp
  have hBcard :
      Fintype.card B = ((H.cut S).erase (splitNewEdge e f)).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp
  rw [hAcard, hBcard] at hcard
  simpa [H] using hcard

lemma cut_card_le_splitOffWithLoops_cut_card_add_two
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (S : Finset V) :
    (cut G S).card ≤ ((splitOffWithLoops G v e f).cut S).card + 2 := by
  have herase := Finset.card_le_erase_erase_add_two (cut G S) e f
  have hsplit := splitOffWithLoops_original_cut_erase_erase_card_le_cut
    G (v := v) (e := e) (f := f) S
  omega

lemma cut_card_le_three_of_splitOffWithLoops_cut_card_le_one
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (S : Finset V)
    (hsmall : ((splitOffWithLoops G v e f).cut S).card ≤ 1) :
    (cut G S).card ≤ 3 := by
  have h := cut_card_le_splitOffWithLoops_cut_card_add_two
    G (v := v) (e := e) (f := f) S
  omega

lemma cut_mem_split_pair_ne_of_new_split_crosses
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (he : IsIncident G v e) (hf : IsIncident G v f) {S : Finset V}
    (hnew : splitNewEdge e f ∈ (splitOffWithLoops G v e f).cut S) :
    (e ∈ cut G S) ≠ (f ∈ cut G S) := by
  have hnewcross :
      (otherEndpoint G v e ∈ S) ≠ (otherEndpoint G v f ∈ S) :=
    (splitOffWithLoops_new_mem_cut_iff G S).mp hnew
  have heiff :
      e ∈ cut G S ↔ (v ∈ S) ≠ (otherEndpoint G v e ∈ S) := by
    simpa [cut] using crosses_iff_incident_otherEndpoint G he S
  have hfiff :
      f ∈ cut G S ↔ (v ∈ S) ≠ (otherEndpoint G v f ∈ S) := by
    simpa [cut] using crosses_iff_incident_otherEndpoint G hf S
  by_cases hv : v ∈ S <;>
    by_cases heS : otherEndpoint G v e ∈ S <;>
    by_cases hfS : otherEndpoint G v f ∈ S <;>
    simp [hv, heS, hfS] at hnewcross heiff hfiff ⊢ <;> tauto

lemma cut_subset_pair_of_splitOffWithLoops_new_mem_small_cut
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} {S : Finset V}
    (hnew : splitNewEdge e f ∈ (splitOffWithLoops G v e f).cut S)
    (hsmall : ((splitOffWithLoops G v e f).cut S).card ≤ 1) :
    cut G S ⊆ ({e, f} : Finset E) := by
  have hHerase :
      (((splitOffWithLoops G v e f).cut S).erase (splitNewEdge e f)).card = 0 := by
    have hcard := Finset.card_erase_add_one hnew
    omega
  have heraseOldCard :
      (((cut G S).erase e).erase f).card = 0 := by
    have hle := splitOffWithLoops_original_cut_erase_erase_card_le_cut_erase_new
      G (v := v) (e := e) (f := f) S
    rw [hHerase] at hle
    omega
  have heraseOld : ((cut G S).erase e).erase f = ∅ :=
    Finset.card_eq_zero.mp heraseOldCard
  intro g hgcut
  by_cases hge : g = e
  · simp [hge]
  · by_cases hgf : g = f
    · simp [hgf]
    · have hgerase : g ∈ ((cut G S).erase e).erase f := by
        exact Finset.mem_erase.mpr
          ⟨hgf, Finset.mem_erase.mpr ⟨hge, hgcut⟩⟩
      rw [heraseOld] at hgerase
      simp at hgerase

lemma cut_card_eq_one_of_splitOffWithLoops_new_mem_small_cut
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} {S : Finset V}
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hnew : splitNewEdge e f ∈ (splitOffWithLoops G v e f).cut S)
    (hsmall : ((splitOffWithLoops G v e f).cut S).card ≤ 1) :
    (cut G S).card = 1 := by
  have hsub := cut_subset_pair_of_splitOffWithLoops_new_mem_small_cut
    G (v := v) (e := e) (f := f) hnew hsmall
  have hxor := cut_mem_split_pair_ne_of_new_split_crosses G he hf hnew
  by_cases hecut : e ∈ cut G S
  · have hfnot : f ∉ cut G S := by
      intro hfcut
      exact hxor (propext ⟨fun _ ↦ hfcut, fun _ ↦ hecut⟩)
    have hcut : cut G S = {e} := by
      ext g
      constructor
      · intro hg
        have hpair := hsub hg
        rw [Finset.mem_insert, Finset.mem_singleton] at hpair
        rcases hpair with hge | hgf
        · exact Finset.mem_singleton.mpr hge
        · subst g
          exact (hfnot hg).elim
      · intro hg
        exact Finset.mem_singleton.mp hg ▸ hecut
    rw [hcut]
    simp
  · have hfcut : f ∈ cut G S := by
      by_contra hfnot
      exact hxor (propext ⟨fun h ↦ (hecut h).elim, fun h ↦ (hfnot h).elim⟩)
    have hcut : cut G S = {f} := by
      ext g
      constructor
      · intro hg
        have hpair := hsub hg
        rw [Finset.mem_insert, Finset.mem_singleton] at hpair
        rcases hpair with hge | hgf
        · subst g
          exact (hecut hg).elim
        · exact Finset.mem_singleton.mpr hgf
      · intro hg
        exact Finset.mem_singleton.mp hg ▸ hfcut
    rw [hcut]
    simp

lemma splitOffWithLoops_new_not_mem_cut_of_bridgeless_small_cut
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} {S : Finset V}
    (hb : Bridgeless G) (he : IsIncident G v e) (hf : IsIncident G v f)
    (hsmall : ((splitOffWithLoops G v e f).cut S).card ≤ 1) :
    splitNewEdge e f ∉ (splitOffWithLoops G v e f).cut S := by
  intro hnew
  exact hb S
    (cut_card_eq_one_of_splitOffWithLoops_new_mem_small_cut G he hf hnew hsmall)

lemma splitOffWithLoops_endpoints_same_side_of_bridgeless_small_cut
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} {S : Finset V}
    (hb : Bridgeless G) (he : IsIncident G v e) (hf : IsIncident G v f)
    (hsmall : ((splitOffWithLoops G v e f).cut S).card ≤ 1) :
    (otherEndpoint G v e ∈ S) = (otherEndpoint G v f ∈ S) := by
  by_contra hside
  exact splitOffWithLoops_new_not_mem_cut_of_bridgeless_small_cut G hb he hf hsmall
    ((splitOffWithLoops_new_mem_cut_iff G S).mpr hside)

lemma cut_card_le_splitOffWithLoops_cut_card_of_pair_not_mem_cut
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} {S : Finset V}
    (hecut : e ∉ cut G S) (hfcut : f ∉ cut G S) :
    (cut G S).card ≤ ((splitOffWithLoops G v e f).cut S).card := by
  have hle := splitOffWithLoops_original_cut_erase_erase_card_le_cut
    G (v := v) (e := e) (f := f) S
  rw [Finset.erase_eq_of_notMem hecut] at hle
  rw [Finset.erase_eq_of_notMem hfcut] at hle
  exact hle

lemma splitOffWithLoops_endpoint_side_ne_split_vertex_side_of_small_cut
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} {S : Finset V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hin : ∃ x ∈ S, x ≠ v) (hout : ∃ y : V, y ∉ S ∧ y ≠ v)
    (hsmall : ((splitOffWithLoops G v e f).cut S).card ≤ 1) :
    (v ∈ S) ≠ (otherEndpoint G v e ∈ S) := by
  have hsame :=
    splitOffWithLoops_endpoints_same_side_of_bridgeless_small_cut G hb he hf hsmall
  rcases hin with ⟨x, hxS, hxv⟩
  have hSnonempty : S.Nonempty := ⟨x, hxS⟩
  have hSproper : S ≠ Finset.univ := by
    rintro rfl
    rcases hout with ⟨y, hyS, _⟩
    exact hyS (Finset.mem_univ y)
  have hlow : 2 ≤ (cut G S).card :=
    two_le_cut_card_of_connects_bridgeless G hconn hb hSnonempty hSproper
  intro hve
  have hecut : e ∉ cut G S := by
    have heiff :
        e ∈ cut G S ↔ (v ∈ S) ≠ (otherEndpoint G v e ∈ S) := by
      simpa [cut] using crosses_iff_incident_otherEndpoint G he S
    rw [heiff]
    exact not_not.mpr hve
  have hvf : (v ∈ S) = (otherEndpoint G v f ∈ S) := hve.trans hsame
  have hfcut : f ∉ cut G S := by
    have hfiff :
        f ∈ cut G S ↔ (v ∈ S) ≠ (otherEndpoint G v f ∈ S) := by
      simpa [cut] using crosses_iff_incident_otherEndpoint G hf S
    rw [hfiff]
    exact not_not.mpr hvf
  have hle := cut_card_le_splitOffWithLoops_cut_card_of_pair_not_mem_cut
    G (v := v) (e := e) (f := f) hecut hfcut
  omega

lemma splitOffWithLoops_endpoints_opposite_split_vertex_side_of_small_cut
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} {S : Finset V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hin : ∃ x ∈ S, x ≠ v) (hout : ∃ y : V, y ∉ S ∧ y ≠ v)
    (hsmall : ((splitOffWithLoops G v e f).cut S).card ≤ 1) :
    (v ∈ S) ≠ (otherEndpoint G v e ∈ S) ∧
      (otherEndpoint G v e ∈ S) = (otherEndpoint G v f ∈ S) := by
  exact ⟨splitOffWithLoops_endpoint_side_ne_split_vertex_side_of_small_cut
      G hconn hb he hf hin hout hsmall,
    splitOffWithLoops_endpoints_same_side_of_bridgeless_small_cut G hb he hf hsmall⟩

def WeakFleischnerDangerousSet
    {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) (v : V) (S : Finset V) : Prop :=
  (∃ x ∈ S, x ≠ v) ∧
    (∃ y : V, y ∉ S ∧ y ≠ v) ∧
      2 ≤ (cut G S).card ∧ (cut G S).card ≤ 3

lemma WeakFleischnerDangerousSet.compl
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {S : Finset V}
    (h : WeakFleischnerDangerousSet G v S) :
    WeakFleischnerDangerousSet G v (Finset.univ \ S) := by
  rcases h with ⟨⟨x, hxS, hxv⟩, ⟨y, hyS, hyv⟩, hlow, hhigh⟩
  have hcut := cut_compl G S
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨y, by simp [hyS], hyv⟩
  · exact ⟨x, by simp [hxS], hxv⟩
  · simpa [hcut] using hlow
  · simpa [hcut] using hhigh

lemma WeakFleischnerDangerousSet.union_of_cut_card_le_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {A B : Finset V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : WeakFleischnerDangerousSet G v A)
    (hout : ∃ y : V, y ∉ A ∪ B ∧ y ≠ v)
    (hcut : (cut G (A ∪ B)).card ≤ 3) :
    WeakFleischnerDangerousSet G v (A ∪ B) := by
  rcases hA with ⟨⟨x, hxA, hxv⟩, _, _, _⟩
  have hin : ∃ x ∈ A ∪ B, x ≠ v :=
    ⟨x, Finset.mem_union_left B hxA, hxv⟩
  have hnonempty : (A ∪ B).Nonempty := ⟨x, Finset.mem_union_left B hxA⟩
  have hproper : A ∪ B ≠ Finset.univ := by
    intro h
    rcases hout with ⟨y, hy, _⟩
    exact hy (by rw [h]; exact Finset.mem_univ y)
  have hlow : 2 ≤ (cut G (A ∪ B)).card :=
    two_le_cut_card_of_connects_bridgeless G hconn hb hnonempty hproper
  exact ⟨hin, hout, hlow, hcut⟩

def FleischnerDangerousSetForPair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (e f : E) (S : Finset V) : Prop :=
  WeakFleischnerDangerousSet G v S ∧
    v ∉ S ∧ otherEndpoint G v e ∈ S ∧ otherEndpoint G v f ∈ S

lemma FleischnerDangerousSetForPair.weak
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S) :
    WeakFleischnerDangerousSet G v S :=
  hS.1

lemma FleischnerDangerousSetForPair.vertex_not_mem
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S) :
    v ∉ S :=
  hS.2.1

lemma FleischnerDangerousSetForPair.left_otherEndpoint_mem
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S) :
    otherEndpoint G v e ∈ S :=
  hS.2.2.1

lemma FleischnerDangerousSetForPair.right_otherEndpoint_mem
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S) :
    otherEndpoint G v f ∈ S :=
  hS.2.2.2

lemma mem_cut_of_incident_otherEndpoint_mem_of_vertex_not_mem
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {g : E} {S : Finset V}
    (hgv : IsIncident G v g) (hvS : v ∉ S)
    (hgS : otherEndpoint G v g ∈ S) :
    g ∈ cut G S := by
  have hcross : Crosses G S g :=
    (crosses_iff_incident_otherEndpoint G hgv S).mpr (by
      intro hiff
      exact hvS (hiff.mpr hgS))
  simpa [cut] using hcross

lemma FleischnerDangerousSetForPair.left_mem_cut
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S)
    (he : IsIncident G v e) :
    e ∈ cut G S :=
  mem_cut_of_incident_otherEndpoint_mem_of_vertex_not_mem G he
    hS.vertex_not_mem hS.left_otherEndpoint_mem

lemma FleischnerDangerousSetForPair.right_mem_cut
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S)
    (hf : IsIncident G v f) :
    f ∈ cut G S :=
  mem_cut_of_incident_otherEndpoint_mem_of_vertex_not_mem G hf
    hS.vertex_not_mem hS.right_otherEndpoint_mem

lemma FleischnerDangerousSetForPair.cut_card_le_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S) :
    (cut G S).card ≤ 3 :=
  hS.weak.2.2.2

lemma WeakFleischnerDangerousSet.to_dangerousSetForPair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : WeakFleischnerDangerousSet G v S)
    (hvS : v ∉ S)
    (heS : otherEndpoint G v e ∈ S)
    (hfS : otherEndpoint G v f ∈ S) :
    FleischnerDangerousSetForPair G v e f S :=
  ⟨hS, hvS, heS, hfS⟩

lemma WeakFleischnerDangerousSet.incidentEdgesInto_card_le_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {S : Finset V}
    (hS : WeakFleischnerDangerousSet G v S) (hvS : v ∉ S) :
    (incidentEdgesInto G v S).card ≤ 3 :=
  (incidentEdgesInto_card_le_cut_card_of_vertex_not_mem G hvS).trans hS.2.2.2

lemma WeakFleischnerDangerousSet.cutAwayFromVertex_card_le_one_of_two_le_incidentEdgesInto
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} {S : Finset V}
    (hS : WeakFleischnerDangerousSet G v S) (hvS : v ∉ S)
    (hinto : 2 ≤ (incidentEdgesInto G v S).card) :
    (cutAwayFromVertex G v S).card ≤ 1 := by
  have hsub : incidentEdgesInto G v S ⊆ cut G S :=
    incidentEdgesInto_subset_cut_of_vertex_not_mem G hvS
  have hcard :
      (cutAwayFromVertex G v S).card =
        (cut G S).card - (incidentEdgesInto G v S).card := by
    rw [cutAwayFromVertex, Finset.card_sdiff_of_subset hsub]
  have hcut := hS.2.2.2
  omega

lemma WeakFleischnerDangerousSet.cutAwayFromVertex_card_eq_zero_of_incidentEdgesInto_card_eq_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} {S : Finset V}
    (hS : WeakFleischnerDangerousSet G v S) (hvS : v ∉ S)
    (hinto : (incidentEdgesInto G v S).card = 3) :
    (cutAwayFromVertex G v S).card = 0 := by
  have hsub : incidentEdgesInto G v S ⊆ cut G S :=
    incidentEdgesInto_subset_cut_of_vertex_not_mem G hvS
  have hcard :
      (cutAwayFromVertex G v S).card =
        (cut G S).card - (incidentEdgesInto G v S).card := by
    rw [cutAwayFromVertex, Finset.card_sdiff_of_subset hsub]
  have hcutHigh := hS.2.2.2
  have hcutLow : (incidentEdgesInto G v S).card ≤ (cut G S).card :=
    Finset.card_le_card hsub
  omega

lemma FleischnerDangerousSetForPair.left_mem_incidentEdgesInto
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S)
    (he : IsIncident G v e) :
    e ∈ incidentEdgesInto G v S :=
  (mem_incidentEdgesInto G v S e).mpr ⟨he, hS.left_otherEndpoint_mem⟩

lemma FleischnerDangerousSetForPair.right_mem_incidentEdgesInto
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S)
    (hf : IsIncident G v f) :
    f ∈ incidentEdgesInto G v S :=
  (mem_incidentEdgesInto G v S f).mpr ⟨hf, hS.right_otherEndpoint_mem⟩

lemma FleischnerDangerousSetForPair.incidentEdgesInto_card_le_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S) :
    (incidentEdgesInto G v S).card ≤ 3 :=
  (incidentEdgesInto_card_le_cut_card_of_vertex_not_mem G
    hS.vertex_not_mem).trans hS.cut_card_le_three

lemma FleischnerDangerousSetForPair.two_le_incidentEdgesInto_card
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f) :
    2 ≤ (incidentEdgesInto G v S).card := by
  classical
  have heIn := hS.left_mem_incidentEdgesInto he
  have hfIn := hS.right_mem_incidentEdgesInto hf
  have hpair :
      ({e, f} : Finset E) ⊆ incidentEdgesInto G v S := by
    intro g hg
    rw [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact heIn
    · exact hfIn
  have hcard := Finset.card_le_card hpair
  rwa [Finset.card_pair hef] at hcard

lemma FleischnerDangerousSetForPair.incidentEdgesInto_card_eq_two_or_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f) :
    (incidentEdgesInto G v S).card = 2 ∨
      (incidentEdgesInto G v S).card = 3 := by
  have hlow := hS.two_le_incidentEdgesInto_card hef he hf
  have hhigh := hS.incidentEdgesInto_card_le_three
  omega

lemma FleischnerDangerousSetForPair.cut_sdiff_incidentEdgesInto_card_le_one
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f) :
    (cut G S \ incidentEdgesInto G v S).card ≤ 1 := by
  have hsub : incidentEdgesInto G v S ⊆ cut G S :=
    incidentEdgesInto_subset_cut_of_vertex_not_mem G hS.vertex_not_mem
  have hcard :
      (cut G S \ incidentEdgesInto G v S).card =
        (cut G S).card - (incidentEdgesInto G v S).card := by
    rw [Finset.card_sdiff_of_subset hsub]
  have hlow := hS.two_le_incidentEdgesInto_card hef he hf
  have hhigh := hS.cut_card_le_three
  omega

lemma FleischnerDangerousSetForPair.cutAwayFromVertex_card_le_one
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f) :
    (cutAwayFromVertex G v S).card ≤ 1 := by
  simpa [cutAwayFromVertex] using
    hS.cut_sdiff_incidentEdgesInto_card_le_one hef he hf

lemma three_le_incidentEdgesInto_card_of_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V} {e f g : E}
    (he : IsIncident G v e) (hf : IsIncident G v f) (hg : IsIncident G v g)
    (heS : otherEndpoint G v e ∈ S)
    (hfS : otherEndpoint G v f ∈ S)
    (hgS : otherEndpoint G v g ∈ S)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    3 ≤ (incidentEdgesInto G v S).card := by
  classical
  have heIn : e ∈ incidentEdgesInto G v S :=
    (mem_incidentEdgesInto G v S e).mpr ⟨he, heS⟩
  have hfIn : f ∈ incidentEdgesInto G v S :=
    (mem_incidentEdgesInto G v S f).mpr ⟨hf, hfS⟩
  have hgIn : g ∈ incidentEdgesInto G v S :=
    (mem_incidentEdgesInto G v S g).mpr ⟨hg, hgS⟩
  have hsub : ({e, f, g} : Finset E) ⊆ incidentEdgesInto G v S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact heIn
    · exact hfIn
    · exact hgIn
  have hcard := Finset.card_le_card hsub
  have htriple : ({e, f, g} : Finset E).card = 3 := by
    simp [hef, heg, hfg]
  rwa [htriple] at hcard

lemma FleischnerDangerousSetForPair.incidentEdgesInto_card_eq_three_of_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {p q : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v p q S)
    {e f g : E}
    (he : IsIncident G v e) (hf : IsIncident G v f) (hg : IsIncident G v g)
    (heS : otherEndpoint G v e ∈ S)
    (hfS : otherEndpoint G v f ∈ S)
    (hgS : otherEndpoint G v g ∈ S)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    (incidentEdgesInto G v S).card = 3 := by
  have hlow := three_le_incidentEdgesInto_card_of_three G
    he hf hg heS hfS hgS hef heg hfg
  have hhigh := hS.incidentEdgesInto_card_le_three
  omega

lemma FleischnerDangerousSetForPair.cut_sdiff_incidentEdgesInto_card_eq_zero_of_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} {p q : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v p q S)
    {e f g : E}
    (he : IsIncident G v e) (hf : IsIncident G v f) (hg : IsIncident G v g)
    (heS : otherEndpoint G v e ∈ S)
    (hfS : otherEndpoint G v f ∈ S)
    (hgS : otherEndpoint G v g ∈ S)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    (cut G S \ incidentEdgesInto G v S).card = 0 := by
  have hsub : incidentEdgesInto G v S ⊆ cut G S :=
    incidentEdgesInto_subset_cut_of_vertex_not_mem G hS.vertex_not_mem
  have hdiff :
      (cut G S \ incidentEdgesInto G v S).card =
        (cut G S).card - (incidentEdgesInto G v S).card := by
    rw [Finset.card_sdiff_of_subset hsub]
  have hinto :
      (incidentEdgesInto G v S).card = 3 :=
    hS.incidentEdgesInto_card_eq_three_of_three
      he hf hg heS hfS hgS hef heg hfg
  have hcutHigh := hS.cut_card_le_three
  have hcutLow : (incidentEdgesInto G v S).card ≤ (cut G S).card :=
    Finset.card_le_card hsub
  omega

lemma FleischnerDangerousSetForPair.cutAwayFromVertex_card_eq_zero_of_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} {p q : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v p q S)
    {e f g : E}
    (he : IsIncident G v e) (hf : IsIncident G v f) (hg : IsIncident G v g)
    (heS : otherEndpoint G v e ∈ S)
    (hfS : otherEndpoint G v f ∈ S)
    (hgS : otherEndpoint G v g ∈ S)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    (cutAwayFromVertex G v S).card = 0 := by
  simpa [cutAwayFromVertex] using
    hS.cut_sdiff_incidentEdgesInto_card_eq_zero_of_three
      he hf hg heS hfS hgS hef heg hfg

lemma FleischnerDangerousSetForPair.union_of_cut_card_le_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f p q : E}
    {A B : Finset V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : FleischnerDangerousSetForPair G v p q A)
    (hv : v ∉ A ∪ B)
    (he : otherEndpoint G v e ∈ A ∪ B)
    (hf : otherEndpoint G v f ∈ A ∪ B)
    (hout : ∃ y : V, y ∉ A ∪ B ∧ y ≠ v)
    (hcut : (cut G (A ∪ B)).card ≤ 3) :
    FleischnerDangerousSetForPair G v e f (A ∪ B) := by
  exact ⟨hA.weak.union_of_cut_card_le_three hconn hb hout hcut,
    hv, he, hf⟩

lemma Finset.card_lt_card_union_of_mem_right_not_mem
    {α : Type*} [DecidableEq α] {A B : Finset α} {x : α}
    (hxB : x ∈ B) (hxA : x ∉ A) :
    A.card < (A ∪ B).card := by
  have hproper : A ⊂ A ∪ B := by
    refine ⟨Finset.subset_union_left, ?_⟩
    intro hsub
    exact hxA (hsub (Finset.mem_union_right A hxB))
  exact Finset.card_lt_card hproper

noncomputable def fleischnerDangerousSetsAt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun S ↦
    ∃ e f : E, e ≠ f ∧ IsIncident G v e ∧ IsIncident G v f ∧
      FleischnerDangerousSetForPair G v e f S

lemma mem_fleischnerDangerousSetsAt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (S : Finset V) :
    S ∈ fleischnerDangerousSetsAt G v ↔
      ∃ e f : E, e ≠ f ∧ IsIncident G v e ∧ IsIncident G v f ∧
        FleischnerDangerousSetForPair G v e f S := by
  classical
  simp [fleischnerDangerousSetsAt]

lemma two_le_incidentEdgesInto_card_of_mem_fleischnerDangerousSetsAt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {S : Finset V}
    (hS : S ∈ fleischnerDangerousSetsAt G v) :
    2 ≤ (incidentEdgesInto G v S).card := by
  rcases (mem_fleischnerDangerousSetsAt G v S).mp hS with
    ⟨e, f, hef, he, hf, hPair⟩
  exact hPair.two_le_incidentEdgesInto_card hef he hf

lemma exists_maximal_fleischnerDangerousSetAt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V)
    (hne : (fleischnerDangerousSetsAt G v).Nonempty) :
    ∃ S ∈ fleischnerDangerousSetsAt G v,
      ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ S.card := by
  exact Finset.exists_max_image (fleischnerDangerousSetsAt G v) Finset.card hne

lemma exists_dangerousSetForPair_with_left_of_mem_fleischnerDangerousSetsAt
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {A : Finset V} {e : E}
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (heA : otherEndpoint G v e ∈ A) :
    ∃ q : E, e ≠ q ∧ IsIncident G v q ∧
      FleischnerDangerousSetForPair G v e q A := by
  rcases (mem_fleischnerDangerousSetsAt G v A).mp hA_mem with
    ⟨p, q, hpq, hp, _hq, hA⟩
  by_cases hep : e = p
  · subst e
    exact ⟨q, hpq, _hq, hA⟩
  · exact ⟨p, hep, hp,
      hA.weak.to_dangerousSetForPair hA.vertex_not_mem
        heA hA.left_otherEndpoint_mem⟩

noncomputable def fleischnerDangerousSetsForPair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (e f : E) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun S ↦ FleischnerDangerousSetForPair G v e f S

lemma mem_fleischnerDangerousSetsForPair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (e f : E) (S : Finset V) :
    S ∈ fleischnerDangerousSetsForPair G v e f ↔
      FleischnerDangerousSetForPair G v e f S := by
  classical
  simp [fleischnerDangerousSetsForPair]

lemma exists_minimal_inter_fleischnerDangerousSetForPair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (e f : E) (A : Finset V)
    (hne : (fleischnerDangerousSetsForPair G v e f).Nonempty) :
    ∃ S ∈ fleischnerDangerousSetsForPair G v e f,
      ∀ T ∈ fleischnerDangerousSetsForPair G v e f,
        (A ∩ S).card ≤ (A ∩ T).card := by
  exact Finset.exists_min_image
    (fleischnerDangerousSetsForPair G v e f)
    (fun S ↦ (A ∩ S).card) hne

noncomputable def weakFleischnerDangerousSetsContainingEndpoint
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (r : E) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun S ↦
    WeakFleischnerDangerousSet G v S ∧ v ∉ S ∧ otherEndpoint G v r ∈ S

lemma mem_weakFleischnerDangerousSetsContainingEndpoint
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (r : E) (S : Finset V) :
    S ∈ weakFleischnerDangerousSetsContainingEndpoint G v r ↔
      WeakFleischnerDangerousSet G v S ∧ v ∉ S ∧ otherEndpoint G v r ∈ S := by
  classical
  simp [weakFleischnerDangerousSetsContainingEndpoint]

lemma one_le_incidentEdgesInto_card_of_mem_weakContainingEndpoint
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {S : Finset V} {r : E}
    (hS : S ∈ weakFleischnerDangerousSetsContainingEndpoint G v r)
    (hr : IsIncident G v r) :
    1 ≤ (incidentEdgesInto G v S).card := by
  rcases (mem_weakFleischnerDangerousSetsContainingEndpoint G v r S).mp hS with
    ⟨_hweak, _hvS, hrS⟩
  have hrIn : r ∈ incidentEdgesInto G v S :=
    (mem_incidentEdgesInto G v S r).mpr ⟨hr, hrS⟩
  exact Finset.card_pos.mpr ⟨r, hrIn⟩

lemma FleischnerDangerousSetForPair.mem_weakContaining_left
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S) :
    S ∈ weakFleischnerDangerousSetsContainingEndpoint G v e :=
  (mem_weakFleischnerDangerousSetsContainingEndpoint G v e S).mpr
    ⟨hS.weak, hS.vertex_not_mem, hS.left_otherEndpoint_mem⟩

lemma FleischnerDangerousSetForPair.mem_weakContaining_right
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S) :
    S ∈ weakFleischnerDangerousSetsContainingEndpoint G v f :=
  (mem_weakFleischnerDangerousSetsContainingEndpoint G v f S).mpr
    ⟨hS.weak, hS.vertex_not_mem, hS.right_otherEndpoint_mem⟩

lemma exists_minimal_inter_weakFleischnerDangerousSetContainingEndpoint
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (r : E) (A : Finset V)
    (hne : (weakFleischnerDangerousSetsContainingEndpoint G v r).Nonempty) :
    ∃ S ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
      ∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
        (A ∩ S).card ≤ (A ∩ T).card := by
  exact Finset.exists_min_image
    (weakFleischnerDangerousSetsContainingEndpoint G v r)
    (fun S ↦ (A ∩ S).card) hne

lemma no_dangerousSet_contains_four_incident_otherEndpoints
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {p q : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v p q S)
    {e f g k : E}
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hg : IsIncident G v g) (hk : IsIncident G v k)
    (heS : otherEndpoint G v e ∈ S)
    (hfS : otherEndpoint G v f ∈ S)
    (hgS : otherEndpoint G v g ∈ S)
    (hkS : otherEndpoint G v k ∈ S)
    (hef : e ≠ f) (heg : e ≠ g) (hek : e ≠ k)
    (hfg : f ≠ g) (hfk : f ≠ k) (hgk : g ≠ k) :
    False := by
  classical
  have hve : e ∈ cut G S :=
    mem_cut_of_incident_otherEndpoint_mem_of_vertex_not_mem G he
      hS.vertex_not_mem heS
  have hvf : f ∈ cut G S :=
    mem_cut_of_incident_otherEndpoint_mem_of_vertex_not_mem G hf
      hS.vertex_not_mem hfS
  have hvg : g ∈ cut G S :=
    mem_cut_of_incident_otherEndpoint_mem_of_vertex_not_mem G hg
      hS.vertex_not_mem hgS
  have hvk : k ∈ cut G S :=
    mem_cut_of_incident_otherEndpoint_mem_of_vertex_not_mem G hk
      hS.vertex_not_mem hkS
  have hfour : 4 ≤ (cut G S).card :=
    Finset.four_le_card_of_mem hve hvf hvg hvk
      hef heg hek hfg hfk hgk
  have hthree := hS.cut_card_le_three
  omega

lemma exists_incident_otherEndpoint_not_mem_of_dangerousSet_and_four_edges
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {p q : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v p q S)
    {e f g k : E}
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hg : IsIncident G v g) (hk : IsIncident G v k)
    (hef : e ≠ f) (heg : e ≠ g) (hek : e ≠ k)
    (hfg : f ≠ g) (hfk : f ≠ k) (hgk : g ≠ k) :
    ∃ r : E, IsIncident G v r ∧ otherEndpoint G v r ∉ S := by
  by_contra hnone
  push Not at hnone
  exact no_dangerousSet_contains_four_incident_otherEndpoints G hS
    he hf hg hk
    (hnone e he) (hnone f hf) (hnone g hg) (hnone k hk)
    hef heg hek hfg hfk hgk

lemma exists_incident_otherEndpoint_not_mem_of_dangerousSet_of_degree_ge_four
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {p q : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v p q S)
    (hdeg : 4 ≤ degree G v) :
    ∃ r : E, IsIncident G v r ∧ otherEndpoint G v r ∉ S := by
  obtain ⟨e, f, g, k, he, hf, hg, hk, hef, heg, hek, hfg, hfk, hgk⟩ :=
    exists_four_distinct_incident_edges_of_degree_ge_four G hdeg
  exact exists_incident_otherEndpoint_not_mem_of_dangerousSet_and_four_edges
    G hS he hf hg hk hef heg hek hfg hfk hgk

lemma two_le_incidentEdgesOutside_card_of_dangerousSet_degree_ge_five
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {p q : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v p q S)
    (hdeg : 5 ≤ degree G v) :
    2 ≤ (incidentEdgesOutside G v S).card := by
  have hsplit := incidentEdgesInto_card_add_incidentEdgesOutside_card G v S
  have hinto := hS.incidentEdgesInto_card_le_three
  omega

lemma exists_two_incident_otherEndpoint_not_mem_of_dangerousSet_degree_ge_five
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {p q : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v p q S)
    (hdeg : 5 ≤ degree G v) :
    ∃ r s : E, r ≠ s ∧ IsIncident G v r ∧ IsIncident G v s ∧
      otherEndpoint G v r ∉ S ∧ otherEndpoint G v s ∉ S := by
  have htwo := two_le_incidentEdgesOutside_card_of_dangerousSet_degree_ge_five
    G hS hdeg
  have hone : 1 < (incidentEdgesOutside G v S).card := by omega
  obtain ⟨r, hrOut, s, hsOut, hrs⟩ := Finset.one_lt_card.mp hone
  have hr := (mem_incidentEdgesOutside G v S r).mp hrOut
  have hs := (mem_incidentEdgesOutside G v S s).mp hsOut
  exact ⟨r, s, hrs, hr.1, hs.1, hr.2, hs.2⟩

lemma exists_incident_otherEndpoint_not_mem_of_weakDangerousSet_of_degree_ge_four
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V}
    (hS : WeakFleischnerDangerousSet G v S) (hvS : v ∉ S)
    (hdeg : 4 ≤ degree G v) :
    ∃ r : E, IsIncident G v r ∧ otherEndpoint G v r ∉ S := by
  have hinto_le : (incidentEdgesInto G v S).card ≤ 3 :=
    (incidentEdgesInto_card_le_cut_card_of_vertex_not_mem G hvS).trans hS.2.2.2
  by_contra hnone
  push Not at hnone
  obtain ⟨e, f, g, k, he, hf, hg, hk, hef, heg, hek, hfg, hfk, hgk⟩ :=
    exists_four_distinct_incident_edges_of_degree_ge_four G hdeg
  have heIn : e ∈ incidentEdgesInto G v S :=
    (mem_incidentEdgesInto G v S e).mpr ⟨he, hnone e he⟩
  have hfIn : f ∈ incidentEdgesInto G v S :=
    (mem_incidentEdgesInto G v S f).mpr ⟨hf, hnone f hf⟩
  have hgIn : g ∈ incidentEdgesInto G v S :=
    (mem_incidentEdgesInto G v S g).mpr ⟨hg, hnone g hg⟩
  have hkIn : k ∈ incidentEdgesInto G v S :=
    (mem_incidentEdgesInto G v S k).mpr ⟨hk, hnone k hk⟩
  have hfour : 4 ≤ (incidentEdgesInto G v S).card :=
    Finset.four_le_card_of_mem heIn hfIn hgIn hkIn
      hef heg hek hfg hfk hgk
  omega

lemma weakFleischnerDangerousSet_of_splitOffWithLoops_cut_card_le_one
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    {S : Finset V}
    (hin : ∃ x ∈ S, x ≠ v) (hout : ∃ y : V, y ∉ S ∧ y ≠ v)
    (hsmall : ((splitOffWithLoops G v e f).cut S).card ≤ 1) :
    WeakFleischnerDangerousSet G v S := by
  rcases hin with ⟨x, hxS, hxv⟩
  have hSnonempty : S.Nonempty := ⟨x, hxS⟩
  have hSproper : S ≠ Finset.univ := by
    rintro rfl
    rcases hout with ⟨y, hyS, _⟩
    exact hyS (Finset.mem_univ y)
  have hlow : 2 ≤ (cut G S).card :=
    two_le_cut_card_of_connects_bridgeless G hconn hb hSnonempty hSproper
  have hhigh : (cut G S).card ≤ 3 :=
    cut_card_le_three_of_splitOffWithLoops_cut_card_le_one G S hsmall
  exact ⟨⟨x, hxS, hxv⟩, hout, hlow, hhigh⟩

lemma exists_weakFleischnerDangerousSet_of_not_admissible
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hbad : ¬ IsFleischnerAdmissibleSplitWithLoops G v e f) :
    ∃ S : Finset V, WeakFleischnerDangerousSet G v S := by
  classical
  rw [IsFleischnerAdmissibleSplitWithLoops] at hbad
  push Not at hbad
  rcases hbad with ⟨S, hin, hout, hsmall⟩
  have hsmall' : ((splitOffWithLoops G v e f).cut S).card ≤ 1 := by
    omega
  exact ⟨S,
    weakFleischnerDangerousSet_of_splitOffWithLoops_cut_card_le_one
      G hconn hb hin hout hsmall'⟩

lemma exists_fleischnerDangerousSetForPair_of_not_admissible
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hbad : ¬ IsFleischnerAdmissibleSplitWithLoops G v e f) :
    ∃ S : Finset V, FleischnerDangerousSetForPair G v e f S := by
  classical
  rw [IsFleischnerAdmissibleSplitWithLoops] at hbad
  push Not at hbad
  rcases hbad with ⟨S, hin, hout, hsmallNat⟩
  have hsmall : ((splitOffWithLoops G v e f).cut S).card ≤ 1 := by
    omega
  have hweak : WeakFleischnerDangerousSet G v S :=
    weakFleischnerDangerousSet_of_splitOffWithLoops_cut_card_le_one
      G hconn hb hin hout hsmall
  have hside :=
    splitOffWithLoops_endpoints_opposite_split_vertex_side_of_small_cut
      G hconn hb he hf hin hout hsmall
  by_cases hvS : v ∈ S
  · let T := Finset.univ \ S
    have hweakT : WeakFleischnerDangerousSet G v T := hweak.compl
    have hvT : v ∉ T := by
      simp [T, hvS]
    have heT : otherEndpoint G v e ∈ T := by
      have heNotS : otherEndpoint G v e ∉ S := by
        intro heS
        exact hside.1 (propext ⟨fun _ ↦ heS, fun _ ↦ hvS⟩)
      simp [T, heNotS]
    have hfT : otherEndpoint G v f ∈ T := by
      have hfNotS : otherEndpoint G v f ∉ S := by
        intro hfS
        have heS : otherEndpoint G v e ∈ S := by
          simpa [hside.2] using hfS
        exact hside.1 (propext ⟨fun _ ↦ heS, fun _ ↦ hvS⟩)
      simp [T, hfNotS]
    exact ⟨T, hweakT, hvT, heT, hfT⟩
  · have heS : otherEndpoint G v e ∈ S := by
      by_contra heNotS
      exact hside.1 (propext ⟨fun hv ↦ (hvS hv).elim,
        fun heS ↦ (heNotS heS).elim⟩)
    have hfS : otherEndpoint G v f ∈ S := by
      simpa [hside.2] using heS
    exact ⟨S, hweak, hvS, heS, hfS⟩

lemma exists_fleischnerDangerousSetForPair_cutAway_card_le_one_of_not_admissible
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f)
    (hbad : ¬ IsFleischnerAdmissibleSplitWithLoops G v e f) :
    ∃ S : Finset V,
      FleischnerDangerousSetForPair G v e f S ∧
        (cutAwayFromVertex G v S).card ≤ 1 := by
  obtain ⟨S, hS⟩ :=
    exists_fleischnerDangerousSetForPair_of_not_admissible
      G hconn hb he hf hbad
  exact ⟨S, hS, hS.cutAwayFromVertex_card_le_one hef he hf⟩

lemma exists_fleischnerDangerousSetForPair_cutAway_card_le_one_of_all_bad
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hbadAll :
      ∀ {e f : E}, e ≠ f → IsIncident G v e → IsIncident G v f →
        ¬ IsFleischnerAdmissibleSplitWithLoops G v e f)
    {e f : E} (hef : e ≠ f) (he : IsIncident G v e)
    (hf : IsIncident G v f) :
    ∃ S : Finset V,
      FleischnerDangerousSetForPair G v e f S ∧
        (cutAwayFromVertex G v S).card ≤ 1 := by
  exact exists_fleischnerDangerousSetForPair_cutAway_card_le_one_of_not_admissible
    G hconn hb hef he hf (hbadAll hef he hf)

lemma exists_minimal_inter_weakFleischnerDangerousSetContainingEndpoint_of_not_admissible
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e r : E} (A : Finset V)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (he : IsIncident G v e) (hr : IsIncident G v r)
    (hbad : ¬ IsFleischnerAdmissibleSplitWithLoops G v e r) :
    ∃ S ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
      ∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
        (A ∩ S).card ≤ (A ∩ T).card := by
  obtain ⟨S, hS⟩ :=
    exists_fleischnerDangerousSetForPair_of_not_admissible
      G hconn hb he hr hbad
  have hne : (weakFleischnerDangerousSetsContainingEndpoint G v r).Nonempty :=
    ⟨S, hS.mem_weakContaining_right⟩
  exact exists_minimal_inter_weakFleischnerDangerousSetContainingEndpoint
    G v r A hne

lemma splitOffWithLoops_cut_card_le_original_cut_erase_erase_of_new_not_mem
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (S : Finset V)
    (hnew :
      splitNewEdge e f ∉ (splitOffWithLoops G v e f).cut S) :
    ((splitOffWithLoops G v e f).cut S).card ≤
      (((cut G S).erase e).erase f).card := by
  classical
  let H := splitOffWithLoops G v e f
  let A := {x : SplitEdge E e f // x ∈ H.cut S}
  let B := {g : E // g ∈ ((cut G S).erase e).erase f}
  let φ : A → B := fun x ↦ by
    rcases x with ⟨x, hx⟩
    cases x with
    | inl g =>
        have hgcut : g.1 ∈ cut G S := by
          have hxold : splitOldEdge g.1 g.2 ∈ H.cut S := by
            simpa [splitOldEdge] using hx
          exact (splitOffWithLoops_old_mem_cut_iff G g.2 S).mp
            (by simpa [H] using hxold)
        exact ⟨g.1, Finset.mem_erase.mpr
          ⟨g.2.2, Finset.mem_erase.mpr ⟨g.2.1, hgcut⟩⟩⟩
    | inr u =>
        exact (hnew (by cases u; simpa [H, splitNewEdge] using hx)).elim
  have hφinj : Function.Injective φ := by
    intro x y hxy
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    cases x with
    | inl gx =>
        cases y with
        | inl gy =>
            have hval : gx.1 = gy.1 := by
              have hsub := congrArg Subtype.val hxy
              simpa [φ] using hsub
            apply Subtype.ext
            apply congrArg Sum.inl
            apply Subtype.ext
            exact hval
        | inr uy =>
            exact (hnew (by cases uy; simpa [H, splitNewEdge] using hy)).elim
    | inr ux =>
        exact (hnew (by cases ux; simpa [H, splitNewEdge] using hx)).elim
  have hcard : Fintype.card A ≤ Fintype.card B :=
    Fintype.card_le_of_injective φ hφinj
  have hAcard : Fintype.card A = (H.cut S).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp
  have hBcard : Fintype.card B = (((cut G S).erase e).erase f).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext g
    simp
  rw [hAcard, hBcard] at hcard
  simpa [H] using hcard

lemma splitOffWithLoops_cut_card_le_one_of_dangerousSetForPair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f) :
    ((splitOffWithLoops G v e f).cut S).card ≤ 1 := by
  classical
  have hnew :
      splitNewEdge e f ∉ (splitOffWithLoops G v e f).cut S := by
    intro hmem
    have hside :
        (otherEndpoint G v e ∈ S) ≠ (otherEndpoint G v f ∈ S) :=
      (splitOffWithLoops_new_mem_cut_iff G S).mp hmem
    exact hside (propext
      ⟨fun _ ↦ hS.right_otherEndpoint_mem, fun _ ↦ hS.left_otherEndpoint_mem⟩)
  have hle :=
    splitOffWithLoops_cut_card_le_original_cut_erase_erase_of_new_not_mem
      G S hnew
  have hecut : e ∈ cut G S := hS.left_mem_cut he
  have hfcut : f ∈ cut G S := hS.right_mem_cut hf
  have hfErase : f ∈ (cut G S).erase e :=
    Finset.mem_erase.mpr ⟨hef.symm, hfcut⟩
  have hEraseF :
      (((cut G S).erase e).erase f).card + 1 = ((cut G S).erase e).card :=
    Finset.card_erase_add_one hfErase
  have hEraseE : ((cut G S).erase e).card + 1 = (cut G S).card :=
    Finset.card_erase_add_one hecut
  have hhigh := hS.cut_card_le_three
  omega

lemma not_isFleischnerAdmissibleSplitWithLoops_of_dangerousSetForPair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f) :
    ¬ IsFleischnerAdmissibleSplitWithLoops G v e f := by
  intro hadm
  have hsmall :=
    splitOffWithLoops_cut_card_le_one_of_dangerousSetForPair
      G hS hef he hf
  have htwo := hadm S hS.weak.1 hS.weak.2.1
  omega

lemma not_isFleischnerAdmissibleSplitWithLoops_iff_exists_dangerousSetForPair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f) :
    ¬ IsFleischnerAdmissibleSplitWithLoops G v e f ↔
      ∃ S : Finset V, FleischnerDangerousSetForPair G v e f S := by
  constructor
  · exact exists_fleischnerDangerousSetForPair_of_not_admissible
      G hconn hb he hf
  · rintro ⟨S, hS⟩
    exact not_isFleischnerAdmissibleSplitWithLoops_of_dangerousSetForPair
      G hS hef he hf

lemma isFleischnerAdmissibleSplitWithLoops_iff_no_dangerousSetForPair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f) :
    IsFleischnerAdmissibleSplitWithLoops G v e f ↔
      ∀ S : Finset V, ¬ FleischnerDangerousSetForPair G v e f S := by
  constructor
  · intro hadm S hS
    exact not_isFleischnerAdmissibleSplitWithLoops_of_dangerousSetForPair
      G hS hef he hf hadm
  · intro hno
    by_contra hbad
    obtain ⟨S, hS⟩ :=
      exists_fleischnerDangerousSetForPair_of_not_admissible
        G hconn hb he hf hbad
    exact hno S hS

lemma not_isFleischnerAdmissibleSplitWithLoops_iff_pairFamily_nonempty
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f) :
    ¬ IsFleischnerAdmissibleSplitWithLoops G v e f ↔
      (fleischnerDangerousSetsForPair G v e f).Nonempty := by
  rw [not_isFleischnerAdmissibleSplitWithLoops_iff_exists_dangerousSetForPair
    G hconn hb hef he hf]
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨S, (mem_fleischnerDangerousSetsForPair G v e f S).mpr hS⟩
  · rintro ⟨S, hS⟩
    exact ⟨S, (mem_fleischnerDangerousSetsForPair G v e f S).mp hS⟩

lemma isFleischnerAdmissibleSplitWithLoops_iff_pairFamily_eq_empty
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f) :
    IsFleischnerAdmissibleSplitWithLoops G v e f ↔
      fleischnerDangerousSetsForPair G v e f = ∅ := by
  constructor
  · intro hadm
    have hno :=
      (isFleischnerAdmissibleSplitWithLoops_iff_no_dangerousSetForPair
        G hconn hb hef he hf).mp hadm
    ext S
    constructor
    · intro hS
      exact (hno S ((mem_fleischnerDangerousSetsForPair G v e f S).mp hS)).elim
    · intro hS
      simp at hS
  · intro hempty
    rw [isFleischnerAdmissibleSplitWithLoops_iff_no_dangerousSetForPair
      G hconn hb hef he hf]
    intro S hS
    have hmem : S ∈ fleischnerDangerousSetsForPair G v e f :=
      (mem_fleischnerDangerousSetsForPair G v e f S).mpr hS
    rw [hempty] at hmem
    simp at hmem

lemma exists_minimal_inter_dangerousSetForPair_of_not_admissible
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} (A : Finset V)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f)
    (hbad : ¬ IsFleischnerAdmissibleSplitWithLoops G v e f) :
    ∃ S ∈ fleischnerDangerousSetsForPair G v e f,
      ∀ T ∈ fleischnerDangerousSetsForPair G v e f,
        (A ∩ S).card ≤ (A ∩ T).card := by
  have hne : (fleischnerDangerousSetsForPair G v e f).Nonempty :=
    (not_isFleischnerAdmissibleSplitWithLoops_iff_pairFamily_nonempty
      G hconn hb hef he hf).mp hbad
  exact exists_minimal_inter_fleischnerDangerousSetForPair G v e f A hne

lemma fleischnerDangerousSetsAt_nonempty_of_no_local_pair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v)
    (hno : ¬ ∃ e f g k : E,
      e ≠ f ∧ IsIncident G v e ∧ IsIncident G v f ∧
      (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
      IsIncident G v g ∧ IsIncident G v k ∧
      IsFleischnerAdmissibleSplitWithLoops G v e f) :
    (fleischnerDangerousSetsAt G v).Nonempty := by
  obtain ⟨e, f, g, k, he, hf, hg, hk, hef, heg, hek, hfg, hfk, hgk⟩ :=
    exists_four_distinct_incident_edges_of_degree_ge_four G hdeg
  have hbad : ¬ IsFleischnerAdmissibleSplitWithLoops G v e f := by
    intro hadm
    apply hno
    exact ⟨e, f, g, k, hef, he, hf, ⟨heg.symm, hfg.symm⟩,
      ⟨hek.symm, hfk.symm⟩, hgk, hg, hk, hadm⟩
  obtain ⟨S, hS⟩ :=
    exists_fleischnerDangerousSetForPair_of_not_admissible
      G hconn hb he hf hbad
  exact ⟨S, (mem_fleischnerDangerousSetsAt G v S).mpr
    ⟨e, f, hef, he, hf, hS⟩⟩

lemma exists_maximal_fleischnerDangerousSetAt_of_no_local_pair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v)
    (hno : ¬ ∃ e f g k : E,
      e ≠ f ∧ IsIncident G v e ∧ IsIncident G v f ∧
      (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
      IsIncident G v g ∧ IsIncident G v k ∧
      IsFleischnerAdmissibleSplitWithLoops G v e f) :
    ∃ S ∈ fleischnerDangerousSetsAt G v,
      ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ S.card := by
  exact exists_maximal_fleischnerDangerousSetAt G v
    (fleischnerDangerousSetsAt_nonempty_of_no_local_pair
      G hconn hb hdeg hno)

lemma maximal_dangerousSet_contradiction_of_uncrossed_union
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hB : FleischnerDangerousSetForPair G v e r B)
    (her : e ≠ r) (he : IsIncident G v e) (hr : IsIncident G v r)
    (heA : otherEndpoint G v e ∈ A)
    (hrA : otherEndpoint G v r ∉ A)
    (hout : ∃ y : V, y ∉ A ∪ B ∧ y ≠ v)
    (hcut : (cut G (A ∪ B)).card ≤ 3) :
    False := by
  rcases (mem_fleischnerDangerousSetsAt G v A).mp hA_mem with
    ⟨p, q, hpq, hp, hq, hA⟩
  have hvUnion : v ∉ A ∪ B := by
    intro hv
    rcases Finset.mem_union.mp hv with hvA | hvB
    · exact hA.vertex_not_mem hvA
    · exact hB.vertex_not_mem hvB
  have heUnion : otherEndpoint G v e ∈ A ∪ B :=
    Finset.mem_union_left B heA
  have hrUnion : otherEndpoint G v r ∈ A ∪ B :=
    Finset.mem_union_right A hB.right_otherEndpoint_mem
  have hUnionDanger :
      FleischnerDangerousSetForPair G v e r (A ∪ B) :=
    hA.union_of_cut_card_le_three hconn hb hvUnion heUnion hrUnion hout hcut
  have hUnionMem : A ∪ B ∈ fleischnerDangerousSetsAt G v :=
    (mem_fleischnerDangerousSetsAt G v (A ∪ B)).mpr
      ⟨e, r, her, he, hr, hUnionDanger⟩
  have hle : (A ∪ B).card ≤ A.card := hAmax (A ∪ B) hUnionMem
  have hlt : A.card < (A ∪ B).card :=
    Finset.card_lt_card_union_of_mem_right_not_mem
      hB.right_otherEndpoint_mem hrA
  omega

lemma maximal_dangerousSet_contradiction_of_uncrossed_weak_union
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e q r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (_hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hA : FleischnerDangerousSetForPair G v e q A)
    (_hB : WeakFleischnerDangerousSet G v B)
    (hvB : v ∉ B) (hrB : otherEndpoint G v r ∈ B)
    (her : e ≠ r) (he : IsIncident G v e) (hr : IsIncident G v r)
    (hrA : otherEndpoint G v r ∉ A)
    (hout : ∃ y : V, y ∉ A ∪ B ∧ y ≠ v)
    (hcut : (cut G (A ∪ B)).card ≤ 3) :
    False := by
  have hvUnion : v ∉ A ∪ B := by
    intro hv
    rcases Finset.mem_union.mp hv with hvA | hvB'
    · exact hA.vertex_not_mem hvA
    · exact hvB hvB'
  have heUnion : otherEndpoint G v e ∈ A ∪ B :=
    Finset.mem_union_left B hA.left_otherEndpoint_mem
  have hrUnion : otherEndpoint G v r ∈ A ∪ B :=
    Finset.mem_union_right A hrB
  have hUnionDanger :
      FleischnerDangerousSetForPair G v e r (A ∪ B) :=
    hA.union_of_cut_card_le_three hconn hb hvUnion heUnion hrUnion hout hcut
  have hUnionMem : A ∪ B ∈ fleischnerDangerousSetsAt G v :=
    (mem_fleischnerDangerousSetsAt G v (A ∪ B)).mpr
      ⟨e, r, her, he, hr, hUnionDanger⟩
  have hle : (A ∪ B).card ≤ A.card := hAmax (A ∪ B) hUnionMem
  have hlt : A.card < (A ∪ B).card :=
    Finset.card_lt_card_union_of_mem_right_not_mem hrB hrA
  omega

lemma maximal_dangerousSet_contradiction_of_larger_dangerousSet
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A T : Finset V} {e f : E}
    (hAmax : ∀ U ∈ fleischnerDangerousSetsAt G v, U.card ≤ A.card)
    (hT : FleischnerDangerousSetForPair G v e f T)
    (he : e ≠ f) (hev : IsIncident G v e) (hfv : IsIncident G v f)
    (hlt : A.card < T.card) :
    False := by
  have hTmem : T ∈ fleischnerDangerousSetsAt G v :=
    (mem_fleischnerDangerousSetsAt G v T).mpr
      ⟨e, f, he, hev, hfv, hT⟩
  have hle := hAmax T hTmem
  omega

lemma cut_card_union_le_four_of_weakDangerousSets_inter_nonempty
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : WeakFleischnerDangerousSet G v A)
    (hB : WeakFleischnerDangerousSet G v B)
    (hvA : v ∉ A)
    (hinter : (A ∩ B).Nonempty) :
    (cut G (A ∪ B)).card ≤ 4 := by
  have hInterProper : A ∩ B ≠ Finset.univ := by
    intro h
    have hvInter : v ∈ A ∩ B := by
      rw [h]
      exact Finset.mem_univ v
    exact hvA (Finset.mem_inter.mp hvInter).1
  have hInterLow : 2 ≤ (cut G (A ∩ B)).card :=
    two_le_cut_card_of_connects_bridgeless G hconn hb hinter hInterProper
  have hsub := cut_card_inter_add_cut_card_union_le G A B
  have hAhigh := hA.2.2.2
  have hBhigh := hB.2.2.2
  omega

lemma cut_card_union_le_four_of_dangerousSets_inter_nonempty
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e f g k : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : FleischnerDangerousSetForPair G v e f A)
    (hB : FleischnerDangerousSetForPair G v g k B)
    (hinter : (A ∩ B).Nonempty) :
    (cut G (A ∪ B)).card ≤ 4 := by
  have hInterProper : A ∩ B ≠ Finset.univ := by
    intro h
    have hvInter : v ∈ A ∩ B := by
      rw [h]
      exact Finset.mem_univ v
    exact hA.vertex_not_mem (Finset.mem_inter.mp hvInter).1
  have hInterLow : 2 ≤ (cut G (A ∩ B)).card :=
    two_le_cut_card_of_connects_bridgeless G hconn hb hinter hInterProper
  have hsub := cut_card_inter_add_cut_card_union_le G A B
  have hAhigh := hA.cut_card_le_three
  have hBhigh := hB.cut_card_le_three
  omega

lemma cut_card_inter_eq_two_of_weakDangerousSets_union_card_eq_four
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : WeakFleischnerDangerousSet G v A)
    (hB : WeakFleischnerDangerousSet G v B)
    (hvA : v ∉ A)
    (hinter : (A ∩ B).Nonempty)
    (hUnion : (cut G (A ∪ B)).card = 4) :
    (cut G (A ∩ B)).card = 2 := by
  have hInterProper : A ∩ B ≠ Finset.univ := by
    intro h
    have hvInter : v ∈ A ∩ B := by
      rw [h]
      exact Finset.mem_univ v
    exact hvA (Finset.mem_inter.mp hvInter).1
  have hInterLow : 2 ≤ (cut G (A ∩ B)).card :=
    two_le_cut_card_of_connects_bridgeless G hconn hb hinter hInterProper
  have hsub := cut_card_inter_add_cut_card_union_le G A B
  have hAhigh := hA.2.2.2
  have hBhigh := hB.2.2.2
  omega

lemma cut_card_inter_eq_two_of_dangerousSets_union_card_eq_four
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e f g k : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : FleischnerDangerousSetForPair G v e f A)
    (hB : FleischnerDangerousSetForPair G v g k B)
    (hinter : (A ∩ B).Nonempty)
    (hUnion : (cut G (A ∪ B)).card = 4) :
    (cut G (A ∩ B)).card = 2 := by
  have hInterProper : A ∩ B ≠ Finset.univ := by
    intro h
    have hvInter : v ∈ A ∩ B := by
      rw [h]
      exact Finset.mem_univ v
    exact hA.vertex_not_mem (Finset.mem_inter.mp hvInter).1
  have hInterLow : 2 ≤ (cut G (A ∩ B)).card :=
    two_le_cut_card_of_connects_bridgeless G hconn hb hinter hInterProper
  have hsub := cut_card_inter_add_cut_card_union_le G A B
  have hAhigh := hA.cut_card_le_three
  have hBhigh := hB.cut_card_le_three
  omega

lemma edgesBetweenDiffs_card_eq_zero_of_weakDangerousSets_union_card_eq_four
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : WeakFleischnerDangerousSet G v A)
    (hB : WeakFleischnerDangerousSet G v B)
    (hvA : v ∉ A)
    (hinter : (A ∩ B).Nonempty)
    (hUnion : (cut G (A ∪ B)).card = 4) :
    (edgesBetweenDiffs G A B).card = 0 := by
  have hInter :
      (cut G (A ∩ B)).card = 2 :=
    cut_card_inter_eq_two_of_weakDangerousSets_union_card_eq_four
      G hconn hb hA hB hvA hinter hUnion
  have hExact :=
    cut_card_add_cut_card_eq_inter_union_add_two_edgesBetweenDiffs G A B
  have hLeft : (cut G A).card + (cut G B).card ≤ 6 := by
    have hAhigh := hA.2.2.2
    have hBhigh := hB.2.2.2
    omega
  have hRight :
      (cut G (A ∩ B)).card + (cut G (A ∪ B)).card +
        2 * (edgesBetweenDiffs G A B).card ≤ 6 := by
    rw [← hExact]
    exact hLeft
  rw [hInter, hUnion] at hRight
  omega

lemma edgesBetweenDiffs_card_eq_zero_of_dangerousSets_union_card_eq_four
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e f g k : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : FleischnerDangerousSetForPair G v e f A)
    (hB : FleischnerDangerousSetForPair G v g k B)
    (hinter : (A ∩ B).Nonempty)
    (hUnion : (cut G (A ∪ B)).card = 4) :
    (edgesBetweenDiffs G A B).card = 0 := by
  have hInter :
      (cut G (A ∩ B)).card = 2 :=
    cut_card_inter_eq_two_of_dangerousSets_union_card_eq_four
      G hconn hb hA hB hinter hUnion
  have hExact :=
    cut_card_add_cut_card_eq_inter_union_add_two_edgesBetweenDiffs G A B
  have hLeft : (cut G A).card + (cut G B).card ≤ 6 := by
    have hAhigh := hA.cut_card_le_three
    have hBhigh := hB.cut_card_le_three
    omega
  have hRight :
      (cut G (A ∩ B)).card + (cut G (A ∪ B)).card +
        2 * (edgesBetweenDiffs G A B).card ≤ 6 := by
    rw [← hExact]
    exact hLeft
  rw [hInter, hUnion] at hRight
  omega

lemma not_crossesBetweenDiffs_of_dangerousSets_union_card_eq_four
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e f g k x : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : FleischnerDangerousSetForPair G v e f A)
    (hB : FleischnerDangerousSetForPair G v g k B)
    (hinter : (A ∩ B).Nonempty)
    (hUnion : (cut G (A ∪ B)).card = 4) :
    ¬ CrossesBetweenDiffs G A B x := by
  intro hx
  have hcard :=
    edgesBetweenDiffs_card_eq_zero_of_dangerousSets_union_card_eq_four
      G hconn hb hA hB hinter hUnion
  have hxmem : x ∈ edgesBetweenDiffs G A B := by
    simp [edgesBetweenDiffs, hx]
  have hpos : 0 < (edgesBetweenDiffs G A B).card :=
    Finset.card_pos.mpr ⟨x, hxmem⟩
  omega

lemma not_crossesBetweenDiffs_of_weakDangerousSets_union_card_eq_four
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {x : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : WeakFleischnerDangerousSet G v A)
    (hB : WeakFleischnerDangerousSet G v B)
    (hvA : v ∉ A)
    (hinter : (A ∩ B).Nonempty)
    (hUnion : (cut G (A ∪ B)).card = 4) :
    ¬ CrossesBetweenDiffs G A B x := by
  intro hx
  have hcard :=
    edgesBetweenDiffs_card_eq_zero_of_weakDangerousSets_union_card_eq_four
      G hconn hb hA hB hvA hinter hUnion
  have hxmem : x ∈ edgesBetweenDiffs G A B := by
    simp [edgesBetweenDiffs, hx]
  have hpos : 0 < (edgesBetweenDiffs G A B).card :=
    Finset.card_pos.mpr ⟨x, hxmem⟩
  omega

lemma crosses_inter_of_crosses_sdiff_not_crosses_right
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (A B : Finset V) {e : E}
    (hR : Crosses G (B \ A) e) (hB : ¬ Crosses G B e) :
    Crosses G (A ∩ B) e := by
  unfold Crosses at hR hB ⊢
  by_cases h0A : G.endAt e 0 ∈ A <;>
    by_cases h1A : G.endAt e 1 ∈ A <;>
    by_cases h0B : G.endAt e 0 ∈ B <;>
    by_cases h1B : G.endAt e 1 ∈ B <;>
    simp [h0A, h1A, h0B, h1B] at hR hB ⊢

lemma cut_card_sdiff_le_three_of_dangerousSets_common_left
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {p q r : E}
    (hA : FleischnerDangerousSetForPair G v p q A)
    (hB : FleischnerDangerousSetForPair G v p r B)
    (hp : IsIncident G v p)
    (hIcard : (cut G (A ∩ B)).card = 2) :
    (cut G (B \ A)).card ≤ 3 := by
  classical
  let R := B \ A
  let I := A ∩ B
  have hpB : p ∈ cut G B := hB.left_mem_cut hp
  have hpI : p ∈ cut G I := by
    have hvI : v ∉ I := by
      intro hv
      exact hA.vertex_not_mem (Finset.mem_inter.mp hv).1
    have hpIvertex : otherEndpoint G v p ∈ I :=
      Finset.mem_inter.mpr
        ⟨hA.left_otherEndpoint_mem, hB.left_otherEndpoint_mem⟩
    exact mem_cut_of_incident_otherEndpoint_mem_of_vertex_not_mem
      G hp hvI hpIvertex
  have hpRnot : p ∉ cut G R := by
    have hiff : p ∈ cut G R ↔ (v ∈ R) ≠ (otherEndpoint G v p ∈ R) := by
      simpa [cut] using crosses_iff_incident_otherEndpoint G hp R
    rw [hiff]
    simp [R, hA.left_otherEndpoint_mem, hB.vertex_not_mem]
  let CRB := (cut G R).filter fun x ↦ x ∈ cut G B
  let CRnB := (cut G R).filter fun x ↦ x ∉ cut G B
  have hcardSplit : (cut G R).card = CRB.card + CRnB.card := by
    simpa [CRB, CRnB, Nat.add_comm] using
      (Finset.card_filter_add_card_filter_not
        (s := cut G R) (p := fun x ↦ x ∈ cut G B)).symm
  have hsubB : CRB ⊆ (cut G B).erase p := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_erase.mpr
      ⟨fun hxp ↦ hpRnot (hxp ▸ hx'.1), hx'.2⟩
  have hCRB : CRB.card ≤ 2 := by
    have hle := Finset.card_le_card hsubB
    have hpBcard := Finset.card_erase_add_one hpB
    have hBhigh := hB.cut_card_le_three
    omega
  have hsubI : CRnB ⊆ (cut G I).erase p := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    have hxRcross : Crosses G R x := by
      simpa [cut] using hx'.1
    have hxBnot : ¬ Crosses G B x := by
      intro hxBcross
      exact hx'.2 (by simpa [cut] using hxBcross)
    have hxIcross : Crosses G I x := by
      simpa [R, I] using
        crosses_inter_of_crosses_sdiff_not_crosses_right G A B hxRcross hxBnot
    have hxI : x ∈ cut G I := by
      simpa [cut] using hxIcross
    exact Finset.mem_erase.mpr
      ⟨fun hxp ↦ hpRnot (hxp ▸ hx'.1), hxI⟩
  have hCRI : CRnB.card ≤ 1 := by
    have hle := Finset.card_le_card hsubI
    have hpIcard := Finset.card_erase_add_one hpI
    have hIcard' : (cut G I).card = 2 := by
      simpa [I] using hIcard
    omega
  have htotal : (cut G R).card ≤ 3 := by
    omega
  simpa [R] using htotal

lemma weakFleischnerDangerousSet_sdiff_of_dangerousSets_common_left
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {p q r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : FleischnerDangerousSetForPair G v p q A)
    (hB : FleischnerDangerousSetForPair G v p r B)
    (hp : IsIncident G v p) (hr : IsIncident G v r)
    (hrA : otherEndpoint G v r ∉ A)
    (hIcard : (cut G (A ∩ B)).card = 2) :
    WeakFleischnerDangerousSet G v (B \ A) := by
  have hrR : otherEndpoint G v r ∈ B \ A := by
    exact Finset.mem_sdiff.mpr ⟨hB.right_otherEndpoint_mem, hrA⟩
  have hpNotR : otherEndpoint G v p ∉ B \ A := by
    intro hpR
    exact (Finset.mem_sdiff.mp hpR).2 hA.left_otherEndpoint_mem
  have hin : ∃ x ∈ B \ A, x ≠ v :=
    ⟨otherEndpoint G v r, hrR, otherEndpoint_ne_of_incident G hr⟩
  have hout : ∃ y : V, y ∉ B \ A ∧ y ≠ v :=
    ⟨otherEndpoint G v p, hpNotR, otherEndpoint_ne_of_incident G hp⟩
  have hnonempty : (B \ A).Nonempty := ⟨otherEndpoint G v r, hrR⟩
  have hproper : B \ A ≠ Finset.univ := by
    intro h
    exact hpNotR (by rw [h]; exact Finset.mem_univ _)
  have hlow : 2 ≤ (cut G (B \ A)).card :=
    two_le_cut_card_of_connects_bridgeless G hconn hb hnonempty hproper
  have hhigh : (cut G (B \ A)).card ≤ 3 :=
    cut_card_sdiff_le_three_of_dangerousSets_common_left
      G hA hB hp hIcard
  exact ⟨hin, hout, hlow, hhigh⟩

lemma dangerousSetForPair_sdiff_of_common_left_and_second_endpoint
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {p q r s : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : FleischnerDangerousSetForPair G v p q A)
    (hB : FleischnerDangerousSetForPair G v p r B)
    (hp : IsIncident G v p) (hr : IsIncident G v r)
    (hrA : otherEndpoint G v r ∉ A)
    (hIcard : (cut G (A ∩ B)).card = 2)
    (hsR : otherEndpoint G v s ∈ B \ A) :
    FleischnerDangerousSetForPair G v r s (B \ A) := by
  have hweak :
      WeakFleischnerDangerousSet G v (B \ A) :=
    weakFleischnerDangerousSet_sdiff_of_dangerousSets_common_left
      G hconn hb hA hB hp hr hrA hIcard
  have hvR : v ∉ B \ A := by
    intro hv
    exact hB.vertex_not_mem (Finset.mem_sdiff.mp hv).1
  have hrR : otherEndpoint G v r ∈ B \ A :=
    Finset.mem_sdiff.mpr ⟨hB.right_otherEndpoint_mem, hrA⟩
  exact hweak.to_dangerousSetForPair hvR hrR hsR

lemma exceptional_union_contradiction_of_large_replacement
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {p q r s : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hA : FleischnerDangerousSetForPair G v p q A)
    (hB : FleischnerDangerousSetForPair G v p r B)
    (hp : IsIncident G v p) (hr : IsIncident G v r) (hs : IsIncident G v s)
    (hrs : r ≠ s)
    (hrA : otherEndpoint G v r ∉ A)
    (hIcard : (cut G (A ∩ B)).card = 2)
    (hsR : otherEndpoint G v s ∈ B \ A)
    (hlt : A.card < (B \ A).card) :
    False := by
  have hRdanger :
      FleischnerDangerousSetForPair G v r s (B \ A) :=
    dangerousSetForPair_sdiff_of_common_left_and_second_endpoint
      G hconn hb hA hB hp hr hrA hIcard hsR
  exact maximal_dangerousSet_contradiction_of_larger_dangerousSet
    G hAmax hRdanger hrs hr hs hlt

lemma weak_replacement_and_outside_edge_of_exceptional_union
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {p q r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v)
    (hA : FleischnerDangerousSetForPair G v p q A)
    (hB : FleischnerDangerousSetForPair G v p r B)
    (hp : IsIncident G v p) (hr : IsIncident G v r)
    (hrA : otherEndpoint G v r ∉ A)
    (hUnion : (cut G (A ∪ B)).card = 4) :
    WeakFleischnerDangerousSet G v (B \ A) ∧
      ∃ s : E, IsIncident G v s ∧ otherEndpoint G v s ∉ B \ A := by
  have hinter : (A ∩ B).Nonempty :=
    ⟨otherEndpoint G v p,
      Finset.mem_inter.mpr
        ⟨hA.left_otherEndpoint_mem, hB.left_otherEndpoint_mem⟩⟩
  have hIcard : (cut G (A ∩ B)).card = 2 :=
    cut_card_inter_eq_two_of_dangerousSets_union_card_eq_four
      G hconn hb hA hB hinter hUnion
  have hweak :
      WeakFleischnerDangerousSet G v (B \ A) :=
    weakFleischnerDangerousSet_sdiff_of_dangerousSets_common_left
      G hconn hb hA hB hp hr hrA hIcard
  have hvR : v ∉ B \ A := by
    intro hv
    exact hB.vertex_not_mem (Finset.mem_sdiff.mp hv).1
  exact ⟨hweak,
    exists_incident_otherEndpoint_not_mem_of_weakDangerousSet_of_degree_ge_four
      G hweak hvR hdeg⟩

lemma weak_replacement_disjoint_of_exceptional_union
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {p q r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : FleischnerDangerousSetForPair G v p q A)
    (hB : FleischnerDangerousSetForPair G v p r B)
    (hp : IsIncident G v p) (hr : IsIncident G v r)
    (hrA : otherEndpoint G v r ∉ A)
    (hUnion : (cut G (A ∪ B)).card = 4) :
    ∃ R : Finset V,
      R ∈ weakFleischnerDangerousSetsContainingEndpoint G v r ∧
        (A ∩ R).card = 0 := by
  have hinter : (A ∩ B).Nonempty :=
    ⟨otherEndpoint G v p,
      Finset.mem_inter.mpr
        ⟨hA.left_otherEndpoint_mem, hB.left_otherEndpoint_mem⟩⟩
  have hIcard : (cut G (A ∩ B)).card = 2 :=
    cut_card_inter_eq_two_of_dangerousSets_union_card_eq_four
      G hconn hb hA hB hinter hUnion
  have hweakR :
      WeakFleischnerDangerousSet G v (B \ A) :=
    weakFleischnerDangerousSet_sdiff_of_dangerousSets_common_left
      G hconn hb hA hB hp hr hrA hIcard
  have hvR : v ∉ B \ A := by
    intro hv
    exact hB.vertex_not_mem (Finset.mem_sdiff.mp hv).1
  have hrR : otherEndpoint G v r ∈ B \ A :=
    Finset.mem_sdiff.mpr ⟨hB.right_otherEndpoint_mem, hrA⟩
  refine ⟨B \ A, ?_, ?_⟩
  · exact (mem_weakFleischnerDangerousSetsContainingEndpoint G v r (B \ A)).mpr
      ⟨hweakR, hvR, hrR⟩
  · have hset : A ∩ (B \ A) = ∅ := by
      ext x
      simp
    rw [hset, Finset.card_empty]

lemma minimal_weak_overlap_contradiction_of_disjoint_replacement
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B R : Finset V} {r : E}
    (hinter : (A ∩ B).Nonempty)
    (hBmin : ∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
      (A ∩ B).card ≤ (A ∩ T).card)
    (hRmem : R ∈ weakFleischnerDangerousSetsContainingEndpoint G v r)
    (hRzero : (A ∩ R).card = 0) :
    False := by
  have hmin := hBmin R hRmem
  have hpos : 0 < (A ∩ B).card := Finset.card_pos.mpr hinter
  omega

lemma exceptional_union_contradiction_of_minimal_weak_overlap
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {p q r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : FleischnerDangerousSetForPair G v p q A)
    (hB : FleischnerDangerousSetForPair G v p r B)
    (hp : IsIncident G v p) (hr : IsIncident G v r)
    (hrA : otherEndpoint G v r ∉ A)
    (hUnion : (cut G (A ∪ B)).card = 4)
    (hBmin : ∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
      (A ∩ B).card ≤ (A ∩ T).card) :
    False := by
  have hinter : (A ∩ B).Nonempty :=
    ⟨otherEndpoint G v p,
      Finset.mem_inter.mpr
        ⟨hA.left_otherEndpoint_mem, hB.left_otherEndpoint_mem⟩⟩
  have hIcard : (cut G (A ∩ B)).card = 2 :=
    cut_card_inter_eq_two_of_dangerousSets_union_card_eq_four
      G hconn hb hA hB hinter hUnion
  have hweakR :
      WeakFleischnerDangerousSet G v (B \ A) :=
    weakFleischnerDangerousSet_sdiff_of_dangerousSets_common_left
      G hconn hb hA hB hp hr hrA hIcard
  have hvR : v ∉ B \ A := by
    intro hv
    exact hB.vertex_not_mem (Finset.mem_sdiff.mp hv).1
  have hrR : otherEndpoint G v r ∈ B \ A :=
    Finset.mem_sdiff.mpr ⟨hB.right_otherEndpoint_mem, hrA⟩
  have hRmem :
      B \ A ∈ weakFleischnerDangerousSetsContainingEndpoint G v r :=
    (mem_weakFleischnerDangerousSetsContainingEndpoint G v r (B \ A)).mpr
      ⟨hweakR, hvR, hrR⟩
  have hmin := hBmin (B \ A) hRmem
  have hzero : (A ∩ (B \ A)).card = 0 := by
    have hset : A ∩ (B \ A) = ∅ := by
      ext x
      simp
    rw [hset, Finset.card_empty]
  have hpos : 0 < (A ∩ B).card := Finset.card_pos.mpr hinter
  omega

lemma inter_sdiff_self_right_eq_empty
    {α : Type*} [DecidableEq α] (A B : Finset α) :
    A ∩ (B \ A) = ∅ := by
  ext x
  simp

lemma union_sdiff_self_right_eq_union
    {α : Type*} [DecidableEq α] (A B : Finset α) :
    A ∪ (B \ A) = A ∪ B := by
  ext x
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [hxA, hxB]

lemma card_inter_sdiff_self_right_eq_zero
    {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∩ (B \ A)).card = 0 := by
  rw [inter_sdiff_self_right_eq_empty, Finset.card_empty]

lemma finset_eq_univ_sdiff_singleton_of_no_outside
    {V : Type*} [Fintype V] [DecidableEq V] {S : Finset V} {v : V}
    (hvS : v ∉ S) (hno : ¬ ∃ y : V, y ∉ S ∧ y ≠ v) :
    S = Finset.univ \ ({v} : Finset V) := by
  ext y
  constructor
  · intro hy
    have hyne : y ≠ v := by
      intro hyv
      exact hvS (hyv ▸ hy)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, by simpa using hyne⟩
  · intro hy
    by_contra hyS
    have hyne : y ≠ v := by
      intro hyv
      have : y ∉ ({v} : Finset V) := (Finset.mem_sdiff.mp hy).2
      exact this (by simp [hyv])
    exact hno ⟨y, hyS, hyne⟩

lemma degree_le_four_of_dangerousSets_union_no_outside
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e f g k : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : FleischnerDangerousSetForPair G v e f A)
    (hB : FleischnerDangerousSetForPair G v g k B)
    (hinter : (A ∩ B).Nonempty)
    (hnoOutside : ¬ ∃ y : V, y ∉ A ∪ B ∧ y ≠ v) :
    degree G v ≤ 4 := by
  classical
  have hvUnion : v ∉ A ∪ B := by
    intro hv
    rcases Finset.mem_union.mp hv with hvA | hvB
    · exact hA.vertex_not_mem hvA
    · exact hB.vertex_not_mem hvB
  have hUnionEq :
      A ∪ B = Finset.univ \ ({v} : Finset V) :=
    finset_eq_univ_sdiff_singleton_of_no_outside hvUnion hnoOutside
  have hleFour : (cut G (A ∪ B)).card ≤ 4 :=
    cut_card_union_le_four_of_dangerousSets_inter_nonempty
      G hconn hb hA hB hinter
  rw [hUnionEq, cut_card_univ_sdiff_singleton_eq_degree] at hleFour
  exact hleFour

lemma degree_le_four_of_weakDangerousSets_union_no_outside
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA : WeakFleischnerDangerousSet G v A)
    (hB : WeakFleischnerDangerousSet G v B)
    (hvA : v ∉ A) (hvB : v ∉ B)
    (hinter : (A ∩ B).Nonempty)
    (hnoOutside : ¬ ∃ y : V, y ∉ A ∪ B ∧ y ≠ v) :
    degree G v ≤ 4 := by
  classical
  have hvUnion : v ∉ A ∪ B := by
    intro hv
    rcases Finset.mem_union.mp hv with hvA' | hvB'
    · exact hvA hvA'
    · exact hvB hvB'
  have hUnionEq :
      A ∪ B = Finset.univ \ ({v} : Finset V) :=
    finset_eq_univ_sdiff_singleton_of_no_outside hvUnion hnoOutside
  have hleFour : (cut G (A ∪ B)).card ≤ 4 :=
    cut_card_union_le_four_of_weakDangerousSets_inter_nonempty
      G hconn hb hA hB hvA hinter
  rw [hUnionEq, cut_card_univ_sdiff_singleton_eq_degree] at hleFour
  exact hleFour

lemma maximal_dangerousSet_contradiction_no_union_outside_of_degree_ge_five
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 5 ≤ degree G v)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hB : FleischnerDangerousSetForPair G v e r B)
    (heA : otherEndpoint G v e ∈ A)
    (hnoOutside : ¬ ∃ y : V, y ∉ A ∪ B ∧ y ≠ v) :
    False := by
  rcases (mem_fleischnerDangerousSetsAt G v A).mp hA_mem with
    ⟨p, q, hpq, hp, hq, hA⟩
  have hinter : (A ∩ B).Nonempty :=
    ⟨otherEndpoint G v e,
      Finset.mem_inter.mpr ⟨heA, hB.left_otherEndpoint_mem⟩⟩
  have hle :=
    degree_le_four_of_dangerousSets_union_no_outside
      G hconn hb hA hB hinter hnoOutside
  omega

lemma maximal_dangerousSet_contradiction_no_union_outside_of_weak_degree_ge_five
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e q : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 5 ≤ degree G v)
    (hA : FleischnerDangerousSetForPair G v e q A)
    (hB : WeakFleischnerDangerousSet G v B) (hvB : v ∉ B)
    (hinter : (A ∩ B).Nonempty)
    (hnoOutside : ¬ ∃ y : V, y ∉ A ∪ B ∧ y ≠ v) :
    False := by
  have hle :=
    degree_le_four_of_weakDangerousSets_union_no_outside
      G hconn hb hA.weak hB hA.vertex_not_mem hvB hinter hnoOutside
  omega

lemma maximal_dangerousSet_contradiction_unless_union_cut_four
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hB : FleischnerDangerousSetForPair G v e r B)
    (her : e ≠ r) (he : IsIncident G v e) (hr : IsIncident G v r)
    (heA : otherEndpoint G v e ∈ A)
    (hrA : otherEndpoint G v r ∉ A)
    (hout : ∃ y : V, y ∉ A ∪ B ∧ y ≠ v)
    (hnotFour : (cut G (A ∪ B)).card ≠ 4) :
    False := by
  rcases (mem_fleischnerDangerousSetsAt G v A).mp hA_mem with
    ⟨p, q, hpq, hp, hq, hA⟩
  have hinter : (A ∩ B).Nonempty :=
    ⟨otherEndpoint G v e,
      Finset.mem_inter.mpr ⟨heA, hB.left_otherEndpoint_mem⟩⟩
  have hleFour : (cut G (A ∪ B)).card ≤ 4 :=
    cut_card_union_le_four_of_dangerousSets_inter_nonempty
      G hconn hb hA hB hinter
  have hleThree : (cut G (A ∪ B)).card ≤ 3 := by
    omega
  exact maximal_dangerousSet_contradiction_of_uncrossed_union
    G hconn hb hA_mem hAmax hB her he hr heA hrA hout hleThree

lemma maximal_dangerousSet_contradiction_unless_union_cut_four_of_weak
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e q r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hA : FleischnerDangerousSetForPair G v e q A)
    (hB : WeakFleischnerDangerousSet G v B)
    (hvB : v ∉ B) (hrB : otherEndpoint G v r ∈ B)
    (her : e ≠ r) (he : IsIncident G v e) (hr : IsIncident G v r)
    (hrA : otherEndpoint G v r ∉ A)
    (hinter : (A ∩ B).Nonempty)
    (hout : ∃ y : V, y ∉ A ∪ B ∧ y ≠ v)
    (hnotFour : (cut G (A ∪ B)).card ≠ 4) :
    False := by
  have hleFour : (cut G (A ∪ B)).card ≤ 4 :=
    cut_card_union_le_four_of_weakDangerousSets_inter_nonempty
      G hconn hb hA.weak hB hA.vertex_not_mem hinter
  have hleThree : (cut G (A ∪ B)).card ≤ 3 := by
    omega
  exact maximal_dangerousSet_contradiction_of_uncrossed_weak_union
    G hconn hb hA_mem hAmax hA hB hvB hrB her he hr
    hrA hout hleThree

lemma maximal_dangerousSet_contradiction_of_degree_ge_five_unless_union_cut_four
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 5 ≤ degree G v)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hB : FleischnerDangerousSetForPair G v e r B)
    (her : e ≠ r) (he : IsIncident G v e) (hr : IsIncident G v r)
    (heA : otherEndpoint G v e ∈ A)
    (hrA : otherEndpoint G v r ∉ A)
    (hnotFour : (cut G (A ∪ B)).card ≠ 4) :
    False := by
  by_cases hout : ∃ y : V, y ∉ A ∪ B ∧ y ≠ v
  · exact maximal_dangerousSet_contradiction_unless_union_cut_four
      G hconn hb hA_mem hAmax hB her he hr heA hrA hout hnotFour
  · exact maximal_dangerousSet_contradiction_no_union_outside_of_degree_ge_five
      G hconn hb hdeg hA_mem hB heA hout

lemma maximal_dangerousSet_contradiction_of_weak_degree_ge_five_unless_union_cut_four
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e q r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 5 ≤ degree G v)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hA : FleischnerDangerousSetForPair G v e q A)
    (hB : WeakFleischnerDangerousSet G v B)
    (hvB : v ∉ B) (hrB : otherEndpoint G v r ∈ B)
    (her : e ≠ r) (he : IsIncident G v e) (hr : IsIncident G v r)
    (hrA : otherEndpoint G v r ∉ A)
    (hinter : (A ∩ B).Nonempty)
    (hnotFour : (cut G (A ∪ B)).card ≠ 4) :
    False := by
  by_cases hout : ∃ y : V, y ∉ A ∪ B ∧ y ≠ v
  · exact maximal_dangerousSet_contradiction_unless_union_cut_four_of_weak
      G hconn hb hA_mem hAmax hA hB hvB hrB her he hr hrA
      hinter hout hnotFour
  · exact maximal_dangerousSet_contradiction_no_union_outside_of_weak_degree_ge_five
      G hconn hb hdeg hA hB hvB hinter hout

lemma maximal_dangerousSet_contradiction_of_minimal_weak_overlap_degree_ge_five
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e q r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 5 ≤ degree G v)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hA : FleischnerDangerousSetForPair G v e q A)
    (hB : FleischnerDangerousSetForPair G v e r B)
    (her : e ≠ r) (he : IsIncident G v e) (hr : IsIncident G v r)
    (hrA : otherEndpoint G v r ∉ A)
    (hBmin : ∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
      (A ∩ B).card ≤ (A ∩ T).card) :
    False := by
  by_cases hout : ∃ y : V, y ∉ A ∪ B ∧ y ≠ v
  · by_cases hfour : (cut G (A ∪ B)).card = 4
    · exact exceptional_union_contradiction_of_minimal_weak_overlap
        G hconn hb hA hB he hr hrA hfour hBmin
    · exact maximal_dangerousSet_contradiction_unless_union_cut_four
        G hconn hb hA_mem hAmax hB her he hr
        hA.left_otherEndpoint_mem hrA hout hfour
  · exact maximal_dangerousSet_contradiction_no_union_outside_of_degree_ge_five
      G hconn hb hdeg hA_mem hB hA.left_otherEndpoint_mem hout

lemma maximal_dangerousSet_contradiction_of_minimal_weak_overlap_degree_ge_five'
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 5 ≤ degree G v)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hB : FleischnerDangerousSetForPair G v e r B)
    (her : e ≠ r) (he : IsIncident G v e) (hr : IsIncident G v r)
    (heA : otherEndpoint G v e ∈ A)
    (hrA : otherEndpoint G v r ∉ A)
    (hBmin : ∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
      (A ∩ B).card ≤ (A ∩ T).card) :
    False := by
  obtain ⟨q, _heq, _hq, hA⟩ :=
    exists_dangerousSetForPair_with_left_of_mem_fleischnerDangerousSetsAt
      hA_mem heA
  exact maximal_dangerousSet_contradiction_of_minimal_weak_overlap_degree_ge_five
    G hconn hb hdeg hA_mem hAmax hA hB her he hr hrA hBmin

lemma maximal_dangerousSet_contradiction_of_weak_minimal_overlap_degree_ge_five_of_left_mem
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 5 ≤ degree G v)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hB : WeakFleischnerDangerousSet G v B)
    (hvB : v ∉ B)
    (her : e ≠ r) (he : IsIncident G v e) (hr : IsIncident G v r)
    (heA : otherEndpoint G v e ∈ A)
    (hrA : otherEndpoint G v r ∉ A)
    (heB : otherEndpoint G v e ∈ B)
    (hrB : otherEndpoint G v r ∈ B)
    (hBmin : ∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
      (A ∩ B).card ≤ (A ∩ T).card) :
    False := by
  have hBpair : FleischnerDangerousSetForPair G v e r B :=
    hB.to_dangerousSetForPair hvB heB hrB
  exact maximal_dangerousSet_contradiction_of_minimal_weak_overlap_degree_ge_five'
    G hconn hb hdeg hA_mem hAmax hBpair her he hr heA hrA hBmin

lemma weak_minimal_obstruction_left_endpoint_not_mem_degree_ge_five
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {e r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 5 ≤ degree G v)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hBmem : B ∈ weakFleischnerDangerousSetsContainingEndpoint G v r)
    (hBmin : ∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
      (A ∩ B).card ≤ (A ∩ T).card)
    (her : e ≠ r) (he : IsIncident G v e) (hr : IsIncident G v r)
    (heA : otherEndpoint G v e ∈ A)
    (hrA : otherEndpoint G v r ∉ A) :
    otherEndpoint G v e ∉ B := by
  rcases (mem_weakFleischnerDangerousSetsContainingEndpoint G v r B).mp hBmem with
    ⟨hB, hvB, hrB⟩
  intro heB
  exact maximal_dangerousSet_contradiction_of_weak_minimal_overlap_degree_ge_five_of_left_mem
    G hconn hb hdeg hA_mem hAmax hB hvB her he hr heA hrA
    heB hrB hBmin

lemma weak_minimal_obstruction_incident_endpoint_not_mem_of_mem_A_degree_ge_five
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {r p : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 5 ≤ degree G v)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hBmem : B ∈ weakFleischnerDangerousSetsContainingEndpoint G v r)
    (hBmin : ∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
      (A ∩ B).card ≤ (A ∩ T).card)
    (hr : IsIncident G v r) (hp : IsIncident G v p)
    (hpA : otherEndpoint G v p ∈ A)
    (hrA : otherEndpoint G v r ∉ A) :
    otherEndpoint G v p ∉ B := by
  have hpr : p ≠ r := by
    intro h
    exact hrA (by simpa [h] using hpA)
  exact weak_minimal_obstruction_left_endpoint_not_mem_degree_ge_five
    G hconn hb hdeg hA_mem hAmax hBmem hBmin
    hpr hp hr hpA hrA

lemma disjoint_incidentEdgesInto_of_weak_minimal_obstruction_degree_ge_five
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 5 ≤ degree G v)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hBmem : B ∈ weakFleischnerDangerousSetsContainingEndpoint G v r)
    (hBmin : ∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
      (A ∩ B).card ≤ (A ∩ T).card)
    (hr : IsIncident G v r)
    (hrA : otherEndpoint G v r ∉ A) :
    Disjoint (incidentEdgesInto G v A) (incidentEdgesInto G v B) := by
  rw [Finset.disjoint_left]
  intro p hpAInto hpBInto
  have hpA := (mem_incidentEdgesInto G v A p).mp hpAInto
  have hpB := (mem_incidentEdgesInto G v B p).mp hpBInto
  exact weak_minimal_obstruction_incident_endpoint_not_mem_of_mem_A_degree_ge_five
    G hconn hb hdeg hA_mem hAmax hBmem hBmin hr hpA.1 hpA.2 hrA hpB.2

lemma incidentEdgesInto_card_add_le_degree_of_disjoint
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) (v : V) (A B : Finset V)
    (hdisj : Disjoint (incidentEdgesInto G v A) (incidentEdgesInto G v B)) :
    (incidentEdgesInto G v A).card + (incidentEdgesInto G v B).card ≤
      degree G v := by
  classical
  have hsub :
      incidentEdgesInto G v A ∪ incidentEdgesInto G v B ⊆
        incidentEdgesAt G v := by
    intro e he
    rcases Finset.mem_union.mp he with heA | heB
    · exact (mem_incidentEdgesAt G v e).mpr
        ((mem_incidentEdgesInto G v A e).mp heA).1
    · exact (mem_incidentEdgesAt G v e).mpr
        ((mem_incidentEdgesInto G v B e).mp heB).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, ← degree_eq_incidentEdgesAt_card G v] at hcard
  exact hcard

lemma incidentEdgesInto_card_add_le_degree_of_weak_minimal_obstruction_degree_ge_five
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 5 ≤ degree G v)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hBmem : B ∈ weakFleischnerDangerousSetsContainingEndpoint G v r)
    (hBmin : ∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
      (A ∩ B).card ≤ (A ∩ T).card)
    (hr : IsIncident G v r)
    (hrA : otherEndpoint G v r ∉ A) :
    (incidentEdgesInto G v A).card + (incidentEdgesInto G v B).card ≤
      degree G v := by
  have hdisj :=
    disjoint_incidentEdgesInto_of_weak_minimal_obstruction_degree_ge_five
      G hconn hb hdeg hA_mem hAmax hBmem hBmin hr hrA
  exact incidentEdgesInto_card_add_le_degree_of_disjoint G v A B hdisj

lemma incidentEdgesInto_card_lt_degree_of_weak_minimal_obstruction_degree_ge_five
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 5 ≤ degree G v)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hBmem : B ∈ weakFleischnerDangerousSetsContainingEndpoint G v r)
    (hBmin : ∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
      (A ∩ B).card ≤ (A ∩ T).card)
    (hr : IsIncident G v r)
    (hrA : otherEndpoint G v r ∉ A) :
    (incidentEdgesInto G v A).card < degree G v := by
  have hone :
      1 ≤ (incidentEdgesInto G v B).card :=
    one_le_incidentEdgesInto_card_of_mem_weakContainingEndpoint hBmem hr
  have hsum :=
    incidentEdgesInto_card_add_le_degree_of_weak_minimal_obstruction_degree_ge_five
      G hconn hb hdeg hA_mem hAmax hBmem hBmin hr hrA
  omega

lemma weak_minimal_obstruction_incidentEdgesInto_card_add_two_le_degree
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V} {r : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 5 ≤ degree G v)
    (hA_mem : A ∈ fleischnerDangerousSetsAt G v)
    (hAmax : ∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card)
    (hBmem : B ∈ weakFleischnerDangerousSetsContainingEndpoint G v r)
    (hBmin : ∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
      (A ∩ B).card ≤ (A ∩ T).card)
    (hr : IsIncident G v r)
    (hrA : otherEndpoint G v r ∉ A) :
    (incidentEdgesInto G v B).card + 2 ≤ degree G v := by
  have htwo :
      2 ≤ (incidentEdgesInto G v A).card :=
    two_le_incidentEdgesInto_card_of_mem_fleischnerDangerousSetsAt hA_mem
  have hsum :=
    incidentEdgesInto_card_add_le_degree_of_weak_minimal_obstruction_degree_ge_five
      G hconn hb hdeg hA_mem hAmax hBmem hBmin hr hrA
  omega

lemma not_exists_weakFleischnerDangerousSet_contains_all_incident_endpoints
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) {v : V}
    (hdeg : 4 ≤ degree G v) :
    ¬ ∃ S : Finset V,
      WeakFleischnerDangerousSet G v S ∧ v ∉ S ∧
        ∀ r : E, IsIncident G v r → otherEndpoint G v r ∈ S := by
  rintro ⟨S, hS, hvS, hAll⟩
  obtain ⟨r, hr, hrS⟩ :=
    exists_incident_otherEndpoint_not_mem_of_weakDangerousSet_of_degree_ge_four
      G hS hvS hdeg
  exact hrS (hAll r hr)

theorem exists_fleischner_admissible_local_pair_of_global_bad_pair_obstruction
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hdeg : 4 ≤ degree G v)
    (hglobal :
      (∀ {e f : E}, e ≠ f → IsIncident G v e → IsIncident G v f →
        ¬ IsFleischnerAdmissibleSplitWithLoops G v e f) →
        ∃ S : Finset V,
          WeakFleischnerDangerousSet G v S ∧ v ∉ S ∧
            ∀ r : E, IsIncident G v r → otherEndpoint G v r ∈ S) :
    ∃ e f g k : E,
      e ≠ f ∧ IsIncident G v e ∧ IsIncident G v f ∧
      (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
      IsIncident G v g ∧ IsIncident G v k ∧
      IsFleischnerAdmissibleSplitWithLoops G v e f := by
  by_contra hno
  have hbadAll :
      ∀ {e f : E}, e ≠ f → IsIncident G v e → IsIncident G v f →
        ¬ IsFleischnerAdmissibleSplitWithLoops G v e f := by
    intro e f hef he hf hadm
    obtain ⟨g, k, hg, hk, hgk, hgv, hkv⟩ :=
      exists_two_remaining_incident_edges_of_degree_ge_four
        G hdeg hef he hf
    exact hno ⟨e, f, g, k, hef, he, hf, hg, hk, hgk, hgv, hkv, hadm⟩
  exact not_exists_weakFleischnerDangerousSet_contains_all_incident_endpoints
    G hdeg (hglobal hbadAll)

lemma isFleischnerAdmissibleSplitWithLoops_of_no_dangerousSetForPair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (he : IsIncident G v e) (hf : IsIncident G v f)
    (hno : ∀ S : Finset V, ¬ FleischnerDangerousSetForPair G v e f S) :
    IsFleischnerAdmissibleSplitWithLoops G v e f := by
  by_contra hbad
  obtain ⟨S, hS⟩ :=
    exists_fleischnerDangerousSetForPair_of_not_admissible
      G hconn hb he hf hbad
  exact hno S hS

lemma FleischnerDangerousSetForPair.cutAway_card_eq_one_of_all_incident_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f)
    (hreach : ∀ r : E, IsIncident G v r →
      (supportAwayFromVertex G v).Reachable
        (otherEndpoint G v e) (otherEndpoint G v r)) :
    (cutAwayFromVertex G v S).card = 1 := by
  rcases hS.weak.2.1 with ⟨y, hyS, hyv⟩
  obtain ⟨r, hr, hry⟩ :=
    exists_incident_endpoint_supportAway_reaches G hconn hb hyv
  have hey :
      (supportAwayFromVertex G v).Reachable (otherEndpoint G v e) y :=
    (hreach r hr).trans hry
  have hnonempty :
      (cutAwayFromVertex G v S).Nonempty :=
    cutAwayFromVertex_nonempty_of_supportAway_reachable_crossing
      G hS.vertex_not_mem hey hS.left_otherEndpoint_mem hyS
  have hpos : 0 < (cutAwayFromVertex G v S).card :=
    Finset.card_pos.mpr hnonempty
  have hone : (cutAwayFromVertex G v S).card ≤ 1 :=
    hS.cutAwayFromVertex_card_le_one hef he hf
  omega

lemma FleischnerDangerousSetForPair.incidentEdgesInto_card_eq_two_of_all_incident_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f)
    (hreach : ∀ r : E, IsIncident G v r →
      (supportAwayFromVertex G v).Reachable
        (otherEndpoint G v e) (otherEndpoint G v r)) :
    (incidentEdgesInto G v S).card = 2 := by
  have hsub : incidentEdgesInto G v S ⊆ cut G S :=
    incidentEdgesInto_subset_cut_of_vertex_not_mem G hS.vertex_not_mem
  have hdiff :
      (cutAwayFromVertex G v S).card =
        (cut G S).card - (incidentEdgesInto G v S).card := by
    rw [cutAwayFromVertex, Finset.card_sdiff_of_subset hsub]
  have haway :
      (cutAwayFromVertex G v S).card = 1 :=
    hS.cutAway_card_eq_one_of_all_incident_reachable
      hconn hb hef he hf hreach
  have hintoLow : 2 ≤ (incidentEdgesInto G v S).card :=
    hS.two_le_incidentEdgesInto_card hef he hf
  have hcutHigh : (cut G S).card ≤ 3 := hS.cut_card_le_three
  have hintoCut : (incidentEdgesInto G v S).card ≤ (cut G S).card :=
    Finset.card_le_card hsub
  omega

lemma FleischnerDangerousSetForPair.incidentEdgesInto_eq_pair_of_all_incident_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f)
    (hreach : ∀ r : E, IsIncident G v r →
      (supportAwayFromVertex G v).Reachable
        (otherEndpoint G v e) (otherEndpoint G v r)) :
    incidentEdgesInto G v S = {e, f} := by
  have heIn := hS.left_mem_incidentEdgesInto he
  have hfIn := hS.right_mem_incidentEdgesInto hf
  have hpairSub : ({e, f} : Finset E) ⊆ incidentEdgesInto G v S := by
    intro g hg
    rw [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact heIn
    · exact hfIn
  have hcard :
      (incidentEdgesInto G v S).card = 2 :=
    hS.incidentEdgesInto_card_eq_two_of_all_incident_reachable
      hconn hb hef he hf hreach
  have hpairCard : ({e, f} : Finset E).card = 2 := Finset.card_pair hef
  have hle : (incidentEdgesInto G v S).card ≤ ({e, f} : Finset E).card := by
    rw [hcard, hpairCard]
  exact (Finset.eq_of_subset_of_card_le hpairSub hle).symm

noncomputable def fleischnerTwoMarkDangerousPairs
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) : Finset (Finset E) := by
  classical
  exact Finset.univ.filter fun P ↦
    P.card = 2 ∧
      ∃ S ∈ fleischnerDangerousSetsAt G v, incidentEdgesInto G v S = P

lemma mem_fleischnerTwoMarkDangerousPairs
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (v : V) (P : Finset E) :
    P ∈ fleischnerTwoMarkDangerousPairs G v ↔
      P.card = 2 ∧
        ∃ S ∈ fleischnerDangerousSetsAt G v, incidentEdgesInto G v S = P := by
  classical
  simp [fleischnerTwoMarkDangerousPairs]

lemma fleischnerTwoMarkDangerousPairs_card_eq_two
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {P : Finset E}
    (hP : P ∈ fleischnerTwoMarkDangerousPairs G v) :
    P.card = 2 :=
  ((mem_fleischnerTwoMarkDangerousPairs G v P).mp hP).1

lemma pair_mem_fleischnerTwoMarkDangerousPairs_of_dangerousSet_all_incident_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} {e f : E} {S : Finset V}
    (hS : FleischnerDangerousSetForPair G v e f S)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f)
    (hreach : ∀ r : E, IsIncident G v r →
      (supportAwayFromVertex G v).Reachable
        (otherEndpoint G v e) (otherEndpoint G v r)) :
    ({e, f} : Finset E) ∈ fleischnerTwoMarkDangerousPairs G v := by
  classical
  have hinto :
      incidentEdgesInto G v S = ({e, f} : Finset E) :=
    hS.incidentEdgesInto_eq_pair_of_all_incident_reachable
      hconn hb hef he hf hreach
  have hSAt : S ∈ fleischnerDangerousSetsAt G v :=
    (mem_fleischnerDangerousSetsAt G v S).mpr
      ⟨e, f, hef, he, hf, hS⟩
  exact (mem_fleischnerTwoMarkDangerousPairs G v ({e, f})).mpr
    ⟨Finset.card_pair hef, S, hSAt, hinto⟩

lemma supportAway_reachable_of_all_incident_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v x y : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hxv : x ≠ v) (hyv : y ≠ v)
    (hreach : ∀ {e f : E}, IsIncident G v e → IsIncident G v f →
      (supportAwayFromVertex G v).Reachable
        (otherEndpoint G v e) (otherEndpoint G v f)) :
    (supportAwayFromVertex G v).Reachable x y := by
  obtain ⟨e, he, hex⟩ :=
    exists_incident_endpoint_supportAway_reaches G hconn hb hxv
  obtain ⟨f, hf, hfy⟩ :=
    exists_incident_endpoint_supportAway_reaches G hconn hb hyv
  exact hex.symm.trans ((hreach he hf).trans hfy)

lemma not_supportAway_delete_symEdge_reachable_of_cutAway_eq_singleton
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V} {x y : V}
    {e : E} (hvS : v ∉ S)
    (hcut : cutAwayFromVertex G v S = {e})
    (hxS : x ∈ S) (hyS : y ∉ S) :
    ¬ ((supportAwayFromVertex G v).deleteEdges {symEdge G e}).Reachable x y := by
  intro hxy
  have hwalk :
      ∃ p : (supportAwayFromVertex G v).Walk x y,
        symEdge G e ∉ p.edges := by
    simpa [symEdge] using
      (SimpleGraph.reachable_deleteEdges_iff_exists_walk
        (G := supportAwayFromVertex G v)
        (v := G.endAt e 0) (w := G.endAt e 1)
        (v' := x) (w' := y)).mp hxy
  rcases hwalk with ⟨p, hp⟩
  let p' : ((supportGraph G) (edgesAwayFromVertex G v)).Walk x y := by
    simpa [supportAwayFromVertex] using p
  have hp' : symEdge G e ∉ p'.edges := by
    simpa [p', supportAwayFromVertex] using hp
  obtain ⟨f, hfAway, hfPath, hfCross⟩ :=
    exists_crossing_edge_on_walk G
      (T := edgesAwayFromVertex G v)
      (S := S) (x := x) (y := y)
      p' hxS hyS
  have hfCut : f ∈ cutAwayFromVertex G v S := by
    exact (mem_cutAwayFromVertex_iff G hvS f).mpr
      ⟨hfCross, (mem_edgesAwayFromVertex_iff G v f).mp hfAway⟩
  have hfe : f = e := by
    have hfSingleton : f ∈ ({e} : Finset E) := by
      simpa [hcut] using hfCut
    exact Finset.mem_singleton.mp hfSingleton
  exact hp' (by simpa [hfe] using hfPath)

lemma supportAway_delete_symEdge_reachable_inside_of_cutAway_eq_singleton
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V} {x y : V}
    {e : E} (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hvS : v ∉ S) (hcut : cutAwayFromVertex G v S = {e})
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hreach : ∀ {a b : E}, IsIncident G v a → IsIncident G v b →
      (supportAwayFromVertex G v).Reachable
        (otherEndpoint G v a) (otherEndpoint G v b)) :
    ((supportAwayFromVertex G v).deleteEdges {symEdge G e}).Reachable x y := by
  have hxv : x ≠ v := by
    intro hxv
    exact hvS (hxv ▸ hxS)
  have hyv : y ≠ v := by
    intro hyv
    exact hvS (hyv ▸ hyS)
  have hxy :
      (supportAwayFromVertex G v).Reachable x y :=
    supportAway_reachable_of_all_incident_reachable G hconn hb hxv hyv hreach
  obtain ⟨p, hp⟩ := hxy.exists_isPath
  have heCut : e ∈ cutAwayFromVertex G v S := by
    rw [hcut]
    exact Finset.mem_singleton_self e
  have heCross : Crosses G S e :=
    ((mem_cutAwayFromVertex_iff G hvS e).mp heCut).1
  have hnoEdge : symEdge G e ∉ p.edges := by
    unfold Crosses at heCross
    by_cases h1S : G.endAt e 1 ∈ S
    · have h0S : G.endAt e 0 ∉ S := by
        intro h0S
        exact heCross (propext ⟨fun _ ↦ h1S, fun _ ↦ h0S⟩)
      have hxNot :
          ¬ ((supportAwayFromVertex G v).deleteEdges
              {symEdge G e}).Reachable x (G.endAt e 0) :=
        not_supportAway_delete_symEdge_reachable_of_cutAway_eq_singleton
          G hvS hcut hxS h0S
      have hyNot :
          ¬ ((supportAwayFromVertex G v).deleteEdges
              {symEdge G e}).Reachable y (G.endAt e 0) :=
        not_supportAway_delete_symEdge_reachable_of_cutAway_eq_singleton
          G hvS hcut hyS h0S
      have hno :
          s(G.endAt e 1, G.endAt e 0) ∉ p.edges :=
        hp.isTrail.not_mem_edges_of_not_reachable
          (x := G.endAt e 1) (y := G.endAt e 0)
          (by simpa [symEdge, Sym2.eq_swap] using hxNot)
          (by simpa [symEdge, Sym2.eq_swap] using hyNot)
      simpa [symEdge, Sym2.eq_swap] using hno
    · have h1not : G.endAt e 1 ∉ S := h1S
      have h0S : G.endAt e 0 ∈ S := by
        by_contra h0not
        exact heCross (propext
          ⟨fun h0 ↦ (h0not h0).elim, fun h1 ↦ (h1not h1).elim⟩)
      have hxNot :
          ¬ ((supportAwayFromVertex G v).deleteEdges
              {symEdge G e}).Reachable x (G.endAt e 1) :=
        not_supportAway_delete_symEdge_reachable_of_cutAway_eq_singleton
          G hvS hcut hxS h1not
      have hyNot :
          ¬ ((supportAwayFromVertex G v).deleteEdges
              {symEdge G e}).Reachable y (G.endAt e 1) :=
        not_supportAway_delete_symEdge_reachable_of_cutAway_eq_singleton
          G hvS hcut hyS h1not
      have hno :
          s(G.endAt e 0, G.endAt e 1) ∉ p.edges :=
        hp.isTrail.not_mem_edges_of_not_reachable
          (x := G.endAt e 0) (y := G.endAt e 1)
          (by simpa [symEdge] using hxNot)
          (by simpa [symEdge] using hyNot)
      simpa [symEdge] using hno
  simpa [symEdge] using
    (SimpleGraph.reachable_deleteEdges_iff_exists_walk
      (G := supportAwayFromVertex G v)
      (v := G.endAt e 0) (w := G.endAt e 1)
      (v' := x) (w' := y)).mpr ⟨p, by simpa [symEdge] using hnoEdge⟩

lemma SimpleGraph.reachable_deleteEdges_of_mem_support_of_not_mem_edges
    {V : Type*} {H : SimpleGraph V} {u v z : V} {e : Sym2 V}
    (p : H.Walk u v) (hp : e ∉ p.edges) (hz : z ∈ p.support) :
    (H.deleteEdges {e}).Reachable u z := by
  classical
  obtain ⟨a, b⟩ := e
  rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk]
  refine ⟨p.takeUntil z hz, ?_⟩
  intro he
  exact hp (p.edges_takeUntil_subset_edges hz he)

lemma cutAwayFromVertex_compl_delete_vertex_eq
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V}
    (hvS : v ∉ S) :
    cutAwayFromVertex G v (Finset.univ \ (S ∪ {v})) =
      cutAwayFromVertex G v S := by
  classical
  let T : Finset V := Finset.univ \ (S ∪ {v})
  have hvT : v ∉ T := by
    simp [T]
  ext e
  change e ∈ cutAwayFromVertex G v T ↔ e ∈ cutAwayFromVertex G v S
  rw [mem_cutAwayFromVertex_iff G hvT e,
    mem_cutAwayFromVertex_iff G hvS e]
  by_cases hinc : IsIncident G v e
  · simp [hinc]
  · have h0v : G.endAt e 0 ≠ v := by
      intro h0
      exact hinc (Or.inl h0)
    have h1v : G.endAt e 1 ≠ v := by
      intro h1
      exact hinc (Or.inr h1)
    by_cases h0S : G.endAt e 0 ∈ S <;>
      by_cases h1S : G.endAt e 1 ∈ S <;>
      simp [Crosses, T, hinc, h0v, h1v, h0S, h1S]

lemma supportAway_delete_symEdge_reachable_outside_of_cutAway_eq_singleton
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {S : Finset V} {x y : V}
    {e : E} (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hvS : v ∉ S) (hcut : cutAwayFromVertex G v S = {e})
    (hxS : x ∉ S) (hyS : y ∉ S) (hxv : x ≠ v) (hyv : y ≠ v)
    (hreach : ∀ {a b : E}, IsIncident G v a → IsIncident G v b →
      (supportAwayFromVertex G v).Reachable
        (otherEndpoint G v a) (otherEndpoint G v b)) :
    ((supportAwayFromVertex G v).deleteEdges {symEdge G e}).Reachable x y := by
  let T : Finset V := Finset.univ \ (S ∪ {v})
  have hvT : v ∉ T := by
    simp [T]
  have hcutT : cutAwayFromVertex G v T = {e} := by
    simpa [T, hcut] using
      cutAwayFromVertex_compl_delete_vertex_eq G hvS
  have hxT : x ∈ T := by
    simp [T, hxS, hxv]
  have hyT : y ∈ T := by
    simp [T, hyS, hyv]
  exact supportAway_delete_symEdge_reachable_inside_of_cutAway_eq_singleton
    G hconn hb hvT hcutT hxT hyT hreach

lemma crossing_singleton_cutAway_contradiction
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V}
    {a b : E} {x y z w : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hreach : ∀ {e f : E}, IsIncident G v e → IsIncident G v f →
      (supportAwayFromVertex G v).Reachable
        (otherEndpoint G v e) (otherEndpoint G v f))
    (hvA : v ∉ A) (hvB : v ∉ B)
    (hcutA : cutAwayFromVertex G v A = {a})
    (hcutB : cutAwayFromVertex G v B = {b})
    (hxA : x ∈ A) (hxB : x ∈ B)
    (hyA : y ∈ A) (hyB : y ∉ B)
    (hzA : z ∉ A) (hzB : z ∈ B)
    (hwA : w ∉ A) (hwB : w ∉ B) (hwv : w ≠ v) :
    False := by
  let H := supportAwayFromVertex G v
  have hzv : z ≠ v := by
    intro hzv
    exact hvB (hzv ▸ hzB)
  have hxyDelA :
      (H.deleteEdges {symEdge G a}).Reachable x y :=
    supportAway_delete_symEdge_reachable_inside_of_cutAway_eq_singleton
      G hconn hb hvA hcutA hxA hyA hreach
  have hzwDelA :
      (H.deleteEdges {symEdge G a}).Reachable z w :=
    supportAway_delete_symEdge_reachable_outside_of_cutAway_eq_singleton
      G hconn hb hvA hcutA hzA hwA hzv hwv hreach
  have hxzNotDelA :
      ¬ (H.deleteEdges {symEdge G a}).Reachable x z :=
    not_supportAway_delete_symEdge_reachable_of_cutAway_eq_singleton
      G hvA hcutA hxA hzA
  have hxyNotDelB :
      ¬ (H.deleteEdges {symEdge G b}).Reachable x y :=
    not_supportAway_delete_symEdge_reachable_of_cutAway_eq_singleton
      G hvB hcutB hxB hyB
  have hzwNotDelB :
      ¬ (H.deleteEdges {symEdge G b}).Reachable z w :=
    not_supportAway_delete_symEdge_reachable_of_cutAway_eq_singleton
      G hvB hcutB hzB hwB
  have hwalkXY :
      ∃ P : H.Walk x y, symEdge G a ∉ P.edges := by
    simpa [H, symEdge] using
      (SimpleGraph.reachable_deleteEdges_iff_exists_walk
        (G := H) (v := G.endAt a 0) (w := G.endAt a 1)
        (v' := x) (w' := y)).mp hxyDelA
  rcases hwalkXY with ⟨Pxy, hPxyA⟩
  have hbXYs : s(G.endAt b 0, G.endAt b 1) ∈ Pxy.edges := by
    simpa [H, symEdge] using
      Pxy.mem_edges_of_not_reachable_deleteEdges
        (by simpa [H, symEdge] using hxyNotDelB)
  have hb0XY : G.endAt b 0 ∈ Pxy.support :=
    Pxy.fst_mem_support_of_mem_edges hbXYs
  have hx_b0 :
      (H.deleteEdges {symEdge G a}).Reachable x (G.endAt b 0) :=
    SimpleGraph.reachable_deleteEdges_of_mem_support_of_not_mem_edges
      Pxy hPxyA hb0XY
  have hwalkZW :
      ∃ P : H.Walk z w, symEdge G a ∉ P.edges := by
    simpa [H, symEdge] using
      (SimpleGraph.reachable_deleteEdges_iff_exists_walk
        (G := H) (v := G.endAt a 0) (w := G.endAt a 1)
        (v' := z) (w' := w)).mp hzwDelA
  rcases hwalkZW with ⟨Pzw, hPzwA⟩
  have hbZWs : s(G.endAt b 0, G.endAt b 1) ∈ Pzw.edges := by
    simpa [H, symEdge] using
      Pzw.mem_edges_of_not_reachable_deleteEdges
        (by simpa [H, symEdge] using hzwNotDelB)
  have hb0ZW : G.endAt b 0 ∈ Pzw.support :=
    Pzw.fst_mem_support_of_mem_edges hbZWs
  have hz_b0 :
      (H.deleteEdges {symEdge G a}).Reachable z (G.endAt b 0) :=
    SimpleGraph.reachable_deleteEdges_of_mem_support_of_not_mem_edges
      Pzw hPzwA hb0ZW
  exact hxzNotDelA (hx_b0.trans hz_b0.symm)

lemma dangerousSets_common_left_contradiction_of_fourth_incident
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {A B : Finset V}
    {p q r s : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hreach : ∀ {e f : E}, IsIncident G v e → IsIncident G v f →
      (supportAwayFromVertex G v).Reachable
        (otherEndpoint G v e) (otherEndpoint G v f))
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hp : IsIncident G v p) (hq : IsIncident G v q)
    (hr : IsIncident G v r) (hs : IsIncident G v s)
    (hA : FleischnerDangerousSetForPair G v p q A)
    (hB : FleischnerDangerousSetForPair G v p r B) :
    False := by
  have hAinto :
      incidentEdgesInto G v A = ({p, q} : Finset E) :=
    hA.incidentEdgesInto_eq_pair_of_all_incident_reachable
      hconn hb hpq hp hq (fun t ht ↦ hreach hp ht)
  have hBinto :
      incidentEdgesInto G v B = ({p, r} : Finset E) :=
    hB.incidentEdgesInto_eq_pair_of_all_incident_reachable
      hconn hb hpr hp hr (fun t ht ↦ hreach hp ht)
  have hqB : otherEndpoint G v q ∉ B := by
    intro hqB
    have hqIn : q ∈ incidentEdgesInto G v B :=
      (mem_incidentEdgesInto G v B q).mpr ⟨hq, hqB⟩
    rw [hBinto] at hqIn
    rw [Finset.mem_insert, Finset.mem_singleton] at hqIn
    rcases hqIn with hqp | hqr'
    · exact hpq hqp.symm
    · exact hqr hqr'
  have hrA : otherEndpoint G v r ∉ A := by
    intro hrA
    have hrIn : r ∈ incidentEdgesInto G v A :=
      (mem_incidentEdgesInto G v A r).mpr ⟨hr, hrA⟩
    rw [hAinto] at hrIn
    rw [Finset.mem_insert, Finset.mem_singleton] at hrIn
    rcases hrIn with hrp | hrq
    · exact hpr hrp.symm
    · exact hqr hrq.symm
  have hsA : otherEndpoint G v s ∉ A := by
    intro hsA
    have hsIn : s ∈ incidentEdgesInto G v A :=
      (mem_incidentEdgesInto G v A s).mpr ⟨hs, hsA⟩
    rw [hAinto] at hsIn
    rw [Finset.mem_insert, Finset.mem_singleton] at hsIn
    rcases hsIn with hsp | hsq
    · exact hps hsp.symm
    · exact hqs hsq.symm
  have hsB : otherEndpoint G v s ∉ B := by
    intro hsB
    have hsIn : s ∈ incidentEdgesInto G v B :=
      (mem_incidentEdgesInto G v B s).mpr ⟨hs, hsB⟩
    rw [hBinto] at hsIn
    rw [Finset.mem_insert, Finset.mem_singleton] at hsIn
    rcases hsIn with hsp | hsr
    · exact hps hsp.symm
    · exact hrs hsr.symm
  obtain ⟨a, hcutA⟩ :=
    Finset.card_eq_one.mp
      (hA.cutAway_card_eq_one_of_all_incident_reachable
        hconn hb hpq hp hq (fun t ht ↦ hreach hp ht))
  obtain ⟨b, hcutB⟩ :=
    Finset.card_eq_one.mp
      (hB.cutAway_card_eq_one_of_all_incident_reachable
        hconn hb hpr hp hr (fun t ht ↦ hreach hp ht))
  exact crossing_singleton_cutAway_contradiction G hconn hb hreach
    hA.vertex_not_mem hB.vertex_not_mem hcutA hcutB
    hA.left_otherEndpoint_mem hB.left_otherEndpoint_mem
    hA.right_otherEndpoint_mem hqB
    hrA hB.right_otherEndpoint_mem
    hsA hsB (otherEndpoint_ne_of_incident G hs)

lemma fleischnerTwoMarkDangerousPairs_pairwise_disjoint_of_all_incident_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v)
    (hreach : ∀ {e f : E}, IsIncident G v e → IsIncident G v f →
      (supportAwayFromVertex G v).Reachable
        (otherEndpoint G v e) (otherEndpoint G v f)) :
    ∀ ⦃P Q : Finset E⦄,
      P ∈ fleischnerTwoMarkDangerousPairs G v →
      Q ∈ fleischnerTwoMarkDangerousPairs G v → P ≠ Q → Disjoint P Q := by
  intro P Q hP hQ hPQ
  rw [Finset.disjoint_left]
  intro p hpP hpQ
  rcases (mem_fleischnerTwoMarkDangerousPairs G v P).mp hP with
    ⟨hPcard, S, hSAt, hSinto⟩
  rcases (mem_fleischnerTwoMarkDangerousPairs G v Q).mp hQ with
    ⟨hQcard, T, hTAt, hTinto⟩
  have hPeraseCard : (P.erase p).card = 1 := by
    have hpCard := Finset.card_erase_add_one hpP
    omega
  have hQeraseCard : (Q.erase p).card = 1 := by
    have hpCard := Finset.card_erase_add_one hpQ
    omega
  obtain ⟨q, hPerase⟩ := Finset.card_eq_one.mp hPeraseCard
  obtain ⟨r, hQerase⟩ := Finset.card_eq_one.mp hQeraseCard
  have hqErase : q ∈ P.erase p := by
    rw [hPerase]
    exact Finset.mem_singleton_self q
  have hrErase : r ∈ Q.erase p := by
    rw [hQerase]
    exact Finset.mem_singleton_self r
  have hpq : p ≠ q := (Finset.mem_erase.mp hqErase).1.symm
  have hpr : p ≠ r := (Finset.mem_erase.mp hrErase).1.symm
  have hqP : q ∈ P := (Finset.mem_erase.mp hqErase).2
  have hrQ : r ∈ Q := (Finset.mem_erase.mp hrErase).2
  have hPeq : P = ({p, q} : Finset E) := by
    rw [← Finset.insert_erase hpP, hPerase]
  have hQeq : Q = ({p, r} : Finset E) := by
    rw [← Finset.insert_erase hpQ, hQerase]
  have hqr : q ≠ r := by
    intro hqr
    exact hPQ (by rw [hPeq, hQeq, hqr])
  have hpSIn : p ∈ incidentEdgesInto G v S := by
    rw [hSinto]
    exact hpP
  have hqSIn : q ∈ incidentEdgesInto G v S := by
    rw [hSinto]
    exact hqP
  have hpTIn : p ∈ incidentEdgesInto G v T := by
    rw [hTinto]
    exact hpQ
  have hrTIn : r ∈ incidentEdgesInto G v T := by
    rw [hTinto]
    exact hrQ
  rcases (mem_incidentEdgesInto G v S p).mp hpSIn with ⟨hp, hpS⟩
  rcases (mem_incidentEdgesInto G v S q).mp hqSIn with ⟨hq, hqS⟩
  rcases (mem_incidentEdgesInto G v T p).mp hpTIn with ⟨_hpT, hpT⟩
  rcases (mem_incidentEdgesInto G v T r).mp hrTIn with ⟨hr, hrT⟩
  rcases (mem_fleischnerDangerousSetsAt G v S).mp hSAt with
    ⟨eS, fS, _heSfS, _heS, _hfS, hSdanger⟩
  rcases (mem_fleischnerDangerousSetsAt G v T).mp hTAt with
    ⟨eT, fT, _heTfT, _heT, _hfT, hTdanger⟩
  have hSpq : FleischnerDangerousSetForPair G v p q S :=
    hSdanger.weak.to_dangerousSetForPair
      hSdanger.vertex_not_mem hpS hqS
  have hTpr : FleischnerDangerousSetForPair G v p r T :=
    hTdanger.weak.to_dangerousSetForPair
      hTdanger.vertex_not_mem hpT hrT
  obtain ⟨s, hsp, hsq, hsr, hs⟩ :=
    exists_remaining_incident_edge_of_degree_ge_four_three
      G hdeg hpq hpr hqr hp hq hr
  exact dangerousSets_common_left_contradiction_of_fourth_incident
    G hconn hb hreach hpq hpr (fun h ↦ hsp h.symm) hqr
    (fun h ↦ hsq h.symm) (fun h ↦ hsr h.symm) hp hq hr hs hSpq hTpr

lemma not_fleischnerDangerousSetForPair_of_not_supportAway_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E} {S : Finset V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f)
    (hxy : ¬ (supportAwayFromVertex G v).Reachable
      (otherEndpoint G v e) (otherEndpoint G v f))
    (hS : FleischnerDangerousSetForPair G v e f S) :
    False := by
  obtain ⟨g, hge, hg, hgC⟩ :=
    exists_other_incident_edge_into_supportAwayComponent G hconn hb he
  obtain ⟨k, hkf, hk, hkC⟩ :=
    exists_other_incident_edge_into_supportAwayComponent G hconn hb hf
  have hxg :
      (supportAwayFromVertex G v).Reachable
        (otherEndpoint G v e) (otherEndpoint G v g) :=
    (mem_supportAwayComponent G v (otherEndpoint G v e)
      (otherEndpoint G v g)).mp hgC
  have hyk :
      (supportAwayFromVertex G v).Reachable
        (otherEndpoint G v f) (otherEndpoint G v k) :=
    (mem_supportAwayComponent G v (otherEndpoint G v f)
      (otherEndpoint G v k)).mp hkC
  have hgf : g ≠ f := by
    intro h
    exact hxy (by simpa [h] using hxg)
  have hke : k ≠ e := by
    intro h
    exact hxy (by simpa [h] using hyk.symm)
  have hgk : g ≠ k := by
    intro h
    subst k
    exact hxy (hxg.trans hyk.symm)
  by_cases hgS : otherEndpoint G v g ∈ S
  · by_cases hkS : otherEndpoint G v k ∈ S
    · exact no_dangerousSet_contains_four_incident_otherEndpoints G hS
        he hf hg hk hS.left_otherEndpoint_mem hS.right_otherEndpoint_mem
        hgS hkS hef (fun h ↦ hge h.symm) (fun h ↦ hke h.symm)
        hgf.symm hkf.symm hgk
    · have hzero :
          (cutAwayFromVertex G v S).card = 0 :=
        hS.cutAwayFromVertex_card_eq_zero_of_three
          he hf hg hS.left_otherEndpoint_mem hS.right_otherEndpoint_mem
          hgS hef (fun h ↦ hge h.symm) hgf.symm
      have hempty : cutAwayFromVertex G v S = ∅ :=
        Finset.card_eq_zero.mp hzero
      have hnonempty :
          (cutAwayFromVertex G v S).Nonempty :=
        cutAwayFromVertex_nonempty_of_supportAway_reachable_crossing
          G hS.vertex_not_mem hyk hS.right_otherEndpoint_mem hkS
      rw [hempty] at hnonempty
      simp at hnonempty
  · by_cases hkS : otherEndpoint G v k ∈ S
    · have hzero :
          (cutAwayFromVertex G v S).card = 0 :=
        hS.cutAwayFromVertex_card_eq_zero_of_three
          he hf hk hS.left_otherEndpoint_mem hS.right_otherEndpoint_mem
          hkS hef (fun h ↦ hke h.symm) hkf.symm
      have hempty : cutAwayFromVertex G v S = ∅ :=
        Finset.card_eq_zero.mp hzero
      have hnonempty :
          (cutAwayFromVertex G v S).Nonempty :=
        cutAwayFromVertex_nonempty_of_supportAway_reachable_crossing
          G hS.vertex_not_mem hxg hS.left_otherEndpoint_mem hgS
      rw [hempty] at hnonempty
      simp at hnonempty
    · have htwo :
          2 ≤ (cutAwayFromVertex G v S).card :=
        two_le_cutAwayFromVertex_card_of_two_supportAway_crossings
          G hS.vertex_not_mem hxg hyk hxy hS.left_otherEndpoint_mem
          hgS hS.right_otherEndpoint_mem hkS
      have hone :
          (cutAwayFromVertex G v S).card ≤ 1 :=
        hS.cutAwayFromVertex_card_le_one hef he hf
      omega

lemma isFleischnerAdmissibleSplitWithLoops_of_not_supportAway_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f : E}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f)
    (hxy : ¬ (supportAwayFromVertex G v).Reachable
      (otherEndpoint G v e) (otherEndpoint G v f)) :
    IsFleischnerAdmissibleSplitWithLoops G v e f := by
  rw [isFleischnerAdmissibleSplitWithLoops_iff_no_dangerousSetForPair
    G hconn hb hef he hf]
  intro S hS
  exact not_fleischnerDangerousSetForPair_of_not_supportAway_reachable
    G hconn hb hef he hf hxy hS

theorem exists_fleischner_admissible_local_pair_of_not_supportAway_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v) {e f : E}
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f)
    (hxy : ¬ (supportAwayFromVertex G v).Reachable
      (otherEndpoint G v e) (otherEndpoint G v f)) :
    ∃ e f g k : E,
      e ≠ f ∧ IsIncident G v e ∧ IsIncident G v f ∧
      (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
      IsIncident G v g ∧ IsIncident G v k ∧
      IsFleischnerAdmissibleSplitWithLoops G v e f := by
  obtain ⟨g, k, hg, hk, hgk, hgv, hkv⟩ :=
    exists_two_remaining_incident_edges_of_degree_ge_four G hdeg hef he hf
  exact ⟨e, f, g, k, hef, he, hf, hg, hk, hgk, hgv, hkv,
    isFleischnerAdmissibleSplitWithLoops_of_not_supportAway_reachable
      G hconn hb hef he hf hxy⟩

theorem exists_fleischner_admissible_local_pair_of_pairwise_disjoint_twoMarkDangerousPairs
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v)
    (hreach : ∀ {e f : E}, IsIncident G v e → IsIncident G v f →
      (supportAwayFromVertex G v).Reachable
        (otherEndpoint G v e) (otherEndpoint G v f))
    (hdisj : ∀ ⦃A B : Finset E⦄,
      A ∈ fleischnerTwoMarkDangerousPairs G v →
      B ∈ fleischnerTwoMarkDangerousPairs G v → A ≠ B → Disjoint A B) :
    ∃ e f g k : E,
      e ≠ f ∧ IsIncident G v e ∧ IsIncident G v f ∧
      (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
      IsIncident G v g ∧ IsIncident G v k ∧
      IsFleischnerAdmissibleSplitWithLoops G v e f := by
  classical
  let F := incidentEdgesAt G v
  have hFcard : 4 ≤ F.card := by
    simpa [F, degree_eq_incidentEdgesAt_card G v] using hdeg
  obtain ⟨e, f, heF, hfF, hef, hnotSub⟩ :=
    Finset.exists_pair_not_subset_pairwise_disjoint_pairs_of_four_le_card
      (F := F) hFcard
      (𝒜 := fleischnerTwoMarkDangerousPairs G v)
      (fun P hP ↦ fleischnerTwoMarkDangerousPairs_card_eq_two G hP)
      (fun {A B} hA hB hne ↦ hdisj (A := A) (B := B) hA hB hne)
  have he : IsIncident G v e := (mem_incidentEdgesAt G v e).mp heF
  have hf : IsIncident G v f := (mem_incidentEdgesAt G v f).mp hfF
  obtain ⟨g, k, hg, hk, hgk, hgv, hkv⟩ :=
    exists_two_remaining_incident_edges_of_degree_ge_four G hdeg hef he hf
  have hadm : IsFleischnerAdmissibleSplitWithLoops G v e f := by
    rw [isFleischnerAdmissibleSplitWithLoops_iff_no_dangerousSetForPair
      G hconn hb hef he hf]
    intro S hS
    have hpair :
        ({e, f} : Finset E) ∈ fleischnerTwoMarkDangerousPairs G v :=
      pair_mem_fleischnerTwoMarkDangerousPairs_of_dangerousSet_all_incident_reachable
        hS hconn hb hef he hf (fun r hr ↦ hreach he hr)
    exact hnotSub ({e, f} : Finset E) hpair (by intro x hx; exact hx)
  exact ⟨e, f, g, k, hef, he, hf, hg, hk, hgk, hgv, hkv, hadm⟩

theorem exists_fleischner_admissible_local_pair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v) :
    ∃ e f g k : E,
      e ≠ f ∧ IsIncident G v e ∧ IsIncident G v f ∧
      (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
      IsIncident G v g ∧ IsIncident G v k ∧
      IsFleischnerAdmissibleSplitWithLoops G v e f := by
  by_cases hreach :
      ∀ e f : E, IsIncident G v e → IsIncident G v f →
        (supportAwayFromVertex G v).Reachable
          (otherEndpoint G v e) (otherEndpoint G v f)
  · exact
      exists_fleischner_admissible_local_pair_of_pairwise_disjoint_twoMarkDangerousPairs
        G hconn hb hdeg
        (fun {e f} he hf ↦ hreach e f he hf)
        (fleischnerTwoMarkDangerousPairs_pairwise_disjoint_of_all_incident_reachable
          G hconn hb hdeg (fun {e f} he hf ↦ hreach e f he hf))
  · push Not at hreach
    rcases hreach with ⟨e, f, he, hf, hefReach⟩
    have hef : e ≠ f := by
      intro hef
      subst f
      exact hefReach (SimpleGraph.Reachable.refl _)
    exact exists_fleischner_admissible_local_pair_of_not_supportAway_reachable
      G hconn hb hdeg hef he hf hefReach

theorem exists_fleischner_admissible_nonloop_local_pair_of_no_parallel_at_vertex
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v)
    (hparallel : ∀ {e f : E}, e ≠ f → IsIncident G v e → IsIncident G v f →
      otherEndpoint G v e ≠ otherEndpoint G v f) :
    ∃ e f g k : E,
      e ≠ f ∧ IsIncident G v e ∧ IsIncident G v f ∧
      (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
      IsIncident G v g ∧ IsIncident G v k ∧
      otherEndpoint G v e ≠ otherEndpoint G v f ∧
      IsFleischnerAdmissibleSplitWithLoops G v e f := by
  obtain ⟨e, f, g, k, hef, he, hf, hg, hk, hgk, hgv, hkv, hadm⟩ :=
    exists_fleischner_admissible_local_pair G hconn hb hdeg
  exact ⟨e, f, g, k, hef, he, hf, hg, hk, hgk, hgv, hkv,
    hparallel hef he hf, hadm⟩

lemma splitOffWithLoops_old_mem_cut_of_incident_side_ne
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f g : E}
    (hg : g ≠ e ∧ g ≠ f) (hgv : IsIncident G v g) {S : Finset V}
    (hside : (v ∈ S) ≠ (otherEndpoint G v g ∈ S)) :
    splitOldEdge g hg ∈ (splitOffWithLoops G v e f).cut S := by
  have hcrossG : Crosses G S g :=
    (crosses_iff_incident_otherEndpoint G hgv S).mpr hside
  have hcrossH :
      (splitOffWithLoops G v e f).Crosses S (splitOldEdge g hg) := by
    simpa [OrientedPseudograph.Crosses, Crosses, splitOffWithLoops,
      splitOldEdge] using hcrossG
  simpa [OrientedPseudograph.cut] using hcrossH

lemma two_le_splitOffWithLoops_cut_card_of_two_remaining
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} {e f g k : E}
    (hg : g ≠ e ∧ g ≠ f) (hk : k ≠ e ∧ k ≠ f) (hgk : g ≠ k)
    (hgv : IsIncident G v g) (hkv : IsIncident G v k) {S : Finset V}
    (hgside : (v ∈ S) ≠ (otherEndpoint G v g ∈ S))
    (hkside : (v ∈ S) ≠ (otherEndpoint G v k ∈ S)) :
    2 ≤ ((splitOffWithLoops G v e f).cut S).card := by
  have heg : splitOldEdge g hg ∈ (splitOffWithLoops G v e f).cut S := by
    exact splitOffWithLoops_old_mem_cut_of_incident_side_ne G hg hgv hgside
  have hek : splitOldEdge k hk ∈ (splitOffWithLoops G v e f).cut S := by
    exact splitOffWithLoops_old_mem_cut_of_incident_side_ne G hk hkv hkside
  have hegk : splitOldEdge g hg ≠ splitOldEdge k hk := by
    intro h
    apply hgk
    simpa [splitOldEdge] using congrArg
      (fun x : SplitEdge E e f =>
        match x with
        | Sum.inl y => y.1
        | Sum.inr _ => g) h
  have hpair :
      ({splitOldEdge g hg, splitOldEdge k hk} : Finset (SplitEdge E e f)) ⊆
        (splitOffWithLoops G v e f).cut S := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact heg
    · exact hek
  have hcard := Finset.card_le_card hpair
  have hpairCard :
      ({splitOldEdge g hg, splitOldEdge k hk} : Finset (SplitEdge E e f)).card = 2 :=
    Finset.card_pair hegk
  rwa [hpairCard] at hcard

lemma IsFleischnerAdmissibleSplitWithLoops.bridgeless
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : OrientedMultigraph V E} {v : V} {e f : E}
    (h : IsFleischnerAdmissibleSplitWithLoops G v e f)
    (hrem : ∃ g k : E,
      (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
        IsIncident G v g ∧ IsIncident G v k) :
    (splitOffWithLoops G v e f).Bridgeless := by
  classical
  intro S hcard
  by_cases hinside : ∃ x ∈ S, x ≠ v
  · by_cases houtside : ∃ y : V, y ∉ S ∧ y ≠ v
    · have htwo := h S hinside houtside
      omega
    · obtain ⟨g, k, hg, hk, hgk, hgv, hkv⟩ := hrem
      have hcutNonempty : ((splitOffWithLoops G v e f).cut S).Nonempty := by
        exact Finset.card_pos.mp (by omega)
      have hvnot : v ∉ S := by
        intro hvS
        obtain ⟨a, ha⟩ := hcutNonempty
        have hcross : (splitOffWithLoops G v e f).Crosses S a := by
          simpa [OrientedPseudograph.cut] using ha
        unfold OrientedPseudograph.Crosses at hcross
        by_cases h0 : (splitOffWithLoops G v e f).endAt a 0 ∈ S
        · have h1 : (splitOffWithLoops G v e f).endAt a 1 ∉ S := by
            intro h1
            exact hcross (propext ⟨fun _ ↦ h1, fun _ ↦ h0⟩)
          have h1v : (splitOffWithLoops G v e f).endAt a 1 = v := by
            by_contra hne
            exact houtside ⟨(splitOffWithLoops G v e f).endAt a 1, h1, hne⟩
          exact h1 (by simpa [h1v] using hvS)
        · have h0v : (splitOffWithLoops G v e f).endAt a 0 = v := by
            by_contra hne
            exact houtside ⟨(splitOffWithLoops G v e f).endAt a 0, h0, hne⟩
          exact h0 (by simpa [h0v] using hvS)
      have hgOther : otherEndpoint G v g ∈ S := by
        by_contra hgS
        exact houtside ⟨otherEndpoint G v g, hgS, otherEndpoint_ne_of_incident G hgv⟩
      have hkOther : otherEndpoint G v k ∈ S := by
        by_contra hkS
        exact houtside ⟨otherEndpoint G v k, hkS, otherEndpoint_ne_of_incident G hkv⟩
      have hgside : (v ∈ S) ≠ (otherEndpoint G v g ∈ S) := by
        intro hiff
        exact hvnot (hiff.mpr hgOther)
      have hkside : (v ∈ S) ≠ (otherEndpoint G v k ∈ S) := by
        intro hiff
        exact hvnot (hiff.mpr hkOther)
      have htwo := two_le_splitOffWithLoops_cut_card_of_two_remaining G
        hg hk hgk hgv hkv hgside hkside
      omega
  · obtain ⟨g, k, hg, hk, hgk, hgv, hkv⟩ := hrem
    have hcutNonempty : ((splitOffWithLoops G v e f).cut S).Nonempty := by
      exact Finset.card_pos.mp (by omega)
    have hvS : v ∈ S := by
      by_contra hvS
      obtain ⟨a, ha⟩ := hcutNonempty
      have hcross : (splitOffWithLoops G v e f).Crosses S a := by
        simpa [OrientedPseudograph.cut] using ha
      unfold OrientedPseudograph.Crosses at hcross
      by_cases h0 : (splitOffWithLoops G v e f).endAt a 0 ∈ S
      · have h0v : (splitOffWithLoops G v e f).endAt a 0 = v := by
          by_contra hne
          exact hinside ⟨(splitOffWithLoops G v e f).endAt a 0, h0, hne⟩
        exact hvS (by simpa [h0v] using h0)
      · have h1 : (splitOffWithLoops G v e f).endAt a 1 ∈ S := by
          by_contra h1
          exact hcross (propext ⟨fun h ↦ (h0 h).elim, fun h ↦ (h1 h).elim⟩)
        have h1v : (splitOffWithLoops G v e f).endAt a 1 = v := by
          by_contra hne
          exact hinside ⟨(splitOffWithLoops G v e f).endAt a 1, h1, hne⟩
        exact hvS (by simpa [h1v] using h1)
    have hgOther : otherEndpoint G v g ∉ S := by
      intro hgS
      exact hinside ⟨otherEndpoint G v g, hgS, otherEndpoint_ne_of_incident G hgv⟩
    have hkOther : otherEndpoint G v k ∉ S := by
      intro hkS
      exact hinside ⟨otherEndpoint G v k, hkS, otherEndpoint_ne_of_incident G hkv⟩
    have hgside : (v ∈ S) ≠ (otherEndpoint G v g ∈ S) := by
      intro hiff
      exact hgOther (hiff.mp hvS)
    have hkside : (v ∈ S) ≠ (otherEndpoint G v k ∈ S) := by
      intro hiff
      exact hkOther (hiff.mp hvS)
    have htwo := two_le_splitOffWithLoops_cut_card_of_two_remaining G
      hg hk hgk hgv hkv hgside hkside
    omega

theorem exists_fleischner_admissible_local_pair_of_maximal_uncrossing
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v)
    (huncross : ∀ {A B : Finset V} {e r : E},
      A ∈ fleischnerDangerousSetsAt G v →
      (∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card) →
      FleischnerDangerousSetForPair G v e r B →
      e ≠ r → IsIncident G v e → IsIncident G v r →
      otherEndpoint G v e ∈ A → otherEndpoint G v r ∉ A → False) :
    ∃ e f g k : E,
      e ≠ f ∧ IsIncident G v e ∧ IsIncident G v f ∧
      (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
      IsIncident G v g ∧ IsIncident G v k ∧
      IsFleischnerAdmissibleSplitWithLoops G v e f := by
  by_contra hno
  obtain ⟨A, hA_mem, hAmax⟩ :=
    exists_maximal_fleischnerDangerousSetAt_of_no_local_pair
      G hconn hb hdeg hno
  rcases (mem_fleischnerDangerousSetsAt G v A).mp hA_mem with
    ⟨p, q, hpq, hp, hq, hA⟩
  obtain ⟨r, hr, hrA⟩ :=
    exists_incident_otherEndpoint_not_mem_of_dangerousSet_of_degree_ge_four
      G hA hdeg
  have hpr : p ≠ r := by
    intro h
    exact hrA (by simpa [h] using hA.left_otherEndpoint_mem)
  have hbad : ¬ IsFleischnerAdmissibleSplitWithLoops G v p r := by
    intro hadm
    obtain ⟨g, k, hg, hk, hgk, hgv, hkv⟩ :=
      exists_two_remaining_incident_edges_of_degree_ge_four
        G hdeg hpr hp hr
    apply hno
    exact ⟨p, r, g, k, hpr, hp, hr, hg, hk, hgk, hgv, hkv, hadm⟩
  obtain ⟨B, hB⟩ :=
    exists_fleischnerDangerousSetForPair_of_not_admissible
      G hconn hb hp hr hbad
  exact huncross hA_mem hAmax hB hpr hp hr
    hA.left_otherEndpoint_mem hrA

theorem exists_fleischner_admissible_local_pair_of_pair_minimal_uncrossing
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v)
    (huncross : ∀ {A B : Finset V} {e r : E},
      A ∈ fleischnerDangerousSetsAt G v →
      (∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card) →
      B ∈ fleischnerDangerousSetsForPair G v e r →
      (∀ T ∈ fleischnerDangerousSetsForPair G v e r,
        (A ∩ B).card ≤ (A ∩ T).card) →
      e ≠ r → IsIncident G v e → IsIncident G v r →
      otherEndpoint G v e ∈ A → otherEndpoint G v r ∉ A → False) :
    ∃ e f g k : E,
      e ≠ f ∧ IsIncident G v e ∧ IsIncident G v f ∧
      (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
      IsIncident G v g ∧ IsIncident G v k ∧
      IsFleischnerAdmissibleSplitWithLoops G v e f := by
  by_contra hno
  obtain ⟨A, hA_mem, hAmax⟩ :=
    exists_maximal_fleischnerDangerousSetAt_of_no_local_pair
      G hconn hb hdeg hno
  rcases (mem_fleischnerDangerousSetsAt G v A).mp hA_mem with
    ⟨p, q, hpq, hp, hq, hA⟩
  obtain ⟨r, hr, hrA⟩ :=
    exists_incident_otherEndpoint_not_mem_of_dangerousSet_of_degree_ge_four
      G hA hdeg
  have hpr : p ≠ r := by
    intro h
    exact hrA (by simpa [h] using hA.left_otherEndpoint_mem)
  have hbad : ¬ IsFleischnerAdmissibleSplitWithLoops G v p r := by
    intro hadm
    obtain ⟨g, k, hg, hk, hgk, hgv, hkv⟩ :=
      exists_two_remaining_incident_edges_of_degree_ge_four
        G hdeg hpr hp hr
    apply hno
    exact ⟨p, r, g, k, hpr, hp, hr, hg, hk, hgk, hgv, hkv, hadm⟩
  obtain ⟨B, hB_mem, hBmin⟩ :=
    exists_minimal_inter_dangerousSetForPair_of_not_admissible
      G A hconn hb hpr hp hr hbad
  exact huncross hA_mem hAmax hB_mem hBmin hpr hp hr
    hA.left_otherEndpoint_mem hrA

theorem exists_fleischner_admissible_local_pair_of_weak_minimal_uncrossing
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v)
    (huncross : ∀ {A B : Finset V} {e r : E},
      A ∈ fleischnerDangerousSetsAt G v →
      (∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card) →
      B ∈ weakFleischnerDangerousSetsContainingEndpoint G v r →
      (∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
        (A ∩ B).card ≤ (A ∩ T).card) →
      e ≠ r → IsIncident G v e → IsIncident G v r →
      otherEndpoint G v e ∈ A → otherEndpoint G v r ∉ A → False) :
    ∃ e f g k : E,
      e ≠ f ∧ IsIncident G v e ∧ IsIncident G v f ∧
      (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
      IsIncident G v g ∧ IsIncident G v k ∧
      IsFleischnerAdmissibleSplitWithLoops G v e f := by
  by_contra hno
  obtain ⟨A, hA_mem, hAmax⟩ :=
    exists_maximal_fleischnerDangerousSetAt_of_no_local_pair
      G hconn hb hdeg hno
  rcases (mem_fleischnerDangerousSetsAt G v A).mp hA_mem with
    ⟨p, q, hpq, hp, hq, hA⟩
  obtain ⟨r, hr, hrA⟩ :=
    exists_incident_otherEndpoint_not_mem_of_dangerousSet_of_degree_ge_four
      G hA hdeg
  have hpr : p ≠ r := by
    intro h
    exact hrA (by simpa [h] using hA.left_otherEndpoint_mem)
  have hbad : ¬ IsFleischnerAdmissibleSplitWithLoops G v p r := by
    intro hadm
    obtain ⟨g, k, hg, hk, hgk, hgv, hkv⟩ :=
      exists_two_remaining_incident_edges_of_degree_ge_four
        G hdeg hpr hp hr
    apply hno
    exact ⟨p, r, g, k, hpr, hp, hr, hg, hk, hgk, hgv, hkv, hadm⟩
  obtain ⟨B, hB_mem, hBmin⟩ :=
    exists_minimal_inter_weakFleischnerDangerousSetContainingEndpoint_of_not_admissible
      G A hconn hb hp hr hbad
  exact huncross hA_mem hAmax hB_mem hBmin hpr hp hr
    hA.left_otherEndpoint_mem hrA

theorem fleischner_splitting_lemma_of_local_pair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} (hconn : Connects G Finset.univ)
    (hpair : ∃ e f g k : E,
      e ≠ f ∧ IsIncident G v e ∧ IsIncident G v f ∧
      (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
      IsIncident G v g ∧ IsIncident G v k ∧
      IsFleischnerAdmissibleSplitWithLoops G v e f) :
    ∃ S : ReducingSplitWithLoops G v,
      S.graph.Connects Finset.univ ∧ S.graph.Bridgeless := by
  rcases hpair with
    ⟨e, f, g, k, hef, hev, hfv, hg, hk, hgk, hgv, hkv, hlocal⟩
  let S : ReducingSplitWithLoops G v :=
    { left := e
      right := f
      distinct := hef
      left_incident := hev
      right_incident := hfv
      admissible := hlocal.to_admissible
      remaining := ⟨g, hg, hgv⟩ }
  refine ⟨S, S.connects_graph hconn, ?_⟩
  exact hlocal.bridgeless ⟨g, k, hg, hk, hgk, hgv, hkv⟩

theorem fleischner_splitting_lemma_of_not_supportAway_reachable
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v) {e f : E}
    (hef : e ≠ f) (he : IsIncident G v e) (hf : IsIncident G v f)
    (hxy : ¬ (supportAwayFromVertex G v).Reachable
      (otherEndpoint G v e) (otherEndpoint G v f)) :
    ∃ S : ReducingSplitWithLoops G v,
      S.graph.Connects Finset.univ ∧ S.graph.Bridgeless := by
  exact fleischner_splitting_lemma_of_local_pair G hconn
    (exists_fleischner_admissible_local_pair_of_not_supportAway_reachable
      G hconn hb hdeg hef he hf hxy)

theorem fleischner_splitting_lemma
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v) :
    ∃ S : ReducingSplitWithLoops G v,
      S.graph.Connects Finset.univ ∧ S.graph.Bridgeless := by
  exact fleischner_splitting_lemma_of_local_pair G hconn
    (exists_fleischner_admissible_local_pair G hconn hb hdeg)

theorem exists_reducingSplitWithLoops_of_high_degree
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hhigh : ∃ v : V, 4 ≤ degree G v) :
    ∃ v : V, ∃ S : ReducingSplitWithLoops G v,
      S.graph.Connects Finset.univ ∧ S.graph.Bridgeless := by
  rcases hhigh with ⟨v, hv⟩
  obtain ⟨S, hconnS, hbS⟩ := fleischner_splitting_lemma G hconn hb hv
  exact ⟨v, S, hconnS, hbS⟩

theorem fleischner_splitting_lemma_of_global_bad_pair_obstruction
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ)
    (hdeg : 4 ≤ degree G v)
    (hglobal :
      (∀ {e f : E}, e ≠ f → IsIncident G v e → IsIncident G v f →
        ¬ IsFleischnerAdmissibleSplitWithLoops G v e f) →
        ∃ S : Finset V,
          WeakFleischnerDangerousSet G v S ∧ v ∉ S ∧
            ∀ r : E, IsIncident G v r → otherEndpoint G v r ∈ S) :
    ∃ S : ReducingSplitWithLoops G v,
      S.graph.Connects Finset.univ ∧ S.graph.Bridgeless := by
  exact fleischner_splitting_lemma_of_local_pair G hconn
    (exists_fleischner_admissible_local_pair_of_global_bad_pair_obstruction
      G hdeg hglobal)

theorem fleischner_splitting_lemma_noLoops_of_local_pair
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V} (hconn : Connects G Finset.univ)
    (hpair : ∃ e f g k : E,
      e ≠ f ∧ IsIncident G v e ∧ IsIncident G v f ∧
      (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
      IsIncident G v g ∧ IsIncident G v k ∧
      otherEndpoint G v e ≠ otherEndpoint G v f ∧
      IsFleischnerAdmissibleSplitWithLoops G v e f) :
    ∃ S : ReducingSplit G v,
      Connects S.graph Finset.univ ∧ Bridgeless S.graph := by
  rcases hpair with
    ⟨e, f, g, k, hef, hev, hfv, hg, hk, hgk, hgv, hkv, hnew, hlocal⟩
  let S : ReducingSplit G v :=
    { left := e
      right := f
      distinct := hef
      left_incident := hev
      right_incident := hfv
      endpoints_distinct := hnew
      admissible := hlocal.to_admissible.toNoLoops
      remaining := ⟨g, hg, hgv⟩ }
  refine ⟨S, S.connects_graph hconn, ?_⟩
  have hbPseudo : (splitOffWithLoops G v e f).Bridgeless :=
    hlocal.bridgeless ⟨g, k, hg, hk, hgk, hgv, hkv⟩
  have hbToPseudo : S.graph.toPseudograph.Bridgeless := by
    simpa [S, ReducingSplit.graph, splitOffWithLoops_toPseudograph G hnew]
      using hbPseudo
  exact (OrientedMultigraph.toPseudograph_bridgeless S.graph).mp hbToPseudo

theorem fleischner_splitting_lemma_noLoops_of_no_parallel_at_vertex
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v)
    (hparallel : ∀ {e f : E}, e ≠ f → IsIncident G v e → IsIncident G v f →
      otherEndpoint G v e ≠ otherEndpoint G v f) :
    ∃ S : ReducingSplit G v,
      Connects S.graph Finset.univ ∧ Bridgeless S.graph := by
  exact fleischner_splitting_lemma_noLoops_of_local_pair G hconn
    (exists_fleischner_admissible_nonloop_local_pair_of_no_parallel_at_vertex
      G hconn hb hdeg hparallel)

theorem fleischner_splitting_lemma_of_maximal_uncrossing
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v)
    (huncross : ∀ {A B : Finset V} {e r : E},
      A ∈ fleischnerDangerousSetsAt G v →
      (∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card) →
      FleischnerDangerousSetForPair G v e r B →
      e ≠ r → IsIncident G v e → IsIncident G v r →
      otherEndpoint G v e ∈ A → otherEndpoint G v r ∉ A → False) :
    ∃ S : ReducingSplitWithLoops G v,
      S.graph.Connects Finset.univ ∧ S.graph.Bridgeless := by
  exact fleischner_splitting_lemma_of_local_pair G hconn
    (exists_fleischner_admissible_local_pair_of_maximal_uncrossing
      G hconn hb hdeg huncross)

theorem fleischner_splitting_lemma_of_pair_minimal_uncrossing
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v)
    (huncross : ∀ {A B : Finset V} {e r : E},
      A ∈ fleischnerDangerousSetsAt G v →
      (∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card) →
      B ∈ fleischnerDangerousSetsForPair G v e r →
      (∀ T ∈ fleischnerDangerousSetsForPair G v e r,
        (A ∩ B).card ≤ (A ∩ T).card) →
      e ≠ r → IsIncident G v e → IsIncident G v r →
      otherEndpoint G v e ∈ A → otherEndpoint G v r ∉ A → False) :
    ∃ S : ReducingSplitWithLoops G v,
      S.graph.Connects Finset.univ ∧ S.graph.Bridgeless := by
  exact fleischner_splitting_lemma_of_local_pair G hconn
    (exists_fleischner_admissible_local_pair_of_pair_minimal_uncrossing
      G hconn hb hdeg huncross)

theorem fleischner_splitting_lemma_of_weak_minimal_uncrossing
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {v : V}
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : 4 ≤ degree G v)
    (huncross : ∀ {A B : Finset V} {e r : E},
      A ∈ fleischnerDangerousSetsAt G v →
      (∀ T ∈ fleischnerDangerousSetsAt G v, T.card ≤ A.card) →
      B ∈ weakFleischnerDangerousSetsContainingEndpoint G v r →
      (∀ T ∈ weakFleischnerDangerousSetsContainingEndpoint G v r,
        (A ∩ B).card ≤ (A ∩ T).card) →
      e ≠ r → IsIncident G v e → IsIncident G v r →
      otherEndpoint G v e ∈ A → otherEndpoint G v r ∉ A → False) :
    ∃ S : ReducingSplitWithLoops G v,
      S.graph.Connects Finset.univ ∧ S.graph.Bridgeless := by
  exact fleischner_splitting_lemma_of_local_pair G hconn
    (exists_fleischner_admissible_local_pair_of_weak_minimal_uncrossing
      G hconn hb hdeg huncross)

lemma isEvenEdgeSet_restrictedCut_card_eq_zero {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq V] (G : OrientedMultigraph V E)
    {F : Finset E} (hF : IsEvenEdgeSet G F) (S : Finset V) :
    ((restrictedCut G F S).card : F₂) = 0 := by
  classical
  have htotal : (∑ v ∈ S, ∑ e ∈ F, edgeIncidence G v e) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    exact hF v
  calc
    ((restrictedCut G F S).card : F₂)
        = ∑ e ∈ F, if Crosses G S e then (1 : F₂) else 0 := by
          rw [Finset.card_eq_sum_ones]
          simp [restrictedCut]
    _ = ∑ e ∈ F, ∑ v ∈ S, edgeIncidence G v e := by
          apply Finset.sum_congr rfl
          intro e _
          by_cases he : Crosses G S e
          · rw [if_pos he, sum_edgeIncidence_over_set_eq_one_of_crosses G S he]
          · rw [if_neg he, sum_edgeIncidence_over_set_eq_zero_of_not_crosses G S he]
    _ = ∑ v ∈ S, ∑ e ∈ F, edgeIncidence G v e := by
          rw [Finset.sum_comm]
    _ = 0 := htotal

lemma isEvenEdgeSet_reachable_erase_of_mem {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : OrientedMultigraph V E)
    {F : Finset E} (hF : IsEvenEdgeSet G F) {e : E} (he : e ∈ F) :
    (ReachableIn G) (F.erase e) (G.endAt e 0) (G.endAt e 1) := by
  classical
  by_contra hnot
  let R := F.erase e
  let S : Finset V := Finset.univ.filter fun v ↦
    (ReachableIn G) R (G.endAt e 0) v
  have heCut : e ∈ restrictedCut G F S := by
    rw [mem_restrictedCut]
    refine ⟨he, ?_⟩
    unfold Crosses
    have h0 : G.endAt e 0 ∈ S := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        SimpleGraph.Reachable.refl _⟩
    have h1 : G.endAt e 1 ∉ S := by
      intro h
      exact hnot (Finset.mem_filter.mp h).2
    exact fun hsides ↦ h1 (show G.endAt e 1 ∈ S from hsides ▸ h0)
  have hunique : ∀ f ∈ restrictedCut G F S, f = e := by
    intro f hf
    by_contra hfe
    have hfm := (mem_restrictedCut G).mp hf
    have hfR : f ∈ R := Finset.mem_erase.mpr ⟨hfe, hfm.1⟩
    have hadj : ((supportGraph G) R).Adj (G.endAt f 0) (G.endAt f 1) := by
      rw [supportGraph_adj_iff]
      exact ⟨G.loopless f, f, hfR, .inl ⟨rfl, rfl⟩⟩
    unfold Crosses at hfm
    by_cases h0 : G.endAt f 0 ∈ S
    · by_cases h1 : G.endAt f 1 ∈ S
      · exact hfm.2 (propext ⟨fun _ ↦ h1, fun _ ↦ h0⟩)
      · have hr0 : (ReachableIn G) R (G.endAt e 0) (G.endAt f 0) :=
          (Finset.mem_filter.mp h0).2
        have hr1 : (ReachableIn G) R (G.endAt e 0) (G.endAt f 1) :=
          hr0.trans (SimpleGraph.Adj.reachable hadj)
        exact h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr1⟩)
    · by_cases h1 : G.endAt f 1 ∈ S
      · have hr1 : (ReachableIn G) R (G.endAt e 0) (G.endAt f 1) :=
          (Finset.mem_filter.mp h1).2
        have hr0 : (ReachableIn G) R (G.endAt e 0) (G.endAt f 0) :=
          hr1.trans (SimpleGraph.Adj.reachable hadj.symm)
        exact h0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr0⟩)
      · exact hfm.2 (propext ⟨fun h ↦ (h0 h).elim, fun h ↦ (h1 h).elim⟩)
  have hcut : restrictedCut G F S = {e} := by
    ext f
    constructor
    · intro hf
      exact Finset.mem_singleton.mpr (hunique f hf)
    · intro hf
      exact Finset.mem_singleton.mp hf ▸ heCut
  have hparity := isEvenEdgeSet_restrictedCut_card_eq_zero G hF S
  rw [hcut] at hparity
  simp at hparity

lemma Circuit.reachable_erase_of_mem {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : OrientedMultigraph V E)
    (C : Circuit G) {e : E} (he : e ∈ C.edges) :
    (ReachableIn G) (C.edges.erase e) (G.endAt e 0) (G.endAt e 1) :=
  isEvenEdgeSet_reachable_erase_of_mem G C.even he

lemma Circuit.isCyclicEdge_of_mem {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : OrientedMultigraph V E)
    (C : Circuit G) {e : E} (he : e ∈ C.edges) :
    (IsCyclicEdge G) C.edges e :=
  ⟨he, C.reachable_erase_of_mem G he⟩

lemma Circuit.not_subset_spanningTree {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : OrientedMultigraph V E)
    [Nonempty V] {T : Finset E} (hT : IsSpanningTree G T)
    (C : Circuit G) :
    ¬ C.edges ⊆ T := by
  classical
  intro hsub
  obtain ⟨e, he⟩ := C.nonempty
  have hreach : (ReachableIn G) (T.erase e) (G.endAt e 0) (G.endAt e 1) := by
    apply reachableIn_mono G ?_ (C.reachable_erase_of_mem G he)
    intro f hf
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hf).1, hsub (Finset.mem_erase.mp hf).2⟩
  exact not_reachableIn_erase_of_mem_spanningTree G hT (hsub he) hreach

lemma Circuit.meets_spanningTree_compl {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : OrientedMultigraph V E)
    [Nonempty V] {T : Finset E} (hT : IsSpanningTree G T)
    (C : Circuit G) :
    (C.edges ∩ (Finset.univ \ T)).Nonempty := by
  by_contra h
  apply C.not_subset_spanningTree G hT
  intro e he
  by_contra heT
  apply h
  exact ⟨e, by simp [he, heT]⟩

lemma isEvenEdgeSet_eq_empty_of_subset_spanningTree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] (G : OrientedMultigraph V E)
    [Nonempty V] {T F : Finset E} (hT : IsSpanningTree G T)
    (hsub : F ⊆ T) (hF : IsEvenEdgeSet G F) :
    F = ∅ := by
  classical
  by_contra hne
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hreach : (ReachableIn G) (T.erase e) (G.endAt e 0) (G.endAt e 1) := by
    apply reachableIn_mono G ?_ (isEvenEdgeSet_reachable_erase_of_mem G hF he)
    intro f hf
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hf).1, hsub (Finset.mem_erase.mp hf).2⟩
  exact not_reachableIn_erase_of_mem_spanningTree G hT (hsub he) hreach

def edgeSetIndicator {E : Type*} [DecidableEq E] (F : Finset E) (e : E) :
    F₂ :=
  if e ∈ F then 1 else 0

lemma edgeSetIndicator_symmDiff {E : Type*} [DecidableEq E]
    (A B : Finset E) (e : E) :
    edgeSetIndicator (A ∆ B) e =
      edgeSetIndicator A e + edgeSetIndicator B e := by
  have htwo : (1 : F₂) + 1 = 0 := by decide
  by_cases hA : e ∈ A <;>
    by_cases hB : e ∈ B <;>
      simp [edgeSetIndicator, Finset.mem_symmDiff, hA, hB, htwo]

lemma sum_edgeIncidence_eq_indicator_sum {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (F : Finset E) (v : V) :
    ∑ e ∈ F, edgeIncidence G v e =
      ∑ e : E, edgeSetIndicator F e * edgeIncidence G v e := by
  simp [edgeSetIndicator]

lemma isEvenEdgeSet_symmDiff {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : OrientedMultigraph V E)
    {A B : Finset E} (hA : IsEvenEdgeSet G A) (hB : IsEvenEdgeSet G B) :
    IsEvenEdgeSet G (A ∆ B) := by
  intro v
  calc
    ∑ e ∈ A ∆ B, edgeIncidence G v e
        = ∑ e : E, edgeSetIndicator (A ∆ B) e * edgeIncidence G v e := by
          rw [sum_edgeIncidence_eq_indicator_sum]
    _ = ∑ e : E,
          (edgeSetIndicator A e + edgeSetIndicator B e) * edgeIncidence G v e := by
          apply Finset.sum_congr rfl
          intro e _
          rw [edgeSetIndicator_symmDiff]
    _ = (∑ e : E, edgeSetIndicator A e * edgeIncidence G v e) +
          ∑ e : E, edgeSetIndicator B e * edgeIncidence G v e := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro e _
          rw [add_mul]
    _ = (∑ e ∈ A, edgeIncidence G v e) +
          ∑ e ∈ B, edgeIncidence G v e := by
          rw [← sum_edgeIncidence_eq_indicator_sum G A v,
            ← sum_edgeIncidence_eq_indicator_sum G B v]
    _ = 0 := by
          rw [hA v, hB v]
          rfl

lemma symmDiff_subset_of_same_off {E : Type*} [DecidableEq E]
    {A B T : Finset E}
    (h : ∀ e : E, e ∉ T → (e ∈ A ↔ e ∈ B)) :
    A ∆ B ⊆ T := by
  intro e he
  by_contra heT
  have hiff := h e heT
  rw [Finset.mem_symmDiff] at he
  tauto

lemma even_edgeSet_eq_of_same_off_spanningTree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) [Nonempty V] {T A B : Finset E}
    (hT : IsSpanningTree G T) (hA : IsEvenEdgeSet G A)
    (hB : IsEvenEdgeSet G B)
    (hcoord : ∀ e : E, e ∉ T → (e ∈ A ↔ e ∈ B)) :
    A = B := by
  classical
  have hsymEven : IsEvenEdgeSet G (A ∆ B) :=
    isEvenEdgeSet_symmDiff G hA hB
  have hsymSub : A ∆ B ⊆ T := symmDiff_subset_of_same_off hcoord
  have hsymEmpty := isEvenEdgeSet_eq_empty_of_subset_spanningTree G hT
    hsymSub hsymEven
  exact Finset.symmDiff_eq_empty.mp hsymEmpty

lemma Circuit.edges_eq_of_same_off_spanningTree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E) [Nonempty V] {T : Finset E}
    (hT : IsSpanningTree G T) {C D : Circuit G}
    (hcoord : ∀ e : E, e ∉ T → (e ∈ C.edges ↔ e ∈ D.edges)) :
    C.edges = D.edges :=
  even_edgeSet_eq_of_same_off_spanningTree G hT C.even D.even hcoord

lemma Circuit.edges_eq_of_same_cotreeTrace {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) [Nonempty V] {T : Finset E}
    (hT : IsSpanningTree G T) {C D : Circuit G}
    (hcoord : C.edges ∩ (Finset.univ \ T) = D.edges ∩ (Finset.univ \ T)) :
    C.edges = D.edges := by
  apply Circuit.edges_eq_of_same_off_spanningTree G hT
  intro e heT
  have hmem := congrArg (fun S : Finset E ↦ e ∈ S) hcoord
  simpa [heT] using hmem

def Circuit.cotreeTraceVector {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : OrientedMultigraph V E) (T : Finset E)
    (C : Circuit G) :
    {e : E // e ∉ T} → F₂ :=
  fun e ↦ if e.1 ∈ C.edges then 1 else 0

lemma Circuit.mem_edges_iff_of_cotreeTraceVector_eq {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) {T : Finset E} {C D : Circuit G}
    (h : Circuit.cotreeTraceVector G T C = Circuit.cotreeTraceVector G T D)
    {e : E} (heT : e ∉ T) :
    e ∈ C.edges ↔ e ∈ D.edges := by
  have hcoord := congrFun h ⟨e, heT⟩
  dsimp [Circuit.cotreeTraceVector] at hcoord
  by_cases hC : e ∈ C.edges <;> by_cases hD : e ∈ D.edges <;>
    simp [hC, hD] at hcoord ⊢

lemma Circuit.edges_eq_of_cotreeTraceVector_eq {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) [Nonempty V] {T : Finset E}
    (hT : IsSpanningTree G T) {C D : Circuit G}
    (h : Circuit.cotreeTraceVector G T C = Circuit.cotreeTraceVector G T D) :
    C.edges = D.edges := by
  exact Circuit.edges_eq_of_same_off_spanningTree G hT
    (fun e heT ↦ Circuit.mem_edges_iff_of_cotreeTraceVector_eq G h heT)

lemma Circuit.ext_edges {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : OrientedMultigraph V E} {C D : Circuit G}
    (h : C.edges = D.edges) :
    C = D := by
  cases C
  cases D
  cases h
  rfl

lemma Circuit.eq_of_cotreeTraceVector_eq {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) [Nonempty V] {T : Finset E}
    (hT : IsSpanningTree G T) {C D : Circuit G}
    (h : Circuit.cotreeTraceVector G T C = Circuit.cotreeTraceVector G T D) :
    C = D :=
  Circuit.ext_edges (Circuit.edges_eq_of_cotreeTraceVector_eq G hT h)

lemma Circuit.cotreeTraceVector_ne_zero {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) [Nonempty V] {T : Finset E}
    (hT : IsSpanningTree G T) (C : Circuit G) :
    Circuit.cotreeTraceVector G T C ≠ 0 := by
  obtain ⟨e, he⟩ := C.meets_spanningTree_compl G hT
  have heC : e ∈ C.edges := (Finset.mem_inter.mp he).1
  have heT : e ∉ T := (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).2).2
  intro hzero
  have hcoord := congrFun hzero ⟨e, heT⟩
  simp [Circuit.cotreeTraceVector, heC] at hcoord

lemma f2_eq_zero_or_one (x : F₂) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact .inl rfl
  · exact .inr rfl

lemma f2_add_self (x : F₂) : x + x = 0 := by
  fin_cases x <;> rfl

lemma f2_eq_zero_of_ne_one {x : F₂} (hx : x ≠ 1) : x = 0 := by
  rcases f2_eq_zero_or_one x with h | h
  · exact h
  · exact (hx h).elim

def vectorFinsetSum {ι X : Type*} [DecidableEq ι]
    (v : ι → X → F₂) (S : Finset ι) :
    X → F₂ :=
  ∑ i ∈ S, v i

lemma vectorFinsetSum_symmDiff {ι X : Type*} [Finite ι] [DecidableEq ι]
    (v : ι → X → F₂) (A B : Finset ι) :
    vectorFinsetSum v (A ∆ B) = vectorFinsetSum v A + vectorFinsetSum v B := by
  classical
  letI := Fintype.ofFinite ι
  ext x
  calc
    vectorFinsetSum v (A ∆ B) x
        = ∑ i : ι, edgeSetIndicator (A ∆ B) i * v i x := by
          simp [vectorFinsetSum, edgeSetIndicator]
    _ = ∑ i : ι, (edgeSetIndicator A i + edgeSetIndicator B i) * v i x := by
          apply Finset.sum_congr rfl
          intro i _
          rw [edgeSetIndicator_symmDiff]
    _ = (∑ i : ι, edgeSetIndicator A i * v i x) +
          ∑ i : ι, edgeSetIndicator B i * v i x := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [add_mul]
    _ = vectorFinsetSum v A x + vectorFinsetSum v B x := by
          simp [vectorFinsetSum, edgeSetIndicator]

lemma vectorFinsetSum_injective_of_proper_sums {ι X : Type*}
    [Fintype ι] [DecidableEq ι]
    (v : ι → X → F₂)
    (hproper : ∀ S : Finset ι, S.Nonempty → S ≠ Finset.univ →
      vectorFinsetSum v S ≠ 0)
    (j : ι) :
    Function.Injective
      (fun S : Finset {i : ι // i ≠ j} ↦
        vectorFinsetSum v (S.image (fun a : {i : ι // i ≠ j} ↦ (a : ι)))) := by
  classical
  intro A B hAB
  let A' : Finset ι := A.image (fun a : {i : ι // i ≠ j} ↦ (a : ι))
  let B' : Finset ι := B.image (fun a : {i : ι // i ≠ j} ↦ (a : ι))
  have hzero : vectorFinsetSum v (A' ∆ B') = 0 := by
    rw [vectorFinsetSum_symmDiff]
    have hAB' : vectorFinsetSum v A' = vectorFinsetSum v B' := hAB
    rw [hAB']
    ext x
    exact f2_add_self (vectorFinsetSum v B' x)
  by_contra hne
  have hdiff_ne : A' ∆ B' ≠ ∅ := by
    intro hempty
    apply hne
    ext a
    have hmem := congrArg (fun S : Finset ι ↦ a.1 ∈ S)
      (Finset.symmDiff_eq_empty.mp hempty)
    simpa [A', B', a.2] using hmem
  have hnonempty : (A' ∆ B').Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hdiff_ne
  have hproper' : A' ∆ B' ≠ Finset.univ := by
    intro huniv
    have hj : j ∈ A' ∆ B' := by simp [huniv]
    have hjA : j ∉ A' := by
      intro hjA
      change j ∈ A.image (fun a : {i : ι // i ≠ j} ↦ (a : ι)) at hjA
      rcases Finset.mem_image.mp hjA with ⟨a, _, ha⟩
      exact a.2 ha
    have hjB : j ∉ B' := by
      intro hjB
      change j ∈ B.image (fun a : {i : ι // i ≠ j} ↦ (a : ι)) at hjB
      rcases Finset.mem_image.mp hjB with ⟨a, _, ha⟩
      exact a.2 ha
    simp [Finset.mem_symmDiff, hjA, hjB] at hj
  exact hproper (A' ∆ B') hnonempty hproper' hzero

lemma card_subtype_ne_le_of_proper_sums {ι X : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype X]
    (v : ι → X → F₂)
    (hproper : ∀ S : Finset ι, S.Nonempty → S ≠ Finset.univ →
      vectorFinsetSum v S ≠ 0)
    (j : ι) :
    Fintype.card {i : ι // i ≠ j} ≤ Fintype.card X := by
  classical
  have hinj := vectorFinsetSum_injective_of_proper_sums v hproper j
  have hcard :=
    Fintype.card_le_of_injective
      (fun S : Finset {i : ι // i ≠ j} ↦
        vectorFinsetSum v (S.image (fun a : {i : ι // i ≠ j} ↦ (a : ι))))
      hinj
  rw [Fintype.card_finset, Fintype.card_fun] at hcard
  have hF2 : Fintype.card F₂ = 2 := ZMod.card 2
  rw [hF2] at hcard
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hcard

lemma card_le_succ_of_proper_sums {ι X : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty ι]
    (v : ι → X → F₂)
    (hproper : ∀ S : Finset ι, S.Nonempty → S ≠ Finset.univ →
      vectorFinsetSum v S ≠ 0) :
    Fintype.card ι ≤ Fintype.card X + 1 := by
  classical
  let j : ι := Classical.arbitrary ι
  have hle := card_subtype_ne_le_of_proper_sums v hproper j
  have hcard : Fintype.card {i : ι // i ≠ j} + 1 = Fintype.card ι := by
    have hfilter :
        (Finset.univ.filter fun i : ι ↦ i ≠ j) = Finset.univ.erase j := by
      ext i
      simp
    rw [Fintype.card_subtype]
    rw [hfilter]
    exact Finset.card_erase_add_one (Finset.mem_univ j)
  omega

lemma cotreeSubtype_card_eq {E : Type*} [Fintype E] [DecidableEq E]
    (T : Finset E) :
    Fintype.card {e : E // e ∉ T} = (Finset.univ \ T).card := by
  rw [Fintype.card_subtype]
  congr 1
  ext e
  simp

def CircuitDoubleCover.traceVector {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : OrientedMultigraph V E)
    (M : CircuitDoubleCover G) (T : Finset E) :
    Fin M.circuits.length → {e : E // e ∉ T} → F₂ :=
  fun i ↦ Circuit.cotreeTraceVector G T (M.circuits.get i)

def CircuitDoubleCover.parityEdgeSet {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : OrientedMultigraph V E)
    (M : CircuitDoubleCover G) (S : Finset (Fin M.circuits.length)) :
    Finset E :=
  Finset.univ.filter fun e ↦
    vectorFinsetSum (fun i ↦ edgeSetIndicator (M.circuits.get i).edges) S e = 1

def CircuitDoubleCover.selectedEdgeSet {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : OrientedMultigraph V E)
    (M : CircuitDoubleCover G) (S : Finset (Fin M.circuits.length)) :
    Finset E :=
  Finset.univ.filter fun e ↦
    ∃ i ∈ S, e ∈ (M.circuits.get i).edges

lemma CircuitDoubleCover.mem_selectedEdgeSet {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (M : CircuitDoubleCover G)
    {S : Finset (Fin M.circuits.length)} {e : E} :
    e ∈ M.selectedEdgeSet G S ↔ ∃ i ∈ S, e ∈ (M.circuits.get i).edges := by
  simp [CircuitDoubleCover.selectedEdgeSet]

lemma CircuitDoubleCover.edgeSetIndicator_parityEdgeSet {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (M : CircuitDoubleCover G)
    (S : Finset (Fin M.circuits.length)) (e : E) :
    edgeSetIndicator (M.parityEdgeSet G S) e =
      vectorFinsetSum (fun i ↦ edgeSetIndicator (M.circuits.get i).edges) S e := by
  by_cases h :
      vectorFinsetSum (fun i ↦ edgeSetIndicator (M.circuits.get i).edges) S e = 1
  · simp only [CircuitDoubleCover.parityEdgeSet, edgeSetIndicator,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_pos h, h]
  · have hz :
        vectorFinsetSum (fun i ↦ edgeSetIndicator (M.circuits.get i).edges) S e = 0 :=
      f2_eq_zero_of_ne_one h
    simp only [CircuitDoubleCover.parityEdgeSet, edgeSetIndicator,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_neg h, hz]

lemma CircuitDoubleCover.parityEdgeSet_even {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (M : CircuitDoubleCover G)
    (S : Finset (Fin M.circuits.length)) :
    IsEvenEdgeSet G (M.parityEdgeSet G S) := by
  intro v
  calc
    ∑ e ∈ M.parityEdgeSet G S, edgeIncidence G v e
        = ∑ e : E, edgeSetIndicator (M.parityEdgeSet G S) e *
            edgeIncidence G v e := by
          rw [sum_edgeIncidence_eq_indicator_sum]
    _ = ∑ e : E,
          vectorFinsetSum (fun i ↦ edgeSetIndicator (M.circuits.get i).edges) S e *
            edgeIncidence G v e := by
          apply Finset.sum_congr rfl
          intro e _
          rw [CircuitDoubleCover.edgeSetIndicator_parityEdgeSet]
    _ = ∑ e : E, (∑ i ∈ S,
          edgeSetIndicator (M.circuits.get i).edges e) * edgeIncidence G v e := by
          apply Finset.sum_congr rfl
          intro e _
          simp [vectorFinsetSum]
    _ = ∑ e : E, ∑ i ∈ S,
          edgeSetIndicator (M.circuits.get i).edges e * edgeIncidence G v e := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.sum_mul]
    _ = ∑ i ∈ S, ∑ e : E,
          edgeSetIndicator (M.circuits.get i).edges e * edgeIncidence G v e := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ S, ∑ e ∈ (M.circuits.get i).edges, edgeIncidence G v e := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← sum_edgeIncidence_eq_indicator_sum]
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          exact (M.circuits.get i).even v

lemma CircuitDoubleCover.parityEdgeSet_subset_of_trace_eq_zero {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (M : CircuitDoubleCover G)
    {T : Finset E} {S : Finset (Fin M.circuits.length)}
    (hzero : vectorFinsetSum (M.traceVector G T) S = 0) :
    M.parityEdgeSet G S ⊆ T := by
  intro e he
  by_contra heT
  have hcoord := congrFun hzero ⟨e, heT⟩
  have hcoord' :
      vectorFinsetSum (fun i ↦ edgeSetIndicator (M.circuits.get i).edges) S e = 0 := by
    simpa [CircuitDoubleCover.traceVector, Circuit.cotreeTraceVector,
      vectorFinsetSum, edgeSetIndicator] using hcoord
  have hparity :
      vectorFinsetSum (fun i ↦ edgeSetIndicator (M.circuits.get i).edges) S e = 1 :=
    (Finset.mem_filter.mp he).2
  rw [hparity] at hcoord'
  simp at hcoord'

lemma CircuitDoubleCover.parityEdgeSet_eq_empty_of_trace_eq_zero {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) [Nonempty V] (M : CircuitDoubleCover G)
    {T : Finset E} (hT : IsSpanningTree G T)
    {S : Finset (Fin M.circuits.length)}
    (hzero : vectorFinsetSum (M.traceVector G T) S = 0) :
    M.parityEdgeSet G S = ∅ := by
  exact isEvenEdgeSet_eq_empty_of_subset_spanningTree G hT
    (M.parityEdgeSet_subset_of_trace_eq_zero G hzero)
    (M.parityEdgeSet_even G S)

lemma list_filter_length_eq_finset_filter_get_card {α : Type*} (L : List α)
    (p : α → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (Fin L.length)).filter fun i ↦ p (L.get i)).card =
      (L.filter p).length := by
  classical
  induction L with
  | nil =>
      simp
  | cons a L ih =>
      by_cases hp : p a
      · have hset :
            ((Finset.univ : Finset (Fin (a :: L).length)).filter
                fun i ↦ p ((a :: L).get i)) =
              insert 0 (((Finset.univ : Finset (Fin L.length)).filter
                fun i ↦ p (L.get i)).image Fin.succ) := by
          ext i
          induction i using Fin.cases with
          | zero =>
              simp [hp]
          | succ i =>
              simp
        rw [hset]
        have hnot : (0 : Fin (a :: L).length) ∉
            (((Finset.univ : Finset (Fin L.length)).filter
              fun i ↦ p (L.get i)).image Fin.succ) := by
          intro h
          rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
          exact Fin.succ_ne_zero i hi
        rw [Finset.card_insert_of_notMem hnot]
        rw [Finset.card_image_of_injective _ (Fin.succ_injective _)]
        rw [ih]
        simp [hp]
      · have hset :
            ((Finset.univ : Finset (Fin (a :: L).length)).filter
                fun i ↦ p ((a :: L).get i)) =
              (((Finset.univ : Finset (Fin L.length)).filter
                fun i ↦ p (L.get i)).image Fin.succ) := by
          ext i
          induction i using Fin.cases with
          | zero =>
              simp [hp]
          | succ i =>
              simp
        rw [hset]
        rw [Finset.card_image_of_injective _ (Fin.succ_injective _)]
        rw [ih]
        simp [hp]

lemma exists_not_mem_of_ne_univ {α : Type*} [Fintype α] (S : Finset α)
    (hS : S ≠ Finset.univ) :
    ∃ x, x ∉ S := by
  by_contra h
  apply hS
  ext x
  constructor
  · intro _
    exact Finset.mem_univ x
  · intro _
    by_contra hx
    exact h ⟨x, hx⟩

def CircuitDoubleCover.edgeIndexSet {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : OrientedMultigraph V E)
    (M : CircuitDoubleCover G) (e : E) :
    Finset (Fin M.circuits.length) :=
  Finset.univ.filter fun i ↦ e ∈ (M.circuits.get i).edges

lemma CircuitDoubleCover.edgeIndexSet_card_eq_two {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (M : CircuitDoubleCover G) (e : E) :
    (M.edgeIndexSet G e).card = 2 := by
  have hcount :=
    list_filter_length_eq_finset_filter_get_card M.circuits
      (fun C : Circuit G ↦ e ∈ C.edges)
  rw [CircuitDoubleCover.edgeIndexSet]
  exact hcount.trans (M.coveredTwice e)

lemma CircuitDoubleCover.exists_index_of_edge {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (M : CircuitDoubleCover G) (e : E) :
    ∃ i : Fin M.circuits.length, e ∈ (M.circuits.get i).edges := by
  have hpos : 0 < (M.edgeIndexSet G e).card := by
    rw [M.edgeIndexSet_card_eq_two G e]
    norm_num
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  refine ⟨i, ?_⟩
  simpa [CircuitDoubleCover.edgeIndexSet] using hi

lemma CircuitDoubleCover.mem_parityEdgeSet_of_selected_and_unselected {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (M : CircuitDoubleCover G)
    {S : Finset (Fin M.circuits.length)} {i j : Fin M.circuits.length}
    (hiS : i ∈ S) (hjS : j ∉ S) {e : E}
    (hei : e ∈ (M.circuits.get i).edges)
    (hej : e ∈ (M.circuits.get j).edges) :
    e ∈ M.parityEdgeSet G S := by
  classical
  let A := M.edgeIndexSet G e
  have hiA : i ∈ A := by
    change i ∈ M.edgeIndexSet G e
    rw [CircuitDoubleCover.edgeIndexSet]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hei⟩
  have hjA : j ∈ A := by
    change j ∈ M.edgeIndexSet G e
    rw [CircuitDoubleCover.edgeIndexSet]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hej⟩
  have hij : i ≠ j := by
    intro hij
    exact hjS (hij ▸ hiS)
  have hpairSub : ({i, j} : Finset (Fin M.circuits.length)) ⊆ A := by
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hiA
    · exact hjA
  have hpairCard : ({i, j} : Finset (Fin M.circuits.length)).card = 2 :=
    Finset.card_pair hij
  have hAcard : A.card = 2 := M.edgeIndexSet_card_eq_two G e
  have hAeq : A = ({i, j} : Finset (Fin M.circuits.length)) := by
    exact (Finset.eq_of_subset_of_card_le hpairSub (by rw [hAcard, hpairCard])).symm
  have hfilter :
      (S.filter fun k ↦ e ∈ (M.circuits.get k).edges) = {i} := by
    ext k
    have hkA : k ∈ A ↔ k = i ∨ k = j := by
      have hmem := congrArg (fun T : Finset (Fin M.circuits.length) ↦ k ∈ T) hAeq
      simpa using hmem
    have hkEdge : e ∈ (M.circuits.get k).edges ↔ k = i ∨ k = j := by
      simpa [A, CircuitDoubleCover.edgeIndexSet] using hkA
    constructor
    · intro hk
      have hkS : k ∈ S := (Finset.mem_filter.mp hk).1
      have hkE : e ∈ (M.circuits.get k).edges := (Finset.mem_filter.mp hk).2
      rcases hkEdge.mp hkE with rfl | rfl
      · exact Finset.mem_singleton.mpr rfl
      · exact (hjS hkS).elim
    · intro hk
      have hki : k = i := Finset.mem_singleton.mp hk
      subst k
      exact Finset.mem_filter.mpr ⟨hiS, hei⟩
  have hsum :
      vectorFinsetSum (fun k ↦ edgeSetIndicator (M.circuits.get k).edges) S e = 1 := by
    have hcard :
        vectorFinsetSum (fun k ↦ edgeSetIndicator (M.circuits.get k).edges) S e =
          ((S.filter fun k ↦ e ∈ (M.circuits.get k).edges).card : F₂) := by
      simp [vectorFinsetSum, edgeSetIndicator]
    rw [hcard, hfilter]
    simp
  rw [CircuitDoubleCover.parityEdgeSet]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hsum⟩

lemma CircuitDoubleCover.disjoint_selected_unselected_of_parity_empty {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (M : CircuitDoubleCover G)
    {S : Finset (Fin M.circuits.length)}
    (hempty : M.parityEdgeSet G S = ∅)
    {i j : Fin M.circuits.length} (hiS : i ∈ S) (hjS : j ∉ S) :
    Disjoint (M.circuits.get i).edges (M.circuits.get j).edges := by
  rw [Finset.disjoint_left]
  intro e hei hej
  have hepar := M.mem_parityEdgeSet_of_selected_and_unselected G hiS hjS hei hej
  rw [hempty] at hepar
  simp at hepar

lemma Circuit.ne_of_disjoint_edges {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] {G : OrientedMultigraph V E} {C D : Circuit G}
    (hdisj : Disjoint C.edges D.edges) :
    C ≠ D := by
  intro h
  subst D
  obtain ⟨e, he⟩ := C.nonempty
  exact (Finset.disjoint_left.mp hdisj) he he

lemma CircuitDoubleCover.exists_perm_get_get_to_head_of_disjoint {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (M : CircuitDoubleCover G)
    {i j : Fin M.circuits.length}
    (hdisj : Disjoint (M.circuits.get i).edges (M.circuits.get j).edges) :
    ∃ L : List (Circuit G),
      List.Perm (M.circuits.get i :: M.circuits.get j :: L) M.circuits := by
  classical
  let C := M.circuits.get i
  let D := M.circuits.get j
  have hCmem : C ∈ M.circuits := by
    simp [C]
  have hDmem : D ∈ M.circuits := by
    simp [D]
  have hCD : C ≠ D := by
    exact Circuit.ne_of_disjoint_edges (G := G) (by simpa [C, D] using hdisj)
  have hpermC : M.circuits.Perm (C :: M.circuits.erase C) :=
    List.perm_cons_erase hCmem
  have hDmemErase : D ∈ M.circuits.erase C := by
    have hmemCons : D ∈ C :: M.circuits.erase C :=
      (List.Perm.mem_iff hpermC).mp hDmem
    simpa [hCD.symm] using hmemCons
  have hpermD : (M.circuits.erase C).Perm (D :: (M.circuits.erase C).erase D) :=
    List.perm_cons_erase hDmemErase
  refine ⟨(M.circuits.erase C).erase D, ?_⟩
  simpa [C, D] using (List.Perm.cons C hpermD.symm).trans hpermC.symm

lemma CircuitDoubleCover.exists_touching_selected_unselected_of_parity_empty
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (M : CircuitDoubleCover G)
    (hconn : Connects G Finset.univ)
    {S : Finset (Fin M.circuits.length)}
    (hSnonempty : S.Nonempty) (hSproper : S ≠ Finset.univ)
    (hempty : M.parityEdgeSet G S = ∅) :
    ∃ i ∈ S, ∃ j, j ∉ S ∧ ∃ w,
      IncidentVertex G (M.circuits.get i).edges w ∧
      IncidentVertex G (M.circuits.get j).edges w ∧
      Disjoint (M.circuits.get i).edges (M.circuits.get j).edges := by
  classical
  let Fsel := M.selectedEdgeSet G S
  obtain ⟨i₀, hi₀S⟩ := hSnonempty
  obtain ⟨e₀, he₀⟩ := (M.circuits.get i₀).nonempty
  have he₀F : e₀ ∈ Fsel := by
    exact (CircuitDoubleCover.mem_selectedEdgeSet G M).mpr ⟨i₀, hi₀S, he₀⟩
  let u := G.endAt e₀ 0
  have huIncF : IncidentVertex G Fsel u := ⟨e₀, he₀F, .inl rfl⟩
  obtain ⟨j₀, hj₀S⟩ := exists_not_mem_of_ne_univ S hSproper
  obtain ⟨e₁, he₁⟩ := (M.circuits.get j₀).nonempty
  let v := G.endAt e₁ 0
  have finish_touch {j : Fin M.circuits.length} {f : E} {w : V}
      (hwR : (ReachableIn G) Fsel u w)
      (hjS : j ∉ S) (hjf : f ∈ (M.circuits.get j).edges)
      (hfw : G.endAt f 0 = w ∨ G.endAt f 1 = w) :
      ∃ i ∈ S, ∃ j, j ∉ S ∧ ∃ w,
        IncidentVertex G (M.circuits.get i).edges w ∧
        IncidentVertex G (M.circuits.get j).edges w ∧
        Disjoint (M.circuits.get i).edges (M.circuits.get j).edges := by
    have hwIncF : IncidentVertex G Fsel w :=
      incidentVertex_of_reachableIn G huIncF hwR
    rcases hwIncF with ⟨g, hgF, hgw⟩
    rcases (CircuitDoubleCover.mem_selectedEdgeSet G M).mp hgF with
      ⟨i, hiS, hig⟩
    refine ⟨i, hiS, j, hjS, w, ?_, ?_, ?_⟩
    · exact ⟨g, hig, hgw⟩
    · rcases hfw with hfw | hfw
      · exact ⟨f, hjf, .inl hfw⟩
      · exact ⟨f, hjf, .inr hfw⟩
    · exact M.disjoint_selected_unselected_of_parity_empty G hempty hiS hjS
  by_cases huv : (ReachableIn G) Fsel u v
  · exact finish_touch huv hj₀S he₁ (.inl rfl)
  · let R : Finset V := Finset.univ.filter fun x ↦ (ReachableIn G) Fsel u x
    have huR : u ∈ R := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, SimpleGraph.Reachable.refl u⟩
    have hvR : v ∉ R := by
      intro hvR
      exact huv (Finset.mem_filter.mp hvR).2
    obtain ⟨p⟩ := hconn.preconnected u v
    obtain ⟨f, _, hfPath, hfCross⟩ :=
      exists_crossing_edge_on_walk G (T := Finset.univ) p huR hvR
    have hfNotF : f ∉ Fsel := by
      intro hfF
      by_cases hf0R : G.endAt f 0 ∈ R
      · have hf1R : G.endAt f 1 ∈ R := by
          have hr0 : (ReachableIn G) Fsel u (G.endAt f 0) :=
            (Finset.mem_filter.mp hf0R).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hr0.trans (endpoint_reachable_of_edge_mem G hfF)⟩
        exact hfCross (propext ⟨fun _ ↦ hf1R, fun _ ↦ hf0R⟩)
      · have hf1R : G.endAt f 1 ∈ R := by
          by_contra hf1R
          exact hfCross
            (propext ⟨fun h ↦ (hf0R h).elim, fun h ↦ (hf1R h).elim⟩)
        have hf0R' : G.endAt f 0 ∈ R := by
          have hr1 : (ReachableIn G) Fsel u (G.endAt f 1) :=
            (Finset.mem_filter.mp hf1R).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hr1.trans (endpoint_reachable_of_edge_mem G hfF).symm⟩
        exact hf0R hf0R'
    obtain ⟨j, hjf⟩ := M.exists_index_of_edge G f
    have hjS : j ∉ S := by
      intro hjS
      apply hfNotF
      exact (CircuitDoubleCover.mem_selectedEdgeSet G M).mpr ⟨j, hjS, hjf⟩
    by_cases hf0R : G.endAt f 0 ∈ R
    · exact finish_touch (Finset.mem_filter.mp hf0R).2 hjS hjf (.inl rfl)
    · have hf1R : G.endAt f 1 ∈ R := by
        by_contra hf1R
        exact hfCross
          (propext ⟨fun h ↦ (hf0R h).elim, fun h ↦ (hf1R h).elim⟩)
      exact finish_touch (Finset.mem_filter.mp hf1R).2 hjS hjf (.inr rfl)

lemma CircuitDoubleCover.length_le_cotree_card_add_one_of_proper_trace_sums
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (M : CircuitDoubleCover G) {T : Finset E}
    (hpos : 0 < M.circuits.length)
    (hproper : ∀ S : Finset (Fin M.circuits.length), S.Nonempty →
      S ≠ Finset.univ → vectorFinsetSum (M.traceVector G T) S ≠ 0) :
    M.circuits.length ≤ (Finset.univ \ T).card + 1 := by
  haveI : Nonempty (Fin M.circuits.length) := Fin.pos_iff_nonempty.mp hpos
  have hle := card_le_succ_of_proper_sums (M.traceVector G T) hproper
  rwa [Fintype.card_fin, cotreeSubtype_card_eq] at hle

lemma CircuitDoubleCover.trace_sum_ne_zero_of_length_minimal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) [Nonempty V] (M : CircuitDoubleCover G)
    (hconn : Connects G Finset.univ)
    (hmin : ∀ N : CircuitDoubleCover G, M.circuits.length ≤ N.circuits.length)
    {T : Finset E} (hT : IsSpanningTree G T)
    {S : Finset (Fin M.circuits.length)}
    (hSnonempty : S.Nonempty) (hSproper : S ≠ Finset.univ) :
    vectorFinsetSum (M.traceVector G T) S ≠ 0 := by
  intro hzero
  have hempty := M.parityEdgeSet_eq_empty_of_trace_eq_zero G hT hzero
  obtain ⟨i, hiS, j, hjS, w, hwI, hwJ, hdisj⟩ :=
    M.exists_touching_selected_unselected_of_parity_empty G hconn
      hSnonempty hSproper hempty
  obtain ⟨L, hperm⟩ := M.exists_perm_get_get_to_head_of_disjoint G hdisj
  exact CircuitDoubleCover.not_mergeable_of_perm_to_head G M hmin
    hperm hdisj hwI hwJ

lemma CircuitDoubleCover.length_le_cotree_card_add_one_of_length_minimal
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) [Nonempty V] (M : CircuitDoubleCover G)
    (hconn : Connects G Finset.univ)
    (hmin : ∀ N : CircuitDoubleCover G, M.circuits.length ≤ N.circuits.length)
    {T : Finset E} (hT : IsSpanningTree G T)
    (hpos : 0 < M.circuits.length) :
    M.circuits.length ≤ (Finset.univ \ T).card + 1 := by
  exact M.length_le_cotree_card_add_one_of_proper_trace_sums G hpos
    (fun S hSnonempty hSproper ↦
      M.trace_sum_ne_zero_of_length_minimal G hconn hmin hT hSnonempty hSproper)

lemma edge_endpoint_component_left {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) {F : Finset E} {e : E} {u : V}
    (he : e ∈ F) (h : ((componentSetoid G F).r) (G.endAt e 0) u) :
    ((componentSetoid G F).r) (G.endAt e 1) u :=
  (endpoint_reachable_of_edge_mem G he).symm.trans h

lemma edge_endpoint_component_right {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) {F : Finset E} {e : E} {u : V}
    (he : e ∈ F) (h : ((componentSetoid G F).r) (G.endAt e 1) u) :
    ((componentSetoid G F).r) (G.endAt e 0) u :=
  (endpoint_reachable_of_edge_mem G he).trans h

lemma incident_edge_mem_inside_component_left {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) {F : Finset E} {e : E} {v : V}
    (he : e ∈ F) (hend : G.endAt e 0 = v) :
    e ∈ insideEdges G F (componentSetoid G F) v := by
  simp only [mem_insideEdges, he, true_and]
  constructor
  · simp [hend]
  · exact edge_endpoint_component_left G he (by simp [hend])

lemma incident_edge_mem_inside_component_right {V E : Type*} [Fintype V] [Fintype E]
    (G : OrientedMultigraph V E) {F : Finset E} {e : E} {v : V}
    (he : e ∈ F) (hend : G.endAt e 1 = v) :
    e ∈ insideEdges G F (componentSetoid G F) v := by
  simp only [mem_insideEdges, he, true_and]
  constructor
  · exact edge_endpoint_component_right G he (by simp [hend])
  · simp [hend]

lemma isEvenEdgeSet_inside_component_of_even {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq V] (G : OrientedMultigraph V E)
    {F : Finset E} (hF : IsEvenEdgeSet G F) (u : V) :
    IsEvenEdgeSet G (insideEdges G F (componentSetoid G F) u) := by
  intro v
  by_cases hv : (componentSetoid G F).r v u
  · have hsubset : insideEdges G F (componentSetoid G F) u ⊆ F := by
      intro e he
      exact ((mem_insideEdges G).mp he).1
    have hzero : ∀ x ∈ F, x ∉ insideEdges G F (componentSetoid G F) u →
        edgeIncidence G v x = 0 := by
      intro e he heNot
      have h0 : G.endAt e 0 ≠ v := by
        intro h0
        apply heNot
        apply (mem_insideEdges G).mpr
        refine ⟨he, h0 ▸ hv, ?_⟩
        exact edge_endpoint_component_left G he (h0 ▸ hv)
      have h1 : G.endAt e 1 ≠ v := by
        intro h1
        apply heNot
        apply (mem_insideEdges G).mpr
        refine ⟨he, ?_, h1 ▸ hv⟩
        exact edge_endpoint_component_right G he (h1 ▸ hv)
      simp [edgeIncidence, h0, h1]
    have hs := Finset.sum_subset hsubset hzero
    rw [hs, hF v]
  · apply Finset.sum_eq_zero
    intro e he
    have hem := (mem_insideEdges G).mp he
    have h0 : G.endAt e 0 ≠ v := by
      intro h0
      exact hv (h0 ▸ hem.2.1)
    have h1 : G.endAt e 1 ≠ v := by
      intro h1
      exact hv (h1 ▸ hem.2.2)
    simp [edgeIncidence, h0, h1]

lemma cycle_edgeSupportConnected {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : OrientedMultigraph V E) (C : Cycle G) :
    EdgeSupportConnected G C.edges := by
  intro u v hu hv
  by_contra hnot
  change ¬ ((supportGraph G) C.edges).Reachable u v at hnot
  let A := insideEdges G C.edges (componentSetoid G C.edges) u
  have hAeven : IsEvenEdgeSet G A := isEvenEdgeSet_inside_component_of_even G C.even u
  have hAsub : A ⊆ C.edges := by
    intro e he
    exact ((mem_insideEdges G).mp he).1
  have hAne : A.Nonempty := by
    rcases hu with ⟨e, he, h0 | h1⟩
    · exact ⟨e, incident_edge_mem_inside_component_left G he h0⟩
    · exact ⟨e, incident_edge_mem_inside_component_right G he h1⟩
  have hAeq : A = C.edges := C.minimal A hAne hAsub hAeven
  rcases hv with ⟨e, he, h0 | h1⟩
  · have heA : e ∈ A := by simpa [hAeq]
    have hem := (mem_insideEdges G).mp heA
    exact hnot (by simpa [h0] using hem.2.1.symm)
  · have heA : e ∈ A := by simpa [hAeq]
    have hem := (mem_insideEdges G).mp heA
    exact hnot (by simpa [h1] using hem.2.2.symm)

noncomputable def Cycle.toCircuit {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : OrientedMultigraph V E) (C : Cycle G) :
    Circuit G where
  edges := C.edges
  nonempty := C.nonempty
  even := C.even
  connected := cycle_edgeSupportConnected G C

noncomputable def CycleDoubleCover.toCircuitDoubleCover {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (C : CycleDoubleCover G) :
    CircuitDoubleCover G where
  circuits := C.cycles.map (Cycle.toCircuit G)
  coveredTwice := by
    intro e
    have hfilter (L : List (Cycle G)) :
        ((L.map (Cycle.toCircuit G)).filter fun Z ↦ e ∈ Z.edges).length =
          (L.filter fun Z ↦ e ∈ Z.edges).length := by
      induction L with
      | nil => simp
      | cons Z L ih =>
          by_cases h : e ∈ Z.edges <;> simp [Cycle.toCircuit, h, ih]
    rw [hfilter]
    exact C.coveredTwice e

theorem circuitDoubleCover_of_bridgeless
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E) (hb : Bridgeless G) :
    Nonempty (CircuitDoubleCover G) := by
  obtain ⟨C⟩ := cycleDoubleCover_of_bridgeless G hb
  exact ⟨CycleDoubleCover.toCircuitDoubleCover G C⟩

theorem OrientedPseudograph.circuitDoubleCover_of_bridgeless
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E) (hb : G.Bridgeless) :
    Nonempty G.CircuitDoubleCover := by
  have hb' :
      _root_.CycleDoubleCoverConjecture.OrientedMultigraph.Bridgeless
        G.nonloopSubgraph :=
    (G.bridgeless_nonloopSubgraph_iff).mpr hb
  exact G.exists_circuitDoubleCover_of_nonloopSubgraph
    (_root_.CycleDoubleCoverConjecture.circuitDoubleCover_of_bridgeless
      G.nonloopSubgraph hb')

theorem exists_circuitDoubleCover_length_le_cotree_card_add_one
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [Nonempty V] (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    {T : Finset E} (hT : IsSpanningTree G T) (hEpos : 0 < Fintype.card E) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ (Finset.univ \ T).card + 1 := by
  obtain ⟨M, hmin⟩ :=
    exists_length_minimal_circuitDoubleCover G
      (circuitDoubleCover_of_bridgeless G hb)
  obtain ⟨e⟩ := Fintype.card_pos_iff.mp hEpos
  have hMpos : 0 < M.circuits.length := by
    have hlen := List.length_eq_length_filter_add
      (l := M.circuits) (fun C : Circuit G ↦ decide (e ∈ C.edges))
    have hcover := M.coveredTwice e
    simp [hcover] at hlen
    omega
  exact ⟨M, M.length_le_cotree_card_add_one_of_length_minimal G hconn hmin hT hMpos⟩

theorem exists_circuitDoubleCover_length_le_cotree_card_add_one_of_connects
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    {T : Finset E} (hT : IsSpanningTree G T) (hEpos : 0 < Fintype.card E) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ (Finset.univ \ T).card + 1 := by
  haveI : Nonempty V := hconn.nonempty
  exact exists_circuitDoubleCover_length_le_cotree_card_add_one G hconn hb hT hEpos

theorem exists_circuitDoubleCover_oddVertices_bound_of_degrees_two_or_three
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : ∀ v : V, degree G v = 2 ∨ degree G v = 3) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  by_cases hE : Fintype.card E = 0
  · exact exists_circuitDoubleCover_oddVertices_bound_of_edge_card_eq_zero G hE
  · haveI : Nonempty V := hconn.nonempty
    obtain ⟨T, _, hT⟩ :=
      exists_isSpanningTree_subset_of_connects G Finset.univ hconn
    have hEpos : 0 < Fintype.card E := Nat.pos_of_ne_zero hE
    obtain ⟨M, hM⟩ :=
      exists_circuitDoubleCover_length_le_cotree_card_add_one
        G hconn hb hT hEpos
    refine ⟨M, hM.trans ?_⟩
    have hcotree :=
      two_mul_cotree_card_eq_oddVertices_card_add_two_of_degrees_two_or_three
        G hT hdeg
    obtain ⟨a, ha⟩ := even_oddVertices_card G
    have hcotree' : 2 * (Finset.univ \ T).card = a + a + 2 := by
      simpa [ha] using hcotree
    rw [ha]
    have hdiv : (a + a) / 2 = a := by omega
    rw [hdiv]
    omega

theorem exists_circuitDoubleCover_oddVertices_bound_of_degrees_between_two_three
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hlow : ∀ v : V, 2 ≤ degree G v)
    (hhigh : ∀ v : V, degree G v ≤ 3) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  apply exists_circuitDoubleCover_oddVertices_bound_of_degrees_two_or_three
    G hconn hb
  intro v
  have hlo := hlow v
  have hhi := hhigh v
  omega

lemma two_le_degree_of_connects_bridgeless_of_oddVertices_nonempty
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hodd : (oddVertices G).Nonempty) (v : V) :
    2 ≤ degree G v := by
  rcases hodd with ⟨w, hw⟩
  by_cases hwv : w = v
  · subst w
    have hvOdd : Odd (degree G v) := by
      simpa [oddVertices] using hw
    have hne0 : degree G v ≠ 0 := by
      intro hzero
      rw [hzero] at hvOdd
      exact (by norm_num : ¬ Odd 0) hvOdd
    have hne1 : degree G v ≠ 1 := degree_ne_one_of_bridgeless hb v
    omega
  · have hproper : ({v} : Finset V) ≠ Finset.univ := by
      intro h
      have hwSingleton : w ∈ ({v} : Finset V) := by
        rw [h]
        exact Finset.mem_univ w
      exact hwv (Finset.mem_singleton.mp hwSingleton)
    have hcut :=
      two_le_cut_card_of_connects_bridgeless G hconn hb
        (Finset.singleton_nonempty v) hproper
    simpa [cut_card_singleton_eq_degree] using hcut

theorem exists_circuitDoubleCover_oddVertices_bound_of_degree_le_three
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hhigh : ∀ v : V, degree G v ≤ 3) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  by_cases hodd : (oddVertices G).Nonempty
  · exact exists_circuitDoubleCover_oddVertices_bound_of_degrees_between_two_three
      G hconn hb
      (two_le_degree_of_connects_bridgeless_of_oddVertices_nonempty
        G hconn hb hodd)
      hhigh
  · have hoddEmpty : oddVertices G = ∅ := by
      ext v
      constructor
      · intro hv
        exact (hodd ⟨v, hv⟩).elim
      · intro hv
        cases hv
    exact exists_circuitDoubleCover_oddVertices_bound_of_oddVertices_eq_empty
      G hoddEmpty hconn

theorem exists_circuitDoubleCover_vertex_bound_of_degrees_two_or_three
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hdeg : ∀ v : V, degree G v = 2 ∨ degree G v = 3)
    (hlarge : 6 ≤ Fintype.card V) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  exact exists_circuitDoubleCover_length_le_vertex_card_sub_one_of_oddVertices_bound
    G hlarge
    (exists_circuitDoubleCover_oddVertices_bound_of_degrees_two_or_three
      G hconn hb hdeg)

theorem exists_circuitDoubleCover_vertex_bound_of_degrees_between_two_three
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hlow : ∀ v : V, 2 ≤ degree G v)
    (hhigh : ∀ v : V, degree G v ≤ 3)
    (hlarge : 6 ≤ Fintype.card V) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  exact exists_circuitDoubleCover_length_le_vertex_card_sub_one_of_oddVertices_bound
    G hlarge
    (exists_circuitDoubleCover_oddVertices_bound_of_degrees_between_two_three
      G hconn hb hlow hhigh)

theorem exists_circuitDoubleCover_vertex_bound_of_degree_le_three
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hhigh : ∀ v : V, degree G v ≤ 3)
    (hlarge : 6 ≤ Fintype.card V) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  exact exists_circuitDoubleCover_length_le_vertex_card_sub_one_of_oddVertices_bound
    G hlarge
    (exists_circuitDoubleCover_oddVertices_bound_of_degree_le_three
      G hconn hb hhigh)

theorem exists_circuitDoubleCover_oddVertices_bound_of_reducingSplitHighDegree
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hsplit : ∀ {E' : Type u} [Fintype E'] [DecidableEq E']
      (H : OrientedMultigraph V E'),
        Connects H Finset.univ → Bridgeless H →
          (∃ v : V, 4 ≤ degree H v) →
            ∃ v : V, ∃ S : ReducingSplit H v, Bridgeless S.graph) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' = n →
        (H : OrientedMultigraph V E') →
          Connects H Finset.univ → Bridgeless H →
            ∃ M : CircuitDoubleCover H,
              M.circuits.length ≤ (oddVertices H).card / 2 + 2
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on (p := P) n ?_
    intro n ih E' _ _ hcard H hconnH hbH
    by_cases hhigh : ∀ v : V, degree H v ≤ 3
    · exact exists_circuitDoubleCover_oddVertices_bound_of_degree_le_three
        H hconnH hbH hhigh
    · have hexHigh : ∃ v : V, 4 ≤ degree H v := by
        push Not at hhigh
        rcases hhigh with ⟨v, hv⟩
        exact ⟨v, by omega⟩
      obtain ⟨v, S, hbS⟩ := hsplit H hconnH hbH hexHigh
      exact S.oddVertices_bound_of_induction hconnH hbS (by
        intro E'' _ _ hlt H' hconn' hb'
        exact ih (Fintype.card E'') (by simpa [hcard] using hlt)
          rfl H' hconn' hb')
  exact hP (Fintype.card E) rfl G hconn hb

theorem exists_circuitDoubleCover_vertex_bound_of_reducingSplitHighDegree
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hlarge : 6 ≤ Fintype.card V)
    (hsplit : ∀ {E' : Type u} [Fintype E'] [DecidableEq E']
      (H : OrientedMultigraph V E'),
        Connects H Finset.univ → Bridgeless H →
          (∃ v : V, 4 ≤ degree H v) →
            ∃ v : V, ∃ S : ReducingSplit H v, Bridgeless S.graph) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  exact exists_circuitDoubleCover_length_le_vertex_card_sub_one_of_oddVertices_bound
    G hlarge
    (exists_circuitDoubleCover_oddVertices_bound_of_reducingSplitHighDegree
      G hconn hb hsplit)

theorem exists_circuitDoubleCover_oddVertices_bound_of_reducingSplitWithLoopsHighDegree
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hsplit : ∀ {E' : Type u} [Fintype E'] [DecidableEq E']
      (H : OrientedMultigraph V E'),
        Connects H Finset.univ → Bridgeless H →
          (∃ v : V, 4 ≤ degree H v) →
            ∃ v : V, ∃ S : ReducingSplitWithLoops H v,
              S.graph.Connects Finset.univ ∧ S.graph.Bridgeless) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ {E' : Type u} [Fintype E'] [DecidableEq E'],
      Fintype.card E' = n →
        (H : OrientedMultigraph V E') →
          Connects H Finset.univ → Bridgeless H →
            ∃ M : CircuitDoubleCover H,
              M.circuits.length ≤ (oddVertices H).card / 2 + 2
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on (p := P) n ?_
    intro n ih E' _ _ hcard H hconnH hbH
    by_cases hhigh : ∀ v : V, degree H v ≤ 3
    · exact exists_circuitDoubleCover_oddVertices_bound_of_degree_le_three
        H hconnH hbH hhigh
    · have hexHigh : ∃ v : V, 4 ≤ degree H v := by
        push Not at hhigh
        rcases hhigh with ⟨v, hv⟩
        exact ⟨v, by omega⟩
      obtain ⟨v, S, _hconnS, hbS⟩ := hsplit H hconnH hbH hexHigh
      exact S.oddVertices_bound_of_induction_absorb_loop hconnH hbS (by
        intro E'' _ _ hlt H' hconn' hb'
        exact ih (Fintype.card E'') (by simpa [hcard] using hlt)
          rfl H' hconn' hb')
  exact hP (Fintype.card E) rfl G hconn hb

theorem exists_circuitDoubleCover_vertex_bound_of_reducingSplitWithLoopsHighDegree
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hlarge : 6 ≤ Fintype.card V)
    (hsplit : ∀ {E' : Type u} [Fintype E'] [DecidableEq E']
      (H : OrientedMultigraph V E'),
        Connects H Finset.univ → Bridgeless H →
          (∃ v : V, 4 ≤ degree H v) →
            ∃ v : V, ∃ S : ReducingSplitWithLoops H v,
              S.graph.Connects Finset.univ ∧ S.graph.Bridgeless) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  exact exists_circuitDoubleCover_length_le_vertex_card_sub_one_of_oddVertices_bound
    G hlarge
    (exists_circuitDoubleCover_oddVertices_bound_of_reducingSplitWithLoopsHighDegree
      G hconn hb hsplit)

theorem exists_circuitDoubleCover_oddVertices_bound
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  exact exists_circuitDoubleCover_oddVertices_bound_of_reducingSplitWithLoopsHighDegree
    G hconn hb
    (fun H hconnH hbH hhigh ↦
      exists_reducingSplitWithLoops_of_high_degree H hconnH hbH hhigh)

theorem simpleGraph_circuitDoubleCover_oddVertices_bound
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ D : SimpleGraphCircuitDoubleCover G,
      D.circuits.length ≤
        (oddVertices ((simpleGraphAsGraph G).toOrientedMultigraph
          (simpleGraphAsGraph_loopless G))).card / 2 + 2 := by
  let H := simpleGraphAsGraph G
  let O := H.toOrientedMultigraph (simpleGraphAsGraph_loopless G)
  have hconnO : Connects O Finset.univ :=
    simpleGraphAsGraph_toOrientedMultigraph_connects G hconn
  have hbO : Bridgeless O :=
    H.toOrientedMultigraph_bridgeless (simpleGraphAsGraph_loopless G)
      (simpleGraphAsGraph_bridgeless G hb)
  obtain ⟨M, hM⟩ := exists_circuitDoubleCover_oddVertices_bound O hconnO hbO
  refine ⟨CircuitDoubleCover.toSimpleGraphCircuitDoubleCover G M, ?_⟩
  simpa [O, H] using hM

theorem simpleGraph_smallCircuitDoubleCoverConjecture_of_oddVertices_bound
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    (hbound :
      (oddVertices ((simpleGraphAsGraph G).toOrientedMultigraph
        (simpleGraphAsGraph_loopless G))).card / 2 + 2 ≤
          Fintype.card V - 1) :
    ∃ D : SimpleGraphCircuitDoubleCover G, D.IsSmall := by
  obtain ⟨D, hD⟩ := simpleGraph_circuitDoubleCover_oddVertices_bound G hconn hb
  exact ⟨D, by
    exact le_trans hD hbound⟩

theorem simpleGraph_smallCircuitDoubleCoverConjecture_of_card_eq_five
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    (hcard : Fintype.card V = 5) :
    ∃ D : SimpleGraphCircuitDoubleCover G, D.IsSmall := by
  apply simpleGraph_smallCircuitDoubleCoverConjecture_of_oddVertices_bound G hconn hb
  let H := simpleGraphAsGraph G
  let O := H.toOrientedMultigraph (simpleGraphAsGraph_loopless G)
  change (oddVertices O).card / 2 + 2 ≤ Fintype.card V - 1
  have hcardH : Fintype.card H.Vertex = Fintype.card V := by
    simp [H, simpleGraphAsGraph, Graph.Vertex]
  have hqle : (oddVertices O).card ≤ Fintype.card V := by
    have h := oddVertices_card_le_vertex_card O
    omega
  rcases even_oddVertices_card O with ⟨q, hq⟩
  omega

theorem simpleGraph_smallCircuitDoubleCoverConjecture_of_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    (hcard : Fintype.card V = 3) :
    ∃ D : SimpleGraphCircuitDoubleCover G, D.IsSmall := by
  classical
  apply simpleGraph_smallCircuitDoubleCoverConjecture_of_oddVertices_bound G hconn hb
  let H := simpleGraphAsGraph G
  let O := H.toOrientedMultigraph (simpleGraphAsGraph_loopless G)
  change (oddVertices O).card / 2 + 2 ≤ Fintype.card V - 1
  have hqzero : (oddVertices O).card = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxOdd : Odd (degree O x) := by
      simpa [oddVertices] using hx
    letI : DecidableRel G.Adj := Classical.decRel _
    have hpar :=
      simpleGraphAsGraph_toOrientedMultigraph_degree_parity G x.1
    have hxOdd' :
        Odd (degree O
          (⟨x.1, Set.mem_univ x.1⟩ : H.Vertex)) := by
      simpa [H, O] using hxOdd
    have hoddG : Odd (G.degree x.1) := by
      exact (odd_iff_of_natCast_f2_eq (by
        simpa [H, O] using hpar)).mp hxOdd'
    have hlt : G.degree x.1 < Fintype.card V :=
      G.degree_lt_card_verts x.1
    have hle : G.degree x.1 ≤ 2 := by omega
    have hne :
        G.degree x.1 ≠ 1 :=
      simpleGraph_degree_ne_one_of_forall_not_isBridge G hb x.1
    rcases hoddG with ⟨k, hk⟩
    have hdeg : G.degree x.1 = 1 := by omega
    exact hne hdeg
  rw [hqzero, hcard]

theorem simpleGraph_smallCircuitDoubleCoverConjecture_of_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (_hconn : G.Connected) (_hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    (hcard : Fintype.card V = 1) :
    ∃ D : SimpleGraphCircuitDoubleCover G, D.IsSmall := by
  classical
  haveI : Subsingleton V :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  let D : SimpleGraphCircuitDoubleCover G :=
    { circuits := []
      isCircuit := by simp
      coveredTwice := by
        intro e he
        exfalso
        revert he
        refine Sym2.inductionOn e ?_
        intro x y he
        exact G.not_isDiag_of_mem_edgeSet he (by
          rw [Sym2.mk_isDiag_iff]
          exact Subsingleton.elim x y) }
  refine ⟨D, ?_⟩
  simp [D, SimpleGraphCircuitDoubleCover.IsSmall, hcard]

theorem simpleGraph_smallCircuitDoubleCoverConjecture_of_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    (hcard : Fintype.card V = 2) :
    ∃ D : SimpleGraphCircuitDoubleCover G, D.IsSmall := by
  classical
  exfalso
  letI : DecidableRel G.Adj := Classical.decRel _
  have huniv : (Finset.univ : Finset V).card = 2 := by
    simpa using hcard
  obtain ⟨x, y, hxy, _⟩ := Finset.card_eq_two.mp huniv
  haveI : Nontrivial V := ⟨⟨x, y, hxy⟩⟩
  have hpos : 0 < G.degree x :=
    hconn.preconnected.degree_pos_of_nontrivial x
  have hlt : G.degree x < Fintype.card V :=
    G.degree_lt_card_verts x
  have hdeg : G.degree x = 1 := by omega
  exact (simpleGraph_degree_ne_one_of_forall_not_isBridge G hb x) hdeg

def topHomOfEquiv {α β : Type*} (e : α ≃ β) :
    (⊤ : SimpleGraph α) →g (⊤ : SimpleGraph β) where
  toFun := e
  map_rel' := by
    intro a b h
    rw [SimpleGraph.top_adj] at h ⊢
    exact e.injective.ne h

@[simp]
lemma topHomOfEquiv_apply {α β : Type*} (e : α ≃ β) (x : α) :
    topHomOfEquiv e x = e x := rfl

def top4Walk01230 :
    (⊤ : SimpleGraph (Fin 4)).Walk (0 : Fin 4) (0 : Fin 4) :=
  SimpleGraph.Walk.cons' (0 : Fin 4) (1 : Fin 4) (0 : Fin 4)
    (by decide)
    (SimpleGraph.Walk.cons' (1 : Fin 4) (2 : Fin 4) (0 : Fin 4)
      (by decide)
      (SimpleGraph.Walk.cons' (2 : Fin 4) (3 : Fin 4) (0 : Fin 4)
        (by decide)
        (SimpleGraph.Walk.cons' (3 : Fin 4) (0 : Fin 4) (0 : Fin 4)
          (by decide)
          SimpleGraph.Walk.nil)))

lemma top4Walk01230_isCircuit : top4Walk01230.IsCircuit := by
  rw [SimpleGraph.Walk.isCircuit_def, SimpleGraph.Walk.isTrail_def]
  constructor
  · decide
  · intro h
    cases h

def top4Walk01320 :
    (⊤ : SimpleGraph (Fin 4)).Walk (0 : Fin 4) (0 : Fin 4) :=
  SimpleGraph.Walk.cons' (0 : Fin 4) (1 : Fin 4) (0 : Fin 4)
    (by decide)
    (SimpleGraph.Walk.cons' (1 : Fin 4) (3 : Fin 4) (0 : Fin 4)
      (by decide)
      (SimpleGraph.Walk.cons' (3 : Fin 4) (2 : Fin 4) (0 : Fin 4)
        (by decide)
        (SimpleGraph.Walk.cons' (2 : Fin 4) (0 : Fin 4) (0 : Fin 4)
          (by decide)
          SimpleGraph.Walk.nil)))

def top4Walk02130 :
    (⊤ : SimpleGraph (Fin 4)).Walk (0 : Fin 4) (0 : Fin 4) :=
  SimpleGraph.Walk.cons' (0 : Fin 4) (2 : Fin 4) (0 : Fin 4)
    (by decide)
    (SimpleGraph.Walk.cons' (2 : Fin 4) (1 : Fin 4) (0 : Fin 4)
      (by decide)
      (SimpleGraph.Walk.cons' (1 : Fin 4) (3 : Fin 4) (0 : Fin 4)
        (by decide)
        (SimpleGraph.Walk.cons' (3 : Fin 4) (0 : Fin 4) (0 : Fin 4)
          (by decide)
          SimpleGraph.Walk.nil)))

lemma top4Walk01320_isCircuit : top4Walk01320.IsCircuit := by
  rw [SimpleGraph.Walk.isCircuit_def, SimpleGraph.Walk.isTrail_def]
  constructor
  · decide
  · intro h
    cases h

lemma top4Walk02130_isCircuit : top4Walk02130.IsCircuit := by
  rw [SimpleGraph.Walk.isCircuit_def, SimpleGraph.Walk.isTrail_def]
  constructor
  · decide
  · intro h
    cases h

def top4CircuitCoverFin :
    SimpleGraphCircuitDoubleCover (⊤ : SimpleGraph (Fin 4)) where
  circuits :=
    [⟨(0 : Fin 4), top4Walk01230⟩,
     ⟨(0 : Fin 4), top4Walk01320⟩,
     ⟨(0 : Fin 4), top4Walk02130⟩]
  isCircuit := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact top4Walk01230_isCircuit
    · exact top4Walk01320_isCircuit
    · exact top4Walk02130_isCircuit
  coveredTwice := by
    decide

lemma sym2_map_equiv_symm_map_eq {α β : Type*} (e : α ≃ β) (x : Sym2 β) :
    Sym2.map e (Sym2.map e.symm x) = x := by
  refine Sym2.inductionOn x ?_
  intro a b
  simp [Sym2.map_mk]

lemma sym2_map_equiv_map_symm_eq {α β : Type*} (e : α ≃ β) (x : Sym2 α) :
    Sym2.map e.symm (Sym2.map e x) = x := by
  refine Sym2.inductionOn x ?_
  intro a b
  simp [Sym2.map_mk]

lemma mem_edges_map_completeGraph_equiv {α β : Type*}
    (e : α ≃ β) {u v : α} (p : (⊤ : SimpleGraph α).Walk u v)
    {x : Sym2 β} :
    x ∈ (p.map (topHomOfEquiv e)).edges ↔
      Sym2.map e.symm x ∈ p.edges := by
  rw [SimpleGraph.Walk.edges_map]
  constructor
  · intro hx
    rcases List.mem_map.mp hx with ⟨y, hy, hyx⟩
    have hyx' : Sym2.map e y = x := by
      simpa [topHomOfEquiv] using hyx
    have hpre : Sym2.map e.symm x = y := by
      calc
        Sym2.map e.symm x = Sym2.map e.symm (Sym2.map e y) := by rw [hyx']
        _ = y := sym2_map_equiv_map_symm_eq e y
    simpa [hpre]
  · intro hx
    exact List.mem_map.mpr
      ⟨Sym2.map e.symm x, hx, by
        simpa [topHomOfEquiv] using sym2_map_equiv_symm_map_eq e x⟩

noncomputable def top4CircuitCoverOfEquiv {V : Type*} [DecidableEq V]
    (e : Fin 4 ≃ V) :
    SimpleGraphCircuitDoubleCover (⊤ : SimpleGraph V) where
  circuits := top4CircuitCoverFin.circuits.map fun p ↦
    ⟨e p.1, p.2.map (topHomOfEquiv e)⟩
  isCircuit := by
    intro p hp
    rw [List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩
    exact (top4CircuitCoverFin.isCircuit q hq).map e.injective
  coveredTwice := by
    intro x hx
    have hmem (p : Σ v, (⊤ : SimpleGraph (Fin 4)).Walk v v) :
        x ∈ (p.2.map (topHomOfEquiv e)).edges ↔
          Sym2.map e.symm x ∈ p.2.edges :=
      mem_edges_map_completeGraph_equiv e p.2
    have hpre : Sym2.map e.symm x ∈ (⊤ : SimpleGraph (Fin 4)).edgeSet := by
      revert hx
      refine Sym2.inductionOn x ?_
      intro a b hx
      rw [Sym2.map_mk]
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
      have hab : a ≠ b := by
        simpa [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] using hx
      intro h
      exact hab (by
        simpa using congrArg e h)
    have hfilter :
        ((top4CircuitCoverFin.circuits.map fun p : Σ v,
            (⊤ : SimpleGraph (Fin 4)).Walk v v ↦
              (⟨e p.1, p.2.map (topHomOfEquiv e)⟩ :
                    Σ v, (⊤ : SimpleGraph V).Walk v v)).filter
          fun p ↦ x ∈ p.2.edges).length =
        (top4CircuitCoverFin.circuits.filter
          fun p ↦ Sym2.map e.symm x ∈ p.2.edges).length := by
      induction top4CircuitCoverFin.circuits with
      | nil => simp
      | cons p L ih =>
          by_cases hp : x ∈ (p.2.map (topHomOfEquiv e)).edges
          · have hp' : Sym2.map e.symm x ∈ p.2.edges := (hmem p).mp hp
            have hpHead :
                x ∈ (⟨e p.1, p.2.map (topHomOfEquiv e)⟩ :
                  Σ v, (⊤ : SimpleGraph V).Walk v v).2.edges := hp
            simp [hpHead, hp', ih]
          · have hp' : Sym2.map e.symm x ∉ p.2.edges :=
              fun h ↦ hp ((hmem p).mpr h)
            have hpHead :
                x ∉ (⟨e p.1, p.2.map (topHomOfEquiv e)⟩ :
                  Σ v, (⊤ : SimpleGraph V).Walk v v).2.edges := hp
            simp [hpHead, hp', ih]
    rw [hfilter]
    exact top4CircuitCoverFin.coveredTwice (Sym2.map e.symm x) hpre

@[simp]
lemma top4CircuitCoverOfEquiv_length {V : Type*} [DecidableEq V] (e : Fin 4 ≃ V) :
    (top4CircuitCoverOfEquiv e).circuits.length = 3 := by
  simp [top4CircuitCoverOfEquiv, top4CircuitCoverFin]

theorem simpleGraph_eq_top_of_card_eq_four_of_oddVertices_card_eq_four
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    (hcard : Fintype.card V = 4)
    (hodd :
      (oddVertices ((simpleGraphAsGraph G).toOrientedMultigraph
        (simpleGraphAsGraph_loopless G))).card = 4) :
    G = ⊤ := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  let H := simpleGraphAsGraph G
  let O := H.toOrientedMultigraph (simpleGraphAsGraph_loopless G)
  have hoddCard :
      (oddVertices O).card = Fintype.card H.Vertex := by
    have hcardH : Fintype.card H.Vertex = Fintype.card V := by
      simp [H, simpleGraphAsGraph, Graph.Vertex]
    simpa [O, H, hcardH, hcard] using hodd
  have hoddUniv : oddVertices O = Finset.univ :=
    Finset.eq_univ_of_card (oddVertices O) hoddCard
  rw [SimpleGraph.eq_top_iff_forall_isUniversal]
  intro v
  have hvOddO :
      Odd (degree O (⟨v, Set.mem_univ v⟩ : H.Vertex)) := by
    have hvMem : (⟨v, Set.mem_univ v⟩ : H.Vertex) ∈ oddVertices O := by
      rw [hoddUniv]
      exact Finset.mem_univ _
    simpa [oddVertices] using hvMem
  have hpar :=
    simpleGraphAsGraph_toOrientedMultigraph_degree_parity G v
  have hvOddG : Odd (G.degree v) := by
    exact (odd_iff_of_natCast_f2_eq (by
      simpa [H, O] using hpar)).mp hvOddO
  have hlt : G.degree v < Fintype.card V :=
    G.degree_lt_card_verts v
  have hne : G.degree v ≠ 1 :=
    simpleGraph_degree_ne_one_of_forall_not_isBridge G hb v
  rcases hvOddG with ⟨k, hk⟩
  have hdeg : G.degree v = Fintype.card V - 1 := by
    omega
  exact (G.degree_eq_card_sub_one v).mp hdeg

theorem simpleGraph_smallCircuitDoubleCoverConjecture_of_card_eq_four_of_odd_eq_four
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (_hconn : G.Connected) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    (hcard : Fintype.card V = 4)
    (hodd :
      (oddVertices ((simpleGraphAsGraph G).toOrientedMultigraph
        (simpleGraphAsGraph_loopless G))).card = 4) :
    ∃ D : SimpleGraphCircuitDoubleCover G, D.IsSmall := by
  classical
  have htop :
      G = ⊤ :=
    simpleGraph_eq_top_of_card_eq_four_of_oddVertices_card_eq_four G hb hcard hodd
  subst G
  let e : Fin 4 ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨top4CircuitCoverOfEquiv e, ?_⟩
  simp [SimpleGraphCircuitDoubleCover.IsSmall, hcard]

theorem simpleGraph_smallCircuitDoubleCoverConjecture_of_card_eq_four_of_odd_ne_four
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    (hcard : Fintype.card V = 4)
    (hodd_ne :
      (oddVertices ((simpleGraphAsGraph G).toOrientedMultigraph
        (simpleGraphAsGraph_loopless G))).card ≠ 4) :
    ∃ D : SimpleGraphCircuitDoubleCover G, D.IsSmall := by
  apply simpleGraph_smallCircuitDoubleCoverConjecture_of_oddVertices_bound G hconn hb
  let H := simpleGraphAsGraph G
  let O := H.toOrientedMultigraph (simpleGraphAsGraph_loopless G)
  change (oddVertices O).card / 2 + 2 ≤ Fintype.card V - 1
  have hcardH : Fintype.card H.Vertex = Fintype.card V := by
    simp [H, simpleGraphAsGraph, Graph.Vertex]
  have hqle : (oddVertices O).card ≤ 4 := by
    have h := oddVertices_card_le_vertex_card O
    omega
  have hqne : (oddVertices O).card ≠ 4 := by
    simpa [O, H] using hodd_ne
  have hqeven := even_oddVertices_card O
  rcases hqeven with ⟨q, hq⟩
  have hqle_two : (oddVertices O).card ≤ 2 := by omega
  omega

theorem exists_circuitDoubleCover_vertex_bound
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hlarge : 6 ≤ Fintype.card V) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  exact exists_circuitDoubleCover_length_le_vertex_card_sub_one_of_oddVertices_bound
    G hlarge (exists_circuitDoubleCover_oddVertices_bound G hconn hb)

theorem simpleGraph_smallCircuitDoubleCoverConjecture_of_six_le_card
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    (hlarge : 6 ≤ Fintype.card V) :
    ∃ D : SimpleGraphCircuitDoubleCover G, D.IsSmall := by
  let H := simpleGraphAsGraph G
  let O := H.toOrientedMultigraph (simpleGraphAsGraph_loopless G)
  have hconnO : Connects O Finset.univ :=
    simpleGraphAsGraph_toOrientedMultigraph_connects G hconn
  have hbO : Bridgeless O :=
    H.toOrientedMultigraph_bridgeless (simpleGraphAsGraph_loopless G)
      (simpleGraphAsGraph_bridgeless G hb)
  have hcardH : Fintype.card H.Vertex = Fintype.card V := by
    simp [H, simpleGraphAsGraph, Graph.Vertex]
  have hlargeO : 6 ≤ Fintype.card H.Vertex := by
    simpa [hcardH] using hlarge
  obtain ⟨M, hM⟩ := exists_circuitDoubleCover_vertex_bound O hconnO hbO hlargeO
  have hM' : M.circuits.length ≤ Fintype.card V - 1 := by
    simpa [hcardH] using hM
  refine ⟨CircuitDoubleCover.toSimpleGraphCircuitDoubleCover G M, ?_⟩
  simpa [SimpleGraphCircuitDoubleCover.IsSmall]
    using hM'

theorem simpleGraph_smallCircuitDoubleCoverConjecture
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ D : SimpleGraphCircuitDoubleCover G, D.IsSmall := by
  classical
  by_cases hlarge : 6 ≤ Fintype.card V
  · exact simpleGraph_smallCircuitDoubleCoverConjecture_of_six_le_card
      G hconn hb hlarge
  · have hle : Fintype.card V ≤ 5 := by omega
    have hpos : 0 < Fintype.card V :=
      Fintype.card_pos_iff.mpr hconn.nonempty
    have hcases :
        Fintype.card V = 1 ∨ Fintype.card V = 2 ∨
          Fintype.card V = 3 ∨ Fintype.card V = 4 ∨
            Fintype.card V = 5 := by
      omega
    rcases hcases with hcard | hcard | hcard | hcard | hcard
    · exact simpleGraph_smallCircuitDoubleCoverConjecture_of_card_eq_one
        G hconn hb hcard
    · exact simpleGraph_smallCircuitDoubleCoverConjecture_of_card_eq_two
        G hconn hb hcard
    · exact simpleGraph_smallCircuitDoubleCoverConjecture_of_card_eq_three
        G hconn hb hcard
    · by_cases hodd :
        (oddVertices ((simpleGraphAsGraph G).toOrientedMultigraph
          (simpleGraphAsGraph_loopless G))).card = 4
      · exact simpleGraph_smallCircuitDoubleCoverConjecture_of_card_eq_four_of_odd_eq_four
          G hconn hb hcard hodd
      · exact simpleGraph_smallCircuitDoubleCoverConjecture_of_card_eq_four_of_odd_ne_four
          G hconn hb hcard hodd
    · exact simpleGraph_smallCircuitDoubleCoverConjecture_of_card_eq_five
        G hconn hb hcard

theorem exists_circuitDoubleCover_oddVertices_bound_of_localNonloopSplitHighDegree
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hsplit : ∀ {E' : Type u} [Fintype E'] [DecidableEq E']
      (H : OrientedMultigraph V E') (v : V),
        Connects H Finset.univ → Bridgeless H → 4 ≤ degree H v →
          ∃ e f g k : E',
            e ≠ f ∧ IsIncident H v e ∧ IsIncident H v f ∧
            (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
            IsIncident H v g ∧ IsIncident H v k ∧
            otherEndpoint H v e ≠ otherEndpoint H v f ∧
            IsFleischnerAdmissibleSplitWithLoops H v e f) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  apply exists_circuitDoubleCover_oddVertices_bound_of_reducingSplitHighDegree
    G hconn hb
  intro E' _ _ H hconnH hbH hexHigh
  rcases hexHigh with ⟨v, hv⟩
  obtain ⟨S, _hconnS, hbS⟩ :=
    fleischner_splitting_lemma_noLoops_of_local_pair H hconnH
      (hsplit H v hconnH hbH hv)
  exact ⟨v, S, hbS⟩

theorem exists_circuitDoubleCover_vertex_bound_of_localNonloopSplitHighDegree
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hlarge : 6 ≤ Fintype.card V)
    (hsplit : ∀ {E' : Type u} [Fintype E'] [DecidableEq E']
      (H : OrientedMultigraph V E') (v : V),
        Connects H Finset.univ → Bridgeless H → 4 ≤ degree H v →
          ∃ e f g k : E',
            e ≠ f ∧ IsIncident H v e ∧ IsIncident H v f ∧
            (g ≠ e ∧ g ≠ f) ∧ (k ≠ e ∧ k ≠ f) ∧ g ≠ k ∧
            IsIncident H v g ∧ IsIncident H v k ∧
            otherEndpoint H v e ≠ otherEndpoint H v f ∧
            IsFleischnerAdmissibleSplitWithLoops H v e f) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  exact exists_circuitDoubleCover_length_le_vertex_card_sub_one_of_oddVertices_bound
    G hlarge
    (exists_circuitDoubleCover_oddVertices_bound_of_localNonloopSplitHighDegree
      G hconn hb hsplit)

theorem exists_circuitDoubleCover_oddVertices_bound_of_noParallelHighDegree
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hparallel : ∀ {E' : Type u} [Fintype E'] [DecidableEq E']
      (H : OrientedMultigraph V E') (v : V),
        Connects H Finset.univ → Bridgeless H → 4 ≤ degree H v →
          ∀ {e f : E'}, e ≠ f → IsIncident H v e → IsIncident H v f →
            otherEndpoint H v e ≠ otherEndpoint H v f) :
    ∃ M : CircuitDoubleCover G,
      M.circuits.length ≤ (oddVertices G).card / 2 + 2 := by
  exact exists_circuitDoubleCover_oddVertices_bound_of_localNonloopSplitHighDegree
    G hconn hb
    (fun H v hconnH hbH hv ↦
      exists_fleischner_admissible_nonloop_local_pair_of_no_parallel_at_vertex
        H hconnH hbH hv (hparallel H v hconnH hbH hv))

theorem exists_circuitDoubleCover_vertex_bound_of_noParallelHighDegree
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedMultigraph V E)
    (hconn : Connects G Finset.univ) (hb : Bridgeless G)
    (hlarge : 6 ≤ Fintype.card V)
    (hparallel : ∀ {E' : Type u} [Fintype E'] [DecidableEq E']
      (H : OrientedMultigraph V E') (v : V),
        Connects H Finset.univ → Bridgeless H → 4 ≤ degree H v →
          ∀ {e f : E'}, e ≠ f → IsIncident H v e → IsIncident H v f →
            otherEndpoint H v e ≠ otherEndpoint H v f) :
    ∃ M : CircuitDoubleCover G, M.circuits.length ≤ Fintype.card V - 1 := by
  exact exists_circuitDoubleCover_length_le_vertex_card_sub_one_of_oddVertices_bound
    G hlarge
    (exists_circuitDoubleCover_oddVertices_bound_of_noParallelHighDegree
      G hconn hb hparallel)

theorem OrientedPseudograph.exists_circuitDoubleCover_length_le_nonloop_cotree_add_loops
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E)
    (hconn : G.Connects Finset.univ) (hb : G.Bridgeless)
    {T : Finset G.NonloopEdge} (hT : IsSpanningTree G.nonloopSubgraph T)
    (hEpos : 0 < Fintype.card G.NonloopEdge) :
    ∃ M : G.CircuitDoubleCover,
      M.circuits.length ≤ (Finset.univ \ T).card + 1 + G.loopCircuitList.length := by
  have hconn' :
      _root_.CycleDoubleCoverConjecture.Connects G.nonloopSubgraph Finset.univ :=
    (G.connects_nonloopSubgraph_univ_iff).mpr hconn
  have hb' :
      _root_.CycleDoubleCoverConjecture.OrientedMultigraph.Bridgeless
        G.nonloopSubgraph :=
    (G.bridgeless_nonloopSubgraph_iff).mpr hb
  obtain ⟨M, hM⟩ :=
    exists_circuitDoubleCover_length_le_cotree_card_add_one_of_connects
      G.nonloopSubgraph hconn' hb' hT hEpos
  apply G.exists_circuitDoubleCover_length_le_of_nonloopSubgraph
  exact ⟨M, by omega⟩

theorem OrientedPseudograph.exists_circuitDoubleCover_length_le_nonloop_cotree_add_two_mul_loops
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : OrientedPseudograph V E)
    (hconn : G.Connects Finset.univ) (hb : G.Bridgeless)
    {T : Finset G.NonloopEdge} (hT : IsSpanningTree G.nonloopSubgraph T)
    (hEpos : 0 < Fintype.card G.NonloopEdge) :
    ∃ M : G.CircuitDoubleCover,
      M.circuits.length ≤
        (Finset.univ \ T).card + 1 + 2 * Fintype.card G.LoopEdge := by
  obtain ⟨M, hM⟩ :=
    G.exists_circuitDoubleCover_length_le_nonloop_cotree_add_loops
      hconn hb hT hEpos
  refine ⟨M, ?_⟩
  simpa [G.loopCircuitList_length] using hM

theorem CubicGraph.exists_circuitDoubleCover_two_mul_length_le_vertex_card_add_four
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [Nonempty V] (K : CubicGraph V E)
    (hconn : Connects K.toOrientedMultigraph Finset.univ)
    (hb : Bridgeless K.toOrientedMultigraph) :
    ∃ M : CircuitDoubleCover K.toOrientedMultigraph,
      2 * M.circuits.length ≤ Fintype.card V + 4 := by
  let G := K.toOrientedMultigraph
  obtain ⟨M, hmin⟩ :=
    exists_length_minimal_circuitDoubleCover G
      (circuitDoubleCover_of_bridgeless G hb)
  obtain ⟨T, _, hT⟩ := (exists_isSpanningTree_subset_of_connects G) _ hconn
  have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  have hEeq := K.two_mul_edge_card_eq_three_mul_vertex_card
  have hEpos : 0 < Fintype.card E := by
    have hRpos : 0 < 3 * Fintype.card V := Nat.mul_pos (by norm_num) hVpos
    have hLpos : 0 < 2 * Fintype.card E := by
      simpa [hEeq] using hRpos
    omega
  obtain ⟨e⟩ := Fintype.card_pos_iff.mp hEpos
  have hMpos : 0 < M.circuits.length := by
    have hlen := List.length_eq_length_filter_add
      (l := M.circuits) (fun C : Circuit G ↦ decide (e ∈ C.edges))
    have hcover := M.coveredTwice e
    simp [hcover] at hlen
    omega
  have hlen :=
    M.length_le_cotree_card_add_one_of_length_minimal G hconn hmin hT hMpos
  have hcotree := K.two_mul_cotree_card_of_spanningTree hT
  refine ⟨M, ?_⟩
  omega

theorem CubicGraph.exists_circuitDoubleCover_two_mul_length_le_vertex_card_add_four_of_connects
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (K : CubicGraph V E)
    (hconn : Connects K.toOrientedMultigraph Finset.univ)
    (hb : Bridgeless K.toOrientedMultigraph) :
    ∃ M : CircuitDoubleCover K.toOrientedMultigraph,
      2 * M.circuits.length ≤ Fintype.card V + 4 := by
  haveI : Nonempty V := hconn.nonempty
  exact K.exists_circuitDoubleCover_two_mul_length_le_vertex_card_add_four hconn hb

theorem CubicGraph.exists_circuitDoubleCover_length_le_oddVertices_half_add_two
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [Nonempty V] (K : CubicGraph V E)
    (hconn : Connects K.toOrientedMultigraph Finset.univ)
    (hb : Bridgeless K.toOrientedMultigraph) :
    ∃ M : CircuitDoubleCover K.toOrientedMultigraph,
      M.circuits.length ≤ (oddVertices K.toOrientedMultigraph).card / 2 + 2 := by
  obtain ⟨M, hM⟩ :=
    K.exists_circuitDoubleCover_two_mul_length_le_vertex_card_add_four hconn hb
  have hq : (oddVertices K.toOrientedMultigraph).card = Fintype.card V :=
    K.oddVertices_card_toOrientedMultigraph
  have hEven : Even (Fintype.card V) := by
    rw [← hq]
    exact even_oddVertices_card K.toOrientedMultigraph
  obtain ⟨r, hr⟩ := hEven
  refine ⟨M, ?_⟩
  rw [hq, hr]
  omega

theorem CubicGraph.exists_circuitDoubleCover_length_le_oddVertices_half_add_two_of_connects
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (K : CubicGraph V E)
    (hconn : Connects K.toOrientedMultigraph Finset.univ)
    (hb : Bridgeless K.toOrientedMultigraph) :
    ∃ M : CircuitDoubleCover K.toOrientedMultigraph,
      M.circuits.length ≤ (oddVertices K.toOrientedMultigraph).card / 2 + 2 := by
  haveI : Nonempty V := hconn.nonempty
  exact K.exists_circuitDoubleCover_length_le_oddVertices_half_add_two hconn hb

theorem CubicGraph.exists_circuitDoubleCover_length_le_vertex_card_sub_one
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [Nonempty V] (K : CubicGraph V E)
    (hconn : Connects K.toOrientedMultigraph Finset.univ)
    (hb : Bridgeless K.toOrientedMultigraph)
    (hlarge : 6 ≤ Fintype.card V) :
    ∃ M : CircuitDoubleCover K.toOrientedMultigraph,
      M.circuits.length ≤ Fintype.card V - 1 := by
  obtain ⟨M, hM⟩ :=
    K.exists_circuitDoubleCover_two_mul_length_le_vertex_card_add_four hconn hb
  refine ⟨M, ?_⟩
  omega

theorem CubicGraph.exists_circuitDoubleCover_length_le_vertex_card_sub_one_of_connects
    {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (K : CubicGraph V E)
    (hconn : Connects K.toOrientedMultigraph Finset.univ)
    (hb : Bridgeless K.toOrientedMultigraph)
    (hlarge : 6 ≤ Fintype.card V) :
    ∃ M : CircuitDoubleCover K.toOrientedMultigraph,
      M.circuits.length ≤ Fintype.card V - 1 := by
  haveI : Nonempty V := hconn.nonempty
  exact K.exists_circuitDoubleCover_length_le_vertex_card_sub_one hconn hb hlarge

end CycleDoubleCoverConjecture
