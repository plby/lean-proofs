import ErdosProblems.Erdos59.GeneralMultiplicity
import ErdosProblems.Erdos59.QuadrilateralComponents
import ErdosProblems.Erdos59.ErdosGallai

/-!
# The unconditional FNV U8 multiplicity estimate

This file discharges the finite certificates used by `GeneralMultiplicity`
from the concrete assumption that the ambient graph has no simple hexagon.
The two parts of the argument are kept public: central fibres are charged to
closed neighbourhoods at cost `25 * Δ * e`, while noncentral fibres are
charged to the quadrilateral components classified by U1 at cost
`10 * Δ * e`.
-/

open scoped BigOperators
open Finset SimpleGraph

namespace Erdos59

noncomputable section

universe u

variable {V : Type u} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

attribute [local instance] Classical.propDecidable

/-! ## Concrete hexagon eliminators -/

/-- Six distinct cyclically adjacent vertices contradict `WalkC6Free`.
This explicit form is convenient in all of the local path classifications
below. -/
private theorem false_of_six_cycle_direct (hC6 : WalkC6Free G)
    {a b c d e f : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hef : G.Adj e f) (hfa : G.Adj f a)
    (hpair : [a, b, c, d, e, f].Nodup) : False := by
  let q : G.Walk a a :=
    .cons hab (.cons hbc (.cons hcd (.cons hde (.cons hef (.cons hfa .nil)))))
  have hq : q.IsCycle := by
    simp only [q, Walk.cons_isCycle_iff]
    simp_all [Walk.isPath_def, List.nodup_cons, eq_comm]
  exact hC6 a q hq (by simp [q])

/-- A four-edge path cannot lie in the open neighbourhood of one vertex in
a hexagon-free graph. -/
private theorem false_of_openNeighborhood_path_four (hC6 : WalkC6Free G)
    {v a b c d e : V}
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c)
    (hvd : G.Adj v d) (hve : G.Adj v e)
    (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hde : G.Adj d e)
    (hpath : [a, b, c, d, e].Nodup) : False := by
  apply false_of_six_cycle_direct G hC6 hva hab hbc hcd hde hve.symm
  apply List.nodup_cons.mpr
  constructor
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hva.ne, hvb.ne, hvc.ne, hvd.ne, hve.ne⟩
  · exact hpath

/-! ## The local noncentral-pair kernel -/

/-- The middle edge of a length-three path. -/
def Path3.u8MiddleEdge (p : Path3 G) : Sym2 V :=
  s(p.vertex 1, p.vertex 2)

@[simp] theorem Path3.u8MiddleEdge_toFinset (p : Path3 G) :
    p.u8MiddleEdge.toFinset = {p.vertex 1, p.vertex 2} := by
  simp only [Path3.u8MiddleEdge, Sym2.toFinset_mk_eq]

/-- In a hexagon-free graph, middle edges belonging to two paths with the
same endpoints must intersect.  If they were disjoint, the two paths, one
traversed backwards, would be a simple hexagon. -/
theorem pathFiber_middleEdges_not_disjoint (hC6 : WalkC6Free G)
    {pi : EndpointPair V} {p q : Path3 G}
    (hp : p ∈ pathFiber G pi) (hq : q ∈ pathFiber G pi) :
    ¬ Disjoint p.u8MiddleEdge.toFinset q.u8MiddleEdge.toFinset := by
  intro hd
  have he : p.endpoints = q.endpoints :=
    ((mem_pathFiber (G := G)).mp hp).trans
      ((mem_pathFiber (G := G)).mp hq).symm
  have h0 : p.vertex 0 = q.vertex 0 := by
    exact congrArg (fun z : EndpointPair V ↦ z.1.1) he
  have h3 : p.vertex 3 = q.vertex 3 := by
    exact congrArg (fun z : EndpointPair V ↦ z.1.2) he
  have hpne (i j : Fin 4) (hij : i ≠ j) : p.vertex i ≠ p.vertex j :=
    p.injective.ne hij
  have hqne (i j : Fin 4) (hij : i ≠ j) : q.vertex i ≠ q.vertex j :=
    q.injective.ne hij
  have hcross :
      p.vertex 1 ≠ q.vertex 1 ∧ p.vertex 1 ≠ q.vertex 2 ∧
      p.vertex 2 ≠ q.vertex 1 ∧ p.vertex 2 ≠ q.vertex 2 := by
    rw [Path3.u8MiddleEdge_toFinset, Path3.u8MiddleEdge_toFinset,
      Finset.disjoint_left] at hd
    exact ⟨
      fun h ↦ hd (a := p.vertex 1) (by simp) (by simpa [h]),
      fun h ↦ hd (a := p.vertex 1) (by simp) (by simpa [h]),
      fun h ↦ hd (a := p.vertex 2) (by simp) (by simpa [h]),
      fun h ↦ hd (a := p.vertex 2) (by simp) (by simpa [h])⟩
  have hbq : G.Adj (p.vertex 3) (q.vertex 2) := by
    rw [h3]
    exact q.adj_two_three.symm
  have hqa : G.Adj (q.vertex 1) (p.vertex 0) := by
    rw [h0]
    exact q.adj_zero_one.symm
  have hp1q3 : p.vertex 1 ≠ q.vertex 3 := by
    intro h
    exact (hpne 1 3 (by decide)) (h.trans h3.symm)
  have hp2q3 : p.vertex 2 ≠ q.vertex 3 := by
    intro h
    exact (hpne 2 3 (by decide)) (h.trans h3.symm)
  apply false_of_six_cycle_direct G hC6
    p.adj_zero_one p.adj_one_two p.adj_two_three
    hbq q.adj_one_two.symm hqa
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, true_and]
  aesop

private theorem finset_eq_pair_of_card_two_mem {X : Type*} [DecidableEq X]
    {S : Finset X} {x : X} (hS : S.card = 2) (hx : x ∈ S) :
    ∃ y, y ≠ x ∧ S = {x, y} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b, hab.symm, rfl⟩
  · exact ⟨a, hab, by rw [Finset.pair_comm]⟩

/-- A pairwise-intersecting finite family of two-sets is a star or is
contained in the three edges of a triangle. -/
private theorem twoSet_family_star_or_triangle {X : Type*} [DecidableEq X]
    (F : Finset (Finset X)) (hne : F.Nonempty)
    (hcard : ∀ S ∈ F, S.card = 2)
    (hinter : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) :
    (∃ x, ∀ S ∈ F, x ∈ S) ∨
      ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        {a, b} ∈ F ∧ {a, c} ∈ F ∧ {b, c} ∈ F ∧
        ∀ S ∈ F, S = {a, b} ∨ S = {a, c} ∨ S = {b, c} := by
  classical
  obtain ⟨S, hSF⟩ := hne
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hcard S hSF)
  by_cases ha : ∀ T ∈ F, a ∈ T
  · exact Or.inl ⟨a, ha⟩
  by_cases hb : ∀ T ∈ F, b ∈ T
  · exact Or.inl ⟨b, hb⟩
  push_neg at ha hb
  obtain ⟨T, hTF, haT⟩ := ha
  obtain ⟨U, hUF, hbU⟩ := hb
  have hbT : b ∈ T := by
    obtain ⟨x, hx⟩ := hinter {a, b} hSF T hTF
    have hxS := (Finset.mem_inter.mp hx).1
    have hxT := (Finset.mem_inter.mp hx).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxS
    rcases hxS with rfl | rfl
    · exact (haT hxT).elim
    · exact hxT
  have haU : a ∈ U := by
    obtain ⟨x, hx⟩ := hinter {a, b} hSF U hUF
    have hxS := (Finset.mem_inter.mp hx).1
    have hxU := (Finset.mem_inter.mp hx).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxS
    rcases hxS with rfl | rfl
    · exact hxU
    · exact (hbU hxU).elim
  obtain ⟨c, hcb, hT⟩ :=
    finset_eq_pair_of_card_two_mem (hcard T hTF) hbT
  obtain ⟨d, hda, hU⟩ :=
    finset_eq_pair_of_card_two_mem (hcard U hUF) haU
  have hac : a ≠ c := by
    intro hac
    apply haT
    rw [hT, hac]
    simp
  have hbd : b ≠ d := by
    intro hbd
    apply hbU
    rw [hU, hbd]
    simp
  have hcd : c = d := by
    obtain ⟨x, hx⟩ := hinter T hTF U hUF
    have hxT := (Finset.mem_inter.mp hx).1
    have hxU := (Finset.mem_inter.mp hx).2
    rw [hT] at hxT
    rw [hU] at hxU
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxT hxU
    rcases hxT with rfl | rfl <;> rcases hxU with rfl | rfl
    · exact (hab rfl).elim
    · exact (hbd rfl).elim
    · exact (hac rfl).elim
    · rfl
  subst d
  have habF : {a, b} ∈ F := hSF
  have hacF : {a, c} ∈ F := by simpa [hU] using hUF
  have hbcF : {b, c} ∈ F := by simpa [hT] using hTF
  refine Or.inr ⟨a, b, c, hab, hac, hcb.symm, habF, hacF, hbcF, ?_⟩
  intro R hRF
  obtain ⟨x, y, hxy, hR⟩ := Finset.card_eq_two.mp (hcard R hRF)
  subst R
  have hRS := hinter {x, y} hRF {a, b} hSF
  have hRT := hinter {x, y} hRF T hTF
  have hRU := hinter {x, y} hRF U hUF
  rw [hT] at hRT
  rw [hU] at hRU
  obtain ⟨z, hz⟩ := hRS
  obtain ⟨w, hw⟩ := hRT
  obtain ⟨t, ht⟩ := hRU
  have hzR := (Finset.mem_inter.mp hz).1
  have hzS := (Finset.mem_inter.mp hz).2
  have hwR := (Finset.mem_inter.mp hw).1
  have hwT := (Finset.mem_inter.mp hw).2
  have htR := (Finset.mem_inter.mp ht).1
  have htU := (Finset.mem_inter.mp ht).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzR hzS hwR hwT htR htU
  have hcases :
      (x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨
      (x = a ∧ y = c) ∨ (x = c ∧ y = a) ∨
      (x = b ∧ y = c) ∨ (x = c ∧ y = b) := by
    grind
  rcases hcases with h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;> simp [Finset.pair_comm]

/-- The finite family of all middle edges in one endpoint fibre. -/
def middleEdgeFamily (pi : EndpointPair V) : Finset (Finset V) :=
  (pathFiber G pi).image fun p ↦ p.u8MiddleEdge.toFinset

@[simp] theorem mem_middleEdgeFamily {pi : EndpointPair V} {S : Finset V} :
    S ∈ middleEdgeFamily G pi ↔
      ∃ p ∈ pathFiber G pi, p.u8MiddleEdge.toFinset = S := by
  simp [middleEdgeFamily]

theorem middleEdgeFamily_nonempty {pi : EndpointPair V}
    (hpi : 1 ≤ pathMultiplicity G pi) : (middleEdgeFamily G pi).Nonempty := by
  have hf : (pathFiber G pi).Nonempty := by
    rw [← Finset.card_pos]
    simpa [pathMultiplicity] using hpi
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.u8MiddleEdge.toFinset, by simp only [mem_middleEdgeFamily]; exact ⟨p, hp, rfl⟩⟩

theorem middleEdgeFamily_card_two {pi : EndpointPair V}
    {S : Finset V} (hS : S ∈ middleEdgeFamily G pi) : S.card = 2 := by
  obtain ⟨p, -, rfl⟩ := (mem_middleEdgeFamily (G := G)).mp hS
  rw [Path3.u8MiddleEdge_toFinset]
  exact Finset.card_pair (p.injective.ne (by decide))

theorem middleEdgeFamily_inter_nonempty (hC6 : WalkC6Free G)
    {pi : EndpointPair V} {S T : Finset V}
    (hS : S ∈ middleEdgeFamily G pi) (hT : T ∈ middleEdgeFamily G pi) :
    (S ∩ T).Nonempty := by
  obtain ⟨p, hp, rfl⟩ := (mem_middleEdgeFamily (G := G)).mp hS
  obtain ⟨q, hq, rfl⟩ := (mem_middleEdgeFamily (G := G)).mp hT
  rw [← not_disjoint_iff_nonempty_inter]
  exact pathFiber_middleEdges_not_disjoint G hC6 hp hq

private theorem endpointAdjacency_of_middle_pair {pi : EndpointPair V} {a b : V}
    (hab : {a, b} ∈ middleEdgeFamily G pi) :
    G.Adj a b ∧
      ((G.Adj pi.1.1 a ∧ G.Adj b pi.1.2) ∨
        (G.Adj pi.1.1 b ∧ G.Adj a pi.1.2)) := by
  obtain ⟨p, hp, he⟩ := (mem_middleEdgeFamily (G := G)).mp hab
  rw [Path3.u8MiddleEdge_toFinset] at he
  have he' : ({p.vertex 1, p.vertex 2} : Set V) = {a, b} := by
    simpa only [Finset.coe_pair] using
      congrArg (fun S : Finset V ↦ (S : Set V)) he
  have hend : p.vertex 0 = pi.1.1 ∧ p.vertex 3 = pi.1.2 := by
    have h := (mem_pathFiber (G := G)).mp hp
    exact ⟨congrArg (fun z : EndpointPair V ↦ z.1.1) h,
      congrArg (fun z : EndpointPair V ↦ z.1.2) h⟩
  rcases Set.pair_eq_pair_iff.mp he' with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨p.adj_one_two, Or.inl ⟨hend.1 ▸ p.adj_zero_one,
      hend.2 ▸ p.adj_two_three⟩⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨p.adj_one_two.symm, Or.inr ⟨hend.1 ▸ p.adj_zero_one,
      hend.2 ▸ p.adj_two_three⟩⟩

private theorem centralPair_of_triangle_middleFamily {pi : EndpointPair V}
    {a b c : V} (habF : {a, b} ∈ middleEdgeFamily G pi)
    (hacF : {a, c} ∈ middleEdgeFamily G pi)
    (hbcF : {b, c} ∈ middleEdgeFamily G pi)
    (hall : ∀ S ∈ middleEdgeFamily G pi,
      S = {a, b} ∨ S = {a, c} ∨ S = {b, c}) :
    IsCentralPair G pi := by
  obtain ⟨hab, habd⟩ := endpointAdjacency_of_middle_pair G habF
  obtain ⟨hac, hacd⟩ := endpointAdjacency_of_middle_pair G hacF
  obtain ⟨hbc, hbcd⟩ := endpointAdjacency_of_middle_pair G hbcF
  have hcenter : ∃ w, (w = a ∨ w = b ∨ w = c) ∧
      G.Adj pi.1.1 w ∧ G.Adj w pi.1.2 := by
    rcases habd with habd | habd <;>
      rcases hacd with hacd | hacd <;>
      rcases hbcd with hbcd | hbcd <;> aesop
  obtain ⟨w, hw, hxw, hwy⟩ := hcenter
  have ha : a ∈ closedNeighborFinset G w := by
    rw [mem_closedNeighborFinset]
    rcases hw with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hab.symm
    · exact Or.inr hac.symm
  have hb : b ∈ closedNeighborFinset G w := by
    rw [mem_closedNeighborFinset]
    rcases hw with rfl | rfl | rfl
    · exact Or.inr hab
    · exact Or.inl rfl
    · exact Or.inr hbc.symm
  have hc : c ∈ closedNeighborFinset G w := by
    rw [mem_closedNeighborFinset]
    rcases hw with rfl | rfl | rfl
    · exact Or.inr hac
    · exact Or.inr hbc
    · exact Or.inl rfl
  refine ⟨w, ?_⟩
  intro p hp i
  have hend := (mem_pathFiber (G := G)).mp hp
  have h0 : p.vertex 0 = pi.1.1 :=
    congrArg (fun z : EndpointPair V ↦ z.1.1) hend
  have h3 : p.vertex 3 = pi.1.2 :=
    congrArg (fun z : EndpointPair V ↦ z.1.2) hend
  have hmid : p.u8MiddleEdge.toFinset ∈ middleEdgeFamily G pi := by
    rw [mem_middleEdgeFamily]
    exact ⟨p, hp, rfl⟩
  have hpairs := hall _ hmid
  have h1 : p.vertex 1 = a ∨ p.vertex 1 = b ∨ p.vertex 1 = c := by
    have hpairs1 := hpairs
    rw [Path3.u8MiddleEdge_toFinset] at hpairs1
    rcases hpairs1 with h | h | h
    · have hm : p.vertex 1 ∈ ({a, b} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (Or.inl hm)
    · have hm : p.vertex 1 ∈ ({a, c} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (Or.inr hm)
    · have hm : p.vertex 1 ∈ ({b, c} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Or.inr (Or.inl hm)
      · exact Or.inr (Or.inr hm)
  have h2 : p.vertex 2 = a ∨ p.vertex 2 = b ∨ p.vertex 2 = c := by
    have hpairs2 := hpairs
    rw [Path3.u8MiddleEdge_toFinset] at hpairs2
    rcases hpairs2 with h | h | h
    · have hm : p.vertex 2 ∈ ({a, b} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (Or.inl hm)
    · have hm : p.vertex 2 ∈ ({a, c} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (Or.inr hm)
    · have hm : p.vertex 2 ∈ ({b, c} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Or.inr (Or.inl hm)
      · exact Or.inr (Or.inr hm)
  fin_cases i
  · change p.vertex 0 ∈ closedNeighborFinset G w
    rw [h0, mem_closedNeighborFinset]
    exact Or.inr hxw.symm
  · rcases h1 with rfl | rfl | rfl <;> assumption
  · rcases h2 with rfl | rfl | rfl <;> assumption
  · change p.vertex 3 ∈ closedNeighborFinset G w
    rw [h3, mem_closedNeighborFinset]
    exact Or.inr hwy

/-- The middle edges in a noncentral endpoint fibre form a genuine star.
This is the local combinatorial kernel of FNV Lemma 5.1. -/
theorem exists_common_middleVertex_of_not_central (hC6 : WalkC6Free G)
    {pi : EndpointPair V} (hmul : 1 ≤ pathMultiplicity G pi)
    (hnc : ¬ IsCentralPair G pi) :
    ∃ w, ∀ p ∈ pathFiber G pi, w ∈ p.u8MiddleEdge.toFinset := by
  have hne : (middleEdgeFamily G pi).Nonempty :=
    middleEdgeFamily_nonempty G hmul
  have hclass := twoSet_family_star_or_triangle (middleEdgeFamily G pi) hne
    (fun S hS ↦ middleEdgeFamily_card_two G hS)
    (fun S hS T hT ↦ middleEdgeFamily_inter_nonempty G hC6 hS hT)
  rcases hclass with ⟨w, hw⟩ | ⟨a, b, c, -, -, -, hab, hac, hbc, hall⟩
  · refine ⟨w, ?_⟩
    intro p hp
    exact hw _ ((mem_middleEdgeFamily (G := G)).mpr ⟨p, hp, rfl⟩)
  · exact (hnc (centralPair_of_triangle_middleFamily G hab hac hbc hall)).elim

private theorem centralPair_of_mixed_common_middle {pi : EndpointPair V} {w : V}
    (hcommon : ∀ p ∈ pathFiber G pi, w ∈ p.u8MiddleEdge.toFinset)
    {p q : Path3 G} (hp : p ∈ pathFiber G pi) (hq : q ∈ pathFiber G pi)
    (hpw : w = p.vertex 1) (hqw : w = q.vertex 2) :
    IsCentralPair G pi := by
  have hep := (mem_pathFiber (G := G)).mp hp
  have heq := (mem_pathFiber (G := G)).mp hq
  have hp0 : p.vertex 0 = pi.1.1 :=
    congrArg (fun z : EndpointPair V ↦ z.1.1) hep
  have hq3 : q.vertex 3 = pi.1.2 :=
    congrArg (fun z : EndpointPair V ↦ z.1.2) heq
  have hxw : G.Adj pi.1.1 w := by
    rw [hpw, ← hp0]
    exact p.adj_zero_one
  have hwy : G.Adj w pi.1.2 := by
    rw [hqw, ← hq3]
    exact q.adj_two_three
  refine ⟨w, ?_⟩
  intro r hr i
  have her := (mem_pathFiber (G := G)).mp hr
  have hr0 : r.vertex 0 = pi.1.1 :=
    congrArg (fun z : EndpointPair V ↦ z.1.1) her
  have hr3 : r.vertex 3 = pi.1.2 :=
    congrArg (fun z : EndpointPair V ↦ z.1.2) her
  have hrw := hcommon r hr
  rw [Path3.u8MiddleEdge_toFinset] at hrw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrw
  fin_cases i
  · change r.vertex 0 ∈ closedNeighborFinset G w
    rw [hr0, mem_closedNeighborFinset]
    exact Or.inr hxw.symm
  · rw [mem_closedNeighborFinset]
    rcases hrw with h | h
    · exact Or.inl h.symm
    · exact Or.inr (h ▸ r.adj_one_two.symm)
  · rw [mem_closedNeighborFinset]
    rcases hrw with h | h
    · exact Or.inr (h ▸ r.adj_one_two)
    · exact Or.inl h.symm
  · change r.vertex 3 ∈ closedNeighborFinset G w
    rw [hr3, mem_closedNeighborFinset]
    exact Or.inr hwy

/-- On a noncentral fibre the common middle vertex occurs consistently on
one side.  Consequently every path is encoded by its other middle vertex. -/
theorem noncentral_middle_star_normal_form (hC6 : WalkC6Free G)
    {pi : EndpointPair V} (hmul : 1 ≤ pathMultiplicity G pi)
    (hnc : ¬ IsCentralPair G pi) :
    ∃ w, (∀ p ∈ pathFiber G pi, w = p.vertex 1) ∨
      ∀ p ∈ pathFiber G pi, w = p.vertex 2 := by
  obtain ⟨w, hcommon⟩ :=
    exists_common_middleVertex_of_not_central G hC6 hmul hnc
  by_cases hleft : ∀ p ∈ pathFiber G pi, w = p.vertex 1
  · exact ⟨w, Or.inl hleft⟩
  · push_neg at hleft
    obtain ⟨p, hp, hpne⟩ := hleft
    have hpw := hcommon p hp
    rw [Path3.u8MiddleEdge_toFinset] at hpw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpw
    have hp2 : w = p.vertex 2 := hpw.resolve_left hpne
    refine ⟨w, Or.inr ?_⟩
    intro q hq
    have hqw := hcommon q hq
    rw [Path3.u8MiddleEdge_toFinset] at hqw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqw
    rcases hqw with hq1 | hq2
    · exact (hnc (centralPair_of_mixed_common_middle G hcommon hq hp hq1 hp2)).elim
    · exact hq2

theorem nondegenerateExceptional_two_le {pi : EndpointPair V}
    (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    2 ≤ pathMultiplicity G pi := by
  have hord : pi ∈ ordinaryExceptionalPairs G :=
    (Finset.mem_sdiff.mp hpi).1
  have h := (Finset.mem_filter.mp hord).2
  rcases h with h | h
  · exact h.1
  · omega

theorem nondegenerateExceptional_not_central {pi : EndpointPair V}
    (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    ¬ IsCentralPair G pi := by
  have hnot : pi ∉ degeneratePairs G := (Finset.mem_sdiff.mp hpi).2
  intro hc
  apply hnot
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨nondegenerateExceptional_two_le G hpi, hc⟩⟩

theorem nondegenerate_middle_star_normal_form (hC6 : WalkC6Free G)
    {pi : EndpointPair V} (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    ∃ w, (∀ p ∈ pathFiber G pi, w = p.vertex 1) ∨
      ∀ p ∈ pathFiber G pi, w = p.vertex 2 := by
  exact noncentral_middle_star_normal_form G hC6
    (Nat.one_le_iff_ne_zero.mpr (by
      have := nondegenerateExceptional_two_le G hpi
      omega))
    (nondegenerateExceptional_not_central G hpi)

/-! ## The concrete biclique attached to a noncentral pair -/

noncomputable def nondegenerateStarCentre (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) : V :=
  (nondegenerate_middle_star_normal_form G hC6 hpi).choose

def nondegenerateStarOnLeft (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) : Prop :=
  ∀ p ∈ pathFiber G pi,
    nondegenerateStarCentre G hC6 pi hpi = p.vertex 1

theorem nondegenerateStarCentre_spec (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    nondegenerateStarOnLeft G hC6 pi hpi ∨
      ∀ p ∈ pathFiber G pi,
        nondegenerateStarCentre G hC6 pi hpi = p.vertex 2 :=
  (nondegenerate_middle_star_normal_form G hC6 hpi).choose_spec

theorem nondegenerateStarCentre_spec_right (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G)
    (hr : ¬ nondegenerateStarOnLeft G hC6 pi hpi) :
    ∀ p ∈ pathFiber G pi,
      nondegenerateStarCentre G hC6 pi hpi = p.vertex 2 :=
  (nondegenerateStarCentre_spec G hC6 pi hpi).resolve_left hr

noncomputable def nondegenerateOtherMiddles (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) : Finset V :=
  if nondegenerateStarOnLeft G hC6 pi hpi then
    (pathFiber G pi).image fun p ↦ p.vertex 2
  else
    (pathFiber G pi).image fun p ↦ p.vertex 1

noncomputable def nondegenerateBaseSide (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) : Finset V :=
  if nondegenerateStarOnLeft G hC6 pi hpi then
    {nondegenerateStarCentre G hC6 pi hpi, pi.1.2}
  else
    {pi.1.1, nondegenerateStarCentre G hC6 pi hpi}

private theorem card_image_vertex_two_of_star_left (hC6 : WalkC6Free G)
    {pi : EndpointPair V} (hpi : pi ∈ nondegenerateExceptionalPairs G)
    (hl : nondegenerateStarOnLeft G hC6 pi hpi) :
    ((pathFiber G pi).image fun p ↦ p.vertex 2).card =
      (pathFiber G pi).card := by
  rw [Finset.card_image_iff]
  intro p hp q hq he
  apply Subtype.ext
  funext i
  have hep := (mem_pathFiber (G := G)).mp hp
  have heq := (mem_pathFiber (G := G)).mp hq
  fin_cases i
  · exact (congrArg (fun z : EndpointPair V ↦ z.1.1) hep).trans
      (congrArg (fun z : EndpointPair V ↦ z.1.1) heq).symm
  · exact (hl p hp).symm.trans (hl q hq)
  · exact he
  · exact (congrArg (fun z : EndpointPair V ↦ z.1.2) hep).trans
      (congrArg (fun z : EndpointPair V ↦ z.1.2) heq).symm

private theorem card_image_vertex_one_of_star_right (hC6 : WalkC6Free G)
    {pi : EndpointPair V} (hpi : pi ∈ nondegenerateExceptionalPairs G)
    (hr : ¬ nondegenerateStarOnLeft G hC6 pi hpi) :
    ((pathFiber G pi).image fun p ↦ p.vertex 1).card =
      (pathFiber G pi).card := by
  have hs := nondegenerateStarCentre_spec_right G hC6 pi hpi hr
  rw [Finset.card_image_iff]
  intro p hp q hq he
  apply Subtype.ext
  funext i
  have hep := (mem_pathFiber (G := G)).mp hp
  have heq := (mem_pathFiber (G := G)).mp hq
  fin_cases i
  · exact (congrArg (fun z : EndpointPair V ↦ z.1.1) hep).trans
      (congrArg (fun z : EndpointPair V ↦ z.1.1) heq).symm
  · exact he
  · exact (hs p hp).symm.trans (hs q hq)
  · exact (congrArg (fun z : EndpointPair V ↦ z.1.2) hep).trans
      (congrArg (fun z : EndpointPair V ↦ z.1.2) heq).symm

theorem card_nondegenerateOtherMiddles (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    (nondegenerateOtherMiddles G hC6 pi hpi).card = pathMultiplicity G pi := by
  classical
  unfold nondegenerateOtherMiddles pathMultiplicity
  split_ifs with h
  · exact card_image_vertex_two_of_star_left G hC6 hpi h
  · exact card_image_vertex_one_of_star_right G hC6 hpi h

/-- Every nondegenerate exceptional fibre has at most maximum-degree many
paths.  The varying middle vertex injects into the open neighbourhood of
one fixed endpoint. -/
theorem nondegenerate_pathMultiplicity_le_maxDegree (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    pathMultiplicity G pi ≤ G.maxDegree := by
  by_cases hl : nondegenerateStarOnLeft G hC6 pi hpi
  · have hsub : nondegenerateOtherMiddles G hC6 pi hpi ⊆
        G.neighborFinset pi.1.2 := by
      intro y hy
      simp only [nondegenerateOtherMiddles, if_pos hl] at hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      apply (G.mem_neighborFinset _ _).2
      have hend := (mem_pathFiber (G := G)).mp hp
      have h3 : p.vertex 3 = pi.1.2 :=
        congrArg (fun z : EndpointPair V ↦ z.1.2) hend
      rw [← h3]
      exact p.adj_two_three.symm
    rw [← card_nondegenerateOtherMiddles G hC6 pi hpi]
    exact (Finset.card_le_card hsub).trans
      ((G.card_neighborFinset_eq_degree pi.1.2).le.trans
        (G.degree_le_maxDegree pi.1.2))
  · have hsub : nondegenerateOtherMiddles G hC6 pi hpi ⊆
        G.neighborFinset pi.1.1 := by
      intro y hy
      simp only [nondegenerateOtherMiddles, if_neg hl] at hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      apply (G.mem_neighborFinset _ _).2
      have hend := (mem_pathFiber (G := G)).mp hp
      have h0 : p.vertex 0 = pi.1.1 :=
        congrArg (fun z : EndpointPair V ↦ z.1.1) hend
      rw [← h0]
      exact p.adj_zero_one
    rw [← card_nondegenerateOtherMiddles G hC6 pi hpi]
    exact (Finset.card_le_card hsub).trans
      ((G.card_neighborFinset_eq_degree pi.1.1).le.trans
        (G.degree_le_maxDegree pi.1.1))

/-- The canonical base side is complete to the canonical set of varying
middle vertices. -/
theorem nondegenerateBaseOther_adj (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G)
    {x y : V} (hx : x ∈ nondegenerateBaseSide G hC6 pi hpi)
    (hy : y ∈ nondegenerateOtherMiddles G hC6 pi hpi) :
    G.Adj x y := by
  by_cases hl : nondegenerateStarOnLeft G hC6 pi hpi
  · simp only [nondegenerateBaseSide, if_pos hl, Finset.mem_insert,
      Finset.mem_singleton] at hx
    simp only [nondegenerateOtherMiddles, if_pos hl] at hy
    obtain ⟨p, hp, hpy⟩ := Finset.mem_image.mp hy
    rcases hx with rfl | rfl
    · change G.Adj (nondegenerateStarCentre G hC6 pi hpi) y
      rw [hl p hp, ← hpy]
      exact p.adj_one_two
    · have hend := (mem_pathFiber (G := G)).mp hp
      have h3 : p.vertex 3 = pi.1.2 :=
        congrArg (fun z : EndpointPair V ↦ z.1.2) hend
      rw [← h3, ← hpy]
      exact p.adj_two_three.symm
  · have hs := nondegenerateStarCentre_spec_right G hC6 pi hpi hl
    simp only [nondegenerateBaseSide, if_neg hl, Finset.mem_insert,
      Finset.mem_singleton] at hx
    simp only [nondegenerateOtherMiddles, if_neg hl] at hy
    obtain ⟨p, hp, hpy⟩ := Finset.mem_image.mp hy
    rcases hx with rfl | rfl
    · have hend := (mem_pathFiber (G := G)).mp hp
      have h0 : p.vertex 0 = pi.1.1 :=
        congrArg (fun z : EndpointPair V ↦ z.1.1) hend
      rw [← h0, ← hpy]
      exact p.adj_zero_one
    · change G.Adj (nondegenerateStarCentre G hC6 pi hpi) y
      rw [hs p hp, ← hpy]
      exact p.adj_one_two.symm

/-- The canonical base of a nondegenerate exceptional fibre has exactly
two vertices. -/
theorem card_nondegenerateBaseSide (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    (nondegenerateBaseSide G hC6 pi hpi).card = 2 := by
  have hpos : 0 < pathMultiplicity G pi := by
    have htwo := nondegenerateExceptional_two_le G hpi
    omega
  obtain ⟨p, hp⟩ : (pathFiber G pi).Nonempty := by
    rw [← Finset.card_pos]
    simpa only [pathMultiplicity] using hpos
  by_cases hl : nondegenerateStarOnLeft G hC6 pi hpi
  · rw [nondegenerateBaseSide, if_pos hl]
    apply Finset.card_pair
    intro heq
    have hend := (mem_pathFiber (G := G)).mp hp
    have h3 : p.vertex 3 = pi.1.2 :=
      congrArg (fun z : EndpointPair V ↦ z.1.2) hend
    exact p.injective.ne (by decide)
      ((hl p hp).symm.trans (heq.trans h3.symm))
  · rw [nondegenerateBaseSide, if_neg hl]
    apply Finset.card_pair
    intro heq
    have hend := (mem_pathFiber (G := G)).mp hp
    have h0 : p.vertex 0 = pi.1.1 :=
      congrArg (fun z : EndpointPair V ↦ z.1.1) hend
    have hs := nondegenerateStarCentre_spec_right G hC6 pi hpi hl p hp
    exact p.injective.ne (by decide) (h0.trans (heq.trans hs))

/-- The two canonical base vertices are disjoint from all varying middle
vertices. -/
theorem disjoint_nondegenerateBaseOther (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    Disjoint (nondegenerateBaseSide G hC6 pi hpi)
      (nondegenerateOtherMiddles G hC6 pi hpi) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  by_cases hl : nondegenerateStarOnLeft G hC6 pi hpi
  · simp only [nondegenerateBaseSide, if_pos hl, Finset.mem_insert,
      Finset.mem_singleton] at hx
    simp only [nondegenerateOtherMiddles, if_pos hl] at hy
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hy
    rcases hx with rfl | rfl
    · exact p.injective.ne (by decide) ((hl p hp).symm.trans hpx.symm)
    · have hend := (mem_pathFiber (G := G)).mp hp
      have h3 : p.vertex 3 = pi.1.2 :=
        congrArg (fun z : EndpointPair V ↦ z.1.2) hend
      exact p.injective.ne (by decide) (h3.trans hpx.symm)
  · have hs := nondegenerateStarCentre_spec_right G hC6 pi hpi hl
    simp only [nondegenerateBaseSide, if_neg hl, Finset.mem_insert,
      Finset.mem_singleton] at hx
    simp only [nondegenerateOtherMiddles, if_neg hl] at hy
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hy
    rcases hx with rfl | rfl
    · have hend := (mem_pathFiber (G := G)).mp hp
      have h0 : p.vertex 0 = pi.1.1 :=
        congrArg (fun z : EndpointPair V ↦ z.1.1) hend
      exact p.injective.ne (by decide) (h0.trans hpx.symm)
    · exact p.injective.ne (by decide) ((hs p hp).symm.trans hpx.symm)

private noncomputable def crossingGraphEdges (L R : Finset V) :
    Finset (GraphEdge G) :=
  Finset.univ.filter fun e ↦ EdgeCrosses G L R e

@[simp] private theorem mem_crossingGraphEdges {L R : Finset V} {e : GraphEdge G} :
    e ∈ crossingGraphEdges G L R ↔ EdgeCrosses G L R e := by
  simp [crossingGraphEdges]

noncomputable def nondegenerateBicliquePiece (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    Finset (GraphEdge G) :=
  crossingGraphEdges G (nondegenerateBaseSide G hC6 pi hpi)
    (nondegenerateOtherMiddles G hC6 pi hpi)

theorem nondegenerateBicliquePiece_isComplete (hC6 : WalkC6Free G)
    (pi : EndpointPair V) (hpi : pi ∈ nondegenerateExceptionalPairs G) :
    IsCompleteBipartitePiece G (nondegenerateBicliquePiece G hC6 pi hpi) := by
  classical
  let w := nondegenerateStarCentre G hC6 pi hpi
  let L := nondegenerateBaseSide G hC6 pi hpi
  let R := nondegenerateOtherMiddles G hC6 pi hpi
  have hmul := nondegenerateExceptional_two_le G hpi
  have hf : (pathFiber G pi).Nonempty := by
    rw [← Finset.card_pos]
    simpa [pathMultiplicity] using (show 0 < pathMultiplicity G pi by omega)
  obtain ⟨p₀, hp₀⟩ := hf
  by_cases hl : nondegenerateStarOnLeft G hC6 pi hpi
  · have hL : L = {w, pi.1.2} := by
      dsimp only [L, nondegenerateBaseSide, w]
      rw [if_pos hl]
      exact Finset.ext fun _ ↦ by simp
    have hR : R = (pathFiber G pi).image (fun p ↦ p.vertex 2) := by
      dsimp only [R, nondegenerateOtherMiddles]
      rw [if_pos hl]
      exact Finset.ext fun _ ↦ by simp
    have hw3 : w ≠ pi.1.2 := by
      intro he
      have hend := (mem_pathFiber (G := G)).mp hp₀
      have h3 : p₀.vertex 3 = pi.1.2 :=
        congrArg (fun z : EndpointPair V ↦ z.1.2) hend
      exact p₀.injective.ne (by decide)
        ((hl p₀ hp₀).symm.trans (he.trans h3.symm))
    have hdisj : Disjoint L R := by
      rw [hL, hR, Finset.disjoint_left]
      intro x hxL hxR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxL
      obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hxR
      rcases hxL with rfl | rfl
      · exact p.injective.ne (by decide) ((hl p hp).symm.trans hpx.symm)
      · have hend := (mem_pathFiber (G := G)).mp hp
        have h3 : p.vertex 3 = pi.1.2 :=
          congrArg (fun z : EndpointPair V ↦ z.1.2) hend
        exact p.injective.ne (by decide) (h3.trans hpx.symm)
    have hadj : ∀ x ∈ L, ∀ y ∈ R, G.Adj x y := by
      intro x hxL y hyR
      rw [hL] at hxL
      rw [hR] at hyR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxL
      obtain ⟨p, hp, hpy⟩ := Finset.mem_image.mp hyR
      rcases hxL with rfl | rfl
      · change G.Adj (nondegenerateStarCentre G hC6 pi hpi) y
        rw [hl p hp, ← hpy]
        exact p.adj_one_two
      · have hend := (mem_pathFiber (G := G)).mp hp
        have h3 : p.vertex 3 = pi.1.2 :=
          congrArg (fun z : EndpointPair V ↦ z.1.2) hend
        rw [← h3, ← hpy]
        exact p.adj_two_three.symm
    refine ⟨L, R, hdisj, ?_, ?_, hadj, ?_⟩
    · rw [hL]
      have hcard := Finset.card_pair hw3
      omega
    · change 2 ≤ (nondegenerateOtherMiddles G hC6 pi hpi).card
      rw [card_nondegenerateOtherMiddles G hC6 pi hpi]
      exact hmul
    · intro e
      simp [nondegenerateBicliquePiece, crossingGraphEdges, L, R]
  · have hs := nondegenerateStarCentre_spec_right G hC6 pi hpi hl
    have hL : L = {pi.1.1, w} := by
      dsimp only [L, nondegenerateBaseSide, w]
      rw [if_neg hl]
      exact Finset.ext fun _ ↦ by simp
    have hR : R = (pathFiber G pi).image (fun p ↦ p.vertex 1) := by
      dsimp only [R, nondegenerateOtherMiddles]
      rw [if_neg hl]
      exact Finset.ext fun _ ↦ by simp
    have h0w : pi.1.1 ≠ w := by
      intro he
      have hend := (mem_pathFiber (G := G)).mp hp₀
      have h0 : p₀.vertex 0 = pi.1.1 :=
        congrArg (fun z : EndpointPair V ↦ z.1.1) hend
      exact p₀.injective.ne (by decide)
        (h0.trans (he.trans (hs p₀ hp₀)))
    have hdisj : Disjoint L R := by
      rw [hL, hR, Finset.disjoint_left]
      intro x hxL hxR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxL
      obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hxR
      rcases hxL with rfl | rfl
      · have hend := (mem_pathFiber (G := G)).mp hp
        have h0 : p.vertex 0 = pi.1.1 :=
          congrArg (fun z : EndpointPair V ↦ z.1.1) hend
        exact p.injective.ne (by decide) (h0.trans hpx.symm)
      · exact p.injective.ne (by decide) ((hs p hp).symm.trans hpx.symm)
    have hadj : ∀ x ∈ L, ∀ y ∈ R, G.Adj x y := by
      intro x hxL y hyR
      rw [hL] at hxL
      rw [hR] at hyR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxL
      obtain ⟨p, hp, hpy⟩ := Finset.mem_image.mp hyR
      rcases hxL with rfl | rfl
      · have hend := (mem_pathFiber (G := G)).mp hp
        have h0 : p.vertex 0 = pi.1.1 :=
          congrArg (fun z : EndpointPair V ↦ z.1.1) hend
        rw [← h0, ← hpy]
        exact p.adj_zero_one
      · change G.Adj (nondegenerateStarCentre G hC6 pi hpi) y
        rw [hs p hp, ← hpy]
        exact p.adj_one_two.symm
    refine ⟨L, R, hdisj, ?_, ?_, hadj, ?_⟩
    · rw [hL]
      have hcard := Finset.card_pair h0w
      omega
    · change 2 ≤ (nondegenerateOtherMiddles G hC6 pi hpi).card
      rw [card_nondegenerateOtherMiddles G hC6 pi hpi]
      exact hmul
    · intro e
      simp [nondegenerateBicliquePiece, crossingGraphEdges, L, R]

/-! ## Canonical charging of central fibres -/

/-- A canonical centre for a central endpoint pair.  The fallback is only
used away from central pairs and makes the definition work even without an
`Inhabited V` instance. -/
def chosenCentralVertex (pi : EndpointPair V) : V :=
  if h : IsCentralPair G pi then h.choose else pi.1.1

theorem chosenCentralVertex_spec {pi : EndpointPair V}
    (hpi : pi ∈ degeneratePairs G) {p : Path3 G}
    (hp : p ∈ pathFiber G pi) (i : Fin 4) :
    p.vertex i ∈ closedNeighborFinset G (chosenCentralVertex G pi) := by
  have hc : IsCentralPair G pi := by
    simpa [degeneratePairs, IsDegeneratePair] using (Finset.mem_filter.mp hpi).2.2
  rw [chosenCentralVertex, dif_pos hc]
  exact hc.choose_spec p hp i

/-- The endpoint fibres assigned to their chosen centres inject into the
corresponding closed-neighbourhood path sets. -/
theorem central_charge_direct :
    multiplicitySum G (degeneratePairs G) ≤
      ∑ v, (closedNeighborhoodPaths G v).card := by
  let A := Σ pi : {pi // pi ∈ degeneratePairs G},
    {p // p ∈ pathFiber G pi.1}
  let B := Σ v : V, {p // p ∈ closedNeighborhoodPaths G v}
  let charge : A → B := fun x ↦
    ⟨chosenCentralVertex G x.1.1,
      ⟨x.2.1, by
        rw [mem_closedNeighborhoodPaths]
        exact fun i ↦ chosenCentralVertex_spec G x.1.2 x.2.2 i⟩⟩
  have hinj : Function.Injective charge := by
    rintro ⟨⟨pi, hpi⟩, ⟨p, hp⟩⟩ ⟨⟨rho, hrho⟩, ⟨q, hq⟩⟩ h
    have hpq : p = q := by
      exact congrArg (fun z : B ↦ z.2.1) h
    have hpi_rho : pi = rho := by
      have hep : p.endpoints = pi := (mem_pathFiber (G := G)).mp hp
      have heq : q.endpoints = rho := (mem_pathFiber (G := G)).mp hq
      exact hep.symm.trans ((congrArg Path3.endpoints hpq).trans heq)
    subst rho
    subst q
    rfl
  have hcard : Fintype.card A ≤ Fintype.card B :=
    Fintype.card_le_of_injective charge hinj
  have hA : Fintype.card A = multiplicitySum G (degeneratePairs G) := by
    dsimp only [A]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    unfold multiplicitySum pathMultiplicity
    have hatt : (degeneratePairs G).attach =
        (Finset.univ : Finset {pi // pi ∈ degeneratePairs G}) := by
      ext pi
      simp
    have hs := Finset.sum_attach (degeneratePairs G)
      (fun pi : EndpointPair V ↦ (pathFiber G pi).card)
    rw [hatt] at hs
    exact hs
  have hB : Fintype.card B = ∑ v, (closedNeighborhoodPaths G v).card := by
    dsimp only [B]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
  rwa [hA, hB] at hcard

/-! ## Counting paths in a closed neighbourhood -/

/-- The edges induced by a closed neighbourhood split into the star at its
centre and the edges internal to the open neighbourhood. -/
theorem card_induced_closedNeighbor_eq (v : V) :
    (G.induce (closedNeighborFinset G v : Set V)).edgeFinset.card =
      closedNeighborhoodEdgeCount G v := by
  rw [← G.card_filter_edgeFinset_toFinset_subset (closedNeighborFinset G v)]
  have hsplit :
      (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ closedNeighborFinset G v) =
        G.incidenceFinset v ∪ openNeighborhoodEdges G v := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
        simp only [Finset.mem_filter, Finset.mem_union, Sym2.toFinset_mk_eq,
          Finset.insert_subset_iff, Finset.singleton_subset_iff]
        rw [G.mem_incidenceFinset]
        simp only [G.mk'_mem_incidenceSet_iff]
        simp [closedNeighborFinset, openNeighborhoodEdges,
          SimpleGraph.mem_edgeFinset, G.adj_comm, eq_comm]
        constructor
        · rintro ⟨hab, ha, hb⟩
          rcases ha with rfl | hva
          · exact Or.inl ⟨hab, Or.inl rfl⟩
          rcases hb with rfl | hvb
          · exact Or.inl ⟨hab, Or.inr rfl⟩
          · exact Or.inr ⟨hab, fun z hz ↦ by
              rcases hz with rfl | rfl
              · exact hva
              · exact hvb⟩
        · rintro (⟨hab, hv⟩ | ⟨hab, hopen⟩)
          · rcases hv with rfl | rfl
            · exact ⟨hab, Or.inl rfl, Or.inr hab⟩
            · exact ⟨hab, Or.inr hab.symm, Or.inl rfl⟩
          · exact ⟨hab, Or.inr (hopen a (Or.inl rfl)),
              Or.inr (hopen b (Or.inr rfl))⟩
  rw [hsplit, Finset.card_union_of_disjoint]
  · simp [closedNeighborhoodEdgeCount, G.card_incidenceFinset_eq_degree]
  · rw [Finset.disjoint_left]
    intro e heI heO
    induction e using Sym2.ind with
    | _ a b =>
        rw [G.mem_incidenceFinset] at heI
        simp only [G.mk'_mem_incidenceSet_iff] at heI
        simp only [openNeighborhoodEdges, Finset.mem_filter,
          Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff] at heO
        rcases heI.2 with (rfl | rfl) <;> simp_all

/-- Ordered pairs of darts whose initial vertices are increasing occupy at
most half of all ordered dart pairs. -/
private theorem twice_card_increasingDartPairs_le
    {W : Type*} [Fintype W] [LinearOrder W]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    2 * Fintype.card {z : H.Dart × H.Dart // z.1.fst < z.2.fst} ≤
      (Fintype.card H.Dart) ^ 2 := by
  let A := {z : H.Dart × H.Dart // z.1.fst < z.2.fst}
  let f : A ⊕ A → H.Dart × H.Dart
    | Sum.inl z => z.1
    | Sum.inr z => (z.1.2, z.1.1)
  have hf : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            congr 1
            exact Subtype.ext hxy
        | inr y =>
            exfalso
            have h1 : x.1.1 = y.1.2 := congrArg Prod.fst hxy
            have h2 : x.1.2 = y.1.1 := congrArg Prod.snd hxy
            have hyx : x.1.2.fst < x.1.1.fst := by
              rw [h2, h1]
              exact y.2
            exact (lt_asymm x.2 hyx)
    | inr x =>
        cases y with
        | inl y =>
            exfalso
            have h1 : x.1.2 = y.1.1 := congrArg Prod.fst hxy
            have h2 : x.1.1 = y.1.2 := congrArg Prod.snd hxy
            have hyx : x.1.2.fst < x.1.1.fst := by
              rw [h1, h2]
              exact y.2
            exact (lt_asymm x.2 hyx)
        | inr y =>
            congr 1
            apply Subtype.ext
            exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [A, Fintype.card_sum, Fintype.card_prod, two_mul, pow_two] using hcard

/-- Choosing the two outward-oriented end edges injects a path in a closed
neighbourhood into an increasing pair of darts of the induced graph. -/
theorem closed_path_pair_count_direct (v : V) :
    (closedNeighborhoodPaths G v).card ≤
      2 * (closedNeighborhoodEdgeCount G v) ^ 2 := by
  let S : Set V := closedNeighborFinset G v
  let H : SimpleGraph S := G.induce S
  let A := {p // p ∈ closedNeighborhoodPaths G v}
  let B := {z : H.Dart × H.Dart // z.1.fst < z.2.fst}
  let code : A → B := fun p ↦ by
    have hp := (mem_closedNeighborhoodPaths (G := G)).mp p.2
    let x0 : S := ⟨p.1.vertex 0, hp 0⟩
    let x1 : S := ⟨p.1.vertex 1, hp 1⟩
    let x2 : S := ⟨p.1.vertex 2, hp 2⟩
    let x3 : S := ⟨p.1.vertex 3, hp 3⟩
    let d0 : H.Dart := ⟨(x0, x1), p.1.adj_zero_one⟩
    let d3 : H.Dart := ⟨(x3, x2), p.1.adj_two_three.symm⟩
    exact ⟨(d0, d3), p.1.2.2⟩
  have hcode : Function.Injective code := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i
    · exact congrArg (fun z : B ↦ z.1.1.fst.1) hpq
    · exact congrArg (fun z : B ↦ z.1.1.snd.1) hpq
    · exact congrArg (fun z : B ↦ z.1.2.snd.1) hpq
    · exact congrArg (fun z : B ↦ z.1.2.fst.1) hpq
  have hAB : Fintype.card A ≤ Fintype.card B :=
    Fintype.card_le_of_injective code hcode
  have hB : 2 * Fintype.card B ≤ (Fintype.card H.Dart) ^ 2 :=
    twice_card_increasingDartPairs_le H
  have hD : Fintype.card H.Dart =
      2 * closedNeighborhoodEdgeCount G v := by
    dsimp only [H, S]
    rw [(G.induce (closedNeighborFinset G v : Set V)).dart_card_eq_twice_card_edges,
      card_induced_closedNeighbor_eq G]
  have hA : Fintype.card A = (closedNeighborhoodPaths G v).card := by
    change Fintype.card ↑(closedNeighborhoodPaths G v) = _
    exact Fintype.card_coe _
  rw [hD] at hB
  rw [← hA]
  apply hAB.trans
  exact Nat.le_of_mul_le_mul_left (by
    calc
      2 * Fintype.card B ≤ (2 * closedNeighborhoodEdgeCount G v) ^ 2 := hB
      _ = 2 * (2 * (closedNeighborhoodEdgeCount G v) ^ 2) := by ring)
    Nat.two_pos

/-! ## The direct central `25 Δ e` estimate -/

/-- The graph induced by an open neighbourhood is `P₅`-free, since a
four-edge path there closes with its centre to a simple hexagon. -/
theorem erdos_gallai_neighborhood_direct (hC6 : WalkC6Free G) (v : V) :
    2 * (openNeighborhoodEdges G v).card ≤ 3 * G.degree v := by
  classical
  let S : Finset V := G.neighborFinset v
  let H : SimpleGraph (S : Set V) := G.induce (S : Set V)
  have hP5 : ¬ ∃ p : Fin 5 → (S : Set V), Function.Injective p ∧
      H.Adj (p 0) (p 1) ∧ H.Adj (p 1) (p 2) ∧
      H.Adj (p 2) (p 3) ∧ H.Adj (p 3) (p 4) := by
    rintro ⟨p, hp, h01, h12, h23, h34⟩
    have hpval : Function.Injective (fun i ↦ (p i).1) := by
      intro i j hij
      exact hp (Subtype.ext hij)
    have hv (i : Fin 5) : G.Adj v (p i).1 := by
      apply (G.mem_neighborFinset _ _).1
      simpa only [S, Finset.mem_coe] using (p i).2
    apply false_of_openNeighborhood_path_four G hC6
      (hv 0) (hv 1) (hv 2) (hv 3) (hv 4)
    · exact h01
    · exact h12
    · exact h23
    · exact h34
    · change List.Nodup (List.ofFn fun i : Fin 5 ↦ (p i).1)
      exact List.nodup_ofFn.mpr hpval
  have hEG := erdosGallai_path5 H hP5
  have hS : Fintype.card (S : Set V) = G.degree v := by
    simpa only [S, G.coe_neighborFinset] using
      G.card_neighborSet_eq_degree v
  have hedge : H.edgeFinset.card = (openNeighborhoodEdges G v).card := by
    dsimp only [H]
    rw [← G.card_filter_edgeFinset_toFinset_subset S]
    congr 1
    ext e
    simp only [Finset.mem_filter, openNeighborhoodEdges]
    constructor
    · rintro ⟨he, hsub⟩
      refine ⟨he, ?_⟩
      intro w hw
      change w ∈ S
      exact hsub (by simpa using hw)
    · rintro ⟨he, hadj⟩
      refine ⟨he, ?_⟩
      intro w hw
      change w ∈ S
      exact hadj w (by simpa using hw)
  rw [hedge, hS] at hEG
  exact hEG

/-- The direct open-neighbourhood estimate gives
`2 e[N[v]] ≤ 5 d(v)`. -/
theorem closedNeighborhoodEdgeCount_le_five_halves_direct
    (hC6 : WalkC6Free G) (v : V) :
    2 * closedNeighborhoodEdgeCount G v ≤ 5 * G.degree v := by
  dsimp [closedNeighborhoodEdgeCount]
  have h := erdos_gallai_neighborhood_direct G hC6 v
  omega

/-- The doubled number of paths charged to one closed neighbourhood is at
most `25 Δ d(v)`. -/
theorem twice_closedNeighborhoodPaths_le_direct
    (hC6 : WalkC6Free G) (v : V) :
    2 * (closedNeighborhoodPaths G v).card ≤
      25 * G.maxDegree * G.degree v := by
  let c := closedNeighborhoodEdgeCount G v
  let p := (closedNeighborhoodPaths G v).card
  have hp : p ≤ 2 * c ^ 2 := closed_path_pair_count_direct G v
  have hc : 2 * c ≤ 5 * G.degree v :=
    closedNeighborhoodEdgeCount_le_five_halves_direct G hC6 v
  have hd : G.degree v ≤ G.maxDegree := G.degree_le_maxDegree v
  calc
    2 * p ≤ 2 * (2 * c ^ 2) := Nat.mul_le_mul_left 2 hp
    _ = (2 * c) ^ 2 := by ring
    _ ≤ (5 * G.degree v) ^ 2 := Nat.pow_le_pow_left hc 2
    _ = 25 * G.degree v * G.degree v := by ring
    _ ≤ 25 * G.maxDegree * G.degree v := by
      exact Nat.mul_le_mul_right (G.degree v) (Nat.mul_le_mul_left 25 hd)

/-- The unconditional central/degenerate half of FNV Lemma 8.1. -/
theorem degenerate_multiplicity_bound_direct (hC6 : WalkC6Free G) :
    multiplicitySum G (degeneratePairs G) ≤
      25 * G.maxDegree * G.edgeFinset.card := by
  have hlocal :
      2 * (∑ v, (closedNeighborhoodPaths G v).card) ≤
        ∑ v, 25 * G.maxDegree * G.degree v := by
    simpa only [Finset.mul_sum] using
      Finset.sum_le_sum (fun v _ ↦
        twice_closedNeighborhoodPaths_le_direct G hC6 v)
  have hdegree : ∑ v, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hcentral := Nat.mul_le_mul_left 2 (central_charge_direct G)
  have htwo :
      2 * multiplicitySum G (degeneratePairs G) ≤
        2 * (25 * G.maxDegree * G.edgeFinset.card) := by
    calc
      2 * multiplicitySum G (degeneratePairs G)
          ≤ 2 * (∑ v, (closedNeighborhoodPaths G v).card) := hcentral
      _ ≤ ∑ v, 25 * G.maxDegree * G.degree v := hlocal
      _ = 2 * (25 * G.maxDegree * G.edgeFinset.card) := by
        rw [← Finset.mul_sum, hdegree]
        ring
  exact Nat.le_of_mul_le_mul_left htwo Nat.two_pos

end

end Erdos59
