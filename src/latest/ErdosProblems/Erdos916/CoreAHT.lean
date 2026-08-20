/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreRigidity

/-!
# The false-twin alternative for Erdős Problem 916

This file formalizes the elementary final step in the Aboulker--Havet--Trotignon
route.  Their wheel-free theorem produces nonadjacent degree-three vertices with
the same open neighbourhood.  Once two vertices of that common three-set also
have ambient degree three, either an edge inside the common neighbourhood gives
an explicit wheel, or the five vertices induce precisely the `K₂,₃` reduction
used by the density induction.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two vertices are false twins when their open neighbourhoods agree. -/
def AreFalseTwins (G : SimpleGraph V) (u v : V) : Prop :=
  u ≠ v ∧ G.neighborSet u = G.neighborSet v

namespace AreFalseTwins

theorem symm {u v : V} (h : AreFalseTwins G u v) : AreFalseTwins G v u := by
  exact ⟨h.1.symm, h.2.symm⟩

/-- Distinct vertices with equal open neighbourhoods cannot be adjacent in a
simple graph: otherwise one of them would belong to its own neighbourhood. -/
theorem not_adj {u v : V} (h : AreFalseTwins G u v) : ¬G.Adj u v := by
  intro huv
  have hvN : v ∈ G.neighborSet u := by simpa using huv
  have hvN' : v ∈ G.neighborSet v := by simpa only [h.2] using hvN
  exact G.loopless.irrefl v (by simpa using hvN')

theorem neighborFinset_eq {u v : V} (h : AreFalseTwins G u v) :
    G.neighborFinset u = G.neighborFinset v := by
  ext w
  simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborSet] using
    Set.ext_iff.mp h.2 w

theorem degree_eq {u v : V} (h : AreFalseTwins G u v) :
    G.degree u = G.degree v := by
  rw [← G.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree,
    h.neighborFinset_eq]

/-- False twins have exactly the same adjacency relation to every third
vertex. -/
theorem adj_iff {u v : V} (h : AreFalseTwins G u v) (w : V) :
    G.Adj u w ↔ G.Adj v w := by
  simpa only [SimpleGraph.mem_neighborSet] using
    Set.ext_iff.mp h.2 w

end AreFalseTwins

/-! ## An explicit wheel on five displayed vertices -/

/-- A four-cycle and a fifth vertex adjacent to three displayed rim vertices
give exactly the witness used in Problem 916. -/
theorem hasWheelWitness_of_fourCycle_threeSpokes
    {r0 r1 r2 r3 x : V}
    (h01 : G.Adj r0 r1) (h12 : G.Adj r1 r2)
    (h23 : G.Adj r2 r3) (h30 : G.Adj r3 r0)
    (hx0 : G.Adj x r0) (hx2 : G.Adj x r2) (hx3 : G.Adj x r3)
    (hr02 : r0 ≠ r2) (hr03 : r0 ≠ r3) (hr13 : r1 ≠ r3)
    (hxr0 : x ≠ r0) (hxr1 : x ≠ r1) (hxr2 : x ≠ r2) (hxr3 : x ≠ r3) :
    HasWheelWitness G := by
  let p : G.Walk r0 r0 :=
    .cons h01 (.cons h12 (.cons h23 (.cons h30 .nil)))
  have hp : p.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def]
    constructor
    · rw [SimpleGraph.Walk.isTrail_def]
      simp [p, h01.ne, h12.ne, h23.ne, h30.ne, hr02, hr02.symm,
        hr03, hr03.symm, hr13, hr13.symm]
    constructor
    · simp [p]
    · simp [p, h01.ne, h01.ne.symm, h12.ne, h23.ne, h30.ne,
        hr02, hr02.symm, hr03, hr03.symm, hr13, hr13.symm]
  refine ⟨r0, p, x, hp, ?_, ?_⟩
  · simp [p, hxr0, hxr1, hxr2, hxr3]
  · have h0 : r0 ∈ G.neighborFinset x ∩ p.support.toFinset := by simp [p, hx0]
    have h2 : r2 ∈ G.neighborFinset x ∩ p.support.toFinset := by simp [p, hx2]
    have h3 : r3 ∈ G.neighborFinset x ∩ p.support.toFinset := by simp [p, hx3]
    have hthree := Finset.two_lt_card_iff.mpr
      ⟨r0, r2, r3, h0, h2, h3, hr02, hr03, h23.ne⟩
    omega

/-- Two specified neighbours of a degree-three vertex leave a third,
different neighbour. -/
theorem exists_third_neighbor_of_degree_three
    {u a b : V} (hdeg : G.degree u = 3)
    (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b) :
    ∃ c : V, G.Adj u c ∧ c ≠ a ∧ c ≠ b := by
  have hcard : (G.neighborFinset u).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, hdeg]
  have haN : a ∈ G.neighborFinset u := by simpa using ha
  have hbN : b ∈ G.neighborFinset u := by simpa using hb
  have hpairSub : ({a, b} : Finset V) ⊆ G.neighborFinset u := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact haN
    · exact hbN
  have hpairCard : ({a, b} : Finset V).card = 2 := by simp [hab]
  have hpairNe : ({a, b} : Finset V) ≠ G.neighborFinset u := by
    intro heq
    have := congrArg Finset.card heq
    omega
  obtain ⟨c, hcN, hcPair⟩ :=
    Finset.exists_of_ssubset (hpairSub.ssubset_of_ne hpairNe)
  refine ⟨c, by simpa using hcN, ?_, ?_⟩
  · intro hca
    exact hcPair (by simp [hca])
  · intro hcb
    exact hcPair (by simp [hcb])

/-- If two common neighbours of degree-three false twins are adjacent, they
form the hub and one rim vertex of an explicit wheel.  Consequently, in a
wheel-free graph the common three-neighbourhood is stable. -/
theorem hasWheelWitness_of_falseTwins_of_adj_common
    {u v a b : V} (htwin : AreFalseTwins G u v)
    (hdeg : G.degree u = 3)
    (ha : G.Adj u a) (hb : G.Adj u b)
    (hab : a ≠ b) (habAdj : G.Adj a b) :
    HasWheelWitness G := by
  obtain ⟨c, hc, hca, hcb⟩ :=
    exists_third_neighbor_of_degree_three hdeg ha hb hab
  have hva : G.Adj v a := by
    rw [← SimpleGraph.mem_neighborFinset]
    rw [← htwin.neighborFinset_eq]
    simpa using ha
  have hvb : G.Adj v b := by
    rw [← SimpleGraph.mem_neighborFinset]
    rw [← htwin.neighborFinset_eq]
    simpa using hb
  have hvc : G.Adj v c := by
    rw [← SimpleGraph.mem_neighborFinset]
    rw [← htwin.neighborFinset_eq]
    simpa using hc
  exact hasWheelWitness_of_fourCycle_threeSpokes
    hc hvc.symm hvb hb.symm ha.symm hva.symm habAdj
    htwin.1 hb.ne hcb ha.ne.symm hca.symm hva.ne.symm hab

theorem not_adj_common_of_noWheel
    {u v a b : V} (htwin : AreFalseTwins G u v)
    (hdeg : G.degree u = 3) (hno : ¬HasWheelWitness G)
    (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b) :
    ¬G.Adj a b := by
  intro habAdj
  exact hno (hasWheelWitness_of_falseTwins_of_adj_common
    htwin hdeg ha hb hab habAdj)

/-! ## The local false-twin conversion -/

/-- Explicit degree-three false twins and an enumeration of their three common
neighbours.  The first two common neighbours are the two additional
degree-three vertices required by `K23Reduction`. -/
structure TwinTriple (G : SimpleGraph V) [DecidableRel G.Adj] where
  u : V
  v : V
  a : V
  b : V
  c : V
  huv : u ≠ v
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  neighbors_u : G.neighborFinset u = {a, b, c}
  neighbors_v : G.neighborFinset v = {a, b, c}
  degree_u : G.degree u = 3
  degree_v : G.degree v = 3
  degree_a : G.degree a = 3
  degree_b : G.degree b = 3

namespace TwinTriple

variable (T : TwinTriple G)

theorem adj_u_a : G.Adj T.u T.a := by
  rw [← SimpleGraph.mem_neighborFinset, T.neighbors_u]
  simp

theorem adj_u_b : G.Adj T.u T.b := by
  rw [← SimpleGraph.mem_neighborFinset, T.neighbors_u]
  simp

theorem adj_u_c : G.Adj T.u T.c := by
  rw [← SimpleGraph.mem_neighborFinset, T.neighbors_u]
  simp

theorem adj_v_a : G.Adj T.v T.a := by
  rw [← SimpleGraph.mem_neighborFinset, T.neighbors_v]
  simp

theorem adj_v_b : G.Adj T.v T.b := by
  rw [← SimpleGraph.mem_neighborFinset, T.neighbors_v]
  simp

theorem adj_v_c : G.Adj T.v T.c := by
  rw [← SimpleGraph.mem_neighborFinset, T.neighbors_v]
  simp

theorem u_ne_a : T.u ≠ T.a := (T.adj_u_a).ne
theorem u_ne_b : T.u ≠ T.b := (T.adj_u_b).ne
theorem u_ne_c : T.u ≠ T.c := (T.adj_u_c).ne
theorem v_ne_a : T.v ≠ T.a := (T.adj_v_a).ne
theorem v_ne_b : T.v ≠ T.b := (T.adj_v_b).ne
theorem v_ne_c : T.v ≠ T.c := (T.adj_v_c).ne

theorem not_adj_uv : ¬G.Adj T.u T.v := by
  intro huv
  have : T.v ∈ G.neighborFinset T.u := by simpa using huv
  rw [T.neighbors_u] at this
  rcases (by simpa using this : T.v = T.a ∨ T.v = T.b ∨ T.v = T.c) with h | h | h
  · exact T.v_ne_a h
  · exact T.v_ne_b h
  · exact T.v_ne_c h

/-- An internal edge of the common neighbourhood makes one endpoint the hub
of the four-cycle through the twins, the third neighbour, and the other
endpoint. -/
theorem wheel_of_adj_ab (h : G.Adj T.a T.b) : HasWheelWitness G := by
  exact hasWheelWitness_of_fourCycle_threeSpokes
    (T.adj_u_c) (T.adj_v_c.symm) (T.adj_v_b) (T.adj_u_b.symm)
    (T.adj_u_a.symm) (T.adj_v_a.symm) h
    T.huv T.u_ne_b T.hbc.symm T.u_ne_a.symm T.hac T.v_ne_a.symm T.hab

theorem wheel_of_adj_ac (h : G.Adj T.a T.c) : HasWheelWitness G := by
  exact hasWheelWitness_of_fourCycle_threeSpokes
    (T.adj_u_b) (T.adj_v_b.symm) (T.adj_v_c) (T.adj_u_c.symm)
    (T.adj_u_a.symm) (T.adj_v_a.symm) h
    T.huv T.u_ne_c T.hbc T.u_ne_a.symm T.hab T.v_ne_a.symm T.hac

theorem wheel_of_adj_bc (h : G.Adj T.b T.c) : HasWheelWitness G := by
  exact hasWheelWitness_of_fourCycle_threeSpokes
    (T.adj_u_a) (T.adj_v_a.symm) (T.adj_v_c) (T.adj_u_c.symm)
    (T.adj_u_b.symm) (T.adj_v_b.symm) h
    T.huv T.u_ne_c T.hac T.u_ne_b.symm T.hab.symm T.v_ne_b.symm T.hbc

/-- If the common three-set is stable, its union with the twin pair is an
induced `K₂,₃`, with the four requested degree-three vertices in the prescribed
positions. -/
def reduction_of_stable
    (hab : ¬G.Adj T.a T.b) (hac : ¬G.Adj T.a T.c) (hbc : ¬G.Adj T.b T.c) :
    K23Reduction G := by
  let f : Fin 2 ⊕ Fin 3 → V := fun z => match z with
    | .inl i => ![T.u, T.v] i
    | .inr j => ![T.a, T.b, T.c] j
  have hf_inj : Function.Injective f := by
    intro x y hxy
    rcases x with i | j <;> rcases y with i' | j'
    · fin_cases i <;> fin_cases i' <;> simp_all [f, T.huv, T.huv.symm]
    · fin_cases i <;> fin_cases j' <;>
        simp_all [f, T.u_ne_a, T.u_ne_b, T.u_ne_c,
          T.v_ne_a, T.v_ne_b, T.v_ne_c,
          T.u_ne_a.symm, T.u_ne_b.symm, T.u_ne_c.symm,
          T.v_ne_a.symm, T.v_ne_b.symm, T.v_ne_c.symm]
    · fin_cases j <;> fin_cases i' <;>
        simp_all [f, T.u_ne_a, T.u_ne_b, T.u_ne_c,
          T.v_ne_a, T.v_ne_b, T.v_ne_c,
          T.u_ne_a.symm, T.u_ne_b.symm, T.u_ne_c.symm,
          T.v_ne_a.symm, T.v_ne_b.symm, T.v_ne_c.symm]
    · fin_cases j <;> fin_cases j' <;>
        simp_all [f, T.hab, T.hac, T.hbc, T.hab.symm, T.hac.symm, T.hbc.symm]
  have hnvu : ¬G.Adj T.v T.u := fun h => T.not_adj_uv h.symm
  have hba : ¬G.Adj T.b T.a := fun h => hab h.symm
  have hca : ¬G.Adj T.c T.a := fun h => hac h.symm
  have hcb : ¬G.Adj T.c T.b := fun h => hbc h.symm
  let copy : completeBipartiteGraph (Fin 2) (Fin 3) ↪g G :=
    { toFun := f
      inj' := hf_inj
      map_rel_iff' := by
        intro x y
        rcases x with i | j <;> rcases y with i' | j'
        · fin_cases i <;> fin_cases i' <;> simp [f, T.not_adj_uv, hnvu]
        · fin_cases i <;> fin_cases j' <;>
            simp [f, T.adj_u_a, T.adj_u_b, T.adj_u_c,
              T.adj_v_a, T.adj_v_b, T.adj_v_c]
        · fin_cases j <;> fin_cases i' <;>
            simp [f, T.adj_u_a, T.adj_u_b, T.adj_u_c,
              T.adj_v_a, T.adj_v_b, T.adj_v_c,
              T.adj_u_a.symm, T.adj_u_b.symm, T.adj_u_c.symm,
              T.adj_v_a.symm, T.adj_v_b.symm, T.adj_v_c.symm]
        · fin_cases j <;> fin_cases j' <;>
            simp [f, hab, hac, hbc, hba, hca, hcb] }
  exact
    { copy := copy
      degree_left := by
        intro i
        fin_cases i
        · exact T.degree_u
        · exact T.degree_v
      degree_right := by
        intro j
        fin_cases j
        · exact T.degree_a
        · exact T.degree_b }

/-- The elementary AHT-to-Thomassen conversion. -/
theorem wheel_or_reduction (T : TwinTriple G) :
    HasWheelWitness G ∨ Nonempty (K23Reduction G) := by
  by_cases hab : G.Adj T.a T.b
  · exact Or.inl (T.wheel_of_adj_ab hab)
  by_cases hac : G.Adj T.a T.c
  · exact Or.inl (T.wheel_of_adj_ac hac)
  by_cases hbc : G.Adj T.b T.c
  · exact Or.inl (T.wheel_of_adj_bc hbc)
  exact Or.inr ⟨T.reduction_of_stable hab hac hbc⟩

end TwinTriple

/-! ## Packaging an AHT false-twin pair -/

/-- Enumerate the common neighbourhood of degree-three false twins, placing
two specified degree-three common neighbours first. -/
theorem exists_twinTriple_of_falseTwins
    {u v a b : V} (htwin : AreFalseTwins G u v)
    (hdeg : G.degree u = 3)
    (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b)
    (hdega : G.degree a = 3) (hdegb : G.degree b = 3) :
    ∃ T : TwinTriple G,
      T.u = u ∧ T.v = v ∧ T.a = a ∧ T.b = b := by
  have hcard : (G.neighborFinset u).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, hdeg]
  have haN : a ∈ G.neighborFinset u := by simpa using ha
  have hbN : b ∈ G.neighborFinset u := by simpa using hb
  have hpairSub : ({a, b} : Finset V) ⊆ G.neighborFinset u := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact haN
    · exact hbN
  have hpairCard : ({a, b} : Finset V).card = 2 := by simp [hab]
  have hpairNe : ({a, b} : Finset V) ≠ G.neighborFinset u := by
    intro heq
    have := congrArg Finset.card heq
    omega
  have hstrict : ({a, b} : Finset V) ⊂ G.neighborFinset u :=
    hpairSub.ssubset_of_ne hpairNe
  obtain ⟨c, hcN, hcPair⟩ := Finset.exists_of_ssubset hstrict
  have hac : a ≠ c := by
    intro h
    apply hcPair
    simp [h]
  have hbc : b ≠ c := by
    intro h
    apply hcPair
    simp [h]
  have htripleSub : ({a, b, c} : Finset V) ⊆ G.neighborFinset u := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact haN
    · exact hbN
    · exact hcN
  have htripleCard : ({a, b, c} : Finset V).card = 3 := by
    simp [hab, hac, hbc]
  have hNu : G.neighborFinset u = {a, b, c} := by
    exact (Finset.eq_of_subset_of_card_le htripleSub (by omega)).symm
  have hNv : G.neighborFinset v = {a, b, c} := by
    rw [← htwin.neighborFinset_eq, hNu]
  let T : TwinTriple G :=
    { u := u
      v := v
      a := a
      b := b
      c := c
      huv := htwin.1
      hab := hab
      hac := hac
      hbc := hbc
      neighbors_u := hNu
      neighbors_v := hNv
      degree_u := hdeg
      degree_v := htwin.degree_eq.symm.trans hdeg
      degree_a := hdega
      degree_b := hdegb }
  exact ⟨T, rfl, rfl, rfl, rfl⟩

/-- A degree-three AHT false-twin pair with two degree-three common neighbours
already yields the full structural alternative required by the density
induction. -/
theorem wheel_or_reduction_of_falseTwins
    {u v a b : V} (htwin : AreFalseTwins G u v)
    (hdeg : G.degree u = 3)
    (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b)
    (hdega : G.degree a = 3) (hdegb : G.degree b = 3) :
    HasWheelWitness G ∨ Nonempty (K23Reduction G) := by
  obtain ⟨T, -, -, -, -⟩ :=
    exists_twinTriple_of_falseTwins htwin hdeg ha hb hab hdega hdegb
  exact T.wheel_or_reduction

/-- Finset-cardinality form of `wheel_or_reduction_of_falseTwins`: at least
two degree-three vertices in the common neighbourhood suffice. -/
theorem wheel_or_reduction_of_falseTwins_card
    {u v : V} (htwin : AreFalseTwins G u v)
    (hdeg : G.degree u = 3)
    (hcommon : 2 ≤
      ((G.neighborFinset u).filter fun w => G.degree w = 3).card) :
    HasWheelWitness G ∨ Nonempty (K23Reduction G) := by
  have htwo : 1 <
      ((G.neighborFinset u).filter fun w => G.degree w = 3).card := by
    omega
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp htwo
  simp only [Finset.mem_filter] at ha hb
  exact wheel_or_reduction_of_falseTwins htwin hdeg
    (by simpa using ha.1) (by simpa using hb.1) hab ha.2 hb.2

/-! ## Equivalence with the exact Thomassen--Toft certificate -/

/-- The exact enriched false-twin statement which is equivalent to the
`K₂,₃` branch of Thomassen--Toft: the common three-neighbourhood contains
two ambient degree-three vertices. -/
def HasRichFalseTwins (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ u v : V,
    AreFalseTwins G u v ∧ G.degree u = 3 ∧
      2 ≤ ((G.neighborFinset u).filter fun w => G.degree w = 3).card

/-- If two degree-three false-twin pairs have any edge between the pairs,
then the first pair is rich.  Indeed one cross edge forces all four cross
edges, so both vertices of the second pair are degree-three common
neighbours of the first pair.  Thus, after the AHT two-pair theorem, only
the cross-anticomplete case requires further structural analysis. -/
theorem hasRichFalseTwins_of_crossing_pairs
    {u v x y : V}
    (huv : AreFalseTwins G u v) (hxy : AreFalseTwins G x y)
    (hdegu : G.degree u = 3) (hdegx : G.degree x = 3)
    (hcross : G.Adj u x ∨ G.Adj u y ∨ G.Adj v x ∨ G.Adj v y) :
    HasRichFalseTwins G := by
  have hux : G.Adj u x := by
    rcases hcross with hux | huy | hvx | hvy
    · exact hux
    · have hyu : G.Adj y u := huy.symm
      exact ((hxy.adj_iff u).mpr hyu).symm
    · exact (huv.adj_iff x).mpr hvx
    · have huy : G.Adj u y := (huv.adj_iff y).mpr hvy
      have hyu : G.Adj y u := huy.symm
      exact ((hxy.adj_iff u).mpr hyu).symm
  have huy : G.Adj u y := by
    exact ((hxy.adj_iff u).mp hux.symm).symm
  have hdegy : G.degree y = 3 :=
    hxy.degree_eq.symm.trans hdegx
  have hxmem : x ∈
      (G.neighborFinset u).filter (fun w => G.degree w = 3) := by
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact ⟨hux, hdegx⟩
  have hymem : y ∈
      (G.neighborFinset u).filter (fun w => G.degree w = 3) := by
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact ⟨huy, hdegy⟩
  have htwo : 1 <
      ((G.neighborFinset u).filter fun w => G.degree w = 3).card :=
    Finset.one_lt_card_iff.mpr ⟨x, y, hxmem, hymem, hxy.1⟩
  exact ⟨u, v, huv, hdegu, by omega⟩

/-- The crossing case of the AHT two-pair alternative already gives the
wheel-or-`K₂,₃` structural alternative used by the density induction. -/
theorem wheel_or_reduction_of_crossing_pairs
    {u v x y : V}
    (huv : AreFalseTwins G u v) (hxy : AreFalseTwins G x y)
    (hdegu : G.degree u = 3) (hdegx : G.degree x = 3)
    (hcross : G.Adj u x ∨ G.Adj u y ∨ G.Adj v x ∨ G.Adj v y) :
    HasWheelWitness G ∨ Nonempty (K23Reduction G) := by
  obtain ⟨u, v, htwin, hdeg, hcommon⟩ :=
    hasRichFalseTwins_of_crossing_pairs huv hxy hdegu hdegx hcross
  exact wheel_or_reduction_of_falseTwins_card htwin hdeg hcommon

/-- The two vertices in the size-two part of a `K₂,₃` reduction are rich
false twins.  This proves that the enriched false-twin target is not a
weaker reformulation: it is precisely the existing reduction certificate. -/
theorem hasRichFalseTwins_of_k23Reduction (R : K23Reduction G) :
    HasRichFalseTwins G := by
  let u : V := R.a 0
  let v : V := R.a 1
  let e : Fin 3 ↪ V :=
    ⟨fun j => R.b j, R.copy.injective.comp Sum.inr_injective⟩
  let N : Finset V := Finset.univ.map e
  have hNcard : N.card = 3 := by simp [N]
  have hNsub (i : Fin 2) : N ⊆ G.neighborFinset (R.a i) := by
    intro x hx
    simp only [N, Finset.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    rw [SimpleGraph.mem_neighborFinset]
    exact R.adj_a_b i j
  have hN_eq (i : Fin 2) : G.neighborFinset (R.a i) = N := by
    have hcard : (G.neighborFinset (R.a i)).card = 3 := by
      rw [G.card_neighborFinset_eq_degree, R.degree_left]
    exact (Finset.eq_of_subset_of_card_le (hNsub i) (by omega)).symm
  have huv : u ≠ v := by
    exact R.copy.injective.ne (by decide)
  have htwin : AreFalseTwins G u v := by
    refine ⟨huv, ?_⟩
    ext x
    simpa only [SimpleGraph.mem_neighborSet, ← SimpleGraph.mem_neighborFinset,
      u, v, hN_eq]
  have hdegU : G.degree u = 3 := by
    exact R.degree_left 0
  have hb0 : R.b 0 ∈
      (G.neighborFinset u).filter (fun w => G.degree w = 3) := by
    simp only [Finset.mem_filter]
    constructor
    · rw [SimpleGraph.mem_neighborFinset]
      exact R.adj_a_b 0 0
    · exact R.degree_right 0
  have hb1 : R.b 1 ∈
      (G.neighborFinset u).filter (fun w => G.degree w = 3) := by
    simp only [Finset.mem_filter]
    constructor
    · rw [SimpleGraph.mem_neighborFinset]
      exact R.adj_a_b 0 1
    · exact R.degree_right 1
  have hb01 : R.b 0 ≠ R.b 1 :=
    R.copy.injective.ne (by decide)
  have hcommon : 2 ≤
      ((G.neighborFinset u).filter fun w => G.degree w = 3).card := by
    have hone : 1 <
        ((G.neighborFinset u).filter fun w => G.degree w = 3).card :=
      Finset.one_lt_card_iff.mpr ⟨R.b 0, R.b 1, hb0, hb1, hb01⟩
    omega
  exact ⟨u, v, htwin, hdegU, hcommon⟩

/-- Rich false twins and the induced `K₂,₃` certificate are interchangeable
after adjoining the common wheel branch. -/
theorem wheel_or_richFalseTwins_iff_wheel_or_k23Reduction :
    (HasWheelWitness G ∨ HasRichFalseTwins G) ↔
      (HasWheelWitness G ∨ Nonempty (K23Reduction G)) := by
  constructor
  · rintro (hW | ⟨u, v, htwin, hdeg, hcommon⟩)
    · exact Or.inl hW
    · exact wheel_or_reduction_of_falseTwins_card htwin hdeg hcommon
  · intro h
    rcases h with hW | hR
    · exact Or.inl hW
    · rcases hR with ⟨R⟩
      exact Or.inr (hasRichFalseTwins_of_k23Reduction R)

/-! ## The density consequence of a three-terminal cut -/

/-- A vertex whose deletion has three explicitly grouped nonempty sides.
There are no edges between different sides, while all vertices other than
the cut vertex occur in exactly one side.  This is the precise certificate
needed from the elementary three-terminal path/cut theorem. -/
structure ThreeWayCut (G : SimpleGraph V) where
  cut : V
  left : Finset V
  middle : Finset V
  right : Finset V
  cut_not_left : cut ∉ left
  cut_not_middle : cut ∉ middle
  cut_not_right : cut ∉ right
  left_disjoint_middle : Disjoint left middle
  left_disjoint_right : Disjoint left right
  middle_disjoint_right : Disjoint middle right
  cover : insert cut (left ∪ middle ∪ right) = Finset.univ
  left_nonempty : left.Nonempty
  middle_nonempty : middle.Nonempty
  right_nonempty : right.Nonempty
  not_adj_left_middle :
    ∀ x, x ∈ left → ∀ y, y ∈ middle → ¬G.Adj x y
  not_adj_left_right :
    ∀ x, x ∈ left → ∀ y, y ∈ right → ¬G.Adj x y
  not_adj_middle_right :
    ∀ x, x ∈ middle → ∀ y, y ∈ right → ¬G.Adj x y

namespace ThreeWayCut

variable (T : ThreeWayCut G)

def leftPiece : Finset V := insert T.cut T.left
def middlePiece : Finset V := insert T.cut T.middle
def rightPiece : Finset V := insert T.cut T.right

private theorem pieces_inter_left_middle :
    T.leftPiece ∩ T.middlePiece = {T.cut} := by
  ext x
  simp only [leftPiece, middlePiece, Finset.mem_inter, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hx | hx, hy | hy⟩
    · exact hx
    · exact hx
    · exact hy
    · exact False.elim (Finset.disjoint_left.mp T.left_disjoint_middle hx hy)
  · intro hx
    exact ⟨Or.inl hx, Or.inl hx⟩

private theorem pieces_inter_left_right :
    T.leftPiece ∩ T.rightPiece = {T.cut} := by
  ext x
  simp only [leftPiece, rightPiece, Finset.mem_inter, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hx | hx, hy | hy⟩
    · exact hx
    · exact hx
    · exact hy
    · exact False.elim (Finset.disjoint_left.mp T.left_disjoint_right hx hy)
  · intro hx
    exact ⟨Or.inl hx, Or.inl hx⟩

private theorem pieces_inter_middle_right :
    T.middlePiece ∩ T.rightPiece = {T.cut} := by
  ext x
  simp only [middlePiece, rightPiece, Finset.mem_inter, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hx | hx, hy | hy⟩
    · exact hx
    · exact hx
    · exact hy
    · exact False.elim (Finset.disjoint_left.mp T.middle_disjoint_right hx hy)
  · intro hx
    exact ⟨Or.inl hx, Or.inl hx⟩

private theorem edgeFilters_disjoint_of_piece_inter_singleton
    (P Q : Finset V) (hPQ : P ∩ Q = {T.cut}) :
    Disjoint (G.edgeFinset ∩ P.sym2) (G.edgeFinset ∩ Q.sym2) := by
  rw [Finset.disjoint_left]
  intro e heP heQ
  cases e using Sym2.inductionOn with
  | _ x y =>
      simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset,
        Finset.mk_mem_sym2_iff] at heP heQ
      have hx : x ∈ P ∩ Q := Finset.mem_inter.mpr ⟨heP.2.1, heQ.2.1⟩
      have hy : y ∈ P ∩ Q := Finset.mem_inter.mpr ⟨heP.2.2, heQ.2.2⟩
      rw [hPQ] at hx hy
      simp only [Finset.mem_singleton] at hx hy
      subst x
      subst y
      exact G.loopless.irrefl T.cut heP.1

private theorem edge_left_disjoint_middle :
    Disjoint (G.edgeFinset ∩ T.leftPiece.sym2)
      (G.edgeFinset ∩ T.middlePiece.sym2) :=
  T.edgeFilters_disjoint_of_piece_inter_singleton
    T.leftPiece T.middlePiece T.pieces_inter_left_middle

private theorem edge_left_disjoint_right :
    Disjoint (G.edgeFinset ∩ T.leftPiece.sym2)
      (G.edgeFinset ∩ T.rightPiece.sym2) :=
  T.edgeFilters_disjoint_of_piece_inter_singleton
    T.leftPiece T.rightPiece T.pieces_inter_left_right

private theorem edge_middle_disjoint_right :
    Disjoint (G.edgeFinset ∩ T.middlePiece.sym2)
      (G.edgeFinset ∩ T.rightPiece.sym2) :=
  T.edgeFilters_disjoint_of_piece_inter_singleton
    T.middlePiece T.rightPiece T.pieces_inter_middle_right

private theorem edge_mem_one_piece {x y : V} (hxy : G.Adj x y) :
    (x ∈ T.leftPiece ∧ y ∈ T.leftPiece) ∨
      (x ∈ T.middlePiece ∧ y ∈ T.middlePiece) ∨
      (x ∈ T.rightPiece ∧ y ∈ T.rightPiece) := by
  have hcL : T.cut ∈ T.leftPiece := by simp [leftPiece]
  have hcM : T.cut ∈ T.middlePiece := by simp [middlePiece]
  have hcR : T.cut ∈ T.rightPiece := by simp [rightPiece]
  have hxall : x ∈ insert T.cut (T.left ∪ T.middle ∪ T.right) := by
    rw [T.cover]
    exact Finset.mem_univ x
  have hyall : y ∈ insert T.cut (T.left ∪ T.middle ∪ T.right) := by
    rw [T.cover]
    exact Finset.mem_univ y
  simp only [Finset.mem_insert, Finset.mem_union] at hxall hyall
  rcases hxall with hx | ((hxL | hxM) | hxR)
  · subst x
    rcases hyall with hy | ((hyL | hyM) | hyR)
    · subst y
      exact False.elim (G.loopless.irrefl T.cut hxy)
    · exact Or.inl ⟨hcL, Finset.mem_insert_of_mem hyL⟩
    · exact Or.inr (Or.inl
        ⟨hcM, Finset.mem_insert_of_mem hyM⟩)
    · exact Or.inr (Or.inr
        ⟨hcR, Finset.mem_insert_of_mem hyR⟩)
  · rcases hyall with hy | ((hyL | hyM) | hyR)
    · subst y
      exact Or.inl ⟨Finset.mem_insert_of_mem hxL, hcL⟩
    · exact Or.inl
        ⟨Finset.mem_insert_of_mem hxL, Finset.mem_insert_of_mem hyL⟩
    · exact False.elim
        (T.not_adj_left_middle x hxL y hyM hxy)
    · exact False.elim
        (T.not_adj_left_right x hxL y hyR hxy)
  · rcases hyall with hy | ((hyL | hyM) | hyR)
    · subst y
      exact Or.inr (Or.inl
        ⟨Finset.mem_insert_of_mem hxM, hcM⟩)
    · exact False.elim
        (T.not_adj_left_middle y hyL x hxM hxy.symm)
    · exact Or.inr (Or.inl
        ⟨Finset.mem_insert_of_mem hxM, Finset.mem_insert_of_mem hyM⟩)
    · exact False.elim
        (T.not_adj_middle_right x hxM y hyR hxy)
  · rcases hyall with hy | ((hyL | hyM) | hyR)
    · subst y
      exact Or.inr (Or.inr
        ⟨Finset.mem_insert_of_mem hxR, hcR⟩)
    · exact False.elim
        (T.not_adj_left_right y hyL x hxR hxy.symm)
    · exact False.elim
        (T.not_adj_middle_right y hyM x hxR hxy.symm)
    · exact Or.inr (Or.inr
        ⟨Finset.mem_insert_of_mem hxR, Finset.mem_insert_of_mem hyR⟩)

private theorem edge_filter_union :
    ((G.edgeFinset ∩ T.leftPiece.sym2) ∪
      (G.edgeFinset ∩ T.middlePiece.sym2)) ∪
      (G.edgeFinset ∩ T.rightPiece.sym2) = G.edgeFinset := by
  ext e
  constructor
  · simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  · intro he
    cases e using Sym2.inductionOn with
    | _ x y =>
      have hxy : G.Adj x y := by simpa using he
      rcases T.edge_mem_one_piece hxy with hL | hM | hR
      · simp only [Finset.mem_union, Finset.mem_inter,
          SimpleGraph.mem_edgeFinset, Finset.mk_mem_sym2_iff]
        exact Or.inl (Or.inl ⟨hxy, hL⟩)
      · simp only [Finset.mem_union, Finset.mem_inter,
          SimpleGraph.mem_edgeFinset, Finset.mk_mem_sym2_iff]
        exact Or.inl (Or.inr ⟨hxy, hM⟩)
      · simp only [Finset.mem_union, Finset.mem_inter,
          SimpleGraph.mem_edgeFinset, Finset.mk_mem_sym2_iff]
        exact Or.inr ⟨hxy, hR⟩

/-- A `(2,3)`-sparse graph admitting a three-way one-vertex cut has at most
`2n-5` edges.  Each of the three cut pieces contributes the usual `-3`,
while the common cut vertex is counted three times. -/
theorem edge_card_add_five_le (T : ThreeWayCut G) (hsparse : Is23Sparse G) :
    G.edgeFinset.card + 5 ≤ 2 * Fintype.card V := by
  let EL := G.edgeFinset ∩ (leftPiece T).sym2
  let EM := G.edgeFinset ∩ (middlePiece T).sym2
  let ER := G.edgeFinset ∩ (rightPiece T).sym2
  have hLM : Disjoint EL EM := edge_left_disjoint_middle T
  have hLR : Disjoint EL ER := edge_left_disjoint_right T
  have hMR : Disjoint EM ER := edge_middle_disjoint_right T
  have hLMR : Disjoint (EL ∪ EM) ER := Finset.disjoint_union_left.mpr ⟨hLR, hMR⟩
  have hcardEdges := congrArg Finset.card (edge_filter_union T)
  rw [Finset.card_union_of_disjoint hLMR,
    Finset.card_union_of_disjoint hLM] at hcardEdges
  have hEL := G.card_filter_edgeFinset_toFinset_subset (leftPiece T)
  have hEM := G.card_filter_edgeFinset_toFinset_subset (middlePiece T)
  have hER := G.card_filter_edgeFinset_toFinset_subset (rightPiece T)
  rw [G.filter_edgeFinset_toFinset_subset] at hEL hEM hER
  have hLcard : (leftPiece T).card = T.left.card + 1 := by
    simp [leftPiece, T.cut_not_left]
  have hMcard : (middlePiece T).card = T.middle.card + 1 := by
    simp [middlePiece, T.cut_not_middle]
  have hRcard : (rightPiece T).card = T.right.card + 1 := by
    simp [rightPiece, T.cut_not_right]
  have hL2 : 2 ≤ (leftPiece T).card := by
    obtain ⟨x, hx⟩ := T.left_nonempty
    rw [hLcard]
    exact Nat.add_le_add_right (Finset.one_le_card.mpr ⟨x, hx⟩) 1
  have hM2 : 2 ≤ (middlePiece T).card := by
    obtain ⟨x, hx⟩ := T.middle_nonempty
    rw [hMcard]
    exact Nat.add_le_add_right (Finset.one_le_card.mpr ⟨x, hx⟩) 1
  have hR2 : 2 ≤ (rightPiece T).card := by
    obtain ⟨x, hx⟩ := T.right_nonempty
    rw [hRcard]
    exact Nat.add_le_add_right (Finset.one_le_card.mpr ⟨x, hx⟩) 1
  have hsL := hsparse (leftPiece T) hL2
  have hsM := hsparse (middlePiece T) hM2
  have hsR := hsparse (rightPiece T) hR2
  have hsideCard :
      T.left.card + T.middle.card + T.right.card + 1 = Fintype.card V := by
    have hcoverCard := congrArg Finset.card T.cover
    have hdisjLM : Disjoint T.left T.middle := T.left_disjoint_middle
    have hdisjLMR : Disjoint (T.left ∪ T.middle) T.right :=
      Finset.disjoint_union_left.mpr
        ⟨T.left_disjoint_right, T.middle_disjoint_right⟩
    rw [Finset.card_insert_of_notMem, Finset.card_union_of_disjoint hdisjLMR,
      Finset.card_union_of_disjoint hdisjLM, Finset.card_univ] at hcoverCard
    · omega
    · simp only [Finset.mem_union]
      rintro ((hL | hM) | hR)
      · exact T.cut_not_left hL
      · exact T.cut_not_middle hM
      · exact T.cut_not_right hR
  dsimp only [EL, EM, ER] at hcardEdges
  omega

end ThreeWayCut

end Erdos916
