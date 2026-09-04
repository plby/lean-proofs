/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSourceLemma
import ErdosProblems.Erdos916.AHTSourceLemma62
import ErdosProblems.Erdos916.AHTSection6
import ErdosProblems.Erdos916.AHTMader41
import ErdosProblems.Erdos916.AHTMinimalThreeConnected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# The close-to-twins step in AHT Lemma 6.5

Aboulker--Havet--Trotignon use the word *twins* for two nonadjacent
degree-three vertices with the same open neighbourhood.  Thus their notion
is slightly stronger than `AreFalseTwins`, which deliberately contains only
the distinctness and neighbourhood-equality clauses.

This file gives the source-exact definition of “close to a twin” and proves
the final, unconditional part of AHT Lemma 6.5.  Once one twin pair
`u,v`, with common neighbourhood `x,y,z`, has been found, the paper first
rules out any additional common neighbour of two of `x,y,z`.  A degree-three
vertex outside these five vertices which is close to a twin then supplies a
second twin pair disjoint from `u,v`.  The proof below formalizes precisely
that argument.

The preceding existence argument in the published proof invokes Mader's two
theorems on minimally three-connected graphs, as well as AHT Lemma 6.2 for
the exceptional `K_{3,3} \ e` branch.  Those genuinely separate inputs are
not hidden here behind a principle-valued definition.
-/

namespace Erdos916

open _root_.SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- AHT's source definition of a pair of twins: false twins whose (common)
degree is three. -/
def AHTTwinPair (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : Prop :=
  AreFalseTwins G u v ∧ G.degree u = 3

namespace AHTTwinPair

theorem falseTwins {u v : V} (h : AHTTwinPair G u v) :
    AreFalseTwins G u v := h.1

theorem degree_left {u v : V} (h : AHTTwinPair G u v) :
    G.degree u = 3 := h.2

theorem degree_right {u v : V} (h : AHTTwinPair G u v) :
    G.degree v = 3 := by
  exact h.1.degree_eq.symm.trans h.2

theorem symm {u v : V} (h : AHTTwinPair G u v) :
    AHTTwinPair G v u := by
  exact ⟨h.1.symm, h.degree_right⟩

end AHTTwinPair

/-- A vertex is close to a twin in the sense of AHT if it belongs to a
degree-three false-twin pair, or is adjacent to a member of such a pair. -/
def IsCloseToAHTTwin (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V) : Prop :=
  ∃ u v : V, AHTTwinPair G u v ∧
    (w = u ∨ w = v ∨ G.Adj w u ∨ G.Adj w v)

theorem AHTTwinPair.close_left {u v : V} (h : AHTTwinPair G u v) :
    IsCloseToAHTTwin G u := by
  exact ⟨u, v, h, Or.inl rfl⟩

theorem AHTTwinPair.close_right {u v : V} (h : AHTTwinPair G u v) :
    IsCloseToAHTTwin G v := by
  exact ⟨u, v, h, Or.inr (Or.inl rfl)⟩

theorem IsCloseToAHTTwin.of_adj_left {u v w : V}
    (h : AHTTwinPair G u v) (hwu : G.Adj w u) :
    IsCloseToAHTTwin G w := by
  exact ⟨u, v, h, Or.inr (Or.inr (Or.inl hwu))⟩

theorem IsCloseToAHTTwin.of_adj_right {u v w : V}
    (h : AHTTwinPair G u v) (hwv : G.Adj w v) :
    IsCloseToAHTTwin G w := by
  exact ⟨u, v, h, Or.inr (Or.inr (Or.inr hwv))⟩

/-! ## Elementary control of the exceptional wheel centres -/

/-- Every wheel centre of an almost-wheel-free graph has degree three. -/
theorem AlmostWheelFree.degree_eq_three_of_center
    (h : AlmostWheelFree G) {w : V} (hw : HasWheelCenteredAt G w) :
    G.degree w = 3 := by
  rcases h with hnone | hone | htwo
  · exact False.elim (hnone w hw)
  · obtain ⟨a, hdeg, hcentres⟩ := hone
    rw [hcentres w hw]
    exact hdeg
  · obtain ⟨a, b, -, hdega, hdegb, hcentres⟩ := htwo
    rcases hcentres w hw with rfl | rfl
    · exact hdega
    · exact hdegb

/-- Distinct wheel centres of an almost-wheel-free graph are adjacent. -/
theorem AlmostWheelFree.eq_or_adj_of_centers
    (h : AlmostWheelFree G) {p q : V}
    (hp : HasWheelCenteredAt G p) (hq : HasWheelCenteredAt G q) :
    p = q ∨ G.Adj p q := by
  rcases h with hnone | hone | htwo
  · exact False.elim (hnone p hp)
  · obtain ⟨a, -, hcentres⟩ := hone
    left
    exact (hcentres p hp).trans (hcentres q hq).symm
  · obtain ⟨a, b, hab, -, -, hcentres⟩ := htwo
    rcases hcentres p hp with rfl | rfl <;>
      rcases hcentres q hq with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hab
    · exact Or.inr hab.symm
    · exact Or.inl rfl

/-- The wheel centres adjacent to a displayed vertex. -/
noncomputable def centerNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V) : Finset V := by
  classical
  exact (G.neighborFinset w).filter fun q => HasWheelCenteredAt G q

/-- The finite set of all wheel centres.  This is the set denoted `W(G)`
in Section 6 of AHT. -/
noncomputable def wheelCenters (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset V := by
  classical
  exact Finset.univ.filter fun q => HasWheelCenteredAt G q

@[simp] theorem mem_wheelCenters {q : V} :
    q ∈ wheelCenters G ↔ HasWheelCenteredAt G q := by
  classical
  rw [wheelCenters, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨Finset.mem_univ q, h⟩

/-- An almost-wheel-free graph has at most two wheel centres. -/
theorem card_wheelCenters_le_two (halmost : AlmostWheelFree G) :
    (wheelCenters G).card ≤ 2 := by
  classical
  rcases halmost with hnone | hone | htwo
  · have hempty : wheelCenters G = ∅ := by
      ext q
      simp only [mem_wheelCenters, Finset.notMem_empty, iff_false]
      exact hnone q
    simp [hempty]
  · obtain ⟨a, -, hcentres⟩ := hone
    have hsub : wheelCenters G ⊆ {a} := by
      intro q hq
      simpa using hcentres q (mem_wheelCenters.mp hq)
    calc
      (wheelCenters G).card ≤ ({a} : Finset V).card :=
        Finset.card_le_card hsub
      _ ≤ 2 := by simp
  · obtain ⟨a, b, -, -, -, hcentres⟩ := htwo
    have hsub : wheelCenters G ⊆ {a, b} := by
      intro q hq
      simpa using hcentres q (mem_wheelCenters.mp hq)
    calc
      (wheelCenters G).card ≤ ({a, b} : Finset V).card :=
        Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two

/-- Three degree-three vertices cannot all be wheel centres in an
almost-wheel-free graph.  This is the counting selection used at the start
of AHT Lemma 6.5 after Mader's bound has supplied the three vertices. -/
theorem exists_degreeThree_not_wheelCenter
    (halmost : AlmostWheelFree G)
    (hthreeVertices : 3 ≤
      (Finset.univ.filter fun q : V => G.degree q = 3).card) :
    ∃ q : V, G.degree q = 3 ∧ ¬HasWheelCenteredAt G q := by
  classical
  let D : Finset V := Finset.univ.filter fun q : V => G.degree q = 3
  have hW : (wheelCenters G).card ≤ 2 := card_wheelCenters_le_two halmost
  have hlt : (wheelCenters G).card < D.card := by
    dsimp only [D]
    omega
  obtain ⟨q, hqD, hqW⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt
  have hqdeg : G.degree q = 3 := by simpa [D] using hqD
  have hqcenter : ¬HasWheelCenteredAt G q := by
    simpa only [mem_wheelCenters] using hqW
  exact ⟨q, hqdeg, hqcenter⟩

/-- The close-to-a-twin hypothesis and the three-vertex count produce the
first source twin pair in Lemma 6.5. -/
theorem exists_ahtTwinPair_of_three_degreeThreeVertices
    (halmost : AlmostWheelFree G)
    (hthreeVertices : 3 ≤
      (Finset.univ.filter fun q : V => G.degree q = 3).card)
    (hclose : ∀ q : V, G.degree q = 3 →
      ¬HasWheelCenteredAt G q → IsCloseToAHTTwin G q) :
    ∃ u v : V, AHTTwinPair G u v := by
  obtain ⟨q, hqdeg, hqcenter⟩ :=
    exists_degreeThree_not_wheelCenter halmost hthreeVertices
  obtain ⟨u, v, huv, -⟩ := hclose q hqdeg hqcenter
  exact ⟨u, v, huv⟩

/-- A three-connected triangle-free graph has at least five vertices.  The
four-vertex case is `K₄`, hence contains a triangle. -/
theorem five_le_card_of_threeConnected_triangleFree
    (hthree : IsThreeConnected G) (htri : AHTTriangleFree G) :
    5 ≤ Fintype.card V := by
  classical
  have hfour : 4 ≤ Fintype.card V := hthree.four_le_card
  by_contra hnotFive
  have hcard : Fintype.card V = 4 := by omega
  have hdeg (q : V) : G.degree q = 3 := by
    have hlo := hthree.degree_ge q
    have hhi := G.degree_lt_card_verts q
    omega
  have huniv (q : V) : G.IsUniversal q := by
    rw [← G.degree_eq_card_sub_one q, hcard]
    exact hdeg q
  have htop : G = ⊤ := G.eq_top_iff_forall_isUniversal.mpr huniv
  have hpos : 0 < Fintype.card V := by omega
  let q : V := Classical.choice (Fintype.card_pos_iff.mp hpos)
  obtain ⟨a, b, c, hab, -, -, hN⟩ :=
    exists_three_neighbors_of_degree_eq_three (hdeg q)
  have hqa : G.Adj q a := by
    rw [← SimpleGraph.mem_neighborFinset, hN]
    simp
  have hqb : G.Adj q b := by
    rw [← SimpleGraph.mem_neighborFinset, hN]
    simp
  have habAdj : G.Adj a b := by
    rw [htop]
    simpa using hab
  exact htri hqa habAdj hqb.symm

/-- Mader's exact count supplies the first twin pair under the hypotheses
available before the `K_{3,3} \ e` split in Lemma 6.5. -/
theorem exists_ahtTwinPair_of_edgeMinimallyThreeConnected
    (hmin : IsEdgeMinimallyThreeConnected G)
    (halmost : AlmostWheelFree G)
    (hclose : ∀ q : V, G.degree q = 3 →
      ¬HasWheelCenteredAt G q → IsCloseToAHTTwin G q) :
    ∃ u v : V, AHTTwinPair G u v := by
  have hthree : IsThreeConnected G := hmin.isThreeConnected
  have htri : AHTTriangleFree G :=
    aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  have hcard : 5 ≤ Fintype.card V :=
    five_le_card_of_threeConnected_triangleFree hthree htri
  have hM : MaderCycleProperty G :=
    maderCycleProperty_of_isEdgeMinimallyThreeConnected hmin
  have hthreeVertices : 3 ≤
      (Finset.univ.filter fun q : V => G.degree q = 3).card :=
    three_le_card_degree_eq_three_of_five_le hcard hthree hM
  exact exists_ahtTwinPair_of_three_degreeThreeVertices
    halmost hthreeVertices hclose

/-- A nonempty finite graph of minimum degree at least two contains a
cycle.  This elementary forest lemma is the graph-theoretic step used for
`G[R \ W(G)]` in AHT Lemma 6.5. -/
theorem exists_cycle_of_nonempty_of_forall_two_le_degree
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (hne : Nonempty W) (hdeg : ∀ w : W, 2 ≤ H.degree w) :
    ∃ r : W, ∃ p : H.Walk r r, p.IsCycle := by
  classical
  by_contra hcycle
  have hacyc : H.IsAcyclic := by
    intro r p hp
    exact hcycle ⟨r, p, hp⟩
  let q : W := Classical.choice hne
  let C : H.ConnectedComponent := H.connectedComponentMk q
  have hqpos : 0 < H.degree q := by
    exact lt_of_lt_of_le (by omega) (hdeg q)
  obtain ⟨w, hqw⟩ := (H.degree_pos_iff_exists_adj q).mp hqpos
  have hqC : q ∈ C := by
    simpa [C] using
      (ConnectedComponent.connectedComponentMk_mem (G := H) (v := q))
  have hwC : w ∈ C := C.mem_supp_of_adj_mem_supp hqC hqw
  let qC : C := ⟨q, hqC⟩
  let wC : C := ⟨w, hwC⟩
  have hqCwC : qC ≠ wC := by
    intro h
    exact hqw.ne (congrArg Subtype.val h)
  let : Nontrivial C := ⟨⟨qC, wC, hqCwC⟩⟩
  let : DecidableRel C.toSimpleGraph.Adj := fun a b =>
    inferInstanceAs (Decidable (H.Adj a.1 b.1))
  have htree : C.toSimpleGraph.IsTree :=
    hacyc.isTree_connectedComponent C
  obtain ⟨leaf, hleaf⟩ := htree.exists_vert_degree_one_of_nontrivial
  have hclosed : H.neighborSet leaf.1 ⊆ C.supp := by
    intro z hz
    exact C.mem_supp_of_adj_mem_supp leaf.property hz
  let e : H.neighborSet leaf.1 ≃ C.toSimpleGraph.neighborSet leaf :=
    { toFun := fun z => ⟨⟨z.1, hclosed z.2⟩, z.2⟩
      invFun := fun z => ⟨z.1.1, z.2⟩
      left_inv := by intro z; exact Subtype.ext rfl
      right_inv := by intro z; exact Subtype.ext (Subtype.ext rfl) }
  have hdegreeEq : H.degree leaf.1 = C.toSimpleGraph.degree leaf := by
    have hcard := Fintype.card_congr e
    rw [H.card_neighborSet_eq_degree,
      C.toSimpleGraph.card_neighborSet_eq_degree] at hcard
    exact hcard
  have hleafLower : 2 ≤ C.toSimpleGraph.degree leaf := by
    rw [← hdegreeEq]
    exact hdeg leaf.1
  omega

/-- An ambient graph isomorphic to `K₃,₃` has the two disjoint degree-three
false-twin pairs needed in Lemma 6.5. -/
theorem twoDisjointPairs_of_isomorphic_k33
    (hiso : Nonempty
      (completeBipartiteGraph (Fin 3) (Fin 3) ≃g G)) :
    Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G) := by
  classical
  obtain ⟨f⟩ := hiso
  let K : SimpleGraph (Fin 3 ⊕ Fin 3) :=
    completeBipartiteGraph (Fin 3) (Fin 3)
  let l₀ : Fin 3 ⊕ Fin 3 := Sum.inl 0
  let l₁ : Fin 3 ⊕ Fin 3 := Sum.inl 1
  let r₀ : Fin 3 ⊕ Fin 3 := Sum.inr 0
  let r₁ : Fin 3 ⊕ Fin 3 := Sum.inr 1
  have htwinL : AreFalseTwins G (f l₀) (f l₁) := by
    constructor
    · intro h
      have := f.injective h
      simp [l₀, l₁] at this
    · ext w
      obtain ⟨t, rfl⟩ := f.surjective w
      simp only [SimpleGraph.mem_neighborSet]
      rw [f.map_rel_iff, f.map_rel_iff]
      rcases t with t | t <;> simp [K, l₀, l₁]
  have htwinR : AreFalseTwins G (f r₀) (f r₁) := by
    constructor
    · intro h
      have := f.injective h
      simp [r₀, r₁] at this
    · ext w
      obtain ⟨t, rfl⟩ := f.surjective w
      simp only [SimpleGraph.mem_neighborSet]
      rw [f.map_rel_iff, f.map_rel_iff]
      rcases t with t | t <;> simp [K, r₀, r₁]
  have hNL : K.neighborFinset l₀ =
      ({Sum.inr 0, Sum.inr 1, Sum.inr 2} :
        Finset (Fin 3 ⊕ Fin 3)) := by
    ext t
    rcases t with t | t
    · simp [K, l₀]
    · fin_cases t <;> simp [K, l₀]
  have hNR : K.neighborFinset r₀ =
      ({Sum.inl 0, Sum.inl 1, Sum.inl 2} :
        Finset (Fin 3 ⊕ Fin 3)) := by
    ext t
    rcases t with t | t
    · fin_cases t <;> simp [K, r₀]
    · simp [K, r₀]
  have hKdegL : K.degree l₀ = 3 := by
    rw [← K.card_neighborFinset_eq_degree, hNL]
    simp
  have hKdegR : K.degree r₀ = 3 := by
    rw [← K.card_neighborFinset_eq_degree, hNR]
    simp
  have hdegL : G.degree (f l₀) = 3 :=
    (f.degree_eq l₀).trans hKdegL
  have hdegR : G.degree (f r₀) = 3 :=
    (f.degree_eq r₀).trans hKdegR
  have hdisj : Disjoint ({f l₀, f l₁} : Finset V)
      ({f r₀, f r₁} : Finset V) := by
    rw [Finset.disjoint_left]
    intro q hqL hqR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqL hqR
    rcases hqL with hqL | hqL <;> rcases hqR with hqR | hqR
    · have h := f.injective (hqL.symm.trans hqR)
      simp [l₀, r₀] at h
    · have h := f.injective (hqL.symm.trans hqR)
      simp [l₀, r₁] at h
    · have h := f.injective (hqL.symm.trans hqR)
      simp [l₁, r₀] at h
    · have h := f.injective (hqL.symm.trans hqR)
      simp [l₁, r₁] at h
  exact ⟨
    { u := f l₀
      v := f l₁
      x := f r₀
      y := f r₁
      twin_uv := htwinL
      twin_xy := htwinR
      degree_u := hdegL
      degree_x := hdegR
      disjoint := hdisj }⟩

/-- In a triangle-free almost-wheel-free graph, a vertex is adjacent to at
most one wheel centre. -/
theorem card_center_neighbors_le_one
    (halmost : AlmostWheelFree G) (htri : AHTTriangleFree G) (w : V) :
    (centerNeighbors G w).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  simp only [centerNeighbors, Finset.mem_filter,
    SimpleGraph.mem_neighborFinset] at hp hq
  by_contra hpq
  have hpqAdj : G.Adj p q :=
    (halmost.eq_or_adj_of_centers hp.2 hq.2).resolve_left hpq
  exact htri hp.1 hpqAdj hq.1.symm

/-! ## Enumerating the neighbourhood of a source twin pair -/

/-- The light-weight triple used in AHT Lemma 6.5.  Unlike `TwinTriple`,
the three common neighbours are not assumed to have degree three. -/
structure AHTSourceTwinTriple
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  u : V
  v : V
  x : V
  y : V
  z : V
  twins : AHTTwinPair G u v
  xy : x ≠ y
  xz : x ≠ z
  yz : y ≠ z
  neighbors_u : G.neighborFinset u = {x, y, z}
  neighbors_v : G.neighborFinset v = {x, y, z}

namespace AHTSourceTwinTriple

variable (T : AHTSourceTwinTriple G)

theorem adj_u_x : G.Adj T.u T.x := by
  rw [← SimpleGraph.mem_neighborFinset, T.neighbors_u]
  simp

theorem adj_u_y : G.Adj T.u T.y := by
  rw [← SimpleGraph.mem_neighborFinset, T.neighbors_u]
  simp

theorem adj_u_z : G.Adj T.u T.z := by
  rw [← SimpleGraph.mem_neighborFinset, T.neighbors_u]
  simp

theorem adj_v_x : G.Adj T.v T.x := by
  rw [← SimpleGraph.mem_neighborFinset, T.neighbors_v]
  simp

theorem adj_v_y : G.Adj T.v T.y := by
  rw [← SimpleGraph.mem_neighborFinset, T.neighbors_v]
  simp

theorem adj_v_z : G.Adj T.v T.z := by
  rw [← SimpleGraph.mem_neighborFinset, T.neighbors_v]
  simp

theorem u_ne_x : T.u ≠ T.x := T.adj_u_x.ne
theorem u_ne_y : T.u ≠ T.y := T.adj_u_y.ne
theorem u_ne_z : T.u ≠ T.z := T.adj_u_z.ne
theorem v_ne_x : T.v ≠ T.x := T.adj_v_x.ne
theorem v_ne_y : T.v ≠ T.y := T.adj_v_y.ne
theorem v_ne_z : T.v ≠ T.z := T.adj_v_z.ne

theorem degree_u : G.degree T.u = 3 := T.twins.degree_left
theorem degree_v : G.degree T.v = 3 := T.twins.degree_right

/-- The residual set `R` in the proof of AHT Lemma 6.5. -/
def InResidual (w : V) : Prop :=
  w ≠ T.u ∧ w ≠ T.v ∧ w ≠ T.x ∧ w ≠ T.y ∧ w ≠ T.z

/-- The finite residual set `R = V(G) \ {u,v,x,y,z}`. -/
noncomputable def residualVertices (T : AHTSourceTwinTriple G) : Finset V := by
  classical
  exact Finset.univ.filter T.InResidual

/-- The residual assumption after the `K_{3,3} \ e` branch of the paper has
been discharged: no two common neighbours of the first twin pair have a
third common neighbour. -/
def PairwiseCommonNeighborsOnlyTwins : Prop :=
  (∀ c : V, G.Adj T.x c → G.Adj T.y c → c = T.u ∨ c = T.v) ∧
  (∀ c : V, G.Adj T.x c → G.Adj T.z c → c = T.u ∨ c = T.v) ∧
  (∀ c : V, G.Adj T.y c → G.Adj T.z c → c = T.u ∨ c = T.v)

/-- Swap the last two displayed common neighbours. -/
def swapLast : AHTSourceTwinTriple G where
  u := T.u
  v := T.v
  x := T.x
  y := T.z
  z := T.y
  twins := T.twins
  xy := T.xz
  xz := T.xy
  yz := T.yz.symm
  neighbors_u := by
    rw [T.neighbors_u]
    ext q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  neighbors_v := by
    rw [T.neighbors_v]
    ext q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- Cyclically permute the three displayed common neighbours. -/
def cycleCommonNeighbors : AHTSourceTwinTriple G where
  u := T.u
  v := T.v
  x := T.y
  y := T.z
  z := T.x
  twins := T.twins
  xy := T.yz
  xz := T.xy.symm
  yz := T.xz.symm
  neighbors_u := by
    rw [T.neighbors_u]
    ext q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  neighbors_v := by
    rw [T.neighbors_v]
    ext q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- The exceptional branch of Lemma 6.5 for the pair `x,y`: an additional
common neighbour gives a literal `K₃,₃-e`; AHT Lemma 6.2 identifies the
whole graph with `K₃,₃`. -/
theorem twoDisjointPairs_of_extra_commonNeighbor_xy
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    {c : V} (hxc : G.Adj T.x c) (hyc : G.Adj T.y c)
    (hcu : c ≠ T.u) (hcv : c ≠ T.v) :
    Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G) := by
  have htri : AHTTriangleFree G :=
    aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  have hcx : c ≠ T.x := hxc.ne'
  have hcy : c ≠ T.y := hyc.ne'
  have hcz : c ≠ T.z := by
    intro h
    subst c
    exact htri T.adj_u_x hxc T.adj_u_z.symm
  have hdistinct : [T.z, T.x, T.y, c, T.u, T.v].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or]
    refine ⟨⟨T.xz.symm, T.yz.symm, hcz.symm, T.u_ne_z.symm,
      T.v_ne_z.symm⟩, ?_⟩
    refine ⟨⟨T.xy, hcx.symm, T.u_ne_x.symm, T.v_ne_x.symm⟩, ?_⟩
    refine ⟨⟨hcy.symm, T.u_ne_y.symm, T.v_ne_y.symm⟩, ?_⟩
    refine ⟨⟨hcu, hcv⟩, ?_⟩
    exact ⟨T.twins.falseTwins.1, by simp⟩
  have hK : ContainsK33MinusEdge G := by
    exact ⟨T.z, T.x, T.y, c, T.u, T.v, hdistinct,
      T.adj_u_z.symm, T.adj_v_z.symm,
      hxc, T.adj_u_x.symm, T.adj_v_x.symm,
      hyc, T.adj_u_y.symm, T.adj_v_y.symm⟩
  exact twoDisjointPairs_of_isomorphic_k33
    (aht_isomorphic_k33_of_k33MinusEdge hthree halmost hK)

/-- The complete exceptional branch for any of the three pairs among
`x,y,z`. -/
theorem twoDisjointPairs_of_not_pairwiseCommonNeighborsOnlyTwins
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hnot : ¬T.PairwiseCommonNeighborsOnlyTwins) :
    Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G) := by
  classical
  by_cases hxy : ∀ c : V, G.Adj T.x c → G.Adj T.y c →
      c = T.u ∨ c = T.v
  · by_cases hxz : ∀ c : V, G.Adj T.x c → G.Adj T.z c →
        c = T.u ∨ c = T.v
    · have hyz : ¬∀ c : V, G.Adj T.y c → G.Adj T.z c →
          c = T.u ∨ c = T.v := by
        intro hyz
        exact hnot ⟨hxy, hxz, hyz⟩
      push_neg at hyz
      obtain ⟨c, hyc, hzc, hcu, hcv⟩ := hyz
      exact T.cycleCommonNeighbors.twoDisjointPairs_of_extra_commonNeighbor_xy
        hthree halmost hyc hzc hcu hcv
    · push_neg at hxz
      obtain ⟨c, hxc, hzc, hcu, hcv⟩ := hxz
      exact T.swapLast.twoDisjointPairs_of_extra_commonNeighbor_xy
        hthree halmost hxc hzc hcu hcv
  · push_neg at hxy
    obtain ⟨c, hxc, hyc, hcu, hcv⟩ := hxy
    exact T.twoDisjointPairs_of_extra_commonNeighbor_xy
      hthree halmost hxc hyc hcu hcv

/-- Minimum degree three gives every displayed common neighbour a neighbour
outside the first twin pair. -/
theorem exists_neighbor_not_first_pair
    (hthree : IsThreeConnected G) (p : V) :
    ∃ w : V, G.Adj p w ∧ w ≠ T.u ∧ w ≠ T.v := by
  classical
  have hpair : ({T.u, T.v} : Finset V).card ≤ 2 := Finset.card_le_two
  have hdegree : 3 ≤ (G.neighborFinset p).card := by
    simpa only [G.card_neighborFinset_eq_degree] using hthree.degree_ge p
  have hlt : ({T.u, T.v} : Finset V).card <
      (G.neighborFinset p).card := by omega
  obtain ⟨w, hwN, hwPair⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt
  have hpw : G.Adj p w := by simpa using hwN
  have hwu : w ≠ T.u := by
    intro h
    apply hwPair
    simp [h]
  have hwv : w ≠ T.v := by
    intro h
    apply hwPair
    simp [h]
  exact ⟨w, hpw, hwu, hwv⟩

/-- Each of `x,y,z` has a neighbour in `R`.  Triangle-freeness rules out
the other two displayed common neighbours. -/
theorem exists_neighbor_inResidual
    (hthree : IsThreeConnected G) (htri : AHTTriangleFree G)
    {p : V} (hp : p = T.x ∨ p = T.y ∨ p = T.z) :
    ∃ w : V, G.Adj p w ∧ T.InResidual w := by
  rcases hp with rfl | rfl | rfl
  · obtain ⟨w, hxw, hwu, hwv⟩ :=
      T.exists_neighbor_not_first_pair hthree T.x
    have hwx : w ≠ T.x := hxw.ne'
    have hwy : w ≠ T.y := by
      intro h
      subst w
      exact htri T.adj_u_x hxw T.adj_u_y.symm
    have hwz : w ≠ T.z := by
      intro h
      subst w
      exact htri T.adj_u_x hxw T.adj_u_z.symm
    exact ⟨w, hxw, hwu, hwv, hwx, hwy, hwz⟩
  · obtain ⟨w, hyw, hwu, hwv⟩ :=
      T.exists_neighbor_not_first_pair hthree T.y
    have hwx : w ≠ T.x := by
      intro h
      subst w
      exact htri T.adj_u_y hyw T.adj_u_x.symm
    have hwy : w ≠ T.y := hyw.ne'
    have hwz : w ≠ T.z := by
      intro h
      subst w
      exact htri T.adj_u_y hyw T.adj_u_z.symm
    exact ⟨w, hyw, hwu, hwv, hwx, hwy, hwz⟩
  · obtain ⟨w, hzw, hwu, hwv⟩ :=
      T.exists_neighbor_not_first_pair hthree T.z
    have hwx : w ≠ T.x := by
      intro h
      subst w
      exact htri T.adj_u_z hzw T.adj_u_x.symm
    have hwy : w ≠ T.y := by
      intro h
      subst w
      exact htri T.adj_u_z hzw T.adj_u_y.symm
    have hwz : w ≠ T.z := hzw.ne'
    exact ⟨w, hzw, hwu, hwv, hwx, hwy, hwz⟩

/-- The source observation `|R| ≥ 3`: the third neighbours of `x,y,z`
are residual and pairwise distinct under the clean common-neighbour
condition. -/
theorem three_le_card_residualVertices
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (honly : T.PairwiseCommonNeighborsOnlyTwins) :
    3 ≤ T.residualVertices.card := by
  classical
  have htri : AHTTriangleFree G :=
    aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  obtain ⟨rx, hxrx, hrx⟩ :=
    T.exists_neighbor_inResidual hthree htri (Or.inl rfl)
  obtain ⟨ry, hyry, hry⟩ :=
    T.exists_neighbor_inResidual hthree htri (Or.inr (Or.inl rfl))
  obtain ⟨rz, hzrz, hrz⟩ :=
    T.exists_neighbor_inResidual hthree htri (Or.inr (Or.inr rfl))
  have hrxy : rx ≠ ry := by
    intro h
    subst ry
    rcases honly.1 rx hxrx hyry with h | h
    · exact hrx.1 h
    · exact hrx.2.1 h
  have hrxz : rx ≠ rz := by
    intro h
    subst rz
    rcases honly.2.1 rx hxrx hzrz with h | h
    · exact hrx.1 h
    · exact hrx.2.1 h
  have hryz : ry ≠ rz := by
    intro h
    subst rz
    rcases honly.2.2 ry hyry hzrz with h | h
    · exact hry.1 h
    · exact hry.2.1 h
  have hsub : ({rx, ry, rz} : Finset V) ⊆ T.residualVertices := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;>
      simpa only [residualVertices, Finset.mem_filter,
        Finset.mem_univ, true_and]
  have hcard : ({rx, ry, rz} : Finset V).card = 3 := by
    simp [hrxy, hrxz, hryz]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- Since `|R| ≥ 3` and `|W(G)| ≤ 2`, the residual graph with wheel
centres removed is nonempty. -/
theorem exists_inResidual_not_wheelCenter
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (honly : T.PairwiseCommonNeighborsOnlyTwins) :
    ∃ w : V, T.InResidual w ∧ ¬HasWheelCenteredAt G w := by
  classical
  have hR : 3 ≤ T.residualVertices.card :=
    T.three_le_card_residualVertices hthree halmost honly
  have hW : (wheelCenters G).card ≤ 2 :=
    card_wheelCenters_le_two halmost
  have hlt : (wheelCenters G).card < T.residualVertices.card := by omega
  obtain ⟨w, hwR, hwW⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt
  have hwResidual : T.InResidual w := by
    simpa only [residualVertices, Finset.mem_filter,
      Finset.mem_univ, true_and] using hwR
  have hwCenter : ¬HasWheelCenteredAt G w := by
    simpa only [mem_wheelCenters] using hwW
  exact ⟨w, hwResidual, hwCenter⟩

/-- Neighbours of `w` which remain in the residual graph after the wheel
centres are removed. -/
noncomputable def residualNoncenterNeighbors
    (T : AHTSourceTwinTriple G) (w : V) : Finset V := by
  classical
  exact (G.neighborFinset w).filter fun q =>
    T.InResidual q ∧ ¬HasWheelCenteredAt G q

/-- The induced graph `G[R \ W(G)]` from the source proof. -/
def residualNoncenterGraph (T : AHTSourceTwinTriple G) :
    SimpleGraph {q : V // T.InResidual q ∧
      ¬HasWheelCenteredAt G q} :=
  G.induce {q : V | T.InResidual q ∧ ¬HasWheelCenteredAt G q}

/-- The source residual graph is nonempty. -/
theorem residualNoncenterGraph_nonempty
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (honly : T.PairwiseCommonNeighborsOnlyTwins) :
    Nonempty {q : V // T.InResidual q ∧
      ¬HasWheelCenteredAt G q} := by
  obtain ⟨w, hwR, hwW⟩ :=
    T.exists_inResidual_not_wheelCenter hthree halmost honly
  exact ⟨⟨w, hwR, hwW⟩⟩

/-- Degree in `G[R \ W(G)]` is exactly the number of neighbours counted by
`residualNoncenterNeighbors`. -/
theorem degree_residualNoncenterGraph
    (w : {q : V // T.InResidual q ∧ ¬HasWheelCenteredAt G q})
    [Fintype ((T.residualNoncenterGraph).neighborSet w)] :
    (T.residualNoncenterGraph).degree w =
      (T.residualNoncenterNeighbors w.1).card := by
  classical
  let inc : {q : V // T.InResidual q ∧ ¬HasWheelCenteredAt G q} ↪ V :=
    Function.Embedding.subtype _
  have hmap :
      ((T.residualNoncenterGraph).neighborFinset w).map inc =
        T.residualNoncenterNeighbors w.1 := by
    ext q
    constructor
    · intro hq
      obtain ⟨z, hz, hzq⟩ := Finset.mem_map.mp hq
      have hAdjInd : T.residualNoncenterGraph.Adj w z := by
        simpa only [SimpleGraph.mem_neighborFinset] using hz
      change G.Adj w.1 z.1 at hAdjInd
      subst q
      simp only [residualNoncenterNeighbors, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hAdjInd, z.2⟩
    · intro hq
      simp only [residualNoncenterNeighbors, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset] at hq
      let z : {q : V // T.InResidual q ∧ ¬HasWheelCenteredAt G q} :=
        ⟨q, hq.2⟩
      apply Finset.mem_map.mpr
      refine ⟨z, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      change G.Adj w.1 q
      exact hq.1
  calc
    (T.residualNoncenterGraph).degree w =
        ((T.residualNoncenterGraph).neighborFinset w).card := by
          rw [(T.residualNoncenterGraph).card_neighborFinset_eq_degree]
    _ = (((T.residualNoncenterGraph).neighborFinset w).map inc).card := by
          rw [Finset.card_map]
    _ = (T.residualNoncenterNeighbors w.1).card := by
          rw [hmap]

/-- Neighbours of `w` among the three common neighbours of the first twin
pair. -/
def tripleNeighbors (w : V) : Finset V :=
  G.neighborFinset w ∩ {T.x, T.y, T.z}

/-- The `K_{3,3} \ e`-free residual condition implies that a residual
vertex is adjacent to at most one of `x,y,z`. -/
theorem card_tripleNeighbors_le_one
    (honly : T.PairwiseCommonNeighborsOnlyTwins)
    {w : V} (hw : T.InResidual w) :
    (T.tripleNeighbors w).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  simp only [tripleNeighbors, Finset.mem_inter,
    SimpleGraph.mem_neighborFinset, Finset.mem_insert,
    Finset.mem_singleton] at hp hq
  rcases hp with ⟨hwp, rfl | rfl | rfl⟩ <;>
    rcases hq with ⟨hwq, rfl | rfl | rfl⟩
  · rfl
  · rcases honly.1 w hwp.symm hwq.symm with h | h
    · exact False.elim (hw.1 h)
    · exact False.elim (hw.2.1 h)
  · rcases honly.2.1 w hwp.symm hwq.symm with h | h
    · exact False.elim (hw.1 h)
    · exact False.elim (hw.2.1 h)
  · rcases honly.1 w hwq.symm hwp.symm with h | h
    · exact False.elim (hw.1 h)
    · exact False.elim (hw.2.1 h)
  · rfl
  · rcases honly.2.2 w hwp.symm hwq.symm with h | h
    · exact False.elim (hw.1 h)
    · exact False.elim (hw.2.1 h)
  · rcases honly.2.1 w hwq.symm hwp.symm with h | h
    · exact False.elim (hw.1 h)
    · exact False.elim (hw.2.1 h)
  · rcases honly.2.2 w hwq.symm hwp.symm with h | h
    · exact False.elim (hw.1 h)
    · exact False.elim (hw.2.1 h)
  · rfl

/-- A residual vertex is adjacent to neither member of the first twin pair,
because their complete neighbourhood is the displayed three-set. -/
theorem not_adj_first_pair_of_inResidual {w : V} (hw : T.InResidual w) :
    ¬G.Adj w T.u ∧ ¬G.Adj w T.v := by
  constructor
  · intro hwu
    have hwN : w ∈ G.neighborFinset T.u := by simpa using hwu.symm
    rw [T.neighbors_u] at hwN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwN
    rcases hwN with h | h | h
    · exact hw.2.2.1 h
    · exact hw.2.2.2.1 h
    · exact hw.2.2.2.2 h
  · intro hwv
    have hwN : w ∈ G.neighborFinset T.v := by simpa using hwv.symm
    rw [T.neighbors_v] at hwN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwN
    rcases hwN with h | h | h
    · exact hw.2.2.1 h
    · exact hw.2.2.2.1 h
    · exact hw.2.2.2.2 h

/-- The low-internal-degree branch of the residual argument in AHT Lemma
6.5.  There is at most one neighbour in `R \ W(G)`, at most one among
`x,y,z`, and at most one wheel centre.  Three-connectivity supplies the
reverse degree bound. -/
theorem degree_eq_three_of_residualNoncenterNeighbors_le_one
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (honly : T.PairwiseCommonNeighborsOnlyTwins)
    {w : V} (hw : T.InResidual w)
    (hsmall : (T.residualNoncenterNeighbors w).card ≤ 1) :
    G.degree w = 3 := by
  classical
  let A : Finset V := T.residualNoncenterNeighbors w
  let B : Finset V := T.tripleNeighbors w
  let C : Finset V := centerNeighbors G w
  have htri : AHTTriangleFree G :=
    aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  have hA : A.card ≤ 1 := by simpa [A] using hsmall
  have hB : B.card ≤ 1 := by
    simpa [B] using T.card_tripleNeighbors_le_one honly hw
  have hC : C.card ≤ 1 := by
    simpa [C] using card_center_neighbors_le_one halmost htri w
  have hnab := T.not_adj_first_pair_of_inResidual hw
  have hsub : G.neighborFinset w ⊆ A ∪ B ∪ C := by
    intro q hq
    have hwq : G.Adj w q := by simpa using hq
    by_cases hqCenter : HasWheelCenteredAt G q
    · have hqC : q ∈ C := by
        simp only [C, centerNeighbors, Finset.mem_filter,
          SimpleGraph.mem_neighborFinset]
        exact ⟨hwq, hqCenter⟩
      exact Finset.mem_union_right _ hqC
    by_cases hqu : q = T.u
    · subst q
      exact False.elim (hnab.1 hwq)
    by_cases hqv : q = T.v
    · subst q
      exact False.elim (hnab.2 hwq)
    by_cases hqx : q = T.x
    · subst q
      exact Finset.mem_union_left _ <| Finset.mem_union_right _ <|
        Finset.mem_inter.mpr ⟨hq, by simp⟩
    by_cases hqy : q = T.y
    · subst q
      exact Finset.mem_union_left _ <| Finset.mem_union_right _ <|
        Finset.mem_inter.mpr ⟨hq, by simp⟩
    by_cases hqz : q = T.z
    · subst q
      exact Finset.mem_union_left _ <| Finset.mem_union_right _ <|
        Finset.mem_inter.mpr ⟨hq, by simp⟩
    have hqResidual : T.InResidual q := ⟨hqu, hqv, hqx, hqy, hqz⟩
    have hqA : q ∈ A := by
      simp only [A, residualNoncenterNeighbors, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hwq, hqResidual, hqCenter⟩
    exact Finset.mem_union_left _ <| Finset.mem_union_left _ hqA
  have hN : (G.neighborFinset w).card ≤ 3 := by
    have hcardSub : (G.neighborFinset w).card ≤ (A ∪ B ∪ C).card :=
      Finset.card_le_card hsub
    have hAB : (A ∪ B).card ≤ A.card + B.card :=
      Finset.card_union_le A B
    have hABC : (A ∪ B ∪ C).card ≤ (A ∪ B).card + C.card :=
      Finset.card_union_le (A ∪ B) C
    omega
  have hle : G.degree w ≤ 3 := by
    simpa only [G.card_neighborFinset_eq_degree] using hN
  have hge : 3 ≤ G.degree w := hthree.degree_ge w
  omega

/-- The complete source claim that `R` contains a degree-three vertex not
in `W(G)`.  If `G[R \ W(G)]` has a vertex of degree at most one, the local
degree partition gives the result.  Otherwise the residual graph contains a
cycle, and Mader's cycle theorem supplies the required vertex. -/
theorem exists_residual_degreeThree_noncenter
    (hmin : IsEdgeMinimallyThreeConnected G)
    (halmost : AlmostWheelFree G)
    (honly : T.PairwiseCommonNeighborsOnlyTwins) :
    ∃ w : V, T.InResidual w ∧ G.degree w = 3 ∧
      ¬HasWheelCenteredAt G w := by
  classical
  let H := T.residualNoncenterGraph
  have hthree : IsThreeConnected G := hmin.isThreeConnected
  have hnonempty : Nonempty {q : V // T.InResidual q ∧
      ¬HasWheelCenteredAt G q} :=
    T.residualNoncenterGraph_nonempty hthree halmost honly
  by_cases hsmall : ∃ w : {q : V // T.InResidual q ∧
      ¬HasWheelCenteredAt G q}, H.degree w ≤ 1
  · obtain ⟨w, hwsmall⟩ := hsmall
    have hsmall' : (T.residualNoncenterNeighbors w.1).card ≤ 1 := by
      rw [← T.degree_residualNoncenterGraph w]
      exact hwsmall
    have hwdeg : G.degree w.1 = 3 :=
      T.degree_eq_three_of_residualNoncenterNeighbors_le_one
        hthree halmost honly w.2.1 hsmall'
    exact ⟨w.1, w.2.1, hwdeg, w.2.2⟩
  · have hlarge : ∀ w : {q : V // T.InResidual q ∧
        ¬HasWheelCenteredAt G q}, 2 ≤ H.degree w := by
      intro w
      have hw : ¬H.degree w ≤ 1 := by
        intro hw
        exact hsmall ⟨w, hw⟩
      omega
    obtain ⟨r, p, hp⟩ :=
      exists_cycle_of_nonempty_of_forall_two_le_degree hnonempty hlarge
    let inc : T.residualNoncenterGraph →g G :=
      (SimpleGraph.Embedding.induce
        (G := G) (s := {q : V | T.InResidual q ∧
          ¬HasWheelCenteredAt G q})).toHom
    have hpMap : (p.map inc).IsCycle := hp.map Subtype.val_injective
    have hM : MaderCycleProperty G :=
      maderCycleProperty_of_isEdgeMinimallyThreeConnected hmin
    obtain ⟨v, hvp, hvdeg⟩ := hM (p.map inc) hpMap
    rw [Walk.support_map] at hvp
    obtain ⟨w, hwp, hwv⟩ := List.mem_map.mp hvp
    change w.1 = v at hwv
    subst v
    exact ⟨w.1, w.2.1, hvdeg, w.2.2⟩

/-- Under the residual common-neighbour condition, every false twin of one
of `u,v` is the other one. -/
theorem falseTwin_mem_first_pair
    (honly : T.PairwiseCommonNeighborsOnlyTwins)
    {a b : V} (hab : AreFalseTwins G a b)
    (ha : a = T.u ∨ a = T.v) : b = T.u ∨ b = T.v := by
  have hax : G.Adj a T.x := by
    rcases ha with rfl | rfl
    · exact T.adj_u_x
    · exact T.adj_v_x
  have hay : G.Adj a T.y := by
    rcases ha with rfl | rfl
    · exact T.adj_u_y
    · exact T.adj_v_y
  have hbx : G.Adj b T.x := (hab.adj_iff T.x).mp hax
  have hby : G.Adj b T.y := (hab.adj_iff T.y).mp hay
  exact honly.1 b hbx.symm hby.symm

/-- The formalized final step of AHT Lemma 6.5.  A residual vertex close to
a source twin pair yields another degree-three twin pair disjoint from the
first pair. -/
theorem twoDisjointPairs_of_inResidual_of_close
    (honly : T.PairwiseCommonNeighborsOnlyTwins)
    {w : V} (hw : T.InResidual w)
    (hclose : IsCloseToAHTTwin G w) :
    Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G) := by
  obtain ⟨a, b, hab, hcloseCases⟩ := hclose
  have hnab := T.not_adj_first_pair_of_inResidual hw
  have hnotCloseFirst :
      ¬(w = T.u ∨ w = T.v ∨ G.Adj w T.u ∨ G.Adj w T.v) := by
    intro h
    rcases h with h | h | h | h
    · exact hw.1 h
    · exact hw.2.1 h
    · exact hnab.1 h
    · exact hnab.2 h
  have closeFirst_of_mem
      (ha : a = T.u ∨ a = T.v) (hb : b = T.u ∨ b = T.v) :
      w = T.u ∨ w = T.v ∨ G.Adj w T.u ∨ G.Adj w T.v := by
    rcases hcloseCases with h | h | h | h
    · rcases ha with rfl | rfl
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hb with rfl | rfl
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases ha with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · rcases hb with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have haOut : ¬(a = T.u ∨ a = T.v) := by
    intro ha
    have hb := T.falseTwin_mem_first_pair honly hab.falseTwins ha
    exact hnotCloseFirst (closeFirst_of_mem ha hb)
  have hbOut : ¬(b = T.u ∨ b = T.v) := by
    intro hb
    have ha := T.falseTwin_mem_first_pair honly hab.falseTwins.symm hb
    exact hnotCloseFirst (closeFirst_of_mem ha hb)
  have hdisj : Disjoint ({T.u, T.v} : Finset V) ({a, b} : Finset V) := by
    rw [Finset.disjoint_left]
    intro q hqFirst hqSecond
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqFirst hqSecond
    rcases hqFirst with rfl | rfl <;> rcases hqSecond with h | h
    · exact haOut (Or.inl h.symm)
    · exact hbOut (Or.inl h.symm)
    · exact haOut (Or.inr h.symm)
    · exact hbOut (Or.inr h.symm)
  exact ⟨
    { u := T.u
      v := T.v
      x := a
      y := b
      twin_uv := T.twins.falseTwins
      twin_xy := hab.falseTwins
      degree_u := T.twins.degree_left
      degree_x := hab.degree_left
      disjoint := hdisj }⟩

/-- Source-shaped wrapper: the global “every degree-three non-centre is
close” hypothesis supplies closeness for the residual vertex constructed by
the Mader part of the published proof. -/
theorem twoDisjointPairs_of_residual_degreeThree_noncenter
    (honly : T.PairwiseCommonNeighborsOnlyTwins)
    (hclose : ∀ q : V, G.degree q = 3 →
      ¬HasWheelCenteredAt G q → IsCloseToAHTTwin G q)
    {w : V} (hw : T.InResidual w)
    (hwdeg : G.degree w = 3) (hwcenter : ¬HasWheelCenteredAt G w) :
    Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G) := by
  exact T.twoDisjointPairs_of_inResidual_of_close honly hw
    (hclose w hwdeg hwcenter)

/-- The complete low-internal-degree branch of AHT Lemma 6.5. -/
theorem twoDisjointPairs_of_residualNoncenterNeighbors_le_one
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (honly : T.PairwiseCommonNeighborsOnlyTwins)
    (hclose : ∀ q : V, G.degree q = 3 →
      ¬HasWheelCenteredAt G q → IsCloseToAHTTwin G q)
    {w : V} (hw : T.InResidual w)
    (hwcenter : ¬HasWheelCenteredAt G w)
    (hsmall : (T.residualNoncenterNeighbors w).card ≤ 1) :
    Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G) := by
  have hwdeg : G.degree w = 3 :=
    T.degree_eq_three_of_residualNoncenterNeighbors_le_one
      hthree halmost honly hw hsmall
  exact T.twoDisjointPairs_of_residual_degreeThree_noncenter
    honly hclose hw hwdeg hwcenter

end AHTSourceTwinTriple

/-- Every AHT twin pair has a source triple enumerating its common
degree-three neighbourhood. -/
theorem exists_ahtSourceTwinTriple_of_twinPair
    {u v : V} (htwin : AHTTwinPair G u v) :
    ∃ T : AHTSourceTwinTriple G, T.u = u ∧ T.v = v := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hNu⟩ :=
    exists_three_neighbors_of_degree_eq_three htwin.degree_left
  have hNv : G.neighborFinset v = {x, y, z} := by
    rw [← htwin.falseTwins.neighborFinset_eq, hNu]
  let T : AHTSourceTwinTriple G :=
    { u := u
      v := v
      x := x
      y := y
      z := z
      twins := htwin
      xy := hxy
      xz := hxz
      yz := hyz
      neighbors_u := hNu
      neighbors_v := hNv }
  exact ⟨T, rfl, rfl⟩

/-- AHT Lemma 6.5 with the genuine edge-minimality conclusion of Corollary
4.6 supplied explicitly.  This is otherwise the full source proof, including
both the `K₃,₃-e` and residual-cycle branches. -/
theorem aht_lemma65_of_edgeMinimallyThreeConnected
    (hmin : IsEdgeMinimallyThreeConnected G)
    (halmost : AlmostWheelFree G)
    (hclose : ∀ q : V, G.degree q = 3 →
      ¬HasWheelCenteredAt G q → IsCloseToAHTTwin G q) :
    Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G) := by
  obtain ⟨u, v, htwin⟩ :=
    exists_ahtTwinPair_of_edgeMinimallyThreeConnected
      hmin halmost hclose
  obtain ⟨T, -, -⟩ := exists_ahtSourceTwinTriple_of_twinPair htwin
  by_cases honly : T.PairwiseCommonNeighborsOnlyTwins
  · obtain ⟨w, hwR, hwdeg, hwcenter⟩ :=
      T.exists_residual_degreeThree_noncenter hmin halmost honly
    exact T.twoDisjointPairs_of_residual_degreeThree_noncenter
      honly hclose hwR hwdeg hwcenter
  · exact T.twoDisjointPairs_of_not_pairwiseCommonNeighborsOnlyTwins
      hmin.isThreeConnected halmost honly

/-- AHT Lemma 6.5, source-exact: in a three-connected almost-wheel-free
graph, if every degree-three vertex outside the exceptional wheel-centre set
is close to a pair of twins, then the graph contains two vertex-disjoint
pairs of degree-three false twins. -/
theorem aht_lemma65
    (hthree : IsThreeConnected G)
    (halmost : AlmostWheelFree G)
    (hclose : ∀ q : V, G.degree q = 3 →
      ¬HasWheelCenteredAt G q → IsCloseToAHTTwin G q) :
    Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G) := by
  exact aht_lemma65_of_edgeMinimallyThreeConnected
    (AHTMinimalThreeConnected.isEdgeMinimallyThreeConnected_of_isThreeConnected_of_almostWheelFree
      hthree halmost)
    halmost hclose

end Erdos916
