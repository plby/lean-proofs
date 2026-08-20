/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreClassification
import ErdosProblems.Erdos916.CoreAHT
import ErdosProblems.Erdos916.CoreTwinDensity
import ErdosProblems.Erdos916.ThreeTerminalCut

/-!
# False twins in a `(2,3)` circuit

This file contains the glue for the ordinary false-twin route to Erdős
Problem 916.  Its main elementary lemma closes a path through the three
common neighbours of degree-three false twins through one twin, making that
twin the rim and the other twin the hub of a wheel.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The `edgeSet.ncard` formulation produced by the minimal-density
construction is the same `(2,3)`-circuit used by the rigidity layer. -/
theorem Minimal23Circuit.toIs23Circuit (h : Minimal23Circuit G) :
    Is23Circuit G := by
  exact (minimal23Circuit_iff_is23Circuit G).mp h

/-- A path whose endpoints are two of `a,b,c` and whose support contains all
three terminals.  This endpoint-normalized form can be closed through a
common neighbour without first trimming the path. -/
def HasThreeTerminalPath (G : SimpleGraph V) (a b c : V) : Prop :=
  ∃ x y : V,
    x ∈ ({a, b, c} : Finset V) ∧
      y ∈ ({a, b, c} : Finset V) ∧ x ≠ y ∧
        ∃ p : G.Walk x y,
          p.IsPath ∧ a ∈ p.support ∧ b ∈ p.support ∧ c ∈ p.support

/-- The graph left after deleting a pair of vertices. -/
abbrev deletePair (G : SimpleGraph V) (u v : V) :
    SimpleGraph {w : V // w ∈ (({u, v} : Set V)ᶜ)} :=
  G.induce (({u, v} : Set V)ᶜ)

/-- The set-complement presentation used for terminal paths is canonically
isomorphic to the conjunction presentation used by the edge-count layer. -/
noncomputable def deletePairIsoPairDeleted (G : SimpleGraph V) (u v : V) :
    deletePair G u v ≃g pairDeleted G u v := by
  let e : {w : V // w ∈ (({u, v} : Set V)ᶜ)} ≃ PairDeletedVertices u v :=
    { toFun := fun w ↦ ⟨w.1, by
        have hw := w.2
        simp only [Set.mem_compl_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or] at hw
        exact hw⟩
      invFun := fun w ↦ ⟨w.1, by
        simp only [Set.mem_compl_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or]
        exact w.2⟩
      left_inv := fun w ↦ by apply Subtype.ext; rfl
      right_inv := fun w ↦ by apply Subtype.ext; rfl }
  exact { toEquiv := e, map_rel_iff' := Iff.rfl }

/-- Exact `(2,4)` count in the set-complement deletion presentation. -/
theorem Is23Circuit.deletePair_has24Count
    (hcircuit : Is23Circuit G) {u v : V}
    (htwin : AreFalseTwins G u v) (hdeg : G.degree u = 3) :
    (deletePair G u v).edgeFinset.card + 4 =
      2 * Fintype.card {w : V // w ∈ (({u, v} : Set V)ᶜ)} := by
  classical
  have hdv : G.degree v = 3 := htwin.degree_eq.symm.trans hdeg
  have hcount := pairDeleted.has24Count hcircuit htwin.1 htwin.not_adj hdeg hdv
  let e := deletePairIsoPairDeleted G u v
  have hedge : (deletePair G u v).edgeFinset.card =
      (pairDeleted G u v).edgeFinset.card := e.card_edgeFinset_eq
  have hcard : Fintype.card {w : V // w ∈ (({u, v} : Set V)ᶜ)} =
      Fintype.card (PairDeletedVertices u v) := Fintype.card_congr e.toEquiv
  rw [hedge, hcard]
  exact hcount

/-- Every vertex set of a two-vertex deletion is a proper vertex set of the
ambient circuit, and hence remains `(2,3)`-sparse. -/
theorem Is23Circuit.is23Sparse_deletePair (hcircuit : Is23Circuit G)
    (u v : V) : Is23Sparse (deletePair G u v) := by
  classical
  intro S hS
  let inc : {w : V // w ∈ (({u, v} : Set V)ᶜ)} ↪ V :=
    Function.Embedding.subtype _
  let T : Finset V := S.map inc
  have hcardT : T.card = S.card := by simp [T]
  have huT : u ∉ T := by
    intro hmem
    simp only [T, Finset.mem_map] at hmem
    obtain ⟨w, -, hwu⟩ := hmem
    have hwne : (w : V) ≠ u := by
      have hw := w.2
      simp only [Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or] at hw
      exact hw.1
    exact hwne (by simpa [inc] using hwu)
  have hTproper : T ≠ Finset.univ := by
    intro hTu
    have : u ∈ T := by rw [hTu]; simp
    exact huT this
  have hsparse := hcircuit.2 T (by omega) hTproper
  have hsets :
      ((fun w : {w : V // w ∈ (({u, v} : Set V)ᶜ)} ↦ (w : V)) ''
          (S : Set {w : V // w ∈ (({u, v} : Set V)ᶜ)})) = (T : Set V) := by
    ext x
    simp [T, inc]
  let e₀ :
      {w : {w : V // w ∈ (({u, v} : Set V)ᶜ)} // w ∈
        (S : Set {w : V // w ∈ (({u, v} : Set V)ᶜ)})} ≃
      {x : V // x ∈ ((fun w : {w : V // w ∈ (({u, v} : Set V)ᶜ)} ↦ (w : V)) ''
        (S : Set {w : V // w ∈ (({u, v} : Set V)ᶜ)}))} :=
    Equiv.Set.image
      (fun w : {w : V // w ∈ (({u, v} : Set V)ᶜ)} ↦ (w : V))
      (S : Set {w : V // w ∈ (({u, v} : Set V)ᶜ)}) Subtype.val_injective
  let e :
      {w : {w : V // w ∈ (({u, v} : Set V)ᶜ)} // w ∈
        (S : Set {w : V // w ∈ (({u, v} : Set V)ᶜ)})} ≃
      {x : V // x ∈ (T : Set V)} :=
    e₀.trans (Equiv.setCongr hsets)
  let gi :
      (deletePair G u v).induce
          (S : Set {w : V // w ∈ (({u, v} : Set V)ᶜ)}) ≃g
        G.induce (T : Set V) := by
    refine { toEquiv := e, map_rel_iff' := ?_ }
    intro x y
    simp only [SimpleGraph.induce_adj]
    rfl
  have hinduce :
      ((deletePair G u v).induce
        (S : Set {w : V // w ∈ (({u, v} : Set V)ᶜ)})).edgeFinset.card =
      (G.induce (T : Set V)).edgeFinset.card :=
    gi.card_edgeFinset_eq
  rw [hinduce]
  simpa only [hcardT] using hsparse

/-- The graph left after deleting degree-three false twins from a circuit is
connected.  Exact `(2,4)` density gives connectedness once every component
has at least two vertices.  A singleton component would have all its ambient
neighbours among the two deleted twins, contradicting the circuit's minimum
degree three. -/
theorem Is23Circuit.deletePair_connected
    (hcircuit : Is23Circuit G) {u v : V}
    (htwin : AreFalseTwins G u v) (hdeg : G.degree u = 3) :
    (deletePair G u v).Connected := by
  have hcardV : 4 ≤ Fintype.card V := by
    have hlt := G.degree_lt_card_verts u
    omega
  have hdv : G.degree v = 3 := htwin.degree_eq.symm.trans hdeg
  have hconn := pairDeleted.connected_of_is23Circuit
    hcircuit hcardV htwin.1 htwin.not_adj hdeg hdv
  exact (deletePairIsoPairDeleted G u v).connected_iff.mpr hconn

/-- Closing a path through the three common neighbours of false twins via
one twin gives a rim cycle; the other twin is adjacent to three distinct
vertices of that rim. -/
theorem hasWheelWitness_of_falseTwins_of_terminalPath
    {u v a b c x y : V}
    (htwin : AreFalseTwins G u v)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.Adj u a) (hb : G.Adj u b) (hc : G.Adj u c)
    (hx : x ∈ ({a, b, c} : Finset V))
    (hy : y ∈ ({a, b, c} : Finset V)) (hxy : x ≠ y)
    (p : G.Walk x y) (hp : p.IsPath)
    (hap : a ∈ p.support) (hbp : b ∈ p.support) (hcp : c ∈ p.support)
    (hup : u ∉ p.support) (hvp : v ∉ p.support) :
    HasWheelWitness G := by
  have hux : G.Adj u x := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have huy : G.Adj u y := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hvx : G.Adj v x := (htwin.adj_iff x).mp hux
  have hvy : G.Adj v y := (htwin.adj_iff y).mp huy
  let q : G.Walk x v := p.concat hvy.symm
  have hqpath : q.IsPath := hp.concat hvp hvy.symm
  have hpCard : 3 ≤ p.support.toFinset.card := by
    have ha' : a ∈ p.support.toFinset := by simpa using hap
    have hb' : b ∈ p.support.toFinset := by simpa using hbp
    have hc' : c ∈ p.support.toFinset := by simpa using hcp
    have hthree := Finset.two_lt_card_iff.mpr
      ⟨a, b, c, ha', hb', hc', hab, hac, hbc⟩
    omega
  have hpLen : 2 ≤ p.length := by
    have hcardEq : p.support.toFinset.card = p.support.length :=
      List.toFinset_card_of_nodup hp.support_nodup
    rw [hcardEq, p.length_support] at hpCard
    omega
  have hedge : s(v, x) ∉ q.edges := by
    intro hedge
    have hlen := hqpath.length_eq_one_of_mem_edges (by
      simpa only [Sym2.eq_swap] using hedge)
    simp only [q, Walk.length_concat] at hlen
    omega
  let rim : G.Walk v v := Walk.cons hvx q
  have hrim : rim.IsCycle := by
    exact (Walk.cons_isCycle_iff q hvx).mpr ⟨hqpath, hedge⟩
  have hsupp : rim.support = v :: (p.support ++ [v]) := by
    simp [rim, q]
  refine ⟨v, rim, u, hrim, ?_, ?_⟩
  · rw [hsupp]
    simp [htwin.1, hup]
  · have haR : a ∈ G.neighborFinset u ∩ rim.support.toFinset := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨ha, by rw [hsupp]; simp [hap]⟩
    have hbR : b ∈ G.neighborFinset u ∩ rim.support.toFinset := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hb, by rw [hsupp]; simp [hbp]⟩
    have hcR : c ∈ G.neighborFinset u ∩ rim.support.toFinset := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hc, by rw [hsupp]; simp [hcp]⟩
    have hthree := Finset.two_lt_card_iff.mpr
      ⟨a, b, c, haR, hbR, hcR, hab, hac, hbc⟩
    omega

/-- The three common neighbours of a degree-three false-twin pair can be
enumerated by distinct vertices. -/
theorem exists_common_neighbors_three_of_falseTwins
    {u v : V} (htwin : AreFalseTwins G u v) (hdeg : G.degree u = 3) :
    ∃ a b c : V,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        G.neighborFinset u = {a, b, c} ∧
        G.neighborFinset v = {a, b, c} := by
  have hcard : (G.neighborFinset u).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, hdeg]
  obtain ⟨a, b, c, hab, hac, hbc, hN⟩ := Finset.card_eq_three.mp hcard
  refine ⟨a, b, c, hab, hac, hbc, hN, ?_⟩
  rw [← htwin.neighborFinset_eq]
  exact hN

/-- A terminal path in the graph obtained by deleting the twins maps to a
path in the ambient graph avoiding both twins, so the preceding closure
lemma applies. -/
theorem hasWheelWitness_of_falseTwins_of_deletePair_terminalPath
    {u v a b c : V}
    (htwin : AreFalseTwins G u v)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.Adj u a) (hb : G.Adj u b) (hc : G.Adj u c)
    (haD : a ∈ (({u, v} : Set V)ᶜ))
    (hbD : b ∈ (({u, v} : Set V)ᶜ))
    (hcD : c ∈ (({u, v} : Set V)ᶜ))
    (hpath : HasThreeTerminalPath (deletePair G u v)
      ⟨a, haD⟩ ⟨b, hbD⟩ ⟨c, hcD⟩) :
    HasWheelWitness G := by
  rcases hpath with ⟨x, y, hx, hy, hxy, p, hp, hap, hbp, hcp⟩
  let inc : deletePair G u v →g G :=
    { toFun := Subtype.val
      map_rel' := fun h ↦ h }
  let pG : G.Walk (x : V) (y : V) := p.map inc
  have hpG : pG.IsPath := hp.map Subtype.val_injective
  have hxG : (x : V) ∈ ({a, b, c} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  have hyG : (y : V) ∈ ({a, b, c} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  have hxyG : (x : V) ≠ (y : V) := by
    exact fun h ↦ hxy (Subtype.ext h)
  have haP : a ∈ pG.support := by
    change a ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨⟨a, haD⟩, hap, rfl⟩
  have hbP : b ∈ pG.support := by
    change b ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨⟨b, hbD⟩, hbp, rfl⟩
  have hcP : c ∈ pG.support := by
    change c ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨⟨c, hcD⟩, hcp, rfl⟩
  have huP : u ∉ pG.support := by
    change u ∉ (p.map inc).support
    rw [Walk.support_map]
    intro hu
    obtain ⟨z, hz, hzu⟩ := List.mem_map.mp hu
    have hzu' : (z : V) = u := hzu
    have hzD := z.2
    simp [hzu'] at hzD
  have hvP : v ∉ pG.support := by
    change v ∉ (p.map inc).support
    rw [Walk.support_map]
    intro hv
    obtain ⟨z, hz, hzv⟩ := List.mem_map.mp hv
    have hzv' : (z : V) = v := hzv
    have hzD := z.2
    simp [hzv'] at hzD
  exact hasWheelWitness_of_falseTwins_of_terminalPath
    htwin hab hac hbc ha hb hc hxG hyG hxyG pG hpG
      haP hbP hcP huP hvP

/-- Every common neighbour of false twins survives deletion of the pair. -/
theorem common_neighbor_mem_deletePair
    {u v a : V} (htwin : AreFalseTwins G u v) (ha : G.Adj u a) :
    a ∈ (({u, v} : Set V)ᶜ) := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or]
  constructor
  · exact ha.ne.symm
  · intro hav
    subst a
    exact htwin.not_adj ha

/-- Final adapter for the recursive block-counting form of the
three-terminal theorem.  A path gives a wheel, while the alternative sharp
edge bound contradicts the exact `(2,4)` deletion count. -/
theorem hasWheelWitness_of_falseTwins_of_deletePair_path_or_densityBound
    {u v a b c : V}
    (htwin : AreFalseTwins G u v)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.Adj u a) (hb : G.Adj u b) (hc : G.Adj u c)
    (hcount : (deletePair G u v).edgeFinset.card + 4 =
      2 * Fintype.card {w : V // w ∈ (({u, v} : Set V)ᶜ)})
    (hpath_or_bound :
      HasThreeTerminalPath (deletePair G u v)
          ⟨a, common_neighbor_mem_deletePair htwin ha⟩
          ⟨b, common_neighbor_mem_deletePair htwin hb⟩
          ⟨c, common_neighbor_mem_deletePair htwin hc⟩ ∨
        (deletePair G u v).edgeFinset.card + 5 ≤
          2 * Fintype.card {w : V // w ∈ (({u, v} : Set V)ᶜ)}) :
    HasWheelWitness G := by
  rcases hpath_or_bound with hpath | hbound
  · exact hasWheelWitness_of_falseTwins_of_deletePair_terminalPath
      htwin hab hac hbc ha hb hc
        (common_neighbor_mem_deletePair htwin ha)
        (common_neighbor_mem_deletePair htwin hb)
        (common_neighbor_mem_deletePair htwin hc) hpath
  · omega

/-- Certificate form used by the block-tree construction: either the three
terminals lie on a path, or the deletion has at least three blocks.  The
abstract block-counting theorem turns the second certificate into the sharp
density contradiction. -/
theorem hasWheelWitness_of_falseTwins_of_deletePair_path_or_threeBlocks
    {u v a b c : V}
    (htwin : AreFalseTwins G u v)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.Adj u a) (hb : G.Adj u b) (hc : G.Adj u c)
    (hcount : (deletePair G u v).edgeFinset.card + 4 =
      2 * Fintype.card {w : V // w ∈ (({u, v} : Set V)ᶜ)})
    (hsparse : Is23Sparse (deletePair G u v))
    (hpath_or_blocks :
      HasThreeTerminalPath (deletePair G u v)
          ⟨a, common_neighbor_mem_deletePair htwin ha⟩
          ⟨b, common_neighbor_mem_deletePair htwin hb⟩
          ⟨c, common_neighbor_mem_deletePair htwin hc⟩ ∨
        ∃ k : ℕ, 3 ≤ k ∧
          Nonempty (BlockCountCertificate (deletePair G u v) k)) :
    HasWheelWitness G := by
  apply hasWheelWitness_of_falseTwins_of_deletePair_path_or_densityBound
    htwin hab hac hbc ha hb hc hcount
  rcases hpath_or_blocks with hpath | ⟨k, hk, D⟩
  · exact Or.inl hpath
  · rcases D with ⟨D⟩
    exact Or.inr (D.edge_card_add_five_le hk hsparse)

/-- Circuit-level wrapper: all numerical hypotheses of the preceding
adapter follow automatically from the circuit count and a degree-three
false-twin pair. -/
theorem Is23Circuit.hasWheelWitness_of_falseTwins_of_path_or_threeBlocks
    (hcircuit : Is23Circuit G) {u v a b c : V}
    (htwin : AreFalseTwins G u v) (hdeg : G.degree u = 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.Adj u a) (hb : G.Adj u b) (hc : G.Adj u c)
    (hpath_or_blocks :
      HasThreeTerminalPath (deletePair G u v)
          ⟨a, common_neighbor_mem_deletePair htwin ha⟩
          ⟨b, common_neighbor_mem_deletePair htwin hb⟩
          ⟨c, common_neighbor_mem_deletePair htwin hc⟩ ∨
        ∃ k : ℕ, 3 ≤ k ∧
          Nonempty (BlockCountCertificate (deletePair G u v) k)) :
    HasWheelWitness G := by
  exact hasWheelWitness_of_falseTwins_of_deletePair_path_or_threeBlocks
    htwin hab hac hbc ha hb hc
      (hcircuit.deletePair_has24Count htwin hdeg)
      (hcircuit.is23Sparse_deletePair u v) hpath_or_blocks

end Erdos916
