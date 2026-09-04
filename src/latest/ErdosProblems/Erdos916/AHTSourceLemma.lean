/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTConnectivity
import ErdosProblems.Erdos916.AHTThreeConnected
import ErdosProblems.Erdos916.ThreeTerminalPath

/-!
# The triangle lemma from AHT Section 6

This file formalizes Lemma 6.1 of Aboulker--Havet--Trotignon: a
three-connected almost-wheel-free graph is triangle-free.  We use the
separation-based finite connectivity predicate from `Erdos718` and the
equivalent, source-faithful formulation of almost wheel-freeness saying that
all possible wheel centres lie in one displayed two-set.

The proof is the paper proof.  If `x y z` is a triangle, three-connectivity
gives a third neighbour `t` of `x`.  After deleting `x` the graph is
vertex-two-connected, so there is a simple path from `y` to `z` through `t`.
Closing this path with the edge `zy` gives a cycle on which `x` has the three
neighbours `y`, `z`, and `t`.  Thus every vertex of the triangle is a wheel
centre.  Three distinct vertices cannot all belong to the exceptional
two-set.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The direct triangle formulation used in AHT Lemma 6.1. -/
def AHTTriangleFree (G : SimpleGraph V) : Prop :=
  ∀ ⦃x y z : V⦄, G.Adj x y → G.Adj y z → G.Adj z x → False

/-- Deleting one vertex from a finite three-connected graph leaves a
vertex-two-connected graph. -/
theorem vertexTwoConnected_delete_of_isThreeConnected
    (hthree : IsThreeConnected G) (x : V) :
    (G.induce fun w : V ↦ w ≠ x).Connected ∧
      ∀ d : {w : V // w ≠ x},
        ((G.induce fun w : V ↦ w ≠ x).induce
          fun w : {w : V // w ≠ x} ↦ w ≠ d).Connected := by
  have hsmallX : ({x} : Finset V).card < Fintype.card V := by
    have := hthree.1
    simp only [Finset.card_singleton]
    omega
  obtain ⟨w, -, hw⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hsmallX
  have hwx : w ≠ x := by simpa using hw
  have hpre0 := hthree.induce_compl_preconnected ({x} : Finset V) (by simp)
  let e0 : {w : V // w ∉ ({x} : Finset V)} ≃ {w : V // w ≠ x} :=
    Equiv.setCongr (by ext q; simp)
  let gi0 :
      (G.induce fun w : V ↦ w ∉ ({x} : Finset V)) ≃g
        (G.induce fun w : V ↦ w ≠ x) :=
    { toEquiv := e0
      map_rel_iff' := by intro u v; rfl }
  have hHpre : (G.induce fun w : V ↦ w ≠ x).Preconnected :=
    gi0.preconnected_iff.mp hpre0
  have hHconn : (G.induce fun w : V ↦ w ≠ x).Connected :=
    { preconnected := hHpre
      nonempty := ⟨⟨w, hwx⟩⟩ }
  refine ⟨hHconn, ?_⟩
  intro d
  have hxd : x ≠ d.1 := fun h ↦ d.2 h.symm
  have hpair0 := hthree.delete_pair_preconnected hxd
  let ePair : {w : V // w ∉ ({x, d.1} : Finset V)} ≃
      {w : V // w ≠ x ∧ w ≠ d.1} :=
    Equiv.setCongr (by ext q; simp)
  let giPair :
      (G.induce fun w : V ↦ w ∉ ({x, d.1} : Finset V)) ≃g
        (G.induce fun w : V ↦ w ≠ x ∧ w ≠ d.1) :=
    { toEquiv := ePair
      map_rel_iff' := by intro u v; rfl }
  have hpair : (G.induce fun w : V ↦ w ≠ x ∧ w ≠ d.1).Preconnected :=
    giPair.preconnected_iff.mp hpair0
  have hpairSmall : ({x, d.1} : Finset V).card < Fintype.card V := by
    have hle := Finset.card_insert_le x ({d.1} : Finset V)
    have hfour := hthree.four_le_card
    simp only [Finset.card_singleton] at hle
    omega
  obtain ⟨q, -, hq⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hpairSmall
  have hqx : q ≠ x := by
    intro h
    exact hq (by simp [h])
  have hqd : q ≠ d.1 := by
    intro h
    exact hq (by simp [h])
  let qFlat : {w : V // w ≠ x ∧ w ≠ d.1} := ⟨q, hqx, hqd⟩
  have hflat : (G.induce fun w : V ↦ w ≠ x ∧ w ≠ d.1).Connected :=
    { preconnected := hpair
      nonempty := ⟨qFlat⟩ }
  let e : {w : V // w ≠ x ∧ w ≠ d.1} ≃
      {w : {w : V // w ≠ x} // w ≠ d} :=
    { toFun := fun r ↦
        ⟨⟨r.1, r.2.1⟩, fun h ↦ r.2.2 (congrArg Subtype.val h)⟩
      invFun := fun r ↦
        ⟨r.1.1, r.1.2, fun h ↦ r.2 (Subtype.ext h)⟩
      left_inv := by intro r; rfl
      right_inv := by intro r; rfl }
  let gi :
      (G.induce fun w : V ↦ w ≠ x ∧ w ≠ d.1) ≃g
        ((G.induce fun w : V ↦ w ≠ x).induce
          fun w : {w : V // w ≠ x} ↦ w ≠ d) :=
    { toEquiv := e
      map_rel_iff' := by intro u v; rfl }
  exact gi.connected_iff.mp hflat

/-- A vertex of degree at least three with two distinct specified neighbours
has a third neighbour. -/
theorem exists_third_neighbor_of_degree_ge_three
    {x y z : V} (hdeg : 3 ≤ G.degree x)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : y ≠ z) :
    ∃ t : V, G.Adj x t ∧ t ≠ y ∧ t ≠ z := by
  have hy : y ∈ G.neighborFinset x := by simpa using hxy
  have hz : z ∈ G.neighborFinset x := by simpa using hxz
  have hpair : ({y, z} : Finset V) ⊆ G.neighborFinset x := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hy
    · exact hz
  have hcard : 3 ≤ (G.neighborFinset x).card := by
    simpa only [G.card_neighborFinset_eq_degree] using hdeg
  have hstrict : ({y, z} : Finset V) ⊂ G.neighborFinset x := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hpair, ?_⟩
    intro heq
    have heqCard := congrArg Finset.card heq
    have hpairCard : ({y, z} : Finset V).card = 2 := by simp [hyz]
    omega
  obtain ⟨t, ht, htPair⟩ := Finset.exists_of_ssubset hstrict
  refine ⟨t, by simpa using ht, ?_, ?_⟩
  · intro hty
    exact htPair (by simp [hty])
  · intro htz
    exact htPair (by simp [htz])

/-- Closing a simple `y`--`z` path through a third vertex `t` by the edge
`zy` produces a rim witnessing that `x` is a wheel centre. -/
theorem hasWheelCenteredAt_of_rooted_path
    {x y z t : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hxt : G.Adj x t)
    (hyz : G.Adj y z) (hyt : y ≠ t) (hzt : z ≠ t)
    (p : G.Walk y z) (hp : p.IsPath) (htp : t ∈ p.support)
    (hxp : x ∉ p.support) :
    HasWheelCenteredAt G x := by
  have hpCard : 3 ≤ p.support.toFinset.card := by
    have hyP : y ∈ p.support.toFinset := by simp
    have hzP : z ∈ p.support.toFinset := by simp
    have htP : t ∈ p.support.toFinset := by simpa using htp
    have hthree := Finset.two_lt_card_iff.mpr
      ⟨y, z, t, hyP, hzP, htP, hyz.ne, hyt, hzt⟩
    omega
  have hpLen : 1 < p.length := by
    have hcardEq : p.support.toFinset.card = p.support.length :=
      List.toFinset_card_of_nodup hp.support_nodup
    rw [hcardEq, p.length_support] at hpCard
    omega
  have hstart : y ∉ p.support.tail := by
    have hnd := hp.support_nodup
    rw [← p.cons_tail_support] at hnd
    exact (List.nodup_cons.mp hnd).1
  have hdisj :
      p.support.tail.Disjoint hyz.symm.toWalk.support.tail := by
    change p.support.tail.Disjoint [y]
    simpa only [List.disjoint_cons_right, List.disjoint_nil_right, and_true]
      using hstart
  let rim : G.Walk y y := p.concat hyz.symm
  have hrim : rim.IsCycle := by
    change (p.concat hyz.symm).IsCycle
    rw [Walk.concat_eq_append]
    exact hp.isCycle_append (Walk.IsPath.of_adj hyz.symm) hdisj (Or.inl hpLen)
  have hxr : x ∉ rim.support := by
    intro hxr
    simp only [rim, Walk.support_concat, List.mem_append,
      List.mem_singleton] at hxr
    rcases hxr with hxP | hxy'
    · exact hxp hxP
    · exact hxy.ne hxy'
  refine ⟨y, rim, hrim, hxr, ?_⟩
  have hyR : y ∈ G.neighborFinset x ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hxy, by simp [rim]⟩
  have hzR : z ∈ G.neighborFinset x ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hxz, by simp [rim]⟩
  have htR : t ∈ G.neighborFinset x ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hxt, by simp [rim, htp]⟩
  have hthree := Finset.two_lt_card_iff.mpr
    ⟨y, z, t, hyR, hzR, htR, hyz.ne, hyt, hzt⟩
  omega

/-- Every vertex of a triangle in a finite three-connected graph is a wheel
centre.  This is the constructive core of AHT Lemma 6.1. -/
theorem hasWheelCenteredAt_of_triangle_of_isThreeConnected
    (hthree : IsThreeConnected G)
    {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hzx : G.Adj z x) :
    HasWheelCenteredAt G x := by
  have hdeg : 3 ≤ G.degree x := hthree.degree_ge x
  obtain ⟨t, hxt, hty, htz⟩ :=
    exists_third_neighbor_of_degree_ge_three hdeg hxy hzx.symm hyz.ne
  let H := G.induce fun w : V ↦ w ≠ x
  have h2 : H.Connected ∧
      ∀ d : {w : V // w ≠ x},
        (H.induce fun w : {w : V // w ≠ x} ↦ w ≠ d).Connected :=
    vertexTwoConnected_delete_of_isThreeConnected hthree x
  let y' : {w : V // w ≠ x} := ⟨y, hxy.ne.symm⟩
  let z' : {w : V // w ≠ x} := ⟨z, hzx.ne⟩
  let t' : {w : V // w ≠ x} := ⟨t, hxt.ne.symm⟩
  have hyt' : y' ≠ t' := by
    intro h
    exact hty (congrArg Subtype.val h).symm
  have hyz' : y' ≠ z' := by
    intro h
    exact hyz.ne (congrArg Subtype.val h)
  have htz' : t' ≠ z' := by
    intro h
    exact htz (congrArg Subtype.val h)
  obtain ⟨p, hp, htp⟩ := exists_rooted_three_path
    (V := {w : V // w ≠ x}) (G := H) (r := y') (a := t') (b := z')
      hyt' hyz' htz' h2.1 h2.2
  let inc : H →g G :=
    (SimpleGraph.Embedding.induce (G := G) (s := fun w : V ↦ w ≠ x)).toHom
  let pG : G.Walk y z := p.map inc
  have hpG : pG.IsPath := hp.map Subtype.val_injective
  have htPG : t ∈ pG.support := by
    change t ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨t', htp, rfl⟩
  have hxPG : x ∉ pG.support := by
    change x ∉ (p.map inc).support
    rw [Walk.support_map]
    intro hx
    obtain ⟨w, -, hw⟩ := List.mem_map.mp hx
    have hwval : w.1 = x := by simpa [inc] using hw
    exact w.2 hwval
  exact hasWheelCenteredAt_of_rooted_path hxy hzx.symm hxt hyz
    hty.symm htz.symm pG hpG htPG hxPG

/-- **AHT Lemma 6.1.**  A finite three-connected graph whose wheel centres
are confined to two displayed vertices is triangle-free.  AHT's
"almost-wheel-free" condition implies precisely this confinement (and adds
degree/adjacency information about the exceptional vertices, which this
lemma does not need). -/
theorem aht_triangleFree_of_threeConnected_almostWheelFreeAt
    {a b : V} (hthree : IsThreeConnected G)
    (halmost : AlmostWheelFreeAt G a b) :
    AHTTriangleFree G := by
  unfold AHTTriangleFree
  intro x y z hxy hyz hzx
  have hxCenter : HasWheelCenteredAt G x :=
    hasWheelCenteredAt_of_triangle_of_isThreeConnected hthree hxy hyz hzx
  have hyCenter : HasWheelCenteredAt G y :=
    hasWheelCenteredAt_of_triangle_of_isThreeConnected
      hthree hyz hzx hxy
  have hzCenter : HasWheelCenteredAt G z :=
    hasWheelCenteredAt_of_triangle_of_isThreeConnected
      hthree hzx hxy hyz
  let T : Finset V := {x, y, z}
  let E : Finset V := {a, b}
  have hTcard : T.card = 3 := by
    simp [T, hxy.ne, hyz.ne, hzx.ne.symm]
  have hEcard : E.card ≤ 2 := by
    exact (Finset.card_insert_le a {b}).trans (by simp)
  have hnsub : ¬T ⊆ E := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  have hwitness : ∃ w, w ∈ T ∧ w ∉ E := by
    by_contra h
    apply hnsub
    intro w hwT
    by_contra hwE
    exact h ⟨w, hwT, hwE⟩
  obtain ⟨w, hwT, hwE⟩ := hwitness
  have hwa : w ≠ a := by
    intro h
    exact hwE (by simp [E, h])
  have hwb : w ≠ b := by
    intro h
    exact hwE (by simp [E, h])
  have hwCases : w = x ∨ w = y ∨ w = z := by
    simpa [T] using hwT
  rcases hwCases with hw | hw | hw
  · exact halmost x (by simpa [hw] using hwa) (by simpa [hw] using hwb)
      hxCenter
  · exact halmost y (by simpa [hw] using hwa) (by simpa [hw] using hwb)
      hyCenter
  · exact halmost z (by simpa [hw] using hwa) (by simpa [hw] using hwb)
      hzCenter

/-- **AHT Lemma 6.1, source-exact form.**  Every finite three-connected
almost-wheel-free graph is triangle-free. -/
theorem aht_triangleFree_of_threeConnected_almostWheelFree
    (hthree : IsThreeConnected G)
    (halmost : AlmostWheelFree G) :
    AHTTriangleFree G := by
  have hnonempty : Nonempty V := by
    exact Fintype.card_pos_iff.mp (by have := hthree.1; omega)
  let : Nonempty V := hnonempty
  obtain hnone | hone | htwo := halmost
  · let a : V := Classical.choice hnonempty
    apply aht_triangleFree_of_threeConnected_almostWheelFreeAt
      (a := a) (b := a) hthree
    intro x _ _ hx
    exact hnone x hx
  · obtain ⟨a, -, hcentres⟩ := hone
    apply aht_triangleFree_of_threeConnected_almostWheelFreeAt
      (a := a) (b := a) hthree
    intro x hxa _ hx
    exact hxa (hcentres x hx)
  · obtain ⟨a, b, -, -, -, hcentres⟩ := htwo
    apply aht_triangleFree_of_threeConnected_almostWheelFreeAt
      (a := a) (b := b) hthree
    intro x hxa hxb hx
    rcases hcentres x hx with rfl | rfl
    · exact hxa rfl
    · exact hxb rfl

end Erdos916
