import ErdosProblems.Erdos577.JointBridgeHeavy
import ErdosProblems.Erdos577.JointFirstTripleFactors

/-! All bridge triple factors are completed with their exact unchanged or replaced blocks. -/

namespace Erdos577.JointBridge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem two_leaves_no_factor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a b j : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks)
    (hb : b ∈ c.blocks) (hj : j ∈ c.blocks)
    (has : a ≠ s) (hab : a ≠ b) (hbs : b ≠ s)
    (hjs : j ≠ s) (haj : a ≠ j) (hjb : j ≠ b)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseTwo p q)
    (hthree : 3 ≤ degreeIn G (q 3) b)
    {z u : V} (hz : z ∈ a) (hu : u ∈ b)
    (hcore : QuadOn G ((p.triangle ∪ a) \ {z, p.center, p.vertices 2})) :
    ¬LocalFactor G (insert p.leaf ({u, z, p.center} ∪ j)) := by
  intro hf
  have hrepP := (JointClaims.eight_terminal_rows hc hcard hn p hp hs hb hbs q hq
    hcase hthree).1 u hu
  have hrepQ := JointClaims.case_two_universal hc p hp hs q hq hcase (q 3)
    ((q.mem_support _).mpr ⟨3, rfl⟩)
  have he : insert p.leaf ({u, z, p.center} ∪ j) =
      insert u (insert p.leaf ({z, p.center} ∪ ({j} : Finset (Finset V)).biUnion id)) := by
    simp only [singleton_biUnion, id_eq, insert_union]
    rw [insert_comm p.leaf u]
  exact hn (hasPacking_of_bridge_partial hcard p hp hs ha hb has hab hbs q hq {j}
    (singleton_subset_iff.mpr hj) (by simpa only [mem_singleton] using haj)
    (by simpa only [mem_singleton] using hjs.symm)
    (by simpa only [mem_singleton] using hjb.symm) hz hu hcore hrepP hrepQ (he ▸ hf.partition))

omit [DecidableRel G.Adj] in
theorem exposed_pair_no_factor {d : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (u : V) (hout : u ∉ p.support) (hru : G.Adj p.center u)
    (ht : d.terminal = u) (hT : d.triangle = p.triangle)
    {a j : Finset V} (ha : a ∈ d.blocks) (hj : j ∈ d.blocks) (haj : a ≠ j)
    {z1 z2 : V} (h1 : z1 ∈ a) (h2 : z2 ∈ a)
    (hr : QuadOn G ((p.triangle ∪ a) \ {p.center, z1, z2})) :
    ¬LocalFactor G (insert u ({p.center, z1, z2} ∪ j)) := by
  let p' := centerPaw p u hout hru
  have hp' : p'.support = d.remainder := by
    rw [centerPaw_support]
    change insert u p.triangle = insert d.terminal d.triangle
    rw [ht, hT]
  exact JointFirst.leaf_pair_no_factor hcard hn p' hp' ha hj haj h1 h2 hr

theorem arms_erase_no_factor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a b j : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks)
    (hb : b ∈ c.blocks) (hj : j ∈ c.blocks)
    (has : a ≠ s) (hab : a ≠ b) (hbs : b ≠ s)
    (hjs : j ≠ s) (haj : a ≠ j) (hjb : j ≠ b)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseTwo p q)
    (hthree : 3 ≤ degreeIn G (q 3) b)
    {u : V} (hu : u ∈ b) (hru : G.Adj p.center u)
    (d : TriangleChain G) (ht : d.terminal = u) (hT : d.triangle = p.triangle)
    (had : a ∈ d.blocks) (hjd : j ∈ d.blocks)
    {z1 z2 : V} (h1 : z1 ∈ a) (h2 : z2 ∈ a) (hne : z1 ≠ z2)
    (hr : QuadOn G ((p.triangle ∪ a) \ {p.center, z1, z2}))
    (hr1 : QuadOn G ((p.triangle ∪ a) \ {z1, p.center, p.vertices 2}))
    (hr2 : QuadOn G ((p.triangle ∪ a) \ {z2, p.center, p.vertices 2})) :
    ∀ w ∈ arms p u z1 z2, ¬LocalFactor G (insert p.center ((arms p u z1 z2).erase w) ∪ j) := by
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hFB : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hAB := c.property.blocks_disjoint ha hb hab
  have hxF : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  have hout : u ∉ p.support := fun hh ↦ disjoint_left.mp hFB hh hu
  have hxu : p.leaf ≠ u := fun he ↦ hout (he ▸ hxF)
  have hx1 : p.leaf ≠ z1 := fun he ↦ disjoint_left.mp hFA hxF (he.symm ▸ h1)
  have hx2 : p.leaf ≠ z2 := fun he ↦ disjoint_left.mp hFA hxF (he.symm ▸ h2)
  have hu1 : u ≠ z1 := fun he ↦ disjoint_left.mp hAB h1 (he ▸ hu)
  have hu2 : u ≠ z2 := fun he ↦ disjoint_left.mp hAB h2 (he ▸ hu)
  intro w hw
  simp only [arms, mem_insert, mem_singleton] at hw
  rcases hw with hw | hw | hw | hw
  · subst w
    have he : (arms p u z1 z2).erase p.leaf = {u, z1, z2} := by
      simp [arms, hxu, hx1, hx2]
    rw [he]
    simpa only [insert_union, singleton_union, insert_comm u p.center] using
      exposed_pair_no_factor hcard hn p u hout hru ht hT had hjd haj h1 h2 hr
  · subst w
    have he : (arms p u z1 z2).erase u = {p.leaf, z1, z2} := by
      rw [arms, erase_insert_of_ne hxu, erase_insert (by simp [hu1, hu2])]
    rw [he]
    simpa only [insert_union, singleton_union, insert_comm p.leaf p.center] using
      JointFirst.leaf_pair_no_factor hcard hn p hp ha hj haj h1 h2 hr
  · subst w
    have he : (arms p u z1 z2).erase z1 = {p.leaf, u, z2} := by
      rw [arms, erase_insert_of_ne hx1, erase_insert_of_ne hu1, erase_insert (by simp [hne])]
    rw [he]
    have hf := two_leaves_no_factor hc hcard hn p hp hs ha hb hj has hab hbs hjs haj hjb
      q hq hcase hthree h2 hu hr2
    have hset : insert p.leaf ({u, z2, p.center} ∪ j) =
        insert p.center {p.leaf, u, z2} ∪ j := by
      simp only [insert_union, singleton_union]
      rw [insert_comm p.center p.leaf, insert_comm p.center u, insert_comm p.center z2]
    exact hset ▸ hf
  · subst w
    have he : (arms p u z1 z2).erase z2 = {p.leaf, u, z1} := by
      rw [arms, erase_insert_of_ne hx2, erase_insert_of_ne hu2, erase_insert_of_ne hne]
      simp
    rw [he]
    have hf := two_leaves_no_factor hc hcard hn p hp hs ha hb hj has hab hbs hjs haj hjb
      q hq hcase hthree h1 hu hr1
    have hset : insert p.leaf ({u, z1, p.center} ∪ j) =
        insert p.center {p.leaf, u, z1} ∪ j := by
      simp only [insert_union, singleton_union]
      rw [insert_comm p.center p.leaf, insert_comm p.center u, insert_comm p.center z1]
    exact hset ▸ hf

end Erdos577.JointBridge
