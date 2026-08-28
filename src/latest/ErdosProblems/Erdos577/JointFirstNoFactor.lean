import ErdosProblems.Erdos577.JointFirstTripleFactors
import ErdosProblems.Erdos577.JointFirstArms
import ErdosProblems.Erdos577.StarCommonInsertion

/-! The four arm-triple exclusions are uniform in the omitted arm. -/

namespace Erdos577.JointFirst

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem arms_erase_no_factor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a j : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (hj : j ∈ c.blocks)
    (has : a ≠ s) (hjs : j ≠ s) (haj : a ≠ j)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseOne p q)
    {z1 z2 : V} (h1 : z1 ∈ a) (h2 : z2 ∈ a) (hne : z1 ≠ z2)
    (hr : QuadOn G ((p.triangle ∪ a) \ {p.center, z1, z2}))
    (hr1 : QuadOn G ((p.triangle ∪ a) \ {z1, p.center, p.vertices 2}))
    (hr2 : QuadOn G ((p.triangle ∪ a) \ {z2, p.center, p.vertices 2})) :
    ∀ w ∈ arms p q z1 z2, ¬LocalFactor G (insert p.center ((arms p q z1 z2).erase w) ∪ j) := by
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hAQ : Disjoint a q.support := by rw [hq]; exact c.property.blocks_disjoint ha hs has
  have hxF : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  have hvQ : q 1 ∈ q.support := (q.mem_support _).mpr ⟨1, rfl⟩
  have hxv : p.leaf ≠ q 1 := fun he ↦ disjoint_left.mp hFQ hxF (he.symm ▸ hvQ)
  have hx1 : p.leaf ≠ z1 := fun he ↦ disjoint_left.mp hFA hxF (he.symm ▸ h1)
  have hx2 : p.leaf ≠ z2 := fun he ↦ disjoint_left.mp hFA hxF (he.symm ▸ h2)
  have hv1 : q 1 ≠ z1 := fun he ↦ disjoint_left.mp hAQ h1 (he ▸ hvQ)
  have hv2 : q 1 ≠ z2 := fun he ↦ disjoint_left.mp hAQ h2 (he ▸ hvQ)
  intro w hw
  simp only [arms, mem_insert, mem_singleton] at hw
  rcases hw with hw | hw | hw | hw
  · subst w
    have he : (arms p q z1 z2).erase p.leaf = {q 1, z1, z2} := by
      simp [arms, hxv, hx1, hx2]
    rw [he]
    simpa only [insert_union, singleton_union, insert_comm (q 1) p.center] using
      center_pair_no_factor hc hcard hn p hp hs ha hj has hjs haj q hq hcase h1 h2 hr
  · subst w
    have he : (arms p q z1 z2).erase (q 1) = {p.leaf, z1, z2} := by
      rw [arms, erase_insert_of_ne hxv, erase_insert (by simp [hv1, hv2])]
    rw [he]
    simpa only [insert_union, singleton_union, insert_comm p.leaf p.center] using
      leaf_pair_no_factor hcard hn p hp ha hj haj h1 h2 hr
  · subst w
    have he : (arms p q z1 z2).erase z1 = {p.leaf, q 1, z2} := by
      rw [arms, erase_insert_of_ne hx1, erase_insert_of_ne hv1,
        erase_insert (by simp [hne])]
    rw [he]
    have hf := two_leaves_no_factor hc hcard hn p hp hs ha hj has hjs haj q hq hcase h2 hr2
    have hset : insert p.leaf ({q 1, z2, p.center} ∪ j) =
        insert p.center {p.leaf, q 1, z2} ∪ j := by
      simp only [insert_union, singleton_union]
      rw [insert_comm p.center p.leaf, insert_comm p.center (q 1), insert_comm p.center z2]
    exact hset ▸ hf
  · subst w
    have he : (arms p q z1 z2).erase z2 = {p.leaf, q 1, z1} := by
      rw [arms, erase_insert_of_ne hx2, erase_insert_of_ne hv2, erase_insert_of_ne hne]
      simp
    rw [he]
    have hf := two_leaves_no_factor hc hcard hn p hp hs ha hj has hjs haj q hq hcase h1 hr1
    have hset : insert p.leaf ({q 1, z1, p.center} ∪ j) =
        insert p.center {p.leaf, q 1, z1} ∪ j := by
      simp only [insert_union, singleton_union]
      rw [insert_comm p.center p.leaf, insert_comm p.center (q 1), insert_comm p.center z1]
    exact hset ▸ hf

end Erdos577.JointFirst
