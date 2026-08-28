import ErdosProblems.Erdos577.JointCoreFirstRows
import ErdosProblems.Erdos577.JointCoreCompletion
import ErdosProblems.Erdos577.JointCoreContactFactor

/-! The distinguished core vertices have no neighbors on the first block. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma no_other_contact {s t : Finset V} (hd : Disjoint s t) {u z : V} (hz : z ∈ t)
    (huz : G.Adj u z) (hdegree : degreeIn G u (s ∪ t) ≤ 1) :
    ∀ v ∈ s, ¬G.Adj u v := by
  have huni := FullRow.unique_row_of_bound (s ∪ t) u z (mem_union_right _ hz) huz hdegree
  intro v hv huv
  have he : v = z := (huni.2 v (mem_union_left _ hv)).mp huv
  exact disjoint_left.mp hd hv (he.symm ▸ hz)

variable [Fintype V]

theorem selected_vertex_first_row_zero {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s)
    (hcase : JointClaims.CaseOne p q ∨ JointClaims.CaseTwo p q)
    (houter : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a)
    (hweighted : 13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a)
    (z : V) (hz : z ∈ a) (hrz : G.Adj p.center z)
    (hrem : QuadOn G ((p.triangle ∪ a) \ {z, p.center, p.vertices 2})) :
    degreeIn G z s = 0 := by
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hAQ : Disjoint a q.support := by rw [hq]; exact c.property.blocks_disjoint ha hs has
  have hT : p.triangle ⊆ p.support := p.support_eq ▸ subset_insert _ _
  have h2T : p.vertices 2 ∈ p.triangle := by simp [Paw.triangle]
  apply (degreeIn_eq_zero_iff (G := G) z s).mpr
  intro u hu hzu
  have huQ : u ∈ q.support := hq.symm ▸ hu
  have hcol := first_core_column hc hcard hn p hp hs ha has q hq hcase houter hweighted u hu
  have hnot := no_other_contact (hFA.mono_left hT) hz hzu.symm hcol
  have hmiss : ¬G.Adj (p.vertices 2) u := fun hh ↦ hnot _ h2T hh.symm
  have hxu : G.Adj p.leaf u := by
    obtain ⟨i, rfl⟩ := (q.mem_support u).mp huQ
    by_cases hi : i = 3
    · subst i
      exact False.elim (hmiss (JointClaims.first_rows p q hcase).2)
    · exact (JointClaims.first_rows p q hcase).1 i hi
  have hrep := noncentral_replacement_of_missed hc p hp hs q hq hcase u huQ hmiss
  have hzF : z ∉ p.support := fun hh ↦ disjoint_left.mp hFA hh hz
  have hzQ : z ∉ q.support := fun hh ↦ disjoint_left.mp hAQ hz hh
  have hf := contact_factor p q hFQ z hzF hzQ u huQ hxu hrz hzu hrep
  rw [hq] at hf
  have hused : ({z, p.center, p.vertices 2} : Finset V) ⊆ p.triangle ∪ a :=
    insert_subset (mem_union_right _ hz) (insert_subset (mem_union_left _ p.center_mem_triangle)
      (singleton_subset_iff.mpr (mem_union_left _ h2T)))
  exact hn (hasPacking_of_partial_core hcard p hp ha hs has hused hrem hf)

end Erdos577.JointCore
