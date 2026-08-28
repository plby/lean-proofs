import ErdosProblems.Erdos577.FullLeafHeavyCrossing

/-! A degree-three second row cannot meet both low columns of an opposite first pair. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

theorem Configuration.low_pair_forces_complete {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a) (hfive : 5 ≤ contacts G (s.erase y) q.support)
    (hfull : degreeIn G (q 0) (insert (p.vertices 3) a) = 5)
    {u : V} (hu : u ∈ insert (p.vertices 3) a) (h1 : G.Adj u (q 1)) (h3 : G.Adj u (q 3)) :
    G.IsNClique 4 q.support := by
  have hm (i : Fin 4) : q i ∈ q.support := (q.mem_support _).mpr ⟨i, rfl⟩
  have huout : u ∉ q.support := fun hh ↦ disjoint_left.mp (h.core_disjoint_block hj hja)
    (h.second_five_subset hu) hh
  have hzero := h.triple_degree_of_second_replacement hcard hn hu hj hjs hja (hm 0)
    (JointFinal.low_pair_replace q u huout h1 h3 0 (Or.inl rfl))
  have hlow (w : V) (hw : w ∈ s.erase y) : ¬(G.Adj w (q 1) ∧ G.Adj w (q 3)) := by
    rintro ⟨hw1, hw3⟩
    have hwZ : w ∈ insert p.leaf s := mem_insert_of_mem (mem_erase.mp hw).2
    have hwout : w ∉ q.support := fun hh ↦
      disjoint_left.mp (h.five_disjoint_block hj hjs) hwZ hh
    have hrep := JointFinal.low_pair_replace q w hwout hw1 hw3 0 (Or.inl rfl)
    have hb := h.core_degree_of_first_replacement hcard hn hwZ hj hjs hja (hm 0) hrep
    have hmono := degreeIn_mono G (q 0) h.second_five_subset
    omega
  obtain ⟨w, hw, hw2, hwlow⟩ := FullLeafHeavy.crossing_of_five q h.first_triple_clique.card_eq
    hfive hzero hlow
  have hwZ : w ∈ insert p.leaf s := mem_insert_of_mem (mem_erase.mp hw).2
  have h2m : q 2 ∈ insert w (q.support.erase (q 0)) := mem_insert_of_mem
    (mem_erase.mpr ⟨q.injective.ne (by decide : (2 : Fin 4) ≠ 0), hm 2⟩)
  have htri : TriangleIn G (insert w (q.support.erase (q 0))) := by
    rcases hwlow with hw1 | hw3
    · refine ⟨{w, q 2, q 1}, insert_subset (mem_insert_self _ _)
        (insert_subset h2m (singleton_subset_iff.mpr ?_)), ?_⟩
      · exact mem_insert_of_mem (mem_erase.mpr ⟨q.injective.ne (by decide), hm 1⟩)
      · exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hw2, hw1, (q.adjacent 1).symm⟩
    · refine ⟨{w, q 2, q 3}, insert_subset (mem_insert_self _ _)
        (insert_subset h2m (singleton_subset_iff.mpr ?_)), ?_⟩
      · exact mem_insert_of_mem (mem_erase.mpr ⟨q.injective.ne (by decide), hm 3⟩)
      · exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hw2, hw3, q.adjacent 2⟩
  have hout : q 0 ∉ p.triangle ∪ a := fun hh ↦
    disjoint_left.mp (h.core_disjoint_block hj hja) hh (hm 0)
  obtain ⟨f, hf⟩ := h.two_complete_core_partition hout hfull
  exact h.complete_of_core_split hwZ hj hjs hja (hm 0) f hf.ge htri

theorem Configuration.two_lows_false {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a) (hfive : 5 ≤ contacts G (s.erase y) q.support)
    (hnine : 9 ≤ degreeIn G (q 0) (insert (p.vertices 3) a) +
      degreeIn G (q 2) (insert (p.vertices 3) a))
    {u : V} (hu : u ∈ insert (p.vertices 3) a) (hrow : 3 ≤ degreeIn G u q.support)
    (h1 : G.Adj u (q 1)) (h3 : G.Adj u (q 3)) : False := by
  have h0b := degreeIn_le_card G (q 0) (insert (p.vertices 3) a)
  have h2b := degreeIn_le_card G (q 2) (insert (p.vertices 3) a)
  rw [h.second_five_card] at h0b h2b
  have hcl : G.IsNClique 4 q.support := by
    by_cases hfull : degreeIn G (q 0) (insert (p.vertices 3) a) = 5
    · exact h.low_pair_forces_complete hcard hn q hj hjs hja hfive hfull hu h1 h3
    · have hfull' : degreeIn G (q 2) (insert (p.vertices 3) a) = 5 := by omega
      have hh := h.low_pair_forces_complete hcard hn (q.rotate 2)
        (by simpa only [Quadrilateral.rotate_support] using hj)
        (by simpa only [Quadrilateral.rotate_support] using hjs)
        (by simpa only [Quadrilateral.rotate_support] using hja)
        (by simpa only [Quadrilateral.rotate_support] using hfive)
        hfull' hu h3 h1
      simpa only [Quadrilateral.rotate_support] using hh
  have hout : u ∉ q.support := fun hh ↦ disjoint_left.mp (h.core_disjoint_block hj hja)
    (h.second_five_subset hu) hh
  exact h.second_not_universal hcard hn hj hjs hja hfive hu
    (fun _ hv ↦ clique_replace_of_degree_three hcl hout hrow hv)

end Erdos577.FullLeafCore
