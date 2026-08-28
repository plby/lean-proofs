import ErdosProblems.Erdos577.TwoCoreBlockScores

/-! Automatic four-clique complements for two full noncentral rows on a complete block. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma core_complement_eq (p : Paw G) (b : Finset V) (hd : Disjoint p.support b)
    (a d : V) (ha : a ∈ b) (hdmem : d ∈ b) :
    (p.triangle ∪ b) \ {a, d, p.center} =
      insert (p.vertices 2) (insert (p.vertices 3) (b \ {a, d})) := by
  have htri : p.triangle ⊆ p.support := p.support_eq ▸ subset_insert _ _
  have haT : a ∉ p.triangle := fun hh ↦ disjoint_left.mp hd (htri hh) ha
  have hdT : d ∉ p.triangle := fun hh ↦ disjoint_left.mp hd (htri hh) hdmem
  have hrB : p.center ∉ b := fun hh ↦ disjoint_left.mp hd
    (show p.center ∈ p.support from (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩) hh
  have hrpair : p.center ∉ ({p.vertices 2, p.vertices 3} : Finset V) := by
    simp only [Paw.center, mem_insert, mem_singleton, p.vertices.injective.eq_iff]
    decide
  have hT : p.triangle \ {a, d, p.center} = {p.vertices 2, p.vertices 3} := by
    rw [sdiff_insert_of_notMem haT, sdiff_insert_of_notMem hdT, sdiff_singleton_eq_erase]
    change (insert p.center {p.vertices 2, p.vertices 3} : Finset V).erase p.center = _
    exact erase_insert hrpair
  have hS : ({a, d, p.center} : Finset V) = insert p.center {a, d} := by
    ext v
    simp only [mem_insert, mem_singleton]
    tauto
  have hB : b \ {a, d, p.center} = b \ {a, d} := by
    rw [hS, sdiff_insert_of_notMem hrB]
  rw [union_sdiff_distrib, hT, hB, insert_union, singleton_union]

variable [DecidableRel G.Adj]

lemma complete_core_complement (p : Paw G) {b : Finset V}
    (hB : G.IsNClique 4 b) (hd : Disjoint p.support b)
    (a d : V) (ha : a ∈ b) (hdmem : d ∈ b) (hne : a ≠ d)
    (hfull2 : degreeIn G (p.vertices 2) b = 4) (hfull3 : degreeIn G (p.vertices 3) b = 4) :
    G.IsNClique 4 ((p.triangle ∪ b) \ {a, d, p.center}) := by
  have hpair : ({a, d} : Finset V) ⊆ b := insert_subset ha (singleton_subset_iff.mpr hdmem)
  have hpaircard : ({a, d} : Finset V).card = 2 := card_pair_eq_two_iff.mpr hne
  have hcard : (b \ {a, d}).card = 2 := by
    rw [card_sdiff_of_subset hpair, hB.card_eq, hpaircard]
  have htwo : G.IsNClique 2 (b \ {a, d}) :=
    ⟨hB.isClique.subset (coe_subset.mpr sdiff_subset), hcard⟩
  have h2row := (degreeIn_eq_card_iff (p.vertices 2) b).mp (hfull2.trans hB.card_eq.symm)
  have h3row := (degreeIn_eq_card_iff (p.vertices 3) b).mp (hfull3.trans hB.card_eq.symm)
  have hthree : G.IsNClique 3 (insert (p.vertices 3) (b \ {a, d})) :=
    htwo.insert (fun u hu ↦ h3row u (mem_sdiff.mp hu).1)
  have hfour : G.IsNClique 4 (insert (p.vertices 2) (insert (p.vertices 3) (b \ {a, d}))) := by
    apply hthree.insert
    intro u hu
    rcases mem_insert.mp hu with rfl | hu
    · exact p.edge23
    · exact h2row u (mem_sdiff.mp hu).1
  rw [core_complement_eq p b hd a d ha hdmem]
  exact hfour

omit [DecidableEq V] in
lemma exists_center_neighbor_ne (p : Paw G) (b : Finset V)
    (hdegree : degreeIn G p.center b = 2) (z : V) :
    ∃ w ∈ b, w ≠ z ∧ G.Adj p.center w := by
  have hcard : 1 < (b.filter (G.Adj p.center)).card := by
    change 1 < degreeIn G p.center b
    rw [hdegree]
    decide
  obtain ⟨w, hw, hne⟩ := exists_mem_ne hcard z
  exact ⟨w, (mem_filter.mp hw).1, hne, (mem_filter.mp hw).2⟩

end Erdos577.TwoCore
