import ErdosProblems.Erdos577.StarCommonInsertion
import ErdosProblems.Erdos577.NeighborRowBounds

/-! Nine contacts from four arms exclude every universally replaceable row. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem no_universal_of_nine_contacts {arms j : Finset V}
    (hfour : arms.card = 4) (hj : j.card = 4) (hnine : 9 ≤ contacts G arms j)
    (hno : ∀ x ∈ arms, ∀ y ∈ arms, ∀ z ∈ arms, x ≠ y → x ≠ z → y ≠ z →
      ¬CommonReplacement G x y z j)
    {z : V} (hz : z ∈ arms) : ¬(∀ u ∈ j, QuadOn G (insert z (j.erase u))) := by
  intro hrep
  have herase : (arms.erase z).card = 3 := by rw [card_erase_of_mem hz, hfour]
  obtain ⟨x, y, t, hxy, hxt, hyt, he⟩ := card_eq_three.mp herase
  have hx : x ∈ arms.erase z := by rw [he]; simp
  have hy : y ∈ arms.erase z := by rw [he]; simp
  have ht : t ∈ arms.erase z := by rw [he]; simp
  have hxy' := hno x (mem_erase.mp hx).2 y (mem_erase.mp hy).2 z hz hxy
    (mem_erase.mp hx).1 (mem_erase.mp hy).1
  have hxt' := hno x (mem_erase.mp hx).2 t (mem_erase.mp ht).2 z hz hxt
    (mem_erase.mp hx).1 (mem_erase.mp ht).1
  have hyt' := hno y (mem_erase.mp hy).2 t (mem_erase.mp ht).2 z hz hyt
    (mem_erase.mp hy).1 (mem_erase.mp ht).1
  have hthree := degree_triple_le_card x y t j
    (no_common_of_universal_insertion x y z j hxy' hrep)
    (no_common_of_universal_insertion x t z j hxt' hrep)
    (no_common_of_universal_insertion y t z j hyt' hrep)
  have hrow := degreeIn_le_card G z j
  have hsum : contacts G arms j = degreeIn G z j +
      (degreeIn G x j + (degreeIn G y j + degreeIn G t j)) := by
    rw [contacts, ← insert_erase hz, sum_insert (by simp : z ∉ arms.erase z), he]
    rw [sum_insert (by simp [hxy, hxt]), sum_insert (by simp [hyt]), sum_singleton]
  omega

theorem row_le_three_of_nine_contacts {arms j : Finset V}
    (hfour : arms.card = 4) (hquad : QuadOn G j) (hd : Disjoint arms j)
    (hnine : 9 ≤ contacts G arms j)
    (hno : ∀ x ∈ arms, ∀ y ∈ arms, ∀ z ∈ arms, x ≠ y → x ≠ z → y ≠ z →
      ¬CommonReplacement G x y z j) :
    ∀ z ∈ arms, degreeIn G z j ≤ 3 := by
  intro z hz
  have hbound := degreeIn_le_card G z j
  have hcard := hquad.card
  by_contra hlarge
  have hrow : degreeIn G z j = 4 := by omega
  exact no_universal_of_nine_contacts hfour hcard hnine hno hz
    (fun _ hu ↦ hquad.replace_of_degree_four (fun hh ↦ disjoint_left.mp hd hz hh) hrow hu)

end Erdos577
