import ErdosProblems.Erdos577.PairReplacements

/-! A first diagonal makes the complement of either odd cycle vertex a triangle. -/

namespace Erdos577.Quadrilateral

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma odd_erase_clique (q : Quadrilateral G) (hdiag : G.Adj (q 0) (q 2))
    (i : Fin 4) (hi : i = 1 ∨ i = 3) : G.IsNClique 3 (q.support.erase (q i)) := by
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  rcases hi with rfl | rfl
  · have he : q.support.erase (q 1) = {q 0, q 2, q 3} := by
      rw [support, ← image_erase hinj, show univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
      simp only [image_insert, image_singleton]
    rw [he]
    exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hdiag, (q.adjacent 3).symm, q.adjacent 2⟩
  · have he : q.support.erase (q 3) = {q 0, q 1, q 2} := by
      rw [support, ← image_erase hinj, show univ.erase (3 : Fin 4) = {0, 1, 2} by decide]
      simp only [image_insert, image_singleton]
    rw [he]
    exact SimpleGraph.is3Clique_triple_iff.mpr ⟨q.adjacent 0, hdiag, q.adjacent 1⟩

variable [DecidableRel G.Adj]

lemma replace_odd_of_two (q : Quadrilateral G) (hdiag : G.Adj (q 0) (q 2))
    (i : Fin 4) (hi : i = 1 ∨ i = 3) (z : V) (hz : z ∉ q.support)
    (hrow : 2 ≤ degreeIn G z (q.support.erase (q i))) :
    QuadOn G (insert z (q.support.erase (q i))) :=
  QuadOn.of_triangle (q.odd_erase_clique hdiag i hi) (fun hh ↦ hz (mem_erase.mp hh).2) hrow

lemma replace_odd_of_three (q : Quadrilateral G) (hdiag : G.Adj (q 0) (q 2))
    (i : Fin 4) (hi : i = 1 ∨ i = 3) (z : V) (hz : z ∉ q.support)
    (hrow : 3 ≤ degreeIn G z q.support) :
    QuadOn G (insert z (q.support.erase (q i))) := by
  apply q.replace_odd_of_two hdiag i hi z hz
  have he := degreeIn_erase_add G z (q i) ((q.mem_support _).mpr ⟨i, rfl⟩)
  split_ifs at he <;> omega

end Erdos577.Quadrilateral
