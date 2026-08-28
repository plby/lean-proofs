import ErdosProblems.Erdos577.FirstPawOutside
import ErdosProblems.Erdos577.QuadSets

/-! Explicit replacements from two prescribed block contacts. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

namespace Quadrilateral

lemma replace_using_path (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (u a mid b : Fin 4) (hab : a ≠ b)
    (hcover : ({a, mid, b} : Finset (Fin 4)) = univ.erase u)
    (hza : G.Adj z (q a)) (ham : G.Adj (q a) (q mid))
    (hmb : G.Adj (q mid) (q b)) (hzb : G.Adj z (q b)) :
    QuadOn G (insert z (q.support.erase (q u))) := by
  have himage := congrArg (fun s : Finset (Fin 4) ↦ s.image q) hcover
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  have hs : q.support.erase (q u) = {q a, q mid, q b} := by
    simpa only [image_insert, image_singleton, image_erase hinj,
      Quadrilateral.support] using himage.symm
  rw [hs]
  exact QuadOn.of_vertices (fun h ↦ hz ((q.mem_support z).mpr ⟨mid, h.symm⟩))
    (fun h ↦ hab (q.injective h)) hza ham hmb hzb.symm

lemma clique_of_diagonals (q : Quadrilateral G)
    (hd0 : G.Adj (q 0) (q 2)) (hd1 : G.Adj (q 1) (q 3)) : G.IsNClique 4 q.support := by
  refine ⟨?_, q.card_support⟩
  intro a ha b hb hab
  obtain ⟨i, rfl⟩ := (q.mem_support a).mp ha
  obtain ⟨j, rfl⟩ := (q.mem_support b).mp hb
  have hij : i ≠ j := fun he ↦ hab (congrArg q he)
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact q.adjacent 0
  · exact hd0
  · exact (q.adjacent 3).symm
  · exact (q.adjacent 0).symm
  · exact False.elim (hij rfl)
  · exact q.adjacent 1
  · exact hd1
  · exact hd0.symm
  · exact (q.adjacent 1).symm
  · exact False.elim (hij rfl)
  · exact q.adjacent 2
  · exact q.adjacent 3
  · exact hd1.symm
  · exact (q.adjacent 2).symm
  · exact False.elim (hij rfl)

end Quadrilateral

end Erdos577
