import ErdosProblems.Erdos577.CycleLabels
import ErdosProblems.Erdos577.Counting

/-! A cycle rotation places the unique contact of an outside row at index zero. -/

namespace Erdos577.Quadrilateral

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma exists_one_contact_labels (q : Quadrilateral G) (z : V)
    (hrow : degreeIn G z q.support = 1) :
    ∃ v : Quadrilateral G, v.support = q.support ∧
      ∀ j : Fin 4, G.Adj z (v j) ↔ j = 0 := by
  obtain ⟨u, hu⟩ := card_eq_one.mp hrow
  have hm : u ∈ q.support.filter (G.Adj z) := by rw [hu]; exact mem_singleton_self _
  obtain ⟨huq, hzu⟩ := mem_filter.mp hm
  obtain ⟨i, hi⟩ := (q.mem_support u).mp huq
  let v := q.rotate i
  have hv : v.support = q.support := q.rotate_support i
  have hv0 : v 0 = u := by change q (0 + i) = u; simpa only [zero_add] using hi
  refine ⟨v, hv, ?_⟩
  intro j
  constructor
  · intro hj
    have hmj : v j ∈ q.support.filter (G.Adj z) :=
      mem_filter.mpr ⟨hv ▸ (v.mem_support _).mpr ⟨j, rfl⟩, hj⟩
    have he : v j = u := mem_singleton.mp (hu ▸ hmj)
    exact v.injective (he.trans hv0.symm)
  · rintro rfl
    rwa [hv0]

end Erdos577.Quadrilateral
