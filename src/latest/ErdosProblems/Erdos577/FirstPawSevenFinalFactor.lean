import ErdosProblems.Erdos577.FirstPawSevenModel
import ErdosProblems.Erdos577.PartitionImages
import ErdosProblems.Erdos577.QuadSets

/-! The common triple gives three explicit disjoint four-cycles on the twelve selected vertices. -/

namespace Erdos577.FirstPawSeven

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma final_partition (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern7 p q) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support)
    (hrows : ∀ j : Fin 4, j ≠ 0 → G.Adj (q 1) (v j) ∧ G.Adj (p.vertices 2) (v j))
    (hx : G.Adj p.leaf (v 2)) :
    Nonempty (BlockPartition G ((p.support ∪ q.support) ∪ v.support)) := by
  let e := joinTuples (PawEncoding.labeling p q hd) v.toEmbedding (by
    change Disjoint (univ.image (PawEncoding.labeling p q hd)) v.support
    rw [PawEncoding.labeling_image]
    exact hv)
  have hne (i j : Fin 12) (hij : i ≠ j) : e i ≠ e j := e.injective.ne hij
  have himage : univ.image e = (p.support ∪ q.support) ∪ v.support := by
    change tupleSupport (joinTuples _ _ _) = _
    rw [tupleSupport_joinTuples]
    change univ.image (PawEncoding.labeling p q hd) ∪ v.support = _
    rw [PawEncoding.labeling_image]
  let s : Finset (Fin 12) := {5, 9, 8, 11}
  let t : Finset (Fin 12) := {0, 1, 2, 10}
  let u : Finset (Fin 12) := {3, 4, 7, 6}
  have hs : QuadOn G (s.image e) := by
    simp only [s, image_insert, image_singleton]
    exact QuadOn.of_vertices (hne 5 8 (by decide)) (hne 9 11 (by decide))
      (hrows 1 (by decide)).1 (v.adjacent 0).symm (v.adjacent 3).symm
      (hrows 3 (by decide)).1.symm
  have ht : QuadOn G (t.image e) := by
    simp only [t, image_insert, image_singleton]
    exact QuadOn.of_vertices (hne 0 2 (by decide)) (hne 1 10 (by decide))
      p.pendant p.edge12 (hrows 2 (by decide)).2 hx.symm
  have hu : QuadOn G (u.image e) := by
    simp only [u, image_insert, image_singleton]
    exact QuadOn.of_vertices (hne 3 7 (by decide)) (hne 4 6 (by decide))
      ((h.2 3 0).mpr (by decide)) (q.adjacent 3).symm (q.adjacent 2).symm
      ((h.2 3 2).mpr (by decide)).symm
  let parts := BlockPartition.threeImages e s t u univ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hs ht hu
  exact ⟨himage ▸ parts⟩

end Erdos577.FirstPawSeven
