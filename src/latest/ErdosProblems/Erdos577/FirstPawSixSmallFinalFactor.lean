import ErdosProblems.Erdos577.FirstPawSixSmallModel
import ErdosProblems.Erdos577.PartitionImages
import ErdosProblems.Erdos577.QuadSets

/-! Three exact four-cycles close the common-triple argument in cases (22)/(23). -/

namespace Erdos577.FirstPawSix.SmallCases

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma final_partition (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (variant : Bool) (hrows : PawBlock.ExactRows p q (caseRows (caseTag variant)))
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support)
    (htriple : ∀ j : Fin 4, j ≠ 0 → G.Adj p.leaf (v j) ∧ G.Adj (q 1) (v j))
    (hz : G.Adj (p.vertices 3) (v 2)) :
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
  let t : Finset (Fin 12) := {0, 1, 3, 10}
  let u : Finset (Fin 12) := {2, 4, 7, 6}
  have hs : QuadOn G (s.image e) := by
    simp only [s, image_insert, image_singleton]
    exact QuadOn.of_vertices (hne 5 8 (by decide)) (hne 9 11 (by decide))
      (htriple 1 (by decide)).2 (v.adjacent 0).symm (v.adjacent 3).symm
      (htriple 3 (by decide)).2.symm
  have ht : QuadOn G (t.image e) := by
    simp only [t, image_insert, image_singleton]
    exact QuadOn.of_vertices (hne 0 3 (by decide)) (hne 1 10 (by decide))
      p.pendant p.edge13 hz (htriple 2 (by decide)).1.symm
  have hu : QuadOn G (u.image e) := by
    simp only [u, image_insert, image_singleton]
    exact QuadOn.of_vertices (hne 2 7 (by decide)) (hne 4 6 (by decide))
      ((hrows 2 0).mpr (by cases variant <;> decide)) (q.adjacent 3).symm (q.adjacent 2).symm
      ((hrows 2 2).mpr (by cases variant <;> decide)).symm
  let parts := BlockPartition.threeImages e s t u univ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hs ht hu
  exact ⟨himage ▸ parts⟩

end Erdos577.FirstPawSix.SmallCases
