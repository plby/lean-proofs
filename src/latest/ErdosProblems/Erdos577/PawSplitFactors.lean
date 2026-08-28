import ErdosProblems.Erdos577.PawEncoding
import ErdosProblems.Erdos577.QuadSets
import ErdosProblems.Erdos577.LocalFactors

/-! Two exact four-set factors used to exclude center contacts in the weighted cases. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma Paw.split_factor (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support)
    (hfirst : QuadOn G {p.vertices 0, p.vertices 1, q 0, q 1})
    (hsecond : QuadOn G {p.vertices 2, p.vertices 3, q 2, q 3}) :
    LocalFactor G (p.support ∪ q.support) := by
  let e := PawEncoding.labeling p q hd
  have hinj : Function.Injective (e : Fin 8 → V) := e.injective
  have hall : univ.image e = p.support ∪ q.support := PawEncoding.labeling_image p q hd
  have hfirstImage : ({0, 1, 4, 5} : Finset (Fin 8)).image e =
      {p.vertices 0, p.vertices 1, q 0, q 1} := by
    simp only [image_insert, image_singleton]
    rfl
  have hsecondImage : ({2, 3, 6, 7} : Finset (Fin 8)).image e =
      {p.vertices 2, p.vertices 3, q 2, q 3} := by
    simp only [image_insert, image_singleton]
    rfl
  refine ⟨({0, 1, 4, 5} : Finset (Fin 8)).image e, ?_, ?_, ?_⟩
  · rw [← hall]
    exact image_subset_image (subset_univ _)
  · rw [hfirstImage]
    exact hfirst
  · rw [← hall, ← image_sdiff _ _ hinj]
    have he : (univ : Finset (Fin 8)) \ {0, 1, 4, 5} = {2, 3, 6, 7} := by decide
    rw [he, hsecondImage]
    exact hsecond

lemma Paw.center_contact_factor (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support)
    (h00 : G.Adj p.leaf (q 0)) (h01 : G.Adj p.leaf (q 1))
    (h23 : G.Adj (p.vertices 2) (q 3)) (h32 : G.Adj (p.vertices 3) (q 2))
    (hcenter : G.Adj p.center (q 0) ∨ G.Adj p.center (q 1)) :
    LocalFactor G (p.support ∪ q.support) := by
  have hne (i j : Fin 4) : p.vertices i ≠ q j := by
    intro he
    exact disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩)
      ((q.mem_support _).mpr ⟨j, he.symm⟩)
  apply p.split_factor q hd
  · rcases hcenter with hcenter | hcenter
    · exact QuadOn.of_vertices (hne 0 0) (hne 1 1) p.pendant hcenter (q.adjacent 0) h01.symm
    · have hq := QuadOn.of_vertices (hne 0 1) (hne 1 0)
        p.pendant hcenter (q.adjacent 0).symm h00.symm
      have he : ({q 1, q 0} : Finset V) = {q 0, q 1} := pair_comm _ _
      change QuadOn G (insert (p.vertices 0) (insert (p.vertices 1) {q 1, q 0})) at hq
      rw [he] at hq
      exact hq
  · exact QuadOn.of_vertices (hne 2 2) (hne 3 3) p.edge23 h32 (q.adjacent 2) h23.symm

end Erdos577
