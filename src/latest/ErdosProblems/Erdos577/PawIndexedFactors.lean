import ErdosProblems.Erdos577.PawEncoding
import ErdosProblems.Erdos577.LocalFactors

/-! Transfer any explicit two-part index partition to the original paw and block. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma Paw.factor_of_index_partition (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (a b : Finset (Fin 8))
    (hcomp : univ \ a = b)
    (ha : QuadOn G (a.image (PawEncoding.labeling p q hd)))
    (hb : QuadOn G (b.image (PawEncoding.labeling p q hd))) :
    LocalFactor G (p.support ∪ q.support) := by
  let e := PawEncoding.labeling p q hd
  have hinj : Function.Injective (e : Fin 8 → V) := e.injective
  have hall : univ.image e = p.support ∪ q.support := PawEncoding.labeling_image p q hd
  refine ⟨a.image e, ?_, ha, ?_⟩
  · rw [← hall]
    exact image_subset_image (subset_univ _)
  · rw [← hall, ← image_sdiff _ _ hinj, hcomp]
    exact hb

end Erdos577
