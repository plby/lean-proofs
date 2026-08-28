import ErdosProblems.Erdos577.PartitionImages

/-! Four explicit cycle blocks with a finite, disjoint image cover. -/

namespace Erdos577.BlockPartition

open Finset

variable {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph V}

def fourImages (e : W ↪ V) (a b c d s : Finset W)
    (hab : Disjoint a b) (hc : Disjoint (a ∪ b) c) (hd : Disjoint ((a ∪ b) ∪ c) d)
    (hcover : ((a ∪ b) ∪ c) ∪ d = s)
    (qa : QuadOn G (a.image e)) (qb : QuadOn G (b.image e))
    (qc : QuadOn G (c.image e)) (qd : QuadOn G (d.image e)) : BlockPartition G (s.image e) := by
  let p := threeImages e a b c ((a ∪ b) ∪ c) hab hc rfl qa qb qc
  have hdis : Disjoint (((a ∪ b) ∪ c).image e) (d.image e) :=
    (disjoint_image e.injective).mpr hd
  have he : ((a ∪ b) ∪ c).image e ∪ d.image e = s.image e := by
    rw [← image_union, hcover]
  exact he ▸ p.union (single qd) hdis

end Erdos577.BlockPartition
