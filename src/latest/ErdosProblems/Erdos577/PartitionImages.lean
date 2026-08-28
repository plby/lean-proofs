import ErdosProblems.Erdos577.TriangleAssembly

/-! Assemble three cycle blocks with disjoint finite index sets and an exact image cover. -/

namespace Erdos577.BlockPartition

open Finset

variable {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph V}

def threeImages (e : W ↪ V) (a b c s : Finset W)
    (hab : Disjoint a b) (hc : Disjoint (a ∪ b) c) (hcover : (a ∪ b) ∪ c = s)
    (qa : QuadOn G (a.image e)) (qb : QuadOn G (b.image e)) (qc : QuadOn G (c.image e)) :
    BlockPartition G (s.image e) := by
  have hinj : Function.Injective (e : W → V) := e.injective
  have hab' : Disjoint (a.image e) (b.image e) := (disjoint_image hinj).mpr hab
  have hc' : Disjoint (a.image e ∪ b.image e) (c.image e) := by
    rw [← image_union, disjoint_image hinj]
    exact hc
  have he : (a.image e ∪ b.image e) ∪ c.image e = s.image e := by
    rw [← image_union, ← image_union, hcover]
  exact he ▸ ((single qa).union (single qb) hab').union (single qc) hc'

end Erdos577.BlockPartition
