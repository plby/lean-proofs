import ErdosProblems.Erdos577.Basic

/-! Relabel genuine four-cycles without changing their vertex sets. -/

namespace Erdos577.Quadrilateral

open Finset

variable {V : Type*} {G : SimpleGraph V}

def relabel (q : Quadrilateral G) (e : Fin 4 ↪ Fin 4)
    (he : ∀ i, (SimpleGraph.cycleGraph 4).Adj (e i) (e (i + 1))) : Quadrilateral G :=
  ofEdges (e.trans q.toEmbedding) (fun i ↦ q.toHom.map_rel' (he i))

@[simp] lemma relabel_apply (q : Quadrilateral G) (e : Fin 4 ↪ Fin 4)
    (he : ∀ i, (SimpleGraph.cycleGraph 4).Adj (e i) (e (i + 1))) (i : Fin 4) :
    q.relabel e he i = q (e i) := rfl

lemma relabel_support [DecidableEq V] (q : Quadrilateral G) (e : Fin 4 ↪ Fin 4)
    (he : ∀ i, (SimpleGraph.cycleGraph 4).Adj (e i) (e (i + 1))) :
    (q.relabel e he).support = q.support := by
  apply eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨i, rfl⟩ := (mem_support _ _).mp hv
    exact (mem_support _ _).mpr ⟨e i, rfl⟩
  · simp only [card_support, le_refl]

def rotate (q : Quadrilateral G) (r : Fin 4) : Quadrilateral G :=
  q.relabel (addRightEmbedding r) (by
    intro i
    apply (cycleGraph_four_adj_iff _ _).mpr
    right
    exact add_right_comm i 1 r)

@[simp] lemma rotate_apply (q : Quadrilateral G) (r i : Fin 4) :
    q.rotate r i = q (i + r) := rfl

lemma rotate_support [DecidableEq V] (q : Quadrilateral G) (r : Fin 4) :
    (q.rotate r).support = q.support := q.relabel_support _ _

def reverse (q : Quadrilateral G) : Quadrilateral G :=
  q.relabel ⟨fun i ↦ -i, neg_injective⟩ (by
    intro i
    apply (cycleGraph_four_adj_iff _ _).mpr
    left
    change -i = -(i + 1) + 1
    abel)

@[simp] lemma reverse_apply (q : Quadrilateral G) (i : Fin 4) : q.reverse i = q (-i) := rfl

lemma reverse_support [DecidableEq V] (q : Quadrilateral G) : q.reverse.support = q.support :=
  q.relabel_support _ _

end Erdos577.Quadrilateral
