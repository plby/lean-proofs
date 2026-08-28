import ErdosProblems.Erdos577.PathLossModel
import ErdosProblems.Erdos577.UnattachedTransport

/-! Reuse the path encoding while retaining the original block's actual diagonals. -/

namespace Erdos577.PathLoss

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def modelCopy (p : FourPath G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    (graph (Unattached.diagonal q) (PathExchange.encoded p q).val).Copy G where
  toHom := {
    toFun := PathExchange.labeling p q hd
    map_rel' := by
      have hold {a b : Fin 8} (hne : a ≠ b)
          (h : PathExchange.relation (PathExchange.encoded p q).val a b) :
          G.Adj (PathExchange.labeling p q hd a) (PathExchange.labeling p q hd b) :=
        (PathExchange.modelCopy p q hd).toHom.map_rel'
          ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl h⟩)
      have hr {a b : Fin 8} (hne : a ≠ b)
          (h : relation (Unattached.diagonal q) (PathExchange.encoded p q).val a b) :
          G.Adj (PathExchange.labeling p q hd a) (PathExchange.labeling p q hd b) := by
        rcases h with h | h
        · rw [basePairs] at h
          rcases mem_union.mp h with h | h1
          · rcases mem_union.mp h with h | h0
            · exact hold hne (Or.inl h)
            · split_ifs at h0 with h0'
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton.mp h0)
                exact (Unattached.diagonal_first q).mp h0'
              · simp at h0
          · split_ifs at h1 with h1'
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton.mp h1)
              exact (Unattached.diagonal_second q).mp h1'
            · simp at h1
        · exact hold hne (Or.inr h)
      intro a b hab
      rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨hne, h | h⟩
      · exact hr hne h
      · exact (hr hne.symm h).symm }
  injective' := (PathExchange.labeling p q hd).injective

lemma modelCopy_image (p : FourPath G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    univ.image (modelCopy p q hd) = p.support ∪ q.support := PathExchange.labeling_image p q hd

lemma Positive.transport (p : FourPath G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : Positive (Unattached.diagonal q) (PathExchange.encoded p q).val) :
    ScoredExchange G (p.support ∪ q.support) (min (edgeCount G q.support) 5) := by
  have hg := h.image (modelCopy p q hd)
  rw [modelCopy_image, Unattached.oldEdges_diagonal] at hg
  exact hg

end Erdos577.PathLoss
