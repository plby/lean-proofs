import ErdosProblems.Erdos577.PawPartialCopy

/-! Preserve specified old diagonals as well as a specified subset of paw cross edges. -/

namespace Erdos577

open Finset

lemma PawModel.graph_diagonal_mono (small large : Fin 4) (m : ℕ)
    (h : large.val &&& small.val = small.val) :
    PawModel.graph small m ≤ PawModel.graph large m := by
  have hfinite : ∀ small large : Fin 4, large.val &&& small.val = small.val →
      Unattached.basePairs small ⊆ Unattached.basePairs large := by decide +kernel
  have hb := hfinite small large h
  have hr {a b : Fin 8} (h : Unattached.relation small m a b) :
      Unattached.relation large m a b := by
    rcases h with h | h
    · exact Or.inl (hb h)
    · exact Or.inr h
  apply sup_le_sup _ le_rfl
  intro a b hab
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨hne, h | h⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl (hr h)⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inr (hr h)⟩

namespace PawEncoding

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def copyWithDiagonalOfRows (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (d : Fin 4)
    (hdiag : (Unattached.diagonal q).val &&& d.val = d.val) (m : Fin 65536)
    (hrows : ∀ i j : Fin 4, m.val.testBit (4 * i.val + j.val) = true →
      G.Adj (p.vertices i) (q j)) : (PawModel.graph d m.val).Copy G :=
  (modelCopy p q hd).comp (SimpleGraph.Copy.ofLE _ _
    ((PawModel.graph_diagonal_mono d (Unattached.diagonal q) m.val hdiag).trans
      (PawModel.graph_mono _ (submask_of_rows p q m hrows))))

lemma copyWithDiagonalOfRows_apply (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (d : Fin 4)
    (hdiag : (Unattached.diagonal q).val &&& d.val = d.val) (m : Fin 65536)
    (hrows : ∀ i j : Fin 4, m.val.testBit (4 * i.val + j.val) = true →
      G.Adj (p.vertices i) (q j)) (i : Fin 8) :
    copyWithDiagonalOfRows p q hd d hdiag m hrows i = labeling p q hd i := rfl

lemma copyWithDiagonalOfRows_image (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (d : Fin 4)
    (hdiag : (Unattached.diagonal q).val &&& d.val = d.val) (m : Fin 65536)
    (hrows : ∀ i j : Fin 4, m.val.testBit (4 * i.val + j.val) = true →
      G.Adj (p.vertices i) (q j)) :
    univ.image (copyWithDiagonalOfRows p q hd d hdiag m hrows) = p.support ∪ q.support :=
  labeling_image p q hd

omit [DecidableEq V] in
lemma first_diagonal_submask (q : Quadrilateral G) (h : G.Adj (q 0) (q 2)) :
    (Unattached.diagonal q).val &&& 1 = 1 := by
  have hfinite : ∀ d : Fin 4, d.val.testBit 0 = true → d.val &&& 1 = 1 := by decide +kernel
  exact hfinite (Unattached.diagonal q) ((Unattached.diagonal_first q).mpr h)

end PawEncoding

end Erdos577
