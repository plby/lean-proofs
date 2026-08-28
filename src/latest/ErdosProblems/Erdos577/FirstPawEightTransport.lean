import ErdosProblems.Erdos577.FirstPawEightUpper
import ErdosProblems.Erdos577.LocalChainSupport

/-! Transport the exact pattern (8) involution, including the swapped paw and block. -/

namespace Erdos577.FirstPawEight

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def swappedPaw (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q) : Paw G :=
  (alternatePaw (Unattached.diagonal q)).image (coreCopy p q hd h)

def swappedQuad (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q) : Quadrilateral G :=
  (coreCopy p q hd h).comp (alternateQuad (Unattached.diagonal q))

def swappedLocal (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q) : LocalChain G (p.support ∪ q.support) :=
  ((alternateLocal (Unattached.diagonal q)).image (coreCopy p q hd h)).withSupport
    (coreCopy_image p q hd h)

lemma swapped_local_terminal (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q) :
    (swappedLocal p q hd h).terminal = p.vertices 3 := rfl

lemma swapped_score_lower (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q) : Unattached.oldEdges (Unattached.diagonal q) ≤
      edgeCount G (swappedLocal p q hd h).block := by
  have hh := (alternateLocal (Unattached.diagonal q)).image_edgeCount_le (coreCopy p q hd h)
  rw [alternate_score _ (diagonal_cases q h.1)] at hh
  exact hh

lemma swapped_paw_support (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q) :
    (swappedPaw p q hd h).support = (swappedLocal p q hd h).remainder := by
  change ((alternatePaw (Unattached.diagonal q)).image (coreCopy p q hd h)).support = _
  rw [Paw.image_support, Paw.support_eq, image_insert]
  rfl

lemma swapped_quad_support (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q) :
    (swappedQuad p q hd h).support = (swappedLocal p q hd h).block :=
  Quadrilateral.support_copy_comp _ _

lemma swapped_disjoint (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q) : Disjoint (swappedPaw p q hd h).support
      (swappedQuad p q hd h).support := by
  rw [swapped_paw_support, swapped_quad_support]
  exact (swappedLocal p q hd h).disjoint

lemma swapped_leaf (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q) : (swappedPaw p q hd h).leaf = p.vertices 3 := rfl

lemma swapped_third (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q) : (swappedPaw p q hd h).vertices 3 = p.leaf := rfl

lemma swapped_labeling (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q) (i : Fin 8) :
    PawEncoding.labeling (swappedPaw p q hd h) (swappedQuad p q hd h)
      (swapped_disjoint p q hd h) i = PawEncoding.labeling p q hd (permutation i) := by
  fin_cases i <;> rfl

lemma swapped_pattern (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern8 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3)) :
    PawBlock.Pattern8 (swappedPaw p q hd h) (swappedQuad p q hd h) := by
  have hm := alternate_pattern (Unattached.diagonal q) (diagonal_cases q h.1)
  refine ⟨(coreCopy p q hd h).toHom.map_rel' hm.1, ?_⟩
  intro i j
  exact (adj_iff p q hd h hleaf ((alternatePaw (Unattached.diagonal q)).vertices i)
    (alternateQuad (Unattached.diagonal q) j)).trans (hm.2 i j)

end Erdos577.FirstPawEight
