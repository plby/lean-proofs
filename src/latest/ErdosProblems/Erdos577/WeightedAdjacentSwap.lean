import ErdosProblems.Erdos577.WeightedAdjacentModel

/-! The explicit alternate paw and block used by the second common-replacement alternative. -/

namespace Erdos577.WeightedAdjacent

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def swappedPaw (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) : Paw G where
  vertices := (⟨![1, 0, 4, 5], by decide +kernel⟩ : Fin 4 ↪ Fin 8).trans
    (PawEncoding.labeling p q hd)
  pendant := by
    change G.Adj (p.vertices 1) (p.vertices 0)
    exact p.pendant.symm
  edge12 := by
    change G.Adj (p.vertices 0) (q 0)
    exact (h.2.1 0).mpr (by decide)
  edge13 := by
    change G.Adj (p.vertices 0) (q 1)
    exact (h.2.1 1).mpr (by decide)
  edge23 := by
    change G.Adj (q 0) (q 1)
    exact q.adjacent 0

lemma swappedPaw_support_image (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) :
    (swappedPaw twenty p q hd h).support =
      ({1, 0, 4, 5} : Finset (Fin 8)).image (PawEncoding.labeling p q hd) := by
  have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [Paw.support, tupleSupport, hu]
  simp only [image_insert, image_singleton]
  rfl

def secondQuad (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) : Quadrilateral G :=
  Quadrilateral.ofEdges
    ((⟨![2, 3, 6, 7], by decide +kernel⟩ : Fin 4 ↪ Fin 8).trans
      (PawEncoding.labeling p q hd)) (by
    intro i
    fin_cases i
    · exact p.edge23
    · exact (h.2.2.2 2).mpr (by cases twenty <;> decide)
    · exact q.adjacent 2
    · exact ((h.2.2.1 3).mpr (by cases twenty <;> decide)).symm)

lemma secondQuad_support_image (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) :
    (secondQuad twenty p q hd h).support =
      ({2, 3, 6, 7} : Finset (Fin 8)).image (PawEncoding.labeling p q hd) := by
  have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [Quadrilateral.support, hu]
  simp only [image_insert, image_singleton]
  rfl

def swappedLocalChain (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) :
    LocalChain G (p.support ∪ q.support) where
  terminal := (swappedPaw twenty p q hd h).leaf
  triangle := (swappedPaw twenty p q hd h).triangle
  block := (secondQuad twenty p q hd h).support
  triangle_clique := (swappedPaw twenty p q hd h).triangle_clique
  terminal_not_mem := (swappedPaw twenty p q hd h).leaf_not_mem_triangle
  quad := ⟨secondQuad twenty p q hd h, rfl⟩
  disjoint := by
    rw [← (swappedPaw twenty p q hd h).support_eq,
      swappedPaw_support_image, secondQuad_support_image]
    have hinj : Function.Injective (PawEncoding.labeling p q hd : Fin 8 → V) :=
      (PawEncoding.labeling p q hd).injective
    rw [disjoint_image hinj]
    decide +kernel
  cover := by
    rw [← (swappedPaw twenty p q hd h).support_eq,
      swappedPaw_support_image, secondQuad_support_image, ← image_union]
    have he : ({1, 0, 4, 5} ∪ {2, 3, 6, 7} : Finset (Fin 8)) = univ := by decide
    rw [he, PawEncoding.labeling_image]

lemma swappedLocalChain_remainder (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q) :
    (swappedLocalChain twenty p q hd h).remainder = (swappedPaw twenty p q hd h).support :=
  (swappedPaw twenty p q hd h).support_eq.symm

end Erdos577.WeightedAdjacent
