import ErdosProblems.Erdos577.FirstPawFourUpper
import ErdosProblems.Erdos577.PawCopy

/-! Ten positive complete-block cores certify the exchange of the two noncentral pairs. -/

namespace Erdos577.FirstPawFour.CompleteModel

open Finset

def graph (miss : Fin 10) : SimpleGraph (Fin 8) :=
  SimpleGraph.fromRel fun i j ↦ (i, j) ∈ pairs miss ∪ {(5, 7)}

instance (miss : Fin 10) : DecidableRel (graph miss).Adj := inferInstanceAs (DecidableRel
  (SimpleGraph.fromRel (fun i j : Fin 8 ↦ (i, j) ∈ pairs miss ∪ {(5, 7)})).Adj)

def useSecond (miss : Fin 10) : Bool := decide (miss = 0 ∨ miss = 4 ∨ miss = 7 ∨ miss = 9)

def firstHigh (miss : Fin 10) : Fin 8 := if useSecond miss then 6 else 4

def otherHigh (miss : Fin 10) : Fin 8 := if useSecond miss then 4 else 6

def paw (miss : Fin 10) : Paw (graph miss) where
  vertices := ⟨![0, firstHigh miss, 5, 7], by fin_cases miss <;> decide +kernel⟩
  pendant := by fin_cases miss <;> decide +kernel
  edge12 := by fin_cases miss <;> decide +kernel
  edge13 := by fin_cases miss <;> decide +kernel
  edge23 := by fin_cases miss <;> decide +kernel

def quad (miss : Fin 10) : Quadrilateral (graph miss) :=
  Quadrilateral.ofEdges
    ⟨![1, 2, otherHigh miss, 3], by fin_cases miss <;> decide +kernel⟩
    (by fin_cases miss <;> decide +kernel)

def chain (miss : Fin 10) : LocalChain (graph miss) univ where
  terminal := (paw miss).leaf
  triangle := (paw miss).triangle
  block := (quad miss).support
  triangle_clique := (paw miss).triangle_clique
  terminal_not_mem := (paw miss).leaf_not_mem_triangle
  quad := ⟨quad miss, rfl⟩
  disjoint := by fin_cases miss <;> decide +kernel
  cover := by fin_cases miss <;> decide +kernel

lemma block_score (miss : Fin 10) : edgeCount (graph miss) (chain miss).block = 6 := by
  fin_cases miss <;> decide +kernel

lemma diagonal (miss : Fin 10) : (graph miss).Adj (quad miss 0) (quad miss 2) := by
  fin_cases miss <;> decide +kernel

lemma center_three (miss : Fin 10) :
    3 ≤ degreeIn (graph miss) (paw miss).center (quad miss).support := by
  fin_cases miss <;> decide +kernel

lemma contacts_nine (miss : Fin 10) :
    9 ≤ contacts (graph miss) (paw miss).support (quad miss).support := by
  fin_cases miss <;> decide +kernel

lemma low_restriction (miss : Fin 10) (j : Fin 4)
    (h : upperGraph.Adj ((paw miss).vertices 0) (quad miss j) ∨
      upperGraph.Adj ((paw miss).vertices 2) (quad miss j) ∨
      upperGraph.Adj ((paw miss).vertices 3) (quad miss j)) : j = 0 ∨ j = 2 := by
  have hall : ∀ (miss : Fin 10) (j : Fin 4),
      (upperGraph.Adj ((paw miss).vertices 0) (quad miss j) ∨
        upperGraph.Adj ((paw miss).vertices 2) (quad miss j) ∨
        upperGraph.Adj ((paw miss).vertices 3) (quad miss j)) → j = 0 ∨ j = 2 := by
    decide +kernel
  exact hall miss j h

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def copy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hdiag : G.Adj (q 0) (q 2)) (hlow : G.Adj (q 1) (q 3)) (miss : Fin 10)
    (hrows : ∀ i : Fin 10, i ≠ miss → G.Adj (p.vertices (row i)) (q (column i))) :
    (graph miss).Copy G := by
  let e := PawEncoding.labeling p q hd
  let f := FirstPawFour.copy p q hd hdiag miss hrows
  have hpos (i j : Fin 8) (hne : i ≠ j) (hij : (i, j) ∈ pairs miss ∪ {(5, 7)}) :
      G.Adj (e i) (e j) := by
    rcases mem_union.mp hij with hij | hij
    · have he : (FirstPawFour.graph miss).Adj i j :=
        (SimpleGraph.fromRel_adj (fun a b : Fin 8 ↦ (a, b) ∈ pairs miss) i j).mpr
          ⟨hne, Or.inl hij⟩
      exact f.toHom.map_rel' he
    · have he : (i, j) = (5, 7) := mem_singleton.mp hij
      have hi : i = 5 := congrArg Prod.fst he
      have hj : j = 7 := congrArg Prod.snd he
      subst i
      subst j
      exact hlow
  refine ⟨⟨e, ?_⟩, e.injective⟩
  intro i j hij
  rcases (SimpleGraph.fromRel_adj (fun a b : Fin 8 ↦
    (a, b) ∈ pairs miss ∪ {(5, 7)}) i j).mp hij with ⟨hne, hij | hji⟩
  · exact hpos i j hne hij
  · exact (hpos j i hne.symm hji).symm

lemma copy_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hdiag : G.Adj (q 0) (q 2)) (hlow : G.Adj (q 1) (q 3)) (miss : Fin 10)
    (hrows : ∀ i : Fin 10, i ≠ miss → G.Adj (p.vertices (row i)) (q (column i))) :
    univ.image (copy p q hd hdiag hlow miss hrows) = p.support ∪ q.support :=
  PawEncoding.labeling_image p q hd

end Erdos577.FirstPawFour.CompleteModel
