import ErdosProblems.Erdos577.WeightedPawPatterns
import ErdosProblems.Erdos577.PawPartialCopy
import ErdosProblems.Erdos577.PawIndexedFactors

/-! The compulsory eight-vertex core of pattern (14), with its two center noncontacts. -/

namespace Erdos577.WeightedFourteen

open Finset

def graph : SimpleGraph (Fin 8) := PawModel.graph 0 23813

def upperGraph : SimpleGraph (Fin 8) := PawModel.graph 1 23893

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (PawModel.graph 0 23813).Adj)

instance : DecidableRel upperGraph.Adj :=
  inferInstanceAs (DecidableRel (PawModel.graph 1 23893).Adj)

def weightSet (second : Bool) : Finset (Fin 8) :=
  if second then {0, 5, 7, 3} else {0, 5, 1, 2}

lemma weightSet_card (second : Bool) : (weightSet second).card = 4 := by
  cases second <;> decide +kernel

lemma inside_weight : contacts upperGraph (weightSet false) univ +
    contacts upperGraph (weightSet true) univ = 27 := by decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
lemma base_rows (p : Paw G) (q : Quadrilateral G) (h : WeightedPawBlock.Pattern14 p q)
    (i j : Fin 4) (hb : (23813 : ℕ).testBit (4 * i.val + j.val) = true) :
    G.Adj (p.vertices i) (q j) := by
  have hbits : ∀ i j : Fin 4, (23813 : ℕ).testBit (4 * i.val + j.val) =
      ((![5, 0, 13, 5] : Fin 4 → ℕ) i).testBit j.val := by decide +kernel
  rw [hbits] at hb
  fin_cases i
  · exact (h.2.1 j).mpr hb
  · change (0 : ℕ).testBit j.val = true at hb
    simp at hb
  · exact (h.2.2.1 j).mpr hb
  · exact (h.2.2.2 j).mpr hb

lemma center_factor (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern14 p q)
    (he : G.Adj p.center (q 1) ∨ G.Adj p.center (q 3)) :
    LocalFactor G (p.support ∪ q.support) := by
  let e := PawEncoding.labeling p q hd
  have hne (i j : Fin 8) (hij : i ≠ j) : e i ≠ e j := fun hh ↦ hij (e.injective hh)
  rcases he with he | he
  · apply p.factor_of_index_partition q hd {0, 1, 5, 4} {2, 3, 6, 7} (by decide +kernel)
    · simp only [image_insert, image_singleton]
      exact QuadOn.of_vertices (hne 0 5 (by decide)) (hne 1 4 (by decide))
        p.pendant he (q.adjacent 0).symm ((h.2.1 0).mpr (by decide)).symm
    · simp only [image_insert, image_singleton]
      exact QuadOn.of_vertices (hne 2 6 (by decide)) (hne 3 7 (by decide))
        p.edge23 ((h.2.2.2 2).mpr (by decide)) (q.adjacent 2)
        ((h.2.2.1 3).mpr (by decide)).symm
  · apply p.factor_of_index_partition q hd {0, 4, 5, 6} {1, 3, 2, 7} (by decide +kernel)
    · simp only [image_insert, image_singleton]
      exact QuadOn.of_vertices (hne 0 5 (by decide)) (hne 4 6 (by decide))
        ((h.2.1 0).mpr (by decide)) (q.adjacent 0) (q.adjacent 1)
        ((h.2.1 2).mpr (by decide)).symm
    · simp only [image_insert, image_singleton]
      exact QuadOn.of_vertices (hne 1 2 (by decide)) (hne 3 7 (by decide))
        p.edge13 p.edge23.symm ((h.2.2.1 3).mpr (by decide)) he.symm

lemma center_absent (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern14 p q) (hn : ¬LocalFactor G (p.support ∪ q.support)) :
    ¬G.Adj p.center (q 1) ∧ ¬G.Adj p.center (q 3) :=
  ⟨fun he ↦ hn (center_factor p q hd h (Or.inl he)),
    fun he ↦ hn (center_factor p q hd h (Or.inr he))⟩

variable [DecidableRel G.Adj]

def coreCopy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern14 p q) : graph.Copy G :=
  PawEncoding.copyOfRows p q hd 23813 (base_rows p q h)

lemma coreCopy_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern14 p q) :
    univ.image (coreCopy p q hd h) = p.support ∪ q.support := PawEncoding.labeling_image p q hd

end Erdos577.WeightedFourteen
