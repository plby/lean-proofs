import ErdosProblems.Erdos577.FirstPawFourColumns
import ErdosProblems.Erdos577.PawEncoding
import ErdosProblems.Erdos577.LocalPathPartition

/-! Ten positive cores cover pattern (4): at most one of its ten allowed contacts is missing. -/

namespace Erdos577.FirstPawFour

open Finset

def row : Fin 10 → Fin 4 := ![0, 0, 1, 1, 1, 1, 2, 2, 3, 3]

def column : Fin 10 → Fin 4 := ![0, 2, 0, 1, 2, 3, 0, 2, 0, 2]

def contactPair (i : Fin 10) : Fin 8 × Fin 8 :=
  (Fin.castAdd 4 (row i), Fin.natAdd 4 (column i))

def basePairs : Finset (Fin 8 × Fin 8) :=
  {(0, 1), (1, 2), (1, 3), (2, 3), (4, 5), (5, 6), (6, 7), (4, 7), (4, 6)}

def pairs (miss : Fin 10) : Finset (Fin 8 × Fin 8) :=
  basePairs ∪ (univ.erase miss).image contactPair

def graph (miss : Fin 10) : SimpleGraph (Fin 8) :=
  SimpleGraph.fromRel fun i j ↦ (i, j) ∈ pairs miss

instance (miss : Fin 10) : DecidableRel (graph miss).Adj := inferInstanceAs (DecidableRel
  (SimpleGraph.fromRel (fun i j : Fin 8 ↦ (i, j) ∈ pairs miss)).Adj)

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma low_absent (p : Paw G) (q : Quadrilateral G) (h : PawBlock.Pattern4 p q)
    (i j : Fin 4) (hi : i ≠ 1) (hj : j = 1 ∨ j = 3) : ¬G.Adj (p.vertices i) (q j) := by
  intro he
  have hjn : j ≠ 0 ∧ j ≠ 2 := by rcases hj with rfl | rfl <;> decide
  have hh : j = 0 ∨ j = 2 := by
    fin_cases i
    · exact h.2.2.2 j (Or.inl he)
    · exact False.elim (hi rfl)
    · exact h.2.2.2 j (Or.inr (Or.inl he))
    · exact h.2.2.2 j (Or.inr (Or.inr he))
  exact hh.elim hjn.1 hjn.2

lemma allowed_contact_count (p : Paw G) (q : Quadrilateral G) (h : PawBlock.Pattern4 p q) :
    (univ.filter (fun i : Fin 10 ↦ G.Adj (p.vertices (row i)) (q (column i)))).card =
      contacts G p.support q.support := by
  rw [card_eq_sum_ones, sum_filter, Paw.support, tupleSupport,
    contacts_image_left G univ p.vertices p.vertices.injective]
  simp_rw [Quadrilateral.support, degreeIn_image G _ univ q q.injective]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  have hn01 := low_absent p q h 0 1 (by decide) (Or.inl rfl)
  have hn03 := low_absent p q h 0 3 (by decide) (Or.inr rfl)
  have hn21 := low_absent p q h 2 1 (by decide) (Or.inl rfl)
  have hn23 := low_absent p q h 2 3 (by decide) (Or.inr rfl)
  have hn31 := low_absent p q h 3 1 (by decide) (Or.inl rfl)
  have hn33 := low_absent p q h 3 3 (by decide) (Or.inr rfl)
  change
    (if G.Adj (p.vertices 0) (q 0) then 1 else 0) +
      ((if G.Adj (p.vertices 0) (q 2) then 1 else 0) +
      ((if G.Adj (p.vertices 1) (q 0) then 1 else 0) +
      ((if G.Adj (p.vertices 1) (q 1) then 1 else 0) +
      ((if G.Adj (p.vertices 1) (q 2) then 1 else 0) +
      ((if G.Adj (p.vertices 1) (q 3) then 1 else 0) +
      ((if G.Adj (p.vertices 2) (q 0) then 1 else 0) +
      ((if G.Adj (p.vertices 2) (q 2) then 1 else 0) +
      ((if G.Adj (p.vertices 3) (q 0) then 1 else 0) +
      ((if G.Adj (p.vertices 3) (q 2) then 1 else 0) + 0))))))))) =
    ((if G.Adj (p.vertices 0) (q 0) then 1 else 0) +
      ((if G.Adj (p.vertices 0) (q 1) then 1 else 0) +
      ((if G.Adj (p.vertices 0) (q 2) then 1 else 0) +
      ((if G.Adj (p.vertices 0) (q 3) then 1 else 0) + 0)))) +
    (((if G.Adj (p.vertices 1) (q 0) then 1 else 0) +
      ((if G.Adj (p.vertices 1) (q 1) then 1 else 0) +
      ((if G.Adj (p.vertices 1) (q 2) then 1 else 0) +
      ((if G.Adj (p.vertices 1) (q 3) then 1 else 0) + 0)))) +
    (((if G.Adj (p.vertices 2) (q 0) then 1 else 0) +
      ((if G.Adj (p.vertices 2) (q 1) then 1 else 0) +
      ((if G.Adj (p.vertices 2) (q 2) then 1 else 0) +
      ((if G.Adj (p.vertices 2) (q 3) then 1 else 0) + 0)))) +
    (((if G.Adj (p.vertices 3) (q 0) then 1 else 0) +
      ((if G.Adj (p.vertices 3) (q 1) then 1 else 0) +
      ((if G.Adj (p.vertices 3) (q 2) then 1 else 0) +
      ((if G.Adj (p.vertices 3) (q 3) then 1 else 0) + 0)))) + 0)))
  simp only [if_neg hn01, if_neg hn03, if_neg hn21, if_neg hn23, if_neg hn31, if_neg hn33]
  omega

lemma exists_lower_rows (p : Paw G) (q : Quadrilateral G) (h : PawBlock.Pattern4 p q)
    (hheavy : 9 ≤ contacts G p.support q.support) :
    ∃ miss : Fin 10, ∀ i : Fin 10, i ≠ miss → G.Adj (p.vertices (row i)) (q (column i)) := by
  let P := fun i : Fin 10 ↦ G.Adj (p.vertices (row i)) (q (column i))
  have hcount : 9 ≤ (univ.filter P).card := by rw [allowed_contact_count p q h]; exact hheavy
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin 10))) P
  have hcard : (univ : Finset (Fin 10)).card = 10 := by decide
  have hsmall : (univ.filter fun i ↦ ¬P i).card ≤ 1 := by omega
  obtain ⟨miss, hmiss⟩ := card_le_one_iff_subset_singleton.mp hsmall
  refine ⟨miss, ?_⟩
  intro i hi
  by_contra hnot
  exact hi (mem_singleton.mp (hmiss (mem_filter.mpr ⟨mem_univ i, hnot⟩)))

def copy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hdiag : G.Adj (q 0) (q 2)) (miss : Fin 10)
    (hrows : ∀ i : Fin 10, i ≠ miss → G.Adj (p.vertices (row i)) (q (column i))) :
    (graph miss).Copy G := by
  let e := PawEncoding.labeling p q hd
  have hpos (a : Fin 8 × Fin 8) (ha : a ∈ pairs miss) : G.Adj (e a.1) (e a.2) := by
    rcases mem_union.mp ha with ha | ha
    · simp only [basePairs, mem_insert, mem_singleton] at ha
      rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha <;> cases ha
      · exact p.pendant
      · exact p.edge12
      · exact p.edge13
      · exact p.edge23
      · exact q.adjacent 0
      · exact q.adjacent 1
      · exact q.adjacent 2
      · exact (q.adjacent 3).symm
      · exact hdiag
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
      change G.Adj (PawEncoding.labeling p q hd (Fin.castAdd 4 (row i)))
        (PawEncoding.labeling p q hd (Fin.natAdd 4 (column i)))
      rw [PawEncoding.labeling_left, PawEncoding.labeling_right]
      exact hrows i (mem_erase.mp hi).1
  refine ⟨⟨e, ?_⟩, e.injective⟩
  intro i j hij
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hij with ⟨_, hij | hji⟩
  · exact hpos (i, j) hij
  · exact (hpos (j, i) hji).symm

omit [DecidableRel G.Adj] in
lemma copy_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hdiag : G.Adj (q 0) (q 2)) (miss : Fin 10)
    (hrows : ∀ i : Fin 10, i ≠ miss → G.Adj (p.vertices (row i)) (q (column i))) :
    univ.image (copy p q hd hdiag miss hrows) = p.support ∪ q.support :=
  PawEncoding.labeling_image p q hd

end Erdos577.FirstPawFour
