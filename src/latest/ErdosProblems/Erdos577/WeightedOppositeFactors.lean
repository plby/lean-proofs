import ErdosProblems.Erdos577.WeightedOppositeModel
import ErdosProblems.Erdos577.PawPartialCopy
import ErdosProblems.Erdos577.LocalPathPartition

/-! Ten explicit three-block factors used to exclude weighted patterns (16) and (17). -/

namespace Erdos577.WeightedOpposite

open Finset

namespace FactorTable

def terminal : Fin 10 → Fin 8 := ![0, 5, 1, 3, 7, 7, 7, 7, 7, 1]

def triple : Fin 10 → Fin 3 → Fin 8 :=
  ![![1, 2, 3], ![1, 2, 3], ![0, 6, 5], ![1, 2, 7], ![1, 2, 3],
    ![0, 1, 3], ![0, 6, 5], ![3, 4, 5], ![1, 3, 5], ![0, 4, 7]]

def block : Fin 10 → Finset (Fin 8) :=
  ![{4, 5, 6, 7}, {0, 4, 7, 6}, {2, 3, 4, 7}, {0, 4, 5, 6}, {0, 4, 5, 6},
    {2, 4, 5, 6}, {1, 2, 4, 3}, {0, 1, 2, 6}, {0, 4, 2, 6}, {2, 3, 5, 6}]

def partition (tag : Fin 10) : LocalPathPartition (PawModel.graph 0 15621) univ where
  terminal := terminal tag
  triple := ⟨triple tag, by fin_cases tag <;> decide +kernel⟩
  edge01 := by fin_cases tag <;> decide +kernel
  edge12 := by fin_cases tag <;> decide +kernel
  terminal_not_mem := by fin_cases tag <;> decide +kernel
  block := block tag
  quad := QuadOn.of_degreeIn (by fin_cases tag <;> decide +kernel)
    (by fin_cases tag <;> decide +kernel)
  disjoint := by fin_cases tag <;> decide +kernel
  cover := by fin_cases tag <;> decide +kernel

end FactorTable

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma Rows.base_rows (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (h : Rows seventeen p q) (i j : Fin 4)
    (hb : (15621 : ℕ).testBit (4 * i.val + j.val) = true) :
    G.Adj (p.vertices i) (q j) := by
  have hbits : ∀ i j : Fin 4, (15621 : ℕ).testBit (4 * i.val + j.val) =
      ((![5, 0, 13, 3] : Fin 4 → ℕ) i).testBit j.val := by decide +kernel
  rw [hbits] at hb
  fin_cases i
  · exact (h.2.1 j).mpr hb
  · change (0 : ℕ).testBit j.val = true at hb
    simp at hb
  · exact (h.2.2.1 j).mpr hb
  · apply (h.2.2.2 j).mpr
    have hsub : ∀ s : Bool, ∀ j : Fin 4, (3 : ℕ).testBit j.val = true →
        (if s then 3 else 7 : ℕ).testBit j.val = true := by decide +kernel
    exact hsub seventeen j hb

def localPathPartition (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) (tag : Fin 10) :
    LocalPathPartition G (p.support ∪ q.support) :=
  ((FactorTable.partition tag).image
    (PawEncoding.copyOfRows p q hd 15621 (h.base_rows seventeen p q))).withSupport
      (PawEncoding.copyOfRows_image p q hd 15621 (h.base_rows seventeen p q))

variable [Fintype V]

omit [DecidableRel G.Adj] in
lemma no_common_replacement {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (seventeen : Bool) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (tag : Fin 10) :
    ¬CommonReplacement G (PawEncoding.labeling p q hd (FactorTable.triple tag 0))
      (PawEncoding.labeling p q hd (FactorTable.triple tag 2))
      (PawEncoding.labeling p q hd (FactorTable.terminal tag)) a := by
  classical
  let d := (localPathPartition seventeen p q hd h tag).withSupport
    (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq])
  exact c.no_common_replacement hcard hn hb ha hab d

end Erdos577.WeightedOpposite
