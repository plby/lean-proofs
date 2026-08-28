import ErdosProblems.Erdos577.FirstPawModel

/-! The eight source patterns (27)--(34) for the dense seven-vertex core.
Vertex 0 is outside the core; 1,2,3 are r,b,c and 4,5,6,7 label A.
The model keeps only required positive edges. -/

namespace Erdos577.JointCore

open Finset

def diagonal : Fin 8 → Fin 4 := ![1, 3, 1, 1, 3, 3, 3, 3]

def centerRow : Fin 8 → ℕ := ![15, 15, 14, 13, 13, 14, 15, 15]

def secondLower : Fin 8 → ℕ := ![1, 1, 5, 5, 9, 9, 7, 11]

def secondUpper : Fin 8 → ℕ := ![5, 15, 5, 5, 15, 15, 7, 15]

def thirdRow : Fin 8 → ℕ := ![15, 15, 15, 15, 15, 15, 7, 7]

def lowerRows (tag : Fin 8) : Fin 4 → ℕ :=
  ![0, centerRow tag, secondLower tag, thirdRow tag]

def upperRows (tag : Fin 8) : Fin 4 → ℕ :=
  ![0, centerRow tag, secondUpper tag, thirdRow tag]

def mask (tag : Fin 8) : ℕ :=
  16 * centerRow tag + 256 * secondLower tag + 4096 * thirdRow tag

def graph (tag : Fin 8) : SimpleGraph (Fin 8) :=
  Unattached.graph (diagonal tag) (mask tag)

instance (tag : Fin 8) : DecidableRel (graph tag).Adj :=
  inferInstanceAs (DecidableRel (Unattached.graph _ _).Adj)

def core : Finset (Fin 8) := {1, 2, 3, 4, 5, 6, 7}

def block : Finset (Fin 8) := {4, 5, 6, 7}

/-- Exact diagonal and row constraints after a cyclic relabeling.
The zero row is intentionally not constrained: it is not in the core. -/
def Pattern (tag : Fin 8) (d : Fin 4) (m : ℕ) (cols : Fin 4 ↪ Fin 4) : Prop :=
  (FirstPaw.quadAdj d cols 0 2 ↔ (diagonal tag).val.testBit 0 = true) ∧
  (FirstPaw.quadAdj d cols 1 3 ↔ (diagonal tag).val.testBit 1 = true) ∧
  ∀ i j : Fin 4, i ≠ 0 →
    ((lowerRows tag i).testBit j.val = true → FirstPaw.bit m false cols i j = true) ∧
    (FirstPaw.bit m false cols i j = true → (upperRows tag i).testBit j.val = true)

instance (tag : Fin 8) (d : Fin 4) (m : ℕ) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern tag d m cols) := inferInstanceAs (Decidable (_ ∧ _))

def Classified (d : Fin 4) (m : ℕ) : Prop :=
  ∃ tag : Fin 8, ∃ cols : Fin 4 ↪ Fin 4, FirstPaw.CycleOrder d cols ∧ Pattern tag d m cols

def outsideGraph (tag : Fin 8) (i j : Fin 7) : SimpleGraph (Fin 8) :=
  graph tag ⊔ SimpleGraph.edge 0 i.succ ⊔ SimpleGraph.edge 0 j.succ

instance (tag : Fin 8) (i j : Fin 7) : DecidableRel (outsideGraph tag i j).Adj := fun a b ↦
  decidable_of_iff
    (((graph tag).Adj a b ∨ ((a = 0 ∧ b = i.succ ∨ a = i.succ ∧ b = 0) ∧ a ≠ b)) ∨
      ((a = 0 ∧ b = j.succ ∨ a = j.succ ∧ b = 0) ∧ a ≠ b))
    (by simp only [outsideGraph, SimpleGraph.sup_adj, SimpleGraph.edge_adj])

lemma outsideGraph_comm (tag : Fin 8) (i j : Fin 7) :
    outsideGraph tag i j = outsideGraph tag j i := by
  simp only [outsideGraph, sup_right_comm]

lemma mask_bit (tag : Fin 8) (i j : Fin 4) :
    (mask tag).testBit (4 * i.val + j.val) = (lowerRows tag i).testBit j.val := by
  have hf : ∀ tag : Fin 8, ∀ i j : Fin 4,
      (mask tag).testBit (4 * i.val + j.val) = (lowerRows tag i).testBit j.val := by
    decide +kernel
  exact hf tag i j

end Erdos577.JointCore
