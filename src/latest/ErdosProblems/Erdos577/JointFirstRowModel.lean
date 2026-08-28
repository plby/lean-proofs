import ErdosProblems.Erdos577.RowReplacementTransport
import ErdosProblems.Erdos577.JointCoreRowReduction

/-! Four independent rows: common insertion, direct core obstruction, or strict crossing gain. -/

namespace Erdos577.JointFirstRows

open Finset

def bit (m : ℕ) (i j : Fin 4) : Bool := m.testBit (4 * i.val + j.val)

def otherNeighbors (m : ℕ) (z u : Fin 4) : Finset (Fin 4) :=
  (univ.erase z).filter fun i ↦ bit m i u = true

def CommonColumn (d : Fin 4) (m : ℕ) : Prop :=
  ∃ z u : Fin 4, (replacementMask d (JointCore.row m z)).testBit u.val = true ∧
    2 ≤ (otherNeighbors m z u).card

instance (d : Fin 4) (m : ℕ) : Decidable (CommonColumn d m) :=
  inferInstanceAs (Decidable (∃ z u : Fin 4,
    (replacementMask d (JointCore.row m z)).testBit u.val = true ∧
      2 ≤ (otherNeighbors m z u).card))

def leafRow (i : Fin 2) : Fin 4 := ⟨i.val, by omega⟩

def coreRow (i : Fin 2) : Fin 4 := Fin.natAdd 2 i

def Direct (d : Fin 4) (m : ℕ) (leaf z : Fin 2) (cols : Fin 4 ↪ Fin 4) : Prop :=
  FirstPaw.CycleOrder d cols ∧ ¬FirstPaw.quadAdj d cols 1 3 ∧
    bit m (leafRow leaf) (cols 0) = true ∧ bit m (leafRow leaf) (cols 2) = true ∧
    bit m (coreRow z) (cols 1) = true ∧ bit m 2 (cols 2) = true ∧ bit m 3 (cols 2) = true

instance (d : Fin 4) (m : ℕ) (leaf z : Fin 2) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Direct d m leaf z cols) := inferInstanceAs (Decidable (_ ∧ _))

def Gain (d : Fin 4) (m : ℕ) (leaf : Fin 2) (cols : Fin 4 ↪ Fin 4) : Prop :=
  d = 0 ∧ FirstPaw.CycleOrder d cols ∧
    bit m (leafRow leaf) (cols 0) = true ∧ bit m (leafRow leaf) (cols 3) = true ∧
    bit m 2 (cols 1) = true ∧ bit m 2 (cols 2) = true ∧
    bit m 3 (cols 1) = true ∧ bit m 3 (cols 2) = true

instance (d : Fin 4) (m : ℕ) (leaf : Fin 2) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Gain d m leaf cols) := inferInstanceAs (Decidable (_ ∧ _))

def Hypotheses (m : ℕ) : Prop :=
  PawNine.rowCount m 0 ≤ 2 ∧ PawNine.rowCount m 1 ≤ 2 ∧
    PawNine.rowCount m 2 ≤ 3 ∧ PawNine.rowCount m 3 ≤ 3 ∧ 9 ≤ PathExchange.crossCount m

instance (m : ℕ) : Decidable (Hypotheses m) := inferInstanceAs (Decidable (_ ∧ _))

def Classified (d : Fin 4) (m : ℕ) : Prop :=
  CommonColumn d m ∨ (∃ leaf z : Fin 2, ∃ cols : Fin 4 ↪ Fin 4, Direct d m leaf z cols) ∨
    ∃ leaf : Fin 2, ∃ cols : Fin 4 ↪ Fin 4, Gain d m leaf cols

end Erdos577.JointFirstRows
