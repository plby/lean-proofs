import ErdosProblems.Erdos577.PawModel
import ErdosProblems.Erdos577.PawLabels
import ErdosProblems.Erdos577.MatchingGain
import ErdosProblems.Erdos577.DenseOutsideModel

/-! The three local obstructions and source patterns (3)–(8) for a paw and block. -/

namespace Erdos577.FirstPaw

open Finset
open scoped BigOperators

def Positive (diagonal : Fin 4) (m : ℕ) : Prop :=
  LocalFactor (PawModel.graph diagonal m) univ ∨
    StrictImprovement (PawModel.graph diagonal m) univ (Unattached.oldEdges diagonal) ∨
    TwoEdgeReduction (PawModel.graph diagonal m) univ (Unattached.oldEdges diagonal + 2)

lemma Positive.mono {diagonal : Fin 4} {small large : ℕ}
    (hs : Positive diagonal small) (h : large &&& small = small) : Positive diagonal large := by
  let f := SimpleGraph.Copy.ofLE (PawModel.graph diagonal small) (PawModel.graph diagonal large)
    (PawModel.graph_mono diagonal h)
  rcases hs with hs | hs | hs
  · left
    simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hs.image f
  · right
    left
    simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hs.image f
  · right
    right
    simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hs.image f

def rowIndex (swap : Bool) (i : Fin 4) : Fin 4 := if swap then Equiv.swap 2 3 i else i

def bit (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) (i j : Fin 4) : Bool :=
  m.testBit (4 * (rowIndex swap i).val + (cols j).val)

def rowCount (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) (i : Fin 4) : ℕ :=
  ∑ j : Fin 4, (bit m swap cols i j).toNat

def quadAdj (diagonal : Fin 4) (cols : Fin 4 ↪ Fin 4) (i j : Fin 4) : Prop :=
  (PawModel.graph diagonal 0).Adj (Fin.natAdd 4 (cols i)) (Fin.natAdd 4 (cols j))

instance (diagonal : Fin 4) (cols : Fin 4 ↪ Fin 4) (i j : Fin 4) :
    Decidable (quadAdj diagonal cols i j) :=
  inferInstanceAs (Decidable ((PawModel.graph _ _).Adj _ _))

def CycleOrder (diagonal : Fin 4) (cols : Fin 4 ↪ Fin 4) : Prop :=
  ∀ i : Fin 4, quadAdj diagonal cols i (i + 1)

instance (diagonal : Fin 4) (cols : Fin 4 ↪ Fin 4) : Decidable (CycleOrder diagonal cols) :=
  inferInstanceAs (Decidable (∀ i : Fin 4, quadAdj diagonal cols i (i + 1)))

def OnlyFirst (diagonal : Fin 4) (cols : Fin 4 ↪ Fin 4) : Prop :=
  quadAdj diagonal cols 0 2 ∧ ¬quadAdj diagonal cols 1 3

instance (diagonal : Fin 4) (cols : Fin 4 ↪ Fin 4) : Decidable (OnlyFirst diagonal cols) :=
  inferInstanceAs (Decidable (_ ∧ _))

def ExactRows (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) (rows : Fin 4 → ℕ) : Prop :=
  ∀ i j : Fin 4, bit m swap cols i j = (rows i).testBit j.val

instance (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) (rows : Fin 4 → ℕ) :
    Decidable (ExactRows m swap cols rows) :=
  inferInstanceAs (Decidable (∀ i j : Fin 4, bit m swap cols i j = (rows i).testBit j.val))

def Pattern3 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  OnlyFirst diagonal cols ∧ ExactRows m swap cols ![1, 15, 9, 3]

instance (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern3 diagonal m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern4 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  quadAdj diagonal cols 0 2 ∧ 3 ≤ rowCount m swap cols 1 ∧ ∀ j : Fin 4,
    bit m swap cols 0 j = true ∨ bit m swap cols 2 j = true ∨ bit m swap cols 3 j = true →
      j = 0 ∨ j = 2

instance (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern4 diagonal m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern5 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  OnlyFirst diagonal cols ∧
    (∀ j : Fin 4, bit m swap cols 0 j = true ∨ bit m swap cols 1 j = true → j = 0 ∨ j = 2) ∧
    (∀ j : Fin 4, bit m swap cols 2 j = true → j ≠ 1) ∧
    (∀ j : Fin 4, bit m swap cols 3 j = true → j ≠ 3)

instance (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern5 diagonal m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern6 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  OnlyFirst diagonal cols ∧
    (∀ j : Fin 4, bit m swap cols 0 j = true → j = 0 ∨ j = 1) ∧
    (∀ j : Fin 4, bit m swap cols 2 j = true → j ≠ 3) ∧
    (∀ j : Fin 4, bit m swap cols 3 j = true → j = 0)

instance (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern6 diagonal m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern7 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  OnlyFirst diagonal cols ∧ ExactRows m swap cols ![1, 7, 7, 5]

instance (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern7 diagonal m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern8 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  quadAdj diagonal cols 0 2 ∧ ExactRows m swap cols ![1, 15, 15, 0]

instance (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern8 diagonal m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Classified (diagonal : Fin 4) (m : ℕ) : Prop :=
  PathExchange.crossCount m ≤ 10 ∧ DenseOutside.terminalCount m ≤ 2 ∧
    ∃ swap : Bool, ∃ cols : Fin 4 ↪ Fin 4, CycleOrder diagonal cols ∧
      (Pattern3 diagonal m swap cols ∨ Pattern4 diagonal m swap cols ∨
        Pattern5 diagonal m swap cols ∨ Pattern6 diagonal m swap cols ∨
        Pattern7 diagonal m swap cols ∨ Pattern8 diagonal m swap cols)

end Erdos577.FirstPaw
