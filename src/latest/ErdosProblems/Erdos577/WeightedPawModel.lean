import ErdosProblems.Erdos577.FirstPawModel
import ErdosProblems.Erdos577.PawNineModel

/-! The initial twelve weighted patterns; no later exclusion is built into the conclusion. -/

namespace Erdos577.WeightedPaw

open FirstPaw

def Row (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) (i : Fin 4) (mask : ℕ) : Prop :=
  ∀ j : Fin 4, bit m swap cols i j = mask.testBit j.val

instance (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) (i : Fin 4) (mask : ℕ) :
    Decidable (Row m swap cols i mask) :=
  inferInstanceAs (Decidable (∀ j : Fin 4, bit m swap cols i j = mask.testBit j.val))

def Pattern9 (_diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  rowCount m swap cols 0 = 1 ∧ Row m swap cols 2 14 ∧ Row m swap cols 3 14

instance (d : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern9 d m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern10 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  quadAdj diagonal cols 0 2 ∧ quadAdj diagonal cols 1 3 ∧
    Row m swap cols 0 15 ∧ Row m swap cols 3 0 ∧
      ∀ j : Fin 4, (14 : ℕ).testBit j.val = true → bit m swap cols 2 j = true

instance (d : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern10 d m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern11 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  quadAdj diagonal cols 1 3 ∧
    Row m swap cols 0 7 ∧ Row m swap cols 2 15 ∧ Row m swap cols 3 0

instance (d : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern11 d m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern12 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  quadAdj diagonal cols 1 3 ∧
    Row m swap cols 0 7 ∧ Row m swap cols 2 7 ∧ Row m swap cols 3 8

instance (d : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern12 d m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern13 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  ¬quadAdj diagonal cols 1 3 ∧
    Row m swap cols 0 1 ∧ Row m swap cols 2 13 ∧ Row m swap cols 3 7

instance (d : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern13 d m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern14 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  ¬quadAdj diagonal cols 1 3 ∧
    Row m swap cols 0 5 ∧ Row m swap cols 2 13 ∧ Row m swap cols 3 5

instance (d : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern14 d m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern15 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  OnlyFirst diagonal cols ∧
    Row m swap cols 0 1 ∧ Row m swap cols 2 15 ∧ Row m swap cols 3 6

instance (d : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern15 d m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern16 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  ¬quadAdj diagonal cols 1 3 ∧
    Row m swap cols 0 5 ∧ Row m swap cols 2 13 ∧ Row m swap cols 3 7

instance (d : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern16 d m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern17 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  ¬quadAdj diagonal cols 1 3 ∧
    Row m swap cols 0 5 ∧ Row m swap cols 2 13 ∧ Row m swap cols 3 3

instance (d : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern17 d m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern18 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  OnlyFirst diagonal cols ∧
    Row m swap cols 0 3 ∧ Row m swap cols 2 15 ∧ Row m swap cols 3 4

instance (d : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern18 d m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern19 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  ¬quadAdj diagonal cols 0 2 ∧ ¬quadAdj diagonal cols 1 3 ∧
    Row m swap cols 0 3 ∧ Row m swap cols 2 7 ∧ Row m swap cols 3 9

instance (d : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern19 d m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Pattern20 (diagonal : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  OnlyFirst diagonal cols ∧
    Row m swap cols 0 3 ∧ Row m swap cols 2 13 ∧ Row m swap cols 3 5

instance (d : Fin 4) (m : ℕ) (swap : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern20 d m swap cols) := inferInstanceAs (Decidable (_ ∧ _))

def Classified (diagonal : Fin 4) (m : ℕ) : Prop :=
  ∃ swap : Bool, ∃ cols : Fin 4 ↪ Fin 4, CycleOrder diagonal cols ∧
    (Pattern9 diagonal m swap cols ∨ Pattern10 diagonal m swap cols ∨
      Pattern11 diagonal m swap cols ∨ Pattern12 diagonal m swap cols ∨
      Pattern13 diagonal m swap cols ∨ Pattern14 diagonal m swap cols ∨
      Pattern15 diagonal m swap cols ∨ Pattern16 diagonal m swap cols ∨
      Pattern17 diagonal m swap cols ∨ Pattern18 diagonal m swap cols ∨
      Pattern19 diagonal m swap cols ∨ Pattern20 diagonal m swap cols)

end Erdos577.WeightedPaw
