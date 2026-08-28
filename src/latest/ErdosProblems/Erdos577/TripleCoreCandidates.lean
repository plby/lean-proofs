import ErdosProblems.Erdos577.TripleCoreWitnessCases
import ErdosProblems.Erdos577.JointCoreRowReduction

/-! Exact row/diagonal patterns and explicit column permutations for all ten-contact cores. -/

namespace Erdos577.TripleCorePatterns

open Finset

def Pattern (tag : Fin 12) (d : Fin 4) (m : ℕ) (cols : Fin 4 ↪ Fin 4) : Prop :=
  (FirstPaw.quadAdj d cols 0 2 ↔ (diagonal tag).val.testBit 0 = true) ∧
    (FirstPaw.quadAdj d cols 1 3 ↔ (diagonal tag).val.testBit 1 = true) ∧
    ∀ i j : Fin 4, i ≠ 0 → FirstPaw.bit m false cols i j = (rows tag i).testBit j.val

instance (tag : Fin 12) (d : Fin 4) (m : ℕ) (cols : Fin 4 ↪ Fin 4) :
    Decidable (Pattern tag d m cols) := inferInstanceAs (Decidable (_ ∧ _))

def Classified (d : Fin 4) (m : ℕ) : Prop :=
  ∃ tag : Fin 12, ∃ cols : Fin 4 ↪ Fin 4, FirstPaw.CycleOrder d cols ∧ Pattern tag d m cols

private def cols_0 : Fin 4 ↪ Fin 4 :=
  ⟨![0, 1, 2, 3], by decide +kernel⟩

private def cols_1 : Fin 4 ↪ Fin 4 :=
  ⟨![0, 1, 3, 2], by decide +kernel⟩

private def cols_2 : Fin 4 ↪ Fin 4 :=
  ⟨![0, 2, 1, 3], by decide +kernel⟩

private def cols_3 : Fin 4 ↪ Fin 4 :=
  ⟨![0, 2, 3, 1], by decide +kernel⟩

private def cols_4 : Fin 4 ↪ Fin 4 :=
  ⟨![0, 3, 1, 2], by decide +kernel⟩

private def cols_5 : Fin 4 ↪ Fin 4 :=
  ⟨![0, 3, 2, 1], by decide +kernel⟩

private def cols_6 : Fin 4 ↪ Fin 4 :=
  ⟨![1, 0, 2, 3], by decide +kernel⟩

private def cols_7 : Fin 4 ↪ Fin 4 :=
  ⟨![1, 0, 3, 2], by decide +kernel⟩

private def cols_8 : Fin 4 ↪ Fin 4 :=
  ⟨![1, 2, 0, 3], by decide +kernel⟩

private def cols_9 : Fin 4 ↪ Fin 4 :=
  ⟨![1, 2, 3, 0], by decide +kernel⟩

private def cols_10 : Fin 4 ↪ Fin 4 :=
  ⟨![1, 3, 0, 2], by decide +kernel⟩

private def cols_11 : Fin 4 ↪ Fin 4 :=
  ⟨![1, 3, 2, 0], by decide +kernel⟩

private def cols_12 : Fin 4 ↪ Fin 4 :=
  ⟨![2, 0, 1, 3], by decide +kernel⟩

private def cols_13 : Fin 4 ↪ Fin 4 :=
  ⟨![2, 0, 3, 1], by decide +kernel⟩

private def cols_14 : Fin 4 ↪ Fin 4 :=
  ⟨![2, 1, 0, 3], by decide +kernel⟩

private def cols_15 : Fin 4 ↪ Fin 4 :=
  ⟨![2, 1, 3, 0], by decide +kernel⟩

private def cols_16 : Fin 4 ↪ Fin 4 :=
  ⟨![2, 3, 0, 1], by decide +kernel⟩

private def cols_17 : Fin 4 ↪ Fin 4 :=
  ⟨![2, 3, 1, 0], by decide +kernel⟩

private def cols_18 : Fin 4 ↪ Fin 4 :=
  ⟨![3, 0, 1, 2], by decide +kernel⟩

private def cols_19 : Fin 4 ↪ Fin 4 :=
  ⟨![3, 0, 2, 1], by decide +kernel⟩

private def cols_20 : Fin 4 ↪ Fin 4 :=
  ⟨![3, 1, 0, 2], by decide +kernel⟩

private def cols_21 : Fin 4 ↪ Fin 4 :=
  ⟨![3, 1, 2, 0], by decide +kernel⟩

private def cols_22 : Fin 4 ↪ Fin 4 :=
  ⟨![3, 2, 0, 1], by decide +kernel⟩

private def cols_23 : Fin 4 ↪ Fin 4 :=
  ⟨![3, 2, 1, 0], by decide +kernel⟩

def candidate (d : Fin 4) (m : ℕ) : Fin 12 × (Fin 4 ↪ Fin 4) :=
  match d.val, m with
  | 1, 65360 => (1, cols_0)
  | 1, 62960 => (7, cols_0)
  | 1, 24560 => (9, cols_0)
  | 2, 65440 => (1, cols_7)
  | 2, 64240 => (7, cols_7)
  | 2, 45040 => (9, cols_7)
  | 3, 65328 => (0, cols_2)
  | 3, 65360 => (0, cols_0)
  | 3, 65376 => (0, cols_6)
  | 3, 63344 => (2, cols_0)
  | 3, 64368 => (3, cols_1)
  | 3, 64880 => (3, cols_3)
  | 3, 65136 => (3, cols_9)
  | 3, 32624 => (4, cols_0)
  | 3, 49008 => (5, cols_1)
  | 3, 57200 => (5, cols_3)
  | 3, 61296 => (5, cols_9)
  | 3, 65424 => (0, cols_1)
  | 3, 65440 => (0, cols_7)
  | 3, 63408 => (3, cols_0)
  | 3, 64432 => (2, cols_1)
  | 3, 64944 => (3, cols_5)
  | 3, 65200 => (3, cols_11)
  | 3, 32688 => (5, cols_0)
  | 3, 49072 => (4, cols_1)
  | 3, 57264 => (5, cols_5)
  | 3, 61360 => (5, cols_11)
  | 3, 65472 => (0, cols_13)
  | 3, 63440 => (3, cols_2)
  | 3, 64464 => (3, cols_4)
  | 3, 64976 => (2, cols_3)
  | 3, 65232 => (3, cols_17)
  | 3, 32720 => (5, cols_2)
  | 3, 49104 => (5, cols_4)
  | 3, 57296 => (4, cols_3)
  | 3, 61392 => (5, cols_17)
  | 3, 63456 => (3, cols_8)
  | 3, 64480 => (3, cols_10)
  | 3, 64992 => (3, cols_16)
  | 3, 65248 => (2, cols_9)
  | 3, 32736 => (5, cols_8)
  | 3, 49120 => (5, cols_10)
  | 3, 57312 => (5, cols_16)
  | 3, 61408 => (4, cols_9)
  | 3, 62448 => (6, cols_0)
  | 3, 62960 => (6, cols_2)
  | 3, 63216 => (6, cols_8)
  | 3, 30704 => (10, cols_0)
  | 3, 47088 => (11, cols_1)
  | 3, 55280 => (11, cols_3)
  | 3, 59376 => (11, cols_9)
  | 3, 63984 => (6, cols_4)
  | 3, 64240 => (6, cols_10)
  | 3, 31728 => (11, cols_0)
  | 3, 48112 => (10, cols_1)
  | 3, 56304 => (11, cols_5)
  | 3, 60400 => (11, cols_11)
  | 3, 64752 => (6, cols_16)
  | 3, 32240 => (11, cols_2)
  | 3, 48624 => (11, cols_4)
  | 3, 56816 => (10, cols_3)
  | 3, 60912 => (11, cols_17)
  | 3, 32496 => (11, cols_8)
  | 3, 48880 => (11, cols_10)
  | 3, 57072 => (11, cols_16)
  | 3, 61168 => (10, cols_9)
  | 3, 16368 => (8, cols_0)
  | 3, 24560 => (8, cols_2)
  | 3, 28656 => (8, cols_8)
  | 3, 40944 => (8, cols_4)
  | 3, 45040 => (8, cols_10)
  | 3, 53232 => (8, cols_16)
  | _, _ => (0, Function.Embedding.refl _)

def Accepted (d : Fin 4) (m : ℕ) : Prop :=
  FirstPaw.CycleOrder d (candidate d m).2 ∧ Pattern (candidate d m).1 d m (candidate d m).2

instance (d : Fin 4) (m : ℕ) : Decidable (Accepted d m) :=
  inferInstanceAs (Decidable (_ ∧ _))

lemma accepted_classified (d : Fin 4) (m : ℕ) (h : Accepted d m) : Classified d m :=
  ⟨(candidate d m).1, (candidate d m).2, h⟩

end Erdos577.TripleCorePatterns
