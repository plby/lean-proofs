import ErdosProblems.Erdos577.JointCoreModel
import ErdosProblems.Erdos577.DenseTriangleWitnesses0
import ErdosProblems.Erdos577.DenseTriangleWitnesses1
import ErdosProblems.Erdos577.DenseTriangleWitnesses2

/-! Bounded row data and explicit cyclic candidates for the eight core patterns. -/

namespace Erdos577.JointCore

open Finset
open scoped BigOperators

def rowSize (r : Fin 16) : ℕ := ∑ j : Fin 4, (r.val.testBit j.val).toNat

def pack (r b c : Fin 16) : ℕ := 16 * r.val + 256 * b.val + 4096 * c.val

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
  ⟨![3, 1, 2, 0], by decide +kernel⟩

def candidate (d : Fin 4) (m : ℕ) : Fin 8 × (Fin 4 ↪ Fin 4) :=
  match d.val, m with
  | 1, 62832 => (3, cols_5)
  | 1, 62896 => (2, cols_14)
  | 1, 62928 => (3, cols_0)
  | 1, 62944 => (2, cols_0)
  | 1, 61936 => (0, cols_0)
  | 1, 62704 => (0, cols_14)
  | 1, 62960 => (0, cols_0)
  | 2, 64112 => (2, cols_18)
  | 2, 64176 => (3, cols_9)
  | 2, 64208 => (2, cols_7)
  | 2, 64224 => (3, cols_7)
  | 2, 62192 => (0, cols_7)
  | 2, 63728 => (0, cols_18)
  | 2, 64240 => (0, cols_7)
  | 3, 62320 => (4, cols_5)
  | 3, 62832 => (4, cols_4)
  | 3, 63088 => (4, cols_10)
  | 3, 63344 => (4, cols_4)
  | 3, 63856 => (5, cols_20)
  | 3, 64112 => (5, cols_19)
  | 3, 64368 => (4, cols_5)
  | 3, 64624 => (5, cols_18)
  | 3, 64880 => (4, cols_4)
  | 3, 65136 => (4, cols_10)
  | 3, 65392 => (4, cols_4)
  | 3, 62384 => (4, cols_3)
  | 3, 62896 => (5, cols_15)
  | 3, 63152 => (5, cols_13)
  | 3, 63408 => (4, cols_3)
  | 3, 63920 => (4, cols_2)
  | 3, 64176 => (4, cols_8)
  | 3, 64432 => (4, cols_2)
  | 3, 64688 => (5, cols_12)
  | 3, 64944 => (4, cols_2)
  | 3, 65200 => (4, cols_8)
  | 3, 65456 => (4, cols_2)
  | 3, 62416 => (5, cols_9)
  | 3, 62928 => (4, cols_1)
  | 3, 63184 => (5, cols_7)
  | 3, 63440 => (4, cols_1)
  | 3, 63952 => (4, cols_0)
  | 3, 64208 => (5, cols_6)
  | 3, 64464 => (4, cols_0)
  | 3, 64720 => (4, cols_14)
  | 3, 64976 => (4, cols_0)
  | 3, 65232 => (5, cols_6)
  | 3, 65488 => (4, cols_0)
  | 3, 62432 => (5, cols_3)
  | 3, 62944 => (5, cols_1)
  | 3, 63200 => (4, cols_7)
  | 3, 63456 => (5, cols_1)
  | 3, 63968 => (5, cols_0)
  | 3, 64224 => (4, cols_6)
  | 3, 64480 => (5, cols_0)
  | 3, 64736 => (4, cols_12)
  | 3, 64992 => (5, cols_0)
  | 3, 65248 => (4, cols_6)
  | 3, 65504 => (5, cols_0)
  | 3, 61936 => (1, cols_0)
  | 3, 62192 => (1, cols_6)
  | 3, 62448 => (1, cols_0)
  | 3, 62704 => (1, cols_12)
  | 3, 62960 => (1, cols_0)
  | 3, 63216 => (1, cols_6)
  | 3, 30704 => (6, cols_0)
  | 3, 47088 => (7, cols_1)
  | 3, 55280 => (7, cols_3)
  | 3, 59376 => (7, cols_9)
  | 3, 63472 => (1, cols_0)
  | 3, 63728 => (1, cols_18)
  | 3, 63984 => (1, cols_0)
  | 3, 64240 => (1, cols_6)
  | 3, 31728 => (7, cols_0)
  | 3, 48112 => (6, cols_1)
  | 3, 56304 => (7, cols_5)
  | 3, 60400 => (7, cols_11)
  | 3, 64496 => (1, cols_0)
  | 3, 64752 => (1, cols_12)
  | 3, 32240 => (7, cols_2)
  | 3, 48624 => (7, cols_4)
  | 3, 56816 => (6, cols_3)
  | 3, 60912 => (7, cols_17)
  | 3, 65008 => (1, cols_0)
  | 3, 32496 => (7, cols_8)
  | 3, 48880 => (7, cols_10)
  | 3, 57072 => (7, cols_16)
  | 3, 61168 => (6, cols_9)
  | 3, 65264 => (1, cols_6)
  | 3, 32752 => (7, cols_0)
  | 3, 49136 => (7, cols_1)
  | 3, 57328 => (7, cols_3)
  | 3, 61424 => (7, cols_9)
  | 3, 65520 => (1, cols_0)
  | _, _ => (0, Function.Embedding.refl _)

def Accepted (d : Fin 4) (m : ℕ) : Prop :=
  FirstPaw.CycleOrder d (candidate d m).2 ∧
    Pattern (candidate d m).1 d m (candidate d m).2

instance (d : Fin 4) (m : ℕ) : Decidable (Accepted d m) :=
  inferInstanceAs (Decidable (_ ∧ _))

def covered (d : Fin 4) (m : ℕ) : Bool :=
  match d.val with
  | 0 => DenseTriangle.D0.covered m
  | 1 => DenseTriangle.D1.covered m
  | 2 => DenseTriangle.D2.covered m
  | _ => false

lemma covered_positive (d : Fin 4) (m : ℕ) (h : covered d m = true) :
    DenseTriangle.Positive d m := by
  fin_cases d
  · change DenseTriangle.D0.covered m = true at h
    obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp h
    exact (DenseTriangle.D0.masks_sound hw).mono (beq_iff_eq.mp hsub)
  · change DenseTriangle.D1.covered m = true at h
    obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp h
    exact (DenseTriangle.D1.masks_sound hw).mono (beq_iff_eq.mp hsub)
  · change DenseTriangle.D2.covered m = true at h
    obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp h
    exact (DenseTriangle.D2.masks_sound hw).mono (beq_iff_eq.mp hsub)
  · change false = true at h
    contradiction

lemma accepted_classified (d : Fin 4) (m : ℕ) (h : Accepted d m) : Classified d m :=
  ⟨(candidate d m).1, (candidate d m).2, h⟩

end Erdos577.JointCore
