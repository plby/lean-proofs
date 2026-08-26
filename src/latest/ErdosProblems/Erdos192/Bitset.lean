import Mathlib

namespace Erdos192

def bitset : List Nat → Nat
  | [] => 0
  | x :: xs => (1 <<< x) ||| bitset xs

theorem testBit_bitset (xs : List Nat) (i : Nat) :
    (bitset xs).testBit i = true ↔ i ∈ xs := by
  induction xs with
  | nil => simp [bitset]
  | cons x xs ih =>
    simp only [bitset, Nat.testBit_or, Bool.or_eq_true, List.mem_cons]
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq, ih]
    simp [eq_comm]

def rotateMask (m bits q : Nat) : Nat :=
  ((bits <<< q) ||| (bits >>> (m - q))) % (2 ^ m)

theorem rotateMask_contains (m bits q i : Nat) (hm : 0 < m) (hq : q < m)
    (hi : i < m) (h : bits.testBit i = true) :
    (rotateMask m bits q).testBit ((i + q) % m) = true := by
  unfold rotateMask
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨Nat.mod_lt _ hm, ?_⟩
  rw [Bool.or_eq_true]
  by_cases hlt : i + q < m
  · left
    rw [Nat.mod_eq_of_lt hlt, Nat.testBit_shiftLeft]
    simp [h]
  · right
    rw [Nat.testBit_shiftRight]
    have hmod : (i + q) % m = i + q - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod, show m - q + (i + q - m) = i by omega]
    exact h

theorem mask_intersection_mem (left right : Nat) (xs : List Nat) (i : Nat)
    (h : left &&& right = bitset xs) (hl : left.testBit i = true)
    (hr : right.testBit i = true) : i ∈ xs := by
  apply (testBit_bitset xs i).mp
  rw [← h, Nat.testBit_and, hl, hr]
  rfl

end Erdos192
