import Mathlib

/-!
# The marked-path counting lemma for Erdős problem 920

This file isolates the elementary tree estimate used in the proof of
Bradač's bound for forward-independent tuples.  A history is stored in
reverse chronological order: if `xs` is the current history and `x` is a
child, the extended history is `x :: xs`.  This convention makes the
recursive finite enumeration particularly simple.

For a fixed Boolean signature, a marked step costs at most `h` choices and
an unmarked step costs at most `Delta` choices.  Summing over all Boolean
signatures with at most `w` unmarked steps gives

`2 ^ m * Delta ^ w * h ^ (m - w)`.
-/

namespace Erdos920.MarkedTree

open Finset

section Definitions

variable {alpha : Type*} [DecidableEq alpha]

/-- All Boolean lists of the specified length. -/
noncomputable def signatures : Nat -> Finset (List Bool)
  | 0 => {[]}
  | m + 1 => (signatures m).biUnion fun s => {false :: s, true :: s}

/--
The histories realizing a prescribed marked/unmarked signature.

Both histories and signatures are written in reverse chronological order.
`true` means that the corresponding child is marked.
-/
noncomputable def pathsOfSignature
    (children : List alpha -> Finset alpha)
    (marked : List alpha -> alpha -> Bool) : List Bool -> Finset (List alpha)
  | [] => {[]}
  | b :: bs =>
      (pathsOfSignature children marked bs).biUnion fun xs =>
        ((children xs).filter fun x => marked xs x = b).image fun x => x :: xs

/-- A reversed history follows the given child finsets at every step. -/
def IsPath (children : List alpha -> Finset alpha) : List alpha -> Prop
  | [] => True
  | x :: xs => IsPath children xs /\ x ∈ children xs

/-- The deterministic Boolean signature of a reversed history. -/
def pathSignature (marked : List alpha -> alpha -> Bool) : List alpha -> List Bool
  | [] => []
  | x :: xs => marked xs x :: pathSignature marked xs

/--
All length-`m` paths having at most `w` unmarked steps.  This definition is
finite even when the ambient type is infinite, since it is generated only
from the finite child sets.
-/
noncomputable def boundedPaths
    (children : List alpha -> Finset alpha)
    (marked : List alpha -> alpha -> Bool) (m w : Nat) : Finset (List alpha) :=
  (signatures m).filter (fun s => s.count false <= w) |>.biUnion
    (pathsOfSignature children marked)

end Definitions

section ElementaryProperties

variable {alpha : Type*}

@[simp] theorem mem_signatures_iff_length (s : List Bool) (m : Nat) :
    s ∈ signatures m <-> s.length = m := by
  induction m generalizing s with
  | zero => simp [signatures]
  | succ m ih =>
      cases s with
      | nil => simp [signatures]
      | cons b s =>
          cases b <;> simp [signatures, ih]

theorem card_signatures_le (m : Nat) :
    (signatures m).card <= 2 ^ m := by
  induction m with
  | zero => simp [signatures]
  | succ m ih =>
      calc
        (signatures (m + 1)).card <=
            ∑ s ∈ signatures m, ({false :: s, true :: s} : Finset (List Bool)).card := by
          simpa [signatures] using
            (Finset.card_biUnion_le
              (s := signatures m)
              (t := fun s => ({false :: s, true :: s} : Finset (List Bool))))
        _ = (signatures m).card * 2 := by simp
        _ <= 2 ^ m * 2 := Nat.mul_le_mul_right 2 ih
        _ = 2 ^ (m + 1) := by rw [pow_succ]

@[simp] theorem pathSignature_length
    (marked : List alpha -> alpha -> Bool) (xs : List alpha) :
    (pathSignature marked xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pathSignature, ih]

variable [DecidableEq alpha]

@[simp] theorem mem_pathsOfSignature_iff
    (children : List alpha -> Finset alpha)
    (marked : List alpha -> alpha -> Bool)
    (xs : List alpha) (s : List Bool) :
    xs ∈ pathsOfSignature children marked s <->
      IsPath children xs /\ pathSignature marked xs = s := by
  classical
  induction s generalizing xs with
  | nil =>
      cases xs <;> simp [pathsOfSignature, IsPath, pathSignature]
  | cons b bs ih =>
      cases xs with
      | nil => simp [pathsOfSignature, IsPath, pathSignature]
      | cons x xs =>
          simp [pathsOfSignature, IsPath, pathSignature, ih, and_assoc,
            and_left_comm, and_comm]

@[simp] theorem mem_boundedPaths_iff
    (children : List alpha -> Finset alpha)
    (marked : List alpha -> alpha -> Bool)
    (xs : List alpha) (m w : Nat) :
    xs ∈ boundedPaths children marked m w <->
      IsPath children xs /\ xs.length = m /\
        (pathSignature marked xs).count false <= w := by
  classical
  constructor
  · intro hxs
    simp only [boundedPaths] at hxs
    obtain ⟨s, hs, hpath⟩ := Finset.mem_biUnion.mp hxs
    have hs' := Finset.mem_filter.mp hs
    have hchar := (mem_pathsOfSignature_iff children marked xs s).mp hpath
    refine ⟨hchar.1, ?_, ?_⟩
    · rw [← pathSignature_length marked xs, hchar.2]
      exact (mem_signatures_iff_length s m).mp hs'.1
    · simpa [hchar.2] using hs'.2
  · rintro ⟨hpath, hlen, hunmarked⟩
    simp only [boundedPaths]
    apply Finset.mem_biUnion.mpr
    refine ⟨pathSignature marked xs, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨(mem_signatures_iff_length _ _).mpr (by simpa using hlen), hunmarked⟩
    · exact (mem_pathsOfSignature_iff children marked xs _).mpr ⟨hpath, rfl⟩

end ElementaryProperties

section Counting

variable {alpha : Type*} [DecidableEq alpha]

/-- Moving unmarked weight from `h` to the larger base `Delta` can only
increase the monomial. -/
private theorem pow_mul_pow_le_pow_mul_pow
    {h Delta j w m : Nat} (hhDelta : h <= Delta) (hjw : j <= w) (hwm : w <= m) :
    Delta ^ j * h ^ (m - j) <= Delta ^ w * h ^ (m - w) := by
  have hmj : m - j = (m - w) + (w - j) := by omega
  calc
    Delta ^ j * h ^ (m - j) =
        (Delta ^ j * h ^ (m - w)) * h ^ (w - j) := by
          rw [hmj, pow_add]
          ac_rfl
    _ <= (Delta ^ j * h ^ (m - w)) * Delta ^ (w - j) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hhDelta _)
    _ = Delta ^ (j + (w - j)) * h ^ (m - w) := by
      rw [pow_add]
      ac_rfl
    _ = Delta ^ w * h ^ (m - w) := by
      rw [Nat.add_sub_of_le hjw]

/-- A fixed Boolean signature has the expected product bound. -/
theorem card_pathsOfSignature_le
    (children : List alpha -> Finset alpha)
    (marked : List alpha -> alpha -> Bool)
    {Delta h : Nat}
    (hchildren : ∀ xs, (children xs).card <= Delta)
    (hmarked : ∀ xs,
      ((children xs).filter fun x => marked xs x = true).card <= h)
    (s : List Bool) :
    (pathsOfSignature children marked s).card <=
      Delta ^ s.count false * h ^ s.count true := by
  classical
  induction s with
  | nil => simp [pathsOfSignature]
  | cons b bs ih =>
      let stepBound := if b then h else Delta
      have hone (xs : List alpha) :
          (((children xs).filter fun x => marked xs x = b).image fun x => x :: xs).card <=
            stepBound := by
        refine Finset.card_image_le.trans ?_
        cases b with
        | false =>
            exact (Finset.card_filter_le _ _).trans (hchildren xs)
        | true =>
            simpa [stepBound] using hmarked xs
      calc
        (pathsOfSignature children marked (b :: bs)).card <=
            ∑ xs ∈ pathsOfSignature children marked bs,
              ((((children xs).filter fun x => marked xs x = b).image
                fun x => x :: xs).card) := by
          simpa [pathsOfSignature] using
            (Finset.card_biUnion_le
              (s := pathsOfSignature children marked bs)
              (t := fun xs =>
                ((children xs).filter fun x => marked xs x = b).image fun x => x :: xs))
        _ <= ∑ _xs ∈ pathsOfSignature children marked bs, stepBound := by
          exact Finset.sum_le_sum fun xs _ => hone xs
        _ = (pathsOfSignature children marked bs).card * stepBound := by simp
        _ <= (Delta ^ bs.count false * h ^ bs.count true) * stepBound :=
          Nat.mul_le_mul_right stepBound ih
        _ = Delta ^ (b :: bs).count false * h ^ (b :: bs).count true := by
          cases b <;> simp [stepBound, pow_succ] <;> ac_rfl

/--
The marked-tree estimate.  Every node has at most `Delta` children and at
most `h` marked children.  Consequently the number of length-`m` paths with
at most `w` unmarked steps is at most
`2^m * Delta^w * h^(m-w)`.
-/
theorem card_boundedPaths_le
    (children : List alpha -> Finset alpha)
    (marked : List alpha -> alpha -> Bool)
    {Delta h m w : Nat}
    (hchildren : ∀ xs, (children xs).card <= Delta)
    (hmarked : ∀ xs,
      ((children xs).filter fun x => marked xs x = true).card <= h)
    (hhDelta : h <= Delta) (hwm : w <= m) :
    (boundedPaths children marked m w).card <=
      2 ^ m * Delta ^ w * h ^ (m - w) := by
  classical
  let S := (signatures m).filter fun s => s.count false <= w
  let B := Delta ^ w * h ^ (m - w)
  have hper (s : List Bool) (hs : s ∈ S) :
      (pathsOfSignature children marked s).card <= B := by
    have hs' := Finset.mem_filter.mp hs
    have hlen : s.length = m := (mem_signatures_iff_length s m).mp hs'.1
    have htrue : s.count true = m - s.count false := by
      have hcounts := List.count_false_add_count_true s
      omega
    calc
      (pathsOfSignature children marked s).card <=
          Delta ^ s.count false * h ^ s.count true :=
        card_pathsOfSignature_le children marked hchildren hmarked s
      _ = Delta ^ s.count false * h ^ (m - s.count false) := by rw [htrue]
      _ <= Delta ^ w * h ^ (m - w) :=
        pow_mul_pow_le_pow_mul_pow hhDelta hs'.2 hwm
      _ = B := rfl
  have hScard : S.card <= 2 ^ m := by
    exact (Finset.card_filter_le _ _).trans (card_signatures_le m)
  calc
    (boundedPaths children marked m w).card <=
        ∑ s ∈ S, (pathsOfSignature children marked s).card := by
      simpa [boundedPaths, S] using
        (Finset.card_biUnion_le
          (s := S) (t := pathsOfSignature children marked))
    _ <= ∑ _s ∈ S, B := Finset.sum_le_sum fun s hs => hper s hs
    _ = S.card * B := by simp
    _ <= 2 ^ m * B := Nat.mul_le_mul_right B hScard
    _ = 2 ^ m * Delta ^ w * h ^ (m - w) := by
      simp only [B, Nat.mul_assoc]

end Counting

end Erdos920.MarkedTree
