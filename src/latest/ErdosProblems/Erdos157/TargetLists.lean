import ErdosProblems.Erdos157.PairedTargets
import Mathlib.Data.Fin.Tuple.Basic

/-! Splitting and assembling carry-compatible target lists. -/

namespace Erdos157.Elementary.PairedTargets

def appendEquiv : (xs ys : List ℕ) → Digits xs × Digits ys ≃ Digits (xs ++ ys)
  | [], ys =>
    { toFun := Prod.snd
      invFun := fun d => ((), d)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  | b :: bs, ys =>
    (Equiv.prodAssoc (Digit b) (Digits bs) (Digits ys)).trans
      (Equiv.prodCongr (Equiv.refl (Digit b)) (appendEquiv bs ys))

theorem place_append (xs ys : List ℕ) : place (xs ++ ys) = place xs * place ys := by
  simp only [place, List.map_append, List.prod_append]

theorem value_append (xs ys : List ℕ) (d : Digits xs) (e : Digits ys) :
    value (appendEquiv xs ys (d, e)) = value d + place xs * value e := by
  induction xs with
  | nil => change value e = 0 + 1 * value e; omega
  | cons b bs ih =>
    change d.1.value + 103 * b * value (appendEquiv bs ys (d.2, e)) =
      d.1.value + 103 * b * value d.2 + (103 * b * place bs) * value e
    rw [ih]
    ring

def replicateEquiv (b : ℕ) : (n : ℕ) → Digits (List.replicate n b) ≃ (Fin n → Digit b)
  | 0 =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => ()
      left_inv := fun _ => rfl
      right_inv := fun _ => funext (fun i => Fin.elim0 i) }
  | n + 1 =>
    (Equiv.prodCongr (Equiv.refl (Digit b)) (replicateEquiv b n)).trans
      (Fin.consEquiv (fun _ => Digit b))

def digitList : {bs : List ℕ} → Digits bs → List (ℕ × ℕ)
  | [], _ => []
  | b :: _, d => (103 * b, d.1.value) :: digitList d.2

theorem encode_digitList {bs : List ℕ} (d : Digits bs) :
    MixedRadix.encode (digitList d) = value d := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change d.1.value + 103 * b * MixedRadix.encode (digitList d.2) = _
    rw [ih]
    rfl

theorem place_digitList {bs : List ℕ} (d : Digits bs) :
    MixedRadix.place (digitList d) = place bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change 103 * b * MixedRadix.place (digitList d.2) = _
    rw [ih]
    rfl

theorem digitList_append (xs ys : List ℕ) (d : Digits xs) (e : Digits ys) :
    digitList (appendEquiv xs ys (d, e)) = digitList d ++ digitList e := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    change (103 * b, d.1.value) :: digitList (appendEquiv bs ys (d.2, e)) =
      (103 * b, d.1.value) :: (digitList d.2 ++ digitList e)
    rw [ih]

theorem digitList_replicate (b n : ℕ) (d : Digits (List.replicate n b)) :
    digitList d = List.ofFn (fun i => (103 * b, (replicateEquiv b n d i).value)) := by
  induction n with
  | zero => simp [digitList]
  | succ n ih =>
    change (103 * b, d.1.value) :: digitList d.2 = _
    rw [ih, List.ofFn_succ]
    rfl

end Erdos157.Elementary.PairedTargets
