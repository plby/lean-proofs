import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.OrderOfElement

/-!
# Powers of cyclically reduced free-product words

A nonempty reduced free-product word is nontrivial. If its first and last letters
belong to different factors, concatenating copies produces reduced representatives
of every positive power. Such a word therefore has infinite order.
-/

namespace Wikipedia.HopfProblem.SpecialPeriods.CoprodTorsion

open Monoid.CoprodI

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]

/-- Multiplication is injective on reduced words. -/
theorem word_prod_injective : Function.Injective (Word.prod (M := M)) := by
  classical
  exact (Word.equiv (M := M)).symm.injective

/-- The identity has precisely the empty reduced representative. -/
theorem word_prod_eq_one_iff (w : Word M) : w.prod = 1 ↔ w = Word.empty := by
  constructor
  · intro h
    apply word_prod_injective
    simpa only [Word.prod_empty] using h
  · rintro rfl
    exact Word.prod_empty

/-- A nonempty reduced word represents a nonidentity element. -/
theorem neWord_prod_ne_one {i j : ι} (w : NeWord M i j) : w.prod ≠ 1 := by
  intro h
  have hw : w.toWord = Word.empty := (word_prod_eq_one_iff w.toWord).mp h
  exact w.toList_ne_nil (congrArg Word.toList hw)

/-- Concatenate `n + 1` copies of a reduced word whose endpoint factors differ. -/
def neWord_pow_succ {i j : ι} (w : NeWord M i j) (h : i ≠ j) :
    ℕ → NeWord M i j
  | 0 => w
  | n + 1 => NeWord.append (neWord_pow_succ w h n) h.symm w

/-- The repeated reduced word represents the corresponding positive power. -/
theorem neWord_pow_succ_prod {i j : ι} (w : NeWord M i j) (h : i ≠ j) (n : ℕ) :
    (neWord_pow_succ w h n).prod = w.prod ^ (n + 1) := by
  induction n with
  | zero => simp [neWord_pow_succ]
  | succ n ih => simp only [neWord_pow_succ, NeWord.append_prod, ih, pow_succ]

/-- No positive power of a cyclically reduced nonsingleton word is the identity. -/
theorem neWord_pow_ne_one {i j : ι} (w : NeWord M i j) (h : i ≠ j)
    (n : ℕ) (hn : 0 < n) : w.prod ^ n ≠ 1 := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
    rw [← neWord_pow_succ_prod w h n]
    exact neWord_prod_ne_one _

/-- A reduced word with distinct endpoint factors has infinite order. -/
theorem neWord_not_isOfFinOrder {i j : ι} (w : NeWord M i j) (h : i ≠ j) :
    ¬ IsOfFinOrder w.prod := by
  rintro hf
  obtain ⟨n, hn, hpow⟩ := hf.exists_pow_eq_one
  exact neWord_pow_ne_one w h n hn hpow

/-- In the `orderOf` convention, the order of this word is zero. -/
theorem neWord_orderOf_eq_zero {i j : ι} (w : NeWord M i j) (h : i ≠ j) :
    orderOf w.prod = 0 :=
  orderOf_eq_zero (neWord_not_isOfFinOrder w h)

/-- The same power criterion for the list-based reduced-word representation. -/
theorem word_pow_ne_one_of_endpoints_ne (w : Word M)
    (h : w.toList.head?.map Sigma.fst ≠ w.toList.getLast?.map Sigma.fst)
    (n : ℕ) (hn : 0 < n) : w.prod ^ n ≠ 1 := by
  have hw : w ≠ Word.empty := by
    rintro rfl
    exact h rfl
  obtain ⟨i, j, v, rfl⟩ := NeWord.of_word w hw
  have hij : i ≠ j := by
    simpa only [NeWord.toWord, NeWord.toList_head?, NeWord.toList_getLast?,
      Option.map_some, ne_eq, Option.some.injEq] using h
  exact neWord_pow_ne_one v hij n hn

/-- Distinct endpoint factors rule out finite order for a list-based reduced word. -/
theorem word_not_isOfFinOrder_of_endpoints_ne (w : Word M)
    (h : w.toList.head?.map Sigma.fst ≠ w.toList.getLast?.map Sigma.fst) :
    ¬ IsOfFinOrder w.prod := by
  rintro hf
  obtain ⟨n, hn, hpow⟩ := hf.exists_pow_eq_one
  exact word_pow_ne_one_of_endpoints_ne w h n hn hpow

/-- A version using explicit first and last letters. -/
theorem word_not_isOfFinOrder_of_head_getLast (w : Word M) (a b : Σ i, M i)
    (ha : w.toList.head? = some a) (hb : w.toList.getLast? = some b)
    (hab : a.1 ≠ b.1) : ¬ IsOfFinOrder w.prod := by
  apply word_not_isOfFinOrder_of_endpoints_ne w
  simpa only [ha, hb, Option.map_some, ne_eq, Option.some.injEq] using hab

end Wikipedia.HopfProblem.SpecialPeriods.CoprodTorsion
