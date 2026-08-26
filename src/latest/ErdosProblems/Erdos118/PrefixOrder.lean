import ErdosProblems.Erdos118.WordResponses
import Mathlib.Logic.Equiv.List

/-!
The literal word encoding reflects the raw nested-shortlex order. Natural
codes order finite construction prefixes after their parents and order
siblings by their new datum. These are interfaces for a prefix construction,
not an assertion of the missing positive partition relation.
-/

namespace Erdos118.PrefixOrder

open Negative Negative.Exact WeakPigeon

theorem flatMap_lex_mono {s t : G2} (h : List.Lex SL s t) :
    List.Lex (· < ·) (s.flatMap levelWord) (t.flatMap levelWord) := by
  induction h with
  | @nil a l =>
    simp [List.flatMap_cons, levelWord]
  | @rel a s b t hab =>
    change List.Shortlex (· < ·) a b at hab
    rw [List.shortlex_def] at hab
    simp only [List.flatMap_cons, levelWord, List.cons_append]
    rcases hab with hlen | ⟨hlen, hlex⟩
    · exact List.Lex.rel hlen
    · rw [hlen]
      exact List.Lex.cons (lex_append_of_length_eq hlex hlen _ _)
  | @cons a s t h ih =>
    simp only [List.flatMap_cons]
    exact List.Lex.append_left _ ih (levelWord a)

theorem word_lex_mono {s t : G2} (h : G2LT s t) :
    List.Lex (· < ·) (word s) (word t) := by
  change List.Shortlex SL s t at h
  rw [List.shortlex_def] at h
  rcases h with hlen | ⟨hlen, hlex⟩
  · exact List.Lex.rel hlen
  · unfold word
    rw [hlen]
    exact List.Lex.cons (flatMap_lex_mono hlex)

theorem word_lex_iff {s t : G2} :
    List.Lex (· < ·) (word s) (word t) ↔ G2LT s t := by
  refine ⟨?_, word_lex_mono⟩
  intro h
  rcases lt_trichotomy (show OrderedG2 from s) (show OrderedG2 from t) with hst | hst | hst
  · exact hst
  · have he : s = t := hst
    subst t
    exact (irrefl _ h).elim
  · exact (asymm h (word_lex_mono hst)).elim

/-- Encoding the reverse makes the last extension the outermost pair. -/
def code (p : List ℕ) : ℕ := Encodable.encode p.reverse

@[simp] theorem code_nil : code [] = 0 := rfl

@[simp] theorem code_append (p : List ℕ) (a : ℕ) :
    code (p ++ [a]) = Nat.pair a (code p) + 1 := by
  simp only [code, List.reverse_append, List.reverse_singleton, List.singleton_append]
  rfl

theorem code_injective : Function.Injective code := by
  intro p q h
  exact List.reverse_injective (Encodable.encode_injective h)

theorem code_lt_child (p : List ℕ) (a : ℕ) : code p < code (p ++ [a]) := by
  rw [code_append]
  exact Nat.lt_succ_of_le (Nat.right_le_pair _ _)

theorem code_le_append (p q : List ℕ) : code p ≤ code (p ++ q) := by
  induction q using List.reverseRecOn with
  | nil => simp
  | append_singleton q a ih =>
    rw [← List.append_assoc]
    exact ih.trans (code_lt_child (p ++ q) a).le

theorem code_lt_append {p q : List ℕ} (hq : q ≠ []) :
    code p < code (p ++ q) := by
  induction q using List.reverseRecOn with
  | nil => exact (hq rfl).elim
  | append_singleton q a _ =>
    rw [← List.append_assoc]
    exact (code_le_append p q).trans_lt (code_lt_child (p ++ q) a)

theorem code_siblings (p : List ℕ) : StrictMono (fun a ↦ code (p ++ [a])) := by
  intro a b hab
  simp only [code_append, Nat.add_lt_add_iff_right]
  exact Nat.pair_lt_pair_left (code p) hab

end Erdos118.PrefixOrder
