import Arxiv.Arxiv2411_18291.Decomposition
import Mathlib.Tactic.Linarith

/-! # An explicit error bound for counting a union with bounded pair intersections -/

open Finset
open scoped BigOperators

namespace Arxiv2411_18291

theorem sum_card_le_biUnion_card_add_sq {I J : Type*} [DecidableEq J]
    (S : Finset I) (F : I → Finset J) (L : ℕ)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((F i) ∩ (F j)).card ≤ L) :
    (∑ i ∈ S, (F i).card) ≤ (S.biUnion F).card + S.card ^ 2 * L := by
  classical
  revert hpair
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    intro hpair
    have hprev := ih (fun j hj k hk hne =>
      hpair j (mem_insert_of_mem hj) k (mem_insert_of_mem hk) hne)
    have heq : F i ∩ S.biUnion F = S.biUnion (fun j => F i ∩ F j) := by
      ext x
      simp only [mem_inter, mem_biUnion]
      aesop
    have hinter : (F i ∩ S.biUnion F).card ≤ S.card * L := by
      rw [heq]
      calc
        _ ≤ ∑ j ∈ S, (F i ∩ F j).card := card_biUnion_le
        _ ≤ ∑ _j ∈ S, L := by
          apply sum_le_sum
          intro j hj
          apply hpair i (mem_insert_self _ _) j (mem_insert_of_mem hj)
          intro hij
          exact hi (hij.symm ▸ hj)
        _ = _ := by simp
    have hcard := card_union_add_card_inter (F i) (S.biUnion F)
    rw [sum_insert hi, biUnion_insert, card_insert_of_notMem hi]
    nlinarith [Nat.zero_le (S.card * L), Nat.zero_le L]

end Arxiv2411_18291
