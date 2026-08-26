import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# A finite greedy covering estimate

The integer argument halves the uncovered set in at most `2*B` choices. It
supplies a logarithmic domination bound without a probabilistic assumption.
-/

namespace Erdos117

open Finset

variable {α ι : Type*} [DecidableEq α]

/-- If some member covers a `1/B` fraction of every remaining set, then at most
`2*B` members cover at least half of any specified target. -/
theorem exists_half_cover (N : ι → Finset α) {B : ℕ} (hB : 0 < B)
    (hcover : ∀ Y : Finset α, ∃ i, Y.card ≤ B * (Y ∩ N i).card) (Y : Finset α) :
    ∃ s : Finset ι, s.card ≤ 2 * B ∧ 2 * (Y \ s.biUnion N).card ≤ Y.card := by
  classical
  have hstep : ∀ t : ℕ, ∃ s : Finset ι, s.card ≤ t ∧
      (2 * (Y \ s.biUnion N).card ≤ Y.card ∨
        2 * B * (Y \ s.biUnion N).card + t * Y.card ≤ 2 * B * Y.card) := by
    intro t
    induction t with
    | zero => exact ⟨∅, by simp, Or.inr (by simp)⟩
    | succ t ih =>
      obtain ⟨s, hs, hrest⟩ := ih
      by_cases hsmall : 2 * (Y \ s.biUnion N).card ≤ Y.card
      · exact ⟨s, hs.trans (Nat.le_succ _), Or.inl hsmall⟩
      have hbudget := hrest.resolve_left hsmall
      let R := Y \ s.biUnion N
      obtain ⟨i, hi⟩ := hcover R
      have hnew : Y \ (insert i s).biUnion N = R \ N i := by
        ext x
        simp only [mem_sdiff, mem_biUnion, mem_insert, forall_eq_or_imp, not_exists,
          not_and, R]
        tauto
      refine ⟨insert i s, (card_insert_le _ _).trans (Nat.succ_le_succ hs), Or.inr ?_⟩
      rw [hnew]
      have hcard := card_sdiff_add_card_inter R (N i)
      have hlarge : Y.card < 2 * R.card := Nat.lt_of_not_ge hsmall
      change 2 * B * R.card + t * Y.card ≤ 2 * B * Y.card at hbudget
      nlinarith
  obtain ⟨s, hs, hrest⟩ := hstep (2 * B)
  refine ⟨s, hs, ?_⟩
  rcases hrest with h | h
  · exact h
  · nlinarith

/-- Iterated halving gives a logarithmic covering bound. -/
theorem exists_logarithmic_cover (N : ι → Finset α) {B : ℕ} (hB : 0 < B)
    (hcover : ∀ Y : Finset α, ∃ i, Y.card ≤ B * (Y ∩ N i).card) (Y : Finset α) :
    ∃ s : Finset ι, s.card ≤ 2 * B * (Nat.log 2 Y.card + 1) ∧ Y ⊆ s.biUnion N := by
  classical
  generalize hm : Y.card = m
  induction m using Nat.strong_induction_on generalizing Y with
  | h m ih =>
    by_cases hY : Y = ∅
    · subst Y
      exact ⟨∅, by simp, by simp⟩
    have hmpos : 0 < m := hm ▸ card_pos.mpr (nonempty_iff_ne_empty.mpr hY)
    obtain ⟨s, hs, hhalf⟩ := exists_half_cover N hB hcover Y
    let R := Y \ s.biUnion N
    have hRsmall : R.card < m := by dsimp [R]; omega
    by_cases hR : R = ∅
    · refine ⟨s, ?_, ?_⟩
      · nlinarith
      · exact sdiff_eq_empty_iff_subset.mp hR
    obtain ⟨t, ht, hcoverR⟩ := ih R.card hRsmall R rfl
    have hlog : Nat.log 2 R.card + 1 ≤ Nat.log 2 m := by
      rw [← Nat.log_mul_base (by decide : 1 < 2)
        (card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hR))]
      apply Nat.log_mono_right
      dsimp [R]
      omega
    refine ⟨s ∪ t, ?_, ?_⟩
    · have hcard := card_union_le s t
      nlinarith
    · intro x hx
      by_cases hxs : x ∈ s.biUnion N
      · obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hxs
        exact mem_biUnion.mpr ⟨i, mem_union_left t hi, hxi⟩
      · have hxR : x ∈ R := mem_sdiff.mpr ⟨hx, hxs⟩
        obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp (hcoverR hxR)
        exact mem_biUnion.mpr ⟨i, mem_union_right s hi, hxi⟩

/-- Double counting turns a minimum-neighborhood bound into the greedy
fractional-cover hypothesis. -/
theorem exists_large_intersection [Fintype α] [Nonempty α] (N : α → Finset α)
    (hsymm : ∀ x y, x ∈ N y ↔ y ∈ N x) {B : ℕ}
    (hdegree : ∀ x, Fintype.card α ≤ B * (N x).card) (Y : Finset α) :
    ∃ x, Y.card ≤ B * (Y ∩ N x).card := by
  have haux (x : α) : (Y ∩ N x).card = ∑ y ∈ Y, if x ∈ N y then 1 else 0 := by
    rw [sum_boole]
    congr 1
    ext y
    simp only [mem_inter, mem_filter, hsymm]
  have hsum : ∑ x : α, (Y ∩ N x).card = ∑ y ∈ Y, (N y).card := by
    simp_rw [haux]
    rw [sum_comm]
    apply sum_congr rfl
    intro y hy
    simp
  by_contra h
  have hbad : ∀ x, B * (Y ∩ N x).card < Y.card := by simpa only [not_exists, not_le] using h
  have hlt := sum_lt_sum_of_nonempty (s := (univ : Finset α)) univ_nonempty
    (fun x _ => hbad x)
  have hself : Fintype.card α * Y.card < Fintype.card α * Y.card := by
    calc
      Fintype.card α * Y.card = ∑ _y ∈ Y, Fintype.card α := by simp [Nat.mul_comm]
      _ ≤ ∑ y ∈ Y, B * (N y).card := sum_le_sum (fun y _ => hdegree y)
      _ = B * ∑ y ∈ Y, (N y).card := (mul_sum _ _ _).symm
      _ = ∑ x : α, B * (Y ∩ N x).card := by rw [← mul_sum, hsum]
      _ < Fintype.card α * Y.card := by simpa using hlt
  exact (lt_irrefl _ hself)

omit [DecidableEq α] in
/-- Logarithmic domination for a finite symmetric neighborhood system. -/
theorem exists_logarithmic_dominating_set [Fintype α] [Nonempty α]
    (N : α → Finset α) (hsymm : ∀ x y, x ∈ N y ↔ y ∈ N x)
    {B : ℕ} (hB : 0 < B) (hdegree : ∀ x, Fintype.card α ≤ B * (N x).card) :
    ∃ s : Finset α, s.card ≤ 2 * B * (Nat.log 2 (Fintype.card α) + 1) ∧
      ∀ x : α, ∃ y ∈ s, x ∈ N y := by
  classical
  obtain ⟨s, hs, hcov⟩ := exists_logarithmic_cover N hB
    (exists_large_intersection N hsymm hdegree) univ
  refine ⟨s, by simpa using hs, fun x => ?_⟩
  exact mem_biUnion.mp (hcov (mem_univ x))

end Erdos117
