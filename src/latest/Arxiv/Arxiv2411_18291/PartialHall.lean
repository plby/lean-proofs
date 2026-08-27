import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic

/-! # Hall's theorem with an explicit bound on unmatched indices -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_partial_transversal {I X : Type*} [Fintype I] [DecidableEq X]
    (t : I → Finset X) (d : ℕ)
    (hHall : ∀ s : Finset I, s.card ≤ (s.biUnion t).card + d) :
    ∃ S : Finset I, Fintype.card I ≤ S.card + d ∧
      ∃ g : S → X, Function.Injective g ∧ ∀ i : S, g i ∈ t i.val := by
  classical
  let t' (i : I) := (t i).disjSum (univ : Finset (Fin d))
  have hfull : ∀ s : Finset I, s.card ≤ (s.biUnion t').card := by
    intro s
    by_cases hs : s.Nonempty
    · have heq : s.biUnion t' = (s.biUnion t).disjSum (univ : Finset (Fin d)) := by
        ext x
        cases x with
        | inl x => simp [t']
        | inr x =>
          simp only [mem_biUnion, t', inr_mem_disjSum, mem_univ, and_true, iff_true]
          exact hs
      rw [heq, card_disjSum, card_univ, Fintype.card_fin]
      exact hHall s
    · have hz : s = ∅ := not_nonempty_iff_eq_empty.mp hs
      rw [hz]
      exact Nat.zero_le _
  obtain ⟨f, hfinj, hf⟩ := (all_card_le_biUnion_card_iff_existsInjective' t').mp hfull
  let S := univ.filter fun i : I => ∃ x : X, f i = Sum.inl x
  let g (i : S) : X := Classical.choose ((mem_filter.mp i.property).2)
  have hg (i : S) : f i.val = Sum.inl (g i) :=
    Classical.choose_spec ((mem_filter.mp i.property).2)
  have hginj : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    apply hfinj
    rw [hg i, hg j, hij]
  have hgt (i : S) : g i ∈ t i.val := by
    have hi := hf i.val
    rw [hg i] at hi
    exact inl_mem_disjSum.mp hi
  let R := (univ : Finset I) \ S
  have hR (i : R) : ∃ j : Fin d, f i.val = Sum.inr j := by
    have hiS : i.val ∉ S := (mem_sdiff.mp i.property).2
    cases hfi : f i.val with
    | inl x => exact (hiS (mem_filter.mpr ⟨mem_univ _, ⟨x, hfi⟩⟩)).elim
    | inr j => exact ⟨j, rfl⟩
  let b (i : R) : Fin d := Classical.choose (hR i)
  have hb (i : R) : f i.val = Sum.inr (b i) := Classical.choose_spec (hR i)
  have hbinj : Function.Injective b := by
    intro i j hij
    apply Subtype.ext
    apply hfinj
    rw [hb i, hb j, hij]
  have hRcard : R.card ≤ d := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective b hbinj
  have hpartition : R.card + S.card = Fintype.card I := by
    simpa only [R, card_univ] using card_sdiff_add_card_eq_card (subset_univ S)
  exact ⟨S, by omega, g, hginj, hgt⟩

end Arxiv2411_18291
