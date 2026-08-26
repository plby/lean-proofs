import ErdosProblems.Erdos73.OrderedFiniteSelection

/-! Two injective ranks contain a large increasing or decreasing matching. -/

namespace Erdos73
noncomputable section
open scoped Classical

open Finset

theorem exists_monotone_pair_selection {I : Type*} (s : Finset I) (a b : I → ℕ)
    (ha : Set.InjOn a (s : Set I)) (hb : Set.InjOn b (s : Set I))
    (k : ℕ) (hsize : twoColorRamseyBound k k ≤ s.card) :
    ∃ f : Fin k → I, Function.Injective f ∧ (∀ i, f i ∈ s) ∧
      StrictMono (a ∘ f) ∧ (StrictMono (b ∘ f) ∨ StrictAnti (b ∘ f)) := by
  let R (i j : I) := (a i < a j ∧ b i < b j) ∨ (a j < a i ∧ b j < b i)
  have hR : Std.Symm R := ⟨fun i j h => h.symm⟩
  obtain ⟨t, hts, ht | ht⟩ := exists_pairwise_or_pairwise_compl R hR k k s hsize
  · obtain ⟨f, hf, hft, hmono⟩ := exists_rank_ordered_selection t a (ha.mono hts) k ht.1
    refine ⟨f, hf, fun i => hts (hft i), hmono, Or.inl ?_⟩
    intro i j hij
    have hh := ht.2 (hft i) (hft j) (hf.ne hij.ne)
    have hm := hmono hij
    dsimp only [Function.comp_apply] at hm ⊢
    dsimp only [R] at hh
    omega
  · obtain ⟨f, hf, hft, hmono⟩ := exists_rank_ordered_selection t a (ha.mono hts) k ht.1
    refine ⟨f, hf, fun i => hts (hft i), hmono, Or.inr ?_⟩
    intro i j hij
    have hh := ht.2 (hft i) (hft j) (hf.ne hij.ne)
    have hm := hmono hij
    have hne : b (f i) ≠ b (f j) := fun he => (hf.ne hij.ne)
      (hb (hts (hft i)) (hts (hft j)) he)
    dsimp only [Function.comp_apply] at hm ⊢
    dsimp only [R] at hh
    omega

end
end Erdos73
