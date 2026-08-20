import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: NatSInfRangeAttained]
lemma NatSInfRangeAttained {α : Type*} (f : α → ℕ) (hα : Nonempty α) :
    ∃ a : α, f a = sInf (Set.range f) ∧
      ∀ b : α, sInf (Set.range f) ≤ f b := by
-- BODY
  classical
  have hRange_nonempty : (Set.range f).Nonempty := by
    rcases hα with ⟨a₀⟩
    exact ⟨f a₀, ⟨a₀, rfl⟩⟩
  have hmem : sInf (Set.range f) ∈ Set.range f :=
    Nat.sInf_mem hRange_nonempty
  rcases hmem with ⟨a, ha⟩
  refine ⟨a, ha, ?_⟩
  intro b
  exact Nat.sInf_le ⟨b, rfl⟩
