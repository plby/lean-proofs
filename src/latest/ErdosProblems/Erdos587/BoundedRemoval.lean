import Mathlib

/-! Bounded deletion with a strictly increasing integer potential. -/

namespace Erdos587.CFP

theorem exists_good_subset_of_bounded_potential {α : Type*} {A : Finset α}
    {r K : ℕ} {P : Finset α → Prop} {potential : Finset α → ℕ}
    (hbound : ∀ B ⊆ A, A.card ≤ B.card + (K + 1) * r → potential B ≤ K)
    (hstep : ∀ B ⊆ A, A.card ≤ B.card + K * r → ¬ P B →
      ∃ D ⊆ B, B.card ≤ D.card + r ∧ potential B < potential D) :
    ∃ B ⊆ A, A.card ≤ B.card + K * r ∧ P B := by
  classical
  have iterate : ∀ t ≤ K + 1,
      (∃ B ⊆ A, A.card ≤ B.card + K * r ∧ P B) ∨
      ∃ B ⊆ A, A.card ≤ B.card + t * r ∧ t ≤ potential B := by
    intro t
    induction t with
    | zero =>
        intro _ht
        exact Or.inr ⟨A, Finset.Subset.refl _, by simp, Nat.zero_le _⟩
    | succ t ih =>
        intro ht
        have htK : t ≤ K := by omega
        rcases ih (by omega) with hgood | ⟨B, hBA, hcost, hpotential⟩
        · exact Or.inl hgood
        · have hcostK : A.card ≤ B.card + K * r := hcost.trans
            (Nat.add_le_add (le_refl _) (Nat.mul_le_mul_right r htK))
          by_cases hPB : P B
          · exact Or.inl ⟨B, hBA, hcostK, hPB⟩
          · obtain ⟨D, hDB, hremove, hincrease⟩ := hstep B hBA hcostK hPB
            refine Or.inr ⟨D, hDB.trans hBA, ?_, by omega⟩
            calc
              A.card ≤ B.card + t * r := hcost
              _ ≤ (D.card + r) + t * r := Nat.add_le_add_right hremove _
              _ = D.card + (t + 1) * r := by ring
  rcases iterate (K + 1) le_rfl with hgood | ⟨B, hBA, hcost, hlarge⟩
  · exact hgood
  · have hh := hbound B hBA hcost
    omega

end Erdos587.CFP
