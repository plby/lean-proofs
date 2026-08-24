import ErdosProblems.Erdos587.TranslationGrowth

/-!
Coset packing for the lattice step of the CFP stability argument.
These estimates do not infer coordinate projection indices from subgroup index.
-/

namespace Erdos587.CFP

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem consecutive_cosets_injective {Γ : AddSubgroup G} {a : G} {M : ℕ}
    (hperiod : ∀ k : ℕ, 0 < k → k < M → k • a ∉ Γ)
    {i j : ℕ} (hi : i < M) (hj : j < M) (hdiff : i • a - j • a ∈ Γ) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have hmem : (j - i) • a ∈ Γ := by
      rw [sub_nsmul a hij.le]
      have hh := Γ.neg_mem hdiff
      rw [neg_sub] at hh
      simpa only [sub_eq_add_neg] using hh
    exact (hperiod (j - i) (by omega) (by omega) hmem).elim
  · exact hij
  · have hmem : (i - j) • a ∈ Γ := by
      rw [sub_nsmul a hij.le]
      simpa only [sub_eq_add_neg] using hdiff
    exact (hperiod (i - j) (by omega) (by omega) hmem).elim

theorem card_mul_le_of_no_short_period {Γ : AddSubgroup G} {S V : Finset G}
    {a : G} {M : ℕ} (hS : ∀ x ∈ S, x ∈ Γ)
    (hperiod : ∀ k : ℕ, 0 < k → k < M → k • a ∉ Γ)
    (hfit : ∀ x ∈ S, ∀ i < M, x + i • a ∈ V) :
    S.card * M ≤ V.card := by
  have hinj : Set.InjOn (fun p : G × ℕ => p.1 + p.2 • a)
      (↑(S.product (Finset.range M)) : Set (G × ℕ)) := by
    intro p hp q hq heq
    change p.1 + p.2 • a = q.1 + q.2 • a at heq
    obtain ⟨hpS, hpM⟩ := Finset.mem_product.mp hp
    obtain ⟨hqS, hqM⟩ := Finset.mem_product.mp hq
    have hdiff : p.2 • a - q.2 • a ∈ Γ := by
      have hid : p.2 • a - q.2 • a = q.1 - p.1 := by
        apply sub_eq_sub_iff_add_eq_add.mpr
        simpa only [add_comm (p.2 • a) p.1] using heq
      rw [hid]
      exact Γ.sub_mem (hS q.1 hqS) (hS p.1 hpS)
    have hindices := consecutive_cosets_injective hperiod
      (Finset.mem_range.mp hpM) (Finset.mem_range.mp hqM) hdiff
    apply Prod.ext _ hindices
    rw [hindices] at heq
    exact add_right_cancel heq
  have hh := Finset.card_le_card_of_injOn (fun p : G × ℕ => p.1 + p.2 • a)
    (show Set.MapsTo (fun p : G × ℕ => p.1 + p.2 • a)
      (↑(S.product (Finset.range M)) : Set (G × ℕ)) V from by
      intro p hp
      obtain ⟨hpS, hpM⟩ := Finset.mem_product.mp hp
      exact hfit p.1 hpS p.2 (Finset.mem_range.mp hpM)) hinj
  change (S ×ˢ Finset.range M : Finset (G × ℕ)).card ≤ V.card at hh
  simpa only [Finset.card_product, Finset.card_range] using hh

/-- A dense enough set in a subgroup forces a short period in any direction
whose consecutive translates fit into the prescribed ambient set. -/
theorem exists_short_period_of_dense_translates {Γ : AddSubgroup G} {S V : Finset G}
    {a : G} {M : ℕ} (hS : ∀ x ∈ S, x ∈ Γ)
    (hfit : ∀ x ∈ S, ∀ i < M, x + i • a ∈ V)
    (hdense : V.card < S.card * M) :
    ∃ k : ℕ, 0 < k ∧ k < M ∧ k • a ∈ Γ := by
  by_contra hn
  push Not at hn
  exact (card_mul_le_of_no_short_period hS hn hfit).not_gt hdense

end Erdos587.CFP
