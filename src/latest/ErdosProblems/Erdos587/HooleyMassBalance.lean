import ErdosProblems.Erdos587.NVDevelopment

/-! # Removing few large elements so every small reserve has small total mass -/

open scoped BigOperators

namespace Erdos587.CFP

lemma delta_remove_largest {α : Type*} [LinearOrder α] (A : Finset α) (k : ℕ)
    (hk : k ≤ A.card) :
    ∃ B ⊆ A, A.card = B.card + k ∧ ∀ a ∈ A \ B, ∀ b ∈ B, b ≤ a := by
  classical
  induction k generalizing A with
  | zero =>
    refine ⟨A, Finset.Subset.refl A, by simp, ?_⟩
    simp
  | succ k ih =>
    have hA : A.Nonempty := Finset.card_pos.mp (by omega)
    let a := A.max' hA
    have ha : a ∈ A := Finset.max'_mem A hA
    have hk' : k ≤ (A.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
    obtain ⟨B, hBA, hcard, horder⟩ := ih (A.erase a) hk'
    refine ⟨B, hBA.trans (Finset.erase_subset _ _), ?_, ?_⟩
    · rw [Finset.card_erase_of_mem ha] at hcard
      omega
    · intro x hx b hb
      by_cases hxa : x = a
      · subst x
        exact Finset.le_max' A b (hBA.trans (Finset.erase_subset _ _) hb)
      · apply horder x _ b hb
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_erase.mpr ⟨hxa, (Finset.mem_sdiff.mp hx).1⟩, (Finset.mem_sdiff.mp hx).2⟩

theorem delta_exists_mass_balanced_subset (A : Finset ℤ) (k L : ℕ)
    (hpos : ∀ a ∈ A, 0 ≤ a) (hsum : ∑ a ∈ A, a ≤ (2 : ℤ) ^ L) :
    ∃ B ⊆ A, A.card ≤ B.card + k * (L + 1) ∧
      ∀ b ∈ B, (k : ℤ) * b ≤ ∑ a ∈ B, a := by
  classical
  induction L generalizing A with
  | zero =>
    by_cases hcard : A.card ≤ k
    · exact ⟨∅, Finset.empty_subset _, by simpa using hcard, by simp⟩
    · obtain ⟨B, hBA, hcardB, horder⟩ := delta_remove_largest A k (by omega)
      refine ⟨B, hBA, by omega, ?_⟩
      intro b hb
      by_contra hbad
      have hbad' : ∑ a ∈ B, a < (k : ℤ) * b := lt_of_not_ge hbad
      have hremoved : (k : ℤ) * b ≤ ∑ a ∈ A \ B, a := by
        have hcardR : (A \ B).card = k := by rw [Finset.card_sdiff_of_subset hBA]; omega
        calc
          _ = ∑ _a ∈ A \ B, b := by simp [hcardR]
          _ ≤ ∑ a ∈ A \ B, a := Finset.sum_le_sum (fun a ha => horder a ha b hb)
      have hsplit := Finset.sum_sdiff hBA (f := fun a : ℤ => a)
      have hnonneg : 0 ≤ ∑ a ∈ B, a := Finset.sum_nonneg (fun a ha => hpos a (hBA ha))
      have hbBound : b ≤ ∑ a ∈ B, a := Finset.single_le_sum (fun a ha => hpos a (hBA ha)) hb
      have hsum0 : ∑ a ∈ B, a = 0 := by norm_num at hsum; omega
      have hb0 : b = 0 := by have := hpos b (hBA hb); omega
      rw [hb0, mul_zero, hsum0] at hbad'
      omega
  | succ L ih =>
    by_cases hcard : A.card ≤ k
    · refine ⟨∅, Finset.empty_subset _, ?_, by simp⟩
      simp only [Finset.card_empty, zero_add]
      exact hcard.trans (by nlinarith)
    · obtain ⟨B, hBA, hcardB, horder⟩ := delta_remove_largest A k (by omega)
      by_cases hbalanced : ∀ b ∈ B, (k : ℤ) * b ≤ ∑ a ∈ B, a
      · exact ⟨B, hBA, by nlinarith, hbalanced⟩
      · push Not at hbalanced
        obtain ⟨b, hb, hbad⟩ := hbalanced
        have hremoved : (k : ℤ) * b ≤ ∑ a ∈ A \ B, a := by
          have hcardR : (A \ B).card = k := by rw [Finset.card_sdiff_of_subset hBA]; omega
          calc
            _ = ∑ _a ∈ A \ B, b := by simp [hcardR]
            _ ≤ ∑ a ∈ A \ B, a := Finset.sum_le_sum (fun a ha => horder a ha b hb)
        have hsplit := Finset.sum_sdiff hBA (f := fun a : ℤ => a)
        have hsumB : ∑ a ∈ B, a ≤ (2 : ℤ) ^ L := by rw [pow_succ] at hsum; omega
        obtain ⟨D, hDB, hcost, hgood⟩ := ih B (fun a ha => hpos a (hBA ha)) hsumB
        refine ⟨D, hDB.trans hBA, ?_, hgood⟩
        calc
          A.card = B.card + k := hcardB
          _ ≤ (D.card + k * (L + 1)) + k := Nat.add_le_add_right hcost k
          _ = D.card + k * (L + 1 + 1) := by ring

theorem delta_small_reserve_mass (A W : Finset ℤ) (s : ℕ) (hs : 0 < s)
    (hWA : W ⊆ A) (hWcard : W.card ≤ s) (hpos : ∀ a ∈ A, 0 ≤ a)
    (hbalanced : ∀ a ∈ A, (4 * s : ℤ) * a ≤ ∑ b ∈ A, b) :
    3 * (∑ a ∈ W, a) ≤ ∑ a ∈ A \ W, a := by
  have htotal : 0 ≤ ∑ a ∈ A, a := Finset.sum_nonneg (fun a ha => hpos a ha)
  have hcardR : (W.card : ℤ) ≤ s := by exact_mod_cast hWcard
  have hscaled : (4 * s : ℤ) * (∑ a ∈ W, a) ≤ (s : ℤ) * (∑ a ∈ A, a) := by
    calc
      _ = ∑ a ∈ W, (4 * s : ℤ) * a := Finset.mul_sum _ _ _
      _ ≤ ∑ _a ∈ W, (∑ b ∈ A, b) := Finset.sum_le_sum (fun a ha => hbalanced a (hWA ha))
      _ = (W.card : ℤ) * (∑ b ∈ A, b) := by simp
      _ ≤ (s : ℤ) * (∑ b ∈ A, b) := mul_le_mul_of_nonneg_right hcardR htotal
  have hquarter : 4 * (∑ a ∈ W, a) ≤ ∑ a ∈ A, a := by
    apply le_of_mul_le_mul_left (a := (s : ℤ)) _ (by exact_mod_cast hs)
    nlinarith
  have hsplit := Finset.sum_sdiff hWA (f := fun a : ℤ => a)
  linarith

end Erdos587.CFP
