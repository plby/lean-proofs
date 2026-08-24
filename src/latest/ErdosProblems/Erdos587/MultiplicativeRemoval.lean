import ErdosProblems.Erdos587.BoundedRemoval

/-! Logarithmic deletion loss when an integer potential decreases by a fixed factor. -/

namespace Erdos587.CFP

def volumeDescentLength (V : ℕ) : ℕ := 3 * (Nat.log 2 V + 1)

theorem volumeDescentLength_budget (V : ℕ) :
    3 ^ volumeDescentLength V * V < 4 ^ volumeDescentLength V := by
  let n := Nat.log 2 V + 1
  have hV : V < 2 ^ n := Nat.lt_pow_succ_log_self Nat.one_lt_two V
  have hpow : (54 : ℕ) ^ n ≤ 64 ^ n := Nat.pow_le_pow_left (by decide) n
  calc
    3 ^ volumeDescentLength V * V < 3 ^ volumeDescentLength V * 2 ^ n :=
      Nat.mul_lt_mul_of_pos_left hV (by positivity)
    _ = 54 ^ n := by
      change 3 ^ (3 * n) * 2 ^ n = 54 ^ n
      rw [pow_mul, ← mul_pow]
      norm_num
    _ ≤ 64 ^ n := hpow
    _ = 4 ^ volumeDescentLength V := by
      change 64 ^ n = 4 ^ (3 * n)
      rw [pow_mul]
      norm_num

theorem exists_good_subset_of_multiplicative_potential {α : Type*} {A : Finset α}
    {r : ℕ} {P : Finset α → Prop} {volume : Finset α → ℕ}
    (hpositive : ∀ B ⊆ A,
      A.card ≤ B.card + volumeDescentLength (volume A) * r → 0 < volume B)
    (hstep : ∀ B ⊆ A,
      A.card ≤ B.card + volumeDescentLength (volume A) * r → ¬ P B →
      ∃ D ⊆ B, B.card ≤ D.card + r ∧ 4 * volume D ≤ 3 * volume B) :
    ∃ B ⊆ A, A.card ≤ B.card + volumeDescentLength (volume A) * r ∧ P B := by
  classical
  let T := volumeDescentLength (volume A)
  have iterate : ∀ t ≤ T,
      (∃ B ⊆ A, A.card ≤ B.card + T * r ∧ P B) ∨
      ∃ B ⊆ A, A.card ≤ B.card + t * r ∧ 4 ^ t * volume B ≤ 3 ^ t * volume A := by
    intro t
    induction t with
    | zero =>
        intro _ht
        exact Or.inr ⟨A, Finset.Subset.refl _, by simp, by simp⟩
    | succ t ih =>
        intro ht
        have htT : t ≤ T := by omega
        rcases ih htT with hgood | ⟨B, hBA, hcost, hvolume⟩
        · exact Or.inl hgood
        · have hcostT : A.card ≤ B.card + T * r := hcost.trans
            (Nat.add_le_add (le_refl _) (Nat.mul_le_mul_right r htT))
          by_cases hPB : P B
          · exact Or.inl ⟨B, hBA, hcostT, hPB⟩
          · obtain ⟨D, hDB, hremove, hdecrease⟩ := hstep B hBA hcostT hPB
            refine Or.inr ⟨D, hDB.trans hBA, ?_, ?_⟩
            · calc
                A.card ≤ B.card + t * r := hcost
                _ ≤ (D.card + r) + t * r := Nat.add_le_add_right hremove _
                _ = D.card + (t + 1) * r := by ring
            · calc
                4 ^ (t + 1) * volume D = 4 ^ t * (4 * volume D) := by rw [pow_succ]; ring
                _ ≤ 4 ^ t * (3 * volume B) := Nat.mul_le_mul_left _ hdecrease
                _ = 3 * (4 ^ t * volume B) := by ring
                _ ≤ 3 * (3 ^ t * volume A) := Nat.mul_le_mul_left 3 hvolume
                _ = 3 ^ (t + 1) * volume A := by rw [pow_succ]; ring
  rcases iterate T le_rfl with hgood | ⟨B, hBA, hcost, hvolume⟩
  · exact hgood
  · have hpos := hpositive B hBA hcost
    have hbase : 4 ^ T ≤ 4 ^ T * volume B := Nat.le_mul_of_pos_right _ hpos
    have hbad := hbase.trans hvolume
    exact ((volumeDescentLength_budget (volume A)).not_ge hbad).elim

end Erdos587.CFP
