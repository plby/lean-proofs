import ErdosProblems.Erdos157b.CandidateEncoding

/-! Elementary growth bounds for the packed radices and their place values. -/

namespace Erdos157.Binary

open Erdos157.Elementary

open AuxiliaryModuli

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

theorem blockRadix_ge_fieldPower (i : ℕ) : Fintype.card K ^ (2 * i + 1) ≤ blockRadix K i := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hp : 2 ≤ Fintype.card K ^ (2 * i + 1) := hq.trans (Nat.le_pow (by omega))
  rw [blockRadix, residueField_units_natCard, Nat.card_eq_fintype_card]
  have h103 : Fintype.card K ^ (2 * i + 1) ≤ 103 * (Fintype.card K ^ (2 * i + 1) - 1) := by omega
  exact h103.trans (Nat.le_mul_of_pos_right _ (by positivity))

theorem blockRadix_ge_two (i : ℕ) : 2 ≤ blockRadix K i := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hp : Fintype.card K ≤ Fintype.card K ^ (2 * i + 1) := Nat.le_pow (by omega)
  exact (hq.trans hp).trans (blockRadix_ge_fieldPower K i)

theorem blockPlace_ge_fieldPower (i n : ℕ) :
    Fintype.card K ^ (n * (2 * i + n)) ≤ blockPlace K i n := by
  induction n generalizing i with
  | zero => simp [blockPlace]
  | succ n ih =>
    have hexp : (n + 1) * (2 * i + (n + 1)) = (2 * i + 1) + n * (2 * (i + 1) + n) := by ring
    rw [hexp, pow_add, blockPlace]
    exact Nat.mul_le_mul (blockRadix_ge_fieldPower K i) (ih (i + 1))

theorem initialPlace_ge_fieldPower (k : ℕ) : Fintype.card K ^ (k ^ 2) ≤ blockPlace K 0 k := by
  simpa only [mul_zero, zero_add, pow_two] using blockPlace_ge_fieldPower K 0 k

theorem blockPlace_mono (i : ℕ) : Monotone (blockPlace K i) := by
  intro m n hmn
  have h := blockPlace_add K i m (n - m)
  rw [Nat.add_sub_of_le hmn] at h
  rw [h]
  exact Nat.le_mul_of_pos_right _ (blockPlace_pos K _ _)

theorem topRange_lt_two_next_blocks (k : ℕ) :
    4 * Fintype.card K ^ (3 * k) < blockPlace K k 2 := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have h16 : 4 < Fintype.card K ^ 4 := by
    have h := Nat.pow_le_pow_left hq 4
    norm_num at h
    omega
  have hpow : 4 < Fintype.card K ^ (k + 4) :=
    h16.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hpos : 0 < Fintype.card K ^ (3 * k) := by positivity
  calc
    _ < Fintype.card K ^ (k + 4) * Fintype.card K ^ (3 * k) :=
      Nat.mul_lt_mul_of_pos_right hpow hpos
    _ = Fintype.card K ^ (2 * (2 * k + 2)) := by rw [← pow_add]; congr 1; omega
    _ ≤ _ := blockPlace_ge_fieldPower K k 2

theorem two_encoded_lt_place_add_two (τ : MaskChoice K) (ω : IntegerParameters K) (f : Label K) :
    2 * encoded K τ ω f < blockPlace K 0 (f.level + 2) := by
  have he := encoded_lt_top_bound K τ ω f
  have hp := topRange_lt_two_next_blocks K f.level
  have hq : 1 ≤ Fintype.card K ^ (3 * f.level) := Nat.one_le_pow _ _ Fintype.card_pos
  have hB := blockPlace_pos K 0 f.level
  rw [blockPlace_add, Nat.zero_add]
  have hm := Nat.mul_lt_mul_of_pos_left hp hB
  nlinarith

theorem encoded_pair_lt_place_add_two (τ : MaskChoice K) (ω : IntegerParameters K)
    (f g : Label K) (k : ℕ) (hf : f.level ≤ k) (hg : g.level ≤ k) :
    encoded K τ ω f + encoded K τ ω g < blockPlace K 0 (k + 2) := by
  have h1 := two_encoded_lt_place_add_two K τ ω f
  have h2 := two_encoded_lt_place_add_two K τ ω g
  have hpf := blockPlace_mono K 0 (Nat.add_le_add_right hf 2)
  have hpg := blockPlace_mono K 0 (Nat.add_le_add_right hg 2)
  omega

theorem level_le_max_add_one_of_encoded_pair_eq (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K) (k : ℕ) (h₃ : f₃.level ≤ k) (h₄ : f₄.level ≤ k)
    (heq : encoded K τ ω f₁ + encoded K τ ω f₂ = encoded K τ ω f₃ + encoded K τ ω f₄) :
    f₁.level ≤ k + 1 := by
  by_contra h
  have hlarge : k + 2 ≤ f₁.level := by omega
  have hp := blockPlace_mono K 0 hlarge
  have hlo := encoded_ge_place K τ ω f₁
  have hhi := encoded_pair_lt_place_add_two K τ ω f₃ f₄ k h₃ h₄
  omega

theorem maximal_levels_close_of_encoded_pair_eq (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K) (h₁₂ : f₂.level ≤ f₁.level) (h₃₄ : f₄.level ≤ f₃.level)
    (heq : encoded K τ ω f₁ + encoded K τ ω f₂ = encoded K τ ω f₃ + encoded K τ ω f₄) :
    f₁.level ≤ f₃.level + 1 ∧ f₃.level ≤ f₁.level + 1 := by
  exact ⟨level_le_max_add_one_of_encoded_pair_eq K τ ω f₁ f₂ f₃ f₄ f₃.level le_rfl h₃₄ heq,
    level_le_max_add_one_of_encoded_pair_eq K τ ω f₃ f₄ f₁ f₂ f₁.level le_rfl h₁₂ heq.symm⟩

end Erdos157.Binary
