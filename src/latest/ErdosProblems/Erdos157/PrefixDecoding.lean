import ErdosProblems.Erdos157.CandidateEncoding

/-! Pair-sum decoding over every common initial sequence of complete blocks. -/

namespace Erdos157.Elementary

open Polynomial PolynomialCharacters AuxiliaryModuli PackedDigits

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

theorem digitBlocks_pair_head_tail (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K) (i n : ℕ)
    (heq : MixedRadix.encode (digitBlocks K τ ω f₁ i (n + 1)) +
      MixedRadix.encode (digitBlocks K τ ω f₂ i (n + 1)) =
      MixedRadix.encode (digitBlocks K τ ω f₃ i (n + 1)) +
      MixedRadix.encode (digitBlocks K τ ω f₄ i (n + 1))) :
    labelResidue K f₁ i * labelResidue K f₂ i = labelResidue K f₃ i * labelResidue K f₄ i ∧
    MixedRadix.encode (digitBlocks K τ ω f₁ (i + 1) n) +
      MixedRadix.encode (digitBlocks K τ ω f₂ (i + 1) n) =
    MixedRadix.encode (digitBlocks K τ ω f₃ (i + 1) n) +
      MixedRadix.encode (digitBlocks K τ ω f₄ (i + 1) n) := by
  simp only [digitBlocks, MixedRadix.encode_append, blockDigits_place] at heq
  have hfront := prefix_pair_encode_eq
    (blockDigits_halfValid K i (τ i) (labelResidue K f₁ i) (ω.block f₁ i))
    (blockDigits_halfValid K i (τ i) (labelResidue K f₂ i) (ω.block f₂ i))
    (blockDigits_halfValid K i (τ i) (labelResidue K f₃ i) (ω.block f₃ i))
    (blockDigits_halfValid K i (τ i) (labelResidue K f₄ i) (ω.block f₄ i))
    (blockRadix K i) (blockDigits_place K i _ _ _) (blockDigits_place K i _ _ _)
    (blockDigits_place K i _ _ _) (blockDigits_place K i _ _ _) _ _ _ _ heq
  refine ⟨block_product_eq_of_encode_pair_eq K i (τ i) _ _ _ _ _ _ _ _ hfront, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (blockRadix_pos K i)
  nlinarith

theorem digitBlocks_pair_residues (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K) (i n : ℕ)
    (heq : MixedRadix.encode (digitBlocks K τ ω f₁ i n) + MixedRadix.encode (digitBlocks K τ ω f₂ i n) =
      MixedRadix.encode (digitBlocks K τ ω f₃ i n) + MixedRadix.encode (digitBlocks K τ ω f₄ i n)) :
    ∀ j < n, labelResidue K f₁ (i + j) * labelResidue K f₂ (i + j) =
      labelResidue K f₃ (i + j) * labelResidue K f₄ (i + j) := by
  induction n generalizing i with
  | zero => intro j hj; omega
  | succ n ih =>
    have h := digitBlocks_pair_head_tail K τ ω f₁ f₂ f₃ f₄ i n heq
    intro j hj
    cases j with
    | zero => simpa only [Nat.add_zero] using h.1
    | succ j =>
      have ht := ih (i + 1) h.2 j (by omega)
      have hidx : i + 1 + j = i + (j + 1) := by omega
      rw [hidx] at ht
      exact ht

theorem encoded_pair_prefix_eq (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K) (m : ℕ)
    (h₁ : m ≤ f₁.level) (h₂ : m ≤ f₂.level) (h₃ : m ≤ f₃.level) (h₄ : m ≤ f₄.level)
    (heq : encoded K τ ω f₁ + encoded K τ ω f₂ = encoded K τ ω f₃ + encoded K τ ω f₄) :
    MixedRadix.encode (digitBlocks K τ ω f₁ 0 m) + MixedRadix.encode (digitBlocks K τ ω f₂ 0 m) =
      MixedRadix.encode (digitBlocks K τ ω f₃ 0 m) + MixedRadix.encode (digitBlocks K τ ω f₄ 0 m) := by
  obtain ⟨t₁, ht₁⟩ := encoded_prefix_decomposition K τ ω f₁ m h₁
  obtain ⟨t₂, ht₂⟩ := encoded_prefix_decomposition K τ ω f₂ m h₂
  obtain ⟨t₃, ht₃⟩ := encoded_prefix_decomposition K τ ω f₃ m h₃
  obtain ⟨t₄, ht₄⟩ := encoded_prefix_decomposition K τ ω f₄ m h₄
  rw [ht₁, ht₂, ht₃, ht₄] at heq
  exact prefix_pair_encode_eq (digitBlocks_halfValid K τ ω f₁ 0 m)
    (digitBlocks_halfValid K τ ω f₂ 0 m) (digitBlocks_halfValid K τ ω f₃ 0 m)
    (digitBlocks_halfValid K τ ω f₄ 0 m) (blockPlace K 0 m)
    (digitBlocks_place K τ ω f₁ 0 m) (digitBlocks_place K τ ω f₂ 0 m)
    (digitBlocks_place K τ ω f₃ 0 m) (digitBlocks_place K τ ω f₄ 0 m) t₁ t₂ t₃ t₄ heq

theorem product_dvd_of_encoded_pair_eq (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K) (m : ℕ)
    (h₁ : m ≤ f₁.level) (h₂ : m ≤ f₂.level) (h₃ : m ≤ f₃.level) (h₄ : m ≤ f₄.level)
    (heq : encoded K τ ω f₁ + encoded K τ ω f₂ = encoded K τ ω f₃ + encoded K τ ω f₄) :
    product K m ∣ f₁.polynomial * f₂.polynomial - f₃.polynomial * f₄.polynomial := by
  have hprefix := encoded_pair_prefix_eq K τ ω f₁ f₂ f₃ f₄ m h₁ h₂ h₃ h₄ heq
  have hres := digitBlocks_pair_residues K τ ω f₁ f₂ f₃ f₄ 0 m hprefix
  apply product_dvd
  intro i hi
  have hri := hres i hi
  rw [Nat.zero_add] at hri
  have hu := congrArg Units.val hri
  simp only [Units.val_mul, labelResidue_val, ← map_mul] at hu
  exact AdjoinRoot.mk_eq_mk.mp hu

end Erdos157.Elementary
