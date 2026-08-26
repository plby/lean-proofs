import ErdosProblems.Erdos157b.EncodingGrowth

/-! Reading complete blocks from sums, beyond the shorter summand's top digit. -/

namespace Erdos157.Binary

open Erdos157.Elementary

open AuxiliaryModuli PackedDigits

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

noncomputable def blockValue (τ : MaskChoice K) (ω : IntegerParameters K) (f : Label K) (i : ℕ) : ℕ :=
  MixedRadix.encode (blockDigits K i (τ i) (labelResidue K f i) (ω.block f i))

noncomputable def blockTrace (n i : ℕ) : ℕ := n / blockPlace K 0 i % blockRadix K i

theorem two_blockValue_lt (τ : MaskChoice K) (ω : IntegerParameters K) (f : Label K) (i : ℕ) :
    2 * blockValue K τ ω f i < blockRadix K i := by
  have h := (blockDigits_halfValid K i (τ i) (labelResidue K f i) (ω.block f i)).two_encode_lt_place
  rwa [blockDigits_place] at h

theorem blockValue_lt (τ : MaskChoice K) (ω : IntegerParameters K) (f : Label K) (i : ℕ) :
    blockValue K τ ω f i < blockRadix K i := by
  have h := two_blockValue_lt K τ ω f i
  omega

theorem encoded_block_decomposition (τ : MaskChoice K) (ω : IntegerParameters K) (f : Label K)
    (i : ℕ) (hi : i < f.level) :
    ∃ lower upper : ℕ, 2 * lower < blockPlace K 0 i ∧
      encoded K τ ω f = lower + blockPlace K 0 i * (blockValue K τ ω f i + blockRadix K i * upper) := by
  obtain ⟨t, ht⟩ := encoded_prefix_decomposition K τ ω f (i + 1) (by omega)
  have hone : digitBlocks K τ ω f i 1 = blockDigits K i (τ i) (labelResidue K f i) (ω.block f i) := by
    rw [digitBlocks, digitBlocks, List.append_nil]
  have hprefix : digitBlocks K τ ω f 0 (i + 1) = digitBlocks K τ ω f 0 i ++
      blockDigits K i (τ i) (labelResidue K f i) (ω.block f i) := by
    have h := digitBlocks_add K τ ω f 0 i 1
    rw [Nat.zero_add, hone] at h
    exact h
  have hplace : blockPlace K 0 (i + 1) = blockPlace K 0 i * blockRadix K i := by
    have h := blockPlace_add K 0 i 1
    rw [Nat.zero_add, show blockPlace K i 1 = blockRadix K i by simp [blockPlace]] at h
    exact h
  refine ⟨MixedRadix.encode (digitBlocks K τ ω f 0 i), t, ?_, ?_⟩
  · have h := (digitBlocks_halfValid K τ ω f 0 i).two_encode_lt_place
    rwa [digitBlocks_place] at h
  · rw [ht, hprefix, MixedRadix.encode_append, digitBlocks_place, hplace]
    unfold blockValue
    ring

theorem blockTrace_encoded (τ : MaskChoice K) (ω : IntegerParameters K) (f : Label K)
    (i : ℕ) (hi : i < f.level) : blockTrace K (encoded K τ ω f) i = blockValue K τ ω f i := by
  obtain ⟨lower, upper, hl, he⟩ := encoded_block_decomposition K τ ω f i hi
  have hl' : lower < blockPlace K 0 i := by omega
  rw [blockTrace, he, Nat.add_mul_div_left _ _ (blockPlace_pos K 0 i),
    Nat.div_eq_of_lt hl', Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (blockValue_lt K τ ω f i)]

theorem blockTrace_pair (τ : MaskChoice K) (ω : IntegerParameters K) (f g : Label K)
    (i : ℕ) (hf : i < f.level) (hg : i < g.level) :
    blockTrace K (encoded K τ ω f + encoded K τ ω g) i = blockValue K τ ω f i + blockValue K τ ω g i := by
  obtain ⟨lf, uf, hlf, hef⟩ := encoded_block_decomposition K τ ω f i hf
  obtain ⟨lg, ug, hlg, heg⟩ := encoded_block_decomposition K τ ω g i hg
  have hl : lf + lg < blockPlace K 0 i := by omega
  have hv : blockValue K τ ω f i + blockValue K τ ω g i < blockRadix K i := by
    have h1 := two_blockValue_lt K τ ω f i
    have h2 := two_blockValue_lt K τ ω g i
    omega
  have he : encoded K τ ω f + encoded K τ ω g = (lf + lg) + blockPlace K 0 i *
      ((blockValue K τ ω f i + blockValue K τ ω g i) + blockRadix K i * (uf + ug)) := by
    rw [hef, heg]
    ring
  rw [blockTrace, he, Nat.add_mul_div_left _ _ (blockPlace_pos K 0 i), Nat.div_eq_of_lt hl,
    Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]

/-- Two whole blocks are enough to absorb the shorter candidate, because
the longer candidate's lower packed prefix occupies less than half the place. -/
theorem blockTrace_long_short (τ : MaskChoice K) (ω : IntegerParameters K) (f g : Label K)
    (i : ℕ) (hf : i < f.level) (hg : g.level + 2 ≤ i) :
    blockTrace K (encoded K τ ω f + encoded K τ ω g) i = blockValue K τ ω f i := by
  obtain ⟨lower, upper, hl, he⟩ := encoded_block_decomposition K τ ω f i hf
  have hsmall := two_encoded_lt_place_add_two K τ ω g
  have hplaces := blockPlace_mono K 0 hg
  have hlo : lower + encoded K τ ω g < blockPlace K 0 i := by omega
  have he' : encoded K τ ω f + encoded K τ ω g =
      (lower + encoded K τ ω g) + blockPlace K 0 i * (blockValue K τ ω f i + blockRadix K i * upper) := by
    rw [he]
    omega
  rw [blockTrace, he', Nat.add_mul_div_left _ _ (blockPlace_pos K 0 i), Nat.div_eq_of_lt hlo,
    Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (blockValue_lt K τ ω f i)]

end Erdos157.Binary
