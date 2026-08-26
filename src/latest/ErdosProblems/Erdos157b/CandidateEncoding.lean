import ErdosProblems.Erdos157b.BlockDecoding
import ErdosProblems.Erdos157.LevelLabels

/-! The actual tagged mixed-radix integers, for arbitrary choices of tags and digits. -/

namespace Erdos157.Binary

open Erdos157.Elementary

open Polynomial PolynomialCharacters AuxiliaryModuli PackedDigits

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

abbrev MaskChoice := ∀ i : ℕ, TagField i → LogDigit K i

structure IntegerParameters where
  block : Label K → ∀ i : ℕ, BlockChoice i
  top : ∀ f : Label K, Fin (Fintype.card K ^ (3 * f.level))

noncomputable def labelResidue (f : Label K) (i : ℕ) : (ResidueField K i)ˣ :=
  (isUnit_mk_of_isCoprime (factor K i) f.polynomial
    ((factor_irreducible K i).coprime_iff_not_dvd.mpr
      (factor_not_dvd_even_prime K (levelDegree_even f.level) f.2 i))).unit

theorem labelResidue_val (f : Label K) (i : ℕ) :
    ↑(labelResidue K f i) = AdjoinRoot.mk (factor K i) f.polynomial := IsUnit.unit_spec _

noncomputable def digitBlocks (τ : MaskChoice K) (ω : IntegerParameters K) (f : Label K) :
    ℕ → ℕ → List (ℕ × ℕ)
  | _, 0 => []
  | i, n + 1 => blockDigits K i (τ i) (labelResidue K f i) (ω.block f i) ++
      digitBlocks τ ω f (i + 1) n

noncomputable def blockPlace : ℕ → ℕ → ℕ
  | _, 0 => 1
  | i, n + 1 => blockRadix K i * blockPlace (i + 1) n

theorem digitBlocks_halfValid (τ : MaskChoice K) (ω : IntegerParameters K) (f : Label K) (i n : ℕ) :
    HalfValid (digitBlocks K τ ω f i n) := by
  induction n generalizing i with
  | zero => trivial
  | succ n ih =>
    rw [digitBlocks, halfValid_append]
    exact ⟨blockDigits_halfValid K _ _ _ _, ih (i + 1)⟩

theorem place_append (xs ys : List (ℕ × ℕ)) :
    MixedRadix.place (xs ++ ys) = MixedRadix.place xs * MixedRadix.place ys := by
  simp only [MixedRadix.place, List.map_append, List.prod_append]

theorem digitBlocks_place (τ : MaskChoice K) (ω : IntegerParameters K) (f : Label K) (i n : ℕ) :
    MixedRadix.place (digitBlocks K τ ω f i n) = blockPlace K i n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => rw [digitBlocks, place_append, blockDigits_place, ih, blockPlace]

theorem digitBlocks_add (τ : MaskChoice K) (ω : IntegerParameters K) (f : Label K) (i m n : ℕ) :
    digitBlocks K τ ω f i (m + n) =
      digitBlocks K τ ω f i m ++ digitBlocks K τ ω f (i + m) n := by
  induction m generalizing i with
  | zero => simp [digitBlocks]
  | succ m ih =>
    rw [Nat.succ_add, digitBlocks, digitBlocks, ih]
    have hidx : i + 1 + m = i + (m + 1) := by omega
    rw [hidx, List.append_assoc]

theorem blockPlace_add (i m n : ℕ) : blockPlace K i (m + n) = blockPlace K i m * blockPlace K (i + m) n := by
  induction m generalizing i with
  | zero => simp [blockPlace]
  | succ m ih =>
    rw [Nat.succ_add, blockPlace, blockPlace, ih]
    have hidx : i + 1 + m = i + (m + 1) := by omega
    rw [hidx]
    ring

theorem blockRadix_pos (i : ℕ) : 0 < blockRadix K i := by
  unfold blockRadix
  exact Nat.mul_pos (Nat.mul_pos (by decide) Nat.card_pos) (by positivity)

theorem blockPlace_pos (i n : ℕ) : 0 < blockPlace K i n := by
  induction n generalizing i with
  | zero => exact Nat.zero_lt_one
  | succ n ih => exact Nat.mul_pos (blockRadix_pos K i) (ih (i + 1))

noncomputable def encoded (τ : MaskChoice K) (ω : IntegerParameters K) (f : Label K) : ℕ :=
  MixedRadix.encode (digitBlocks K τ ω f 0 f.level) +
    blockPlace K 0 f.level * (1 + (ω.top f).val)

theorem encoded_ge_place (τ : MaskChoice K) (ω : IntegerParameters K) (f : Label K) :
    blockPlace K 0 f.level ≤ encoded K τ ω f := by
  unfold encoded
  nlinarith

theorem encoded_lt_top_bound (τ : MaskChoice K) (ω : IntegerParameters K) (f : Label K) :
    encoded K τ ω f < (Fintype.card K ^ (3 * f.level) + 1) * blockPlace K 0 f.level := by
  have hl := MixedRadix.encode_lt_place (digitBlocks_halfValid K τ ω f 0 f.level).valid
  rw [digitBlocks_place] at hl
  have ht : 1 + (ω.top f).val ≤ Fintype.card K ^ (3 * f.level) := by have := (ω.top f).isLt; omega
  have hm := Nat.mul_le_mul_left (blockPlace K 0 f.level) ht
  unfold encoded
  nlinarith

/-- A common prefix is followed by a nonnegative integral tail. -/
theorem encoded_prefix_decomposition (τ : MaskChoice K) (ω : IntegerParameters K) (f : Label K)
    (m : ℕ) (hm : m ≤ f.level) :
    ∃ t : ℕ, encoded K τ ω f = MixedRadix.encode (digitBlocks K τ ω f 0 m) + blockPlace K 0 m * t := by
  have hsplit : digitBlocks K τ ω f 0 f.level =
      digitBlocks K τ ω f 0 m ++ digitBlocks K τ ω f m (f.level - m) := by
    have h := digitBlocks_add K τ ω f 0 m (f.level - m)
    simpa only [Nat.add_sub_of_le hm, zero_add] using h
  have hplace : blockPlace K 0 f.level = blockPlace K 0 m * blockPlace K m (f.level - m) := by
    have h := blockPlace_add K 0 m (f.level - m)
    simpa only [Nat.add_sub_of_le hm, zero_add] using h
  refine ⟨MixedRadix.encode (digitBlocks K τ ω f m (f.level - m)) +
    blockPlace K m (f.level - m) * (1 + (ω.top f).val), ?_⟩
  rw [encoded, hsplit, MixedRadix.encode_append, digitBlocks_place, hplace]
  ring

end Erdos157.Binary
