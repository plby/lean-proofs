import ErdosProblems.Erdos157.PackedAddition

/-! Equality of two packed-block pair sums recovers the product residue. -/

namespace Erdos157.Elementary

open AuxiliaryModuli PackedDigits

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

theorem packed_digit_eq_of_lists_eq {xs ys : List (ℕ × ℕ)} (j b d e : ℕ)
    (hx : xs[j]? = some (b, d)) (hy : ys[j]? = some (b, e)) (h : xs = ys) : d = e := by
  have he := congrArg (fun ls : List (ℕ × ℕ) => ls[j]?) h
  simpa only [hx, hy, Option.some.injEq, Prod.mk.injEq, true_and] using he

theorem block_residue_eq_of_encode_eq (i : ℕ) (τ : TagField i → LogDigit K i)
    (u v : (ResidueField K i)ˣ) (c d : BlockChoice i)
    (heq : MixedRadix.encode (blockDigits K i τ u c) = MixedRadix.encode (blockDigits K i τ v d)) :
    u = v := by
  have hlist := MixedRadix.encode_injective_of_valid (blockDigits_halfValid K i τ u c).valid
    (blockDigits_halfValid K i τ v d).valid (blockDigits_radices_eq K i τ τ u v c d) heq
  have htag : c.tag = d.tag := by
    apply (tagCoordinates i).injective
    ext j
    apply PairDigits.zmod_eq_of_pack_eq 7 _ _ (c.auxiliary (.inr (.inl j))) (d.auxiliary (.inr (.inl j)))
    exact packed_digit_eq_of_lists_eq (j.1 + 1) 721 _ _
      (blockDigits_get_tag K i τ u c j) (blockDigits_get_tag K i τ v d j) hlist
  have hlog : maskedLog K i τ c.tag u = maskedLog K i τ d.tag v := by
    apply PairDigits.zmod_eq_of_pack_eq (Nat.card (ResidueField K i)ˣ) _ _
      (c.auxiliary (.inl ())) (d.auxiliary (.inl ()))
    exact packed_digit_eq_of_lists_eq 0 _ _ _ (blockDigits_get_log K i τ u c)
      (blockDigits_get_log K i τ v d) hlist
  apply CyclicLog.log_injective
  dsimp only [maskedLog] at hlog
  rw [htag] at hlog
  exact add_right_cancel hlog

theorem block_encode_ne_pair_encode (i : ℕ) (τ : TagField i → LogDigit K i)
    (u v w : (ResidueField K i)ˣ) (c d e : BlockChoice i) :
    MixedRadix.encode (blockDigits K i τ u c) ≠
      MixedRadix.encode (blockDigits K i τ v d) + MixedRadix.encode (blockDigits K i τ w e) := by
  intro heq
  have hbase := blockDigits_radices_eq K i τ τ v w d e
  have hlist : blockDigits K i τ u c = pairSum (blockDigits K i τ v d) (blockDigits K i τ w e) := by
    apply MixedRadix.encode_injective_of_valid (blockDigits_halfValid K i τ u c).valid
      (pairSum_valid (blockDigits_halfValid K i τ v d) (blockDigits_halfValid K i τ w e) hbase)
    · rw [pairSum_radices hbase]
      exact blockDigits_radices_eq K i τ τ u v c d
    · rw [encode_pairSum hbase]
      exact heq
  have hhead := congrArg (fun ls : List (ℕ × ℕ) => ls[0]?) hlist
  have hp : PairDigits.pack (Nat.card (ResidueField K i)ˣ) (maskedLog K i τ c.tag u).val
      (c.auxiliary (.inl ())) =
    PairDigits.pack (Nat.card (ResidueField K i)ˣ) (maskedLog K i τ d.tag v).val (d.auxiliary (.inl ())) +
      PairDigits.pack (Nat.card (ResidueField K i)ˣ) (maskedLog K i τ e.tag w).val (e.auxiliary (.inl ())) := by
    simpa only [pairSum, List.getElem?_zipWith, blockDigits_get_log, Option.some.injEq,
      Prod.mk.injEq, true_and] using hhead
  exact PairDigits.single_ne_pair _ _ _ _ 0 (c.auxiliary (.inl ())) (d.auxiliary (.inl ()))
    (e.auxiliary (.inl ())) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (by decide)
    (by simpa only [Nat.add_zero] using hp)

theorem block_product_eq_of_encode_pair_eq (i : ℕ) (τ : TagField i → LogDigit K i)
    (u₁ u₂ u₃ u₄ : (ResidueField K i)ˣ) (c₁ c₂ c₃ c₄ : BlockChoice i)
    (heq : MixedRadix.encode (blockDigits K i τ u₁ c₁) + MixedRadix.encode (blockDigits K i τ u₂ c₂) =
      MixedRadix.encode (blockDigits K i τ u₃ c₃) + MixedRadix.encode (blockDigits K i τ u₄ c₄)) :
    u₁ * u₂ = u₃ * u₄ := by
  have hsum := pairSum_eq_of_encode_add_eq (blockDigits_halfValid K i τ u₁ c₁)
    (blockDigits_halfValid K i τ u₂ c₂) (blockDigits_halfValid K i τ u₃ c₃)
    (blockDigits_halfValid K i τ u₄ c₄)
    (blockDigits_radices_eq K i τ τ u₁ u₂ c₁ c₂)
    (blockDigits_radices_eq K i τ τ u₁ u₃ c₁ c₃)
    (blockDigits_radices_eq K i τ τ u₃ u₄ c₃ c₄) heq
  apply maskedLog_pair_decoding K i τ c₁.tag c₂.tag c₃.tag c₄.tag u₁ u₂ u₃ u₄
  · intro j
    apply PairDigits.zmod_pair_eq_of_pack_pair_eq 7
      (tagCoordinates i c₁.tag j) (tagCoordinates i c₂.tag j)
      (tagCoordinates i c₃.tag j) (tagCoordinates i c₄.tag j)
      (c₁.auxiliary (.inr (.inl j))) (c₂.auxiliary (.inr (.inl j)))
      (c₃.auxiliary (.inr (.inl j))) (c₄.auxiliary (.inr (.inl j)))
    exact pair_digit_eq_of_pairSum_eq (j.1 + 1) 721 _ _ _ _
      (blockDigits_get_tag K i τ u₁ c₁ j) (blockDigits_get_tag K i τ u₂ c₂ j)
      (blockDigits_get_tag K i τ u₃ c₃ j) (blockDigits_get_tag K i τ u₄ c₄ j) hsum
  · intro j
    apply PairDigits.zmod_pair_eq_of_pack_pair_eq 7
      (tagCoordinates i (c₁.tag ^ 2) j) (tagCoordinates i (c₂.tag ^ 2) j)
      (tagCoordinates i (c₃.tag ^ 2) j) (tagCoordinates i (c₄.tag ^ 2) j)
      (c₁.auxiliary (.inr (.inr j))) (c₂.auxiliary (.inr (.inr j)))
      (c₃.auxiliary (.inr (.inr j))) (c₄.auxiliary (.inr (.inr j)))
    exact pair_digit_eq_of_pairSum_eq (i + 2 + j.1 + 1) 721 _ _ _ _
      (blockDigits_get_square K i τ u₁ c₁ j) (blockDigits_get_square K i τ u₂ c₂ j)
      (blockDigits_get_square K i τ u₃ c₃ j) (blockDigits_get_square K i τ u₄ c₄ j) hsum
  · apply PairDigits.zmod_pair_eq_of_pack_pair_eq (Nat.card (ResidueField K i)ˣ)
      (maskedLog K i τ c₁.tag u₁) (maskedLog K i τ c₂.tag u₂)
      (maskedLog K i τ c₃.tag u₃) (maskedLog K i τ c₄.tag u₄)
      (c₁.auxiliary (.inl ())) (c₂.auxiliary (.inl ()))
      (c₃.auxiliary (.inl ())) (c₄.auxiliary (.inl ()))
    exact pair_digit_eq_of_pairSum_eq 0 (103 * Nat.card (ResidueField K i)ˣ) _ _ _ _
      (blockDigits_get_log K i τ u₁ c₁) (blockDigits_get_log K i τ u₂ c₂)
      (blockDigits_get_log K i τ u₃ c₃) (blockDigits_get_log K i τ u₄ c₄) hsum

end Erdos157.Elementary
