import Arxiv.Arxiv2411_18291.FiniteDecoderAugmentation

/-! # Local decoder augmentation preserves an additive edge cap -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem containing_union_le {V : Type*} [DecidableEq V] {q r : ℕ}
    (D E : Finset (Block V q)) {a b : ℝ}
    (hD : ∀ e : Block V r, ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ a)
    (hE : ∀ e : Block V r, ((E.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ b)
    (e : Block V r) :
    (((D ∪ E).filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ a + b := by
  rw [filter_union]
  have hcard : (((D.filter fun Q => e.val ⊆ Q.val) ∪
      (E.filter fun Q => e.val ⊆ Q.val)).card : ℝ) ≤
      (D.filter fun Q => e.val ⊆ Q.val).card +
        (E.filter fun Q => e.val ⊆ Q.val).card := by
    exact_mod_cast card_union_le (D.filter fun Q => e.val ⊆ Q.val)
      (E.filter fun Q => e.val ⊆ Q.val)
  exact hcard.trans (add_le_add (hD e) (hE e))

theorem augment_with_local_decoders_and_cap_at_exponent {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {C s M : ℝ} (hC : 1 ≤ C) (hCb : C ≤ (4 * q : ℝ) ^ (24 * q))
    (hs : paperAlpha q (r + 1) / 3 ≤ s) (hshalf : s ≤ 1 / 2)
    (F : Finset (Block (Fin n) q))
    (hF : IsCliqueFamilyBounded r F (C * (n : ℝ) ^ (-s)))
    (hM : ∀ e : Block (Fin n) (r + 1),
      ((F.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M) :
    ∃ D : Finset (Block (Fin n) q), F ⊆ D ∧
      IsCliqueFamilyBounded r D
        ((1 + q.choose (r + 1) *
          (1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1))) *
            (C * (n : ℝ) ^ (-s))) ∧
      (∀ e : Block (Fin n) (r + 1),
        ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M + q.choose (r + 1)) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ,
        (∀ e, e ∉ cliqueSupport (r + 1) F → J e = 0) →
        (∀ e, (((r + 1).factorial * q.choose (r + 1) : ℕ) : ℤ) ∣ J e) →
          GeneratedBy D J := by
  obtain ⟨D₀, hD₀, _, hD₀b⟩ := exists_bounded_local_decoder_family_at_exponent
    hqr hn hC hCb hs hshalf (cliqueSupport (r + 1) F) hF.support_graphBounded
  refine ⟨F ∪ D₀, subset_union_left, ?_, ?_, fun J hJ hdiv => ?_⟩
  · simpa only [add_mul, one_mul] using hF.union hD₀b
  · exact containing_union_le F D₀ hM (fun e => by exact_mod_cast hD₀.multiplicity e)
  · exact (hD₀.generates_multiples J hJ hdiv).mono subset_union_right

end Arxiv2411_18291
