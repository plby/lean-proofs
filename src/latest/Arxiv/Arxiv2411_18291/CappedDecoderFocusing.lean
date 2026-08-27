import Arxiv.Arxiv2411_18291.CappedFocusing
import Arxiv.Arxiv2411_18291.CappedDecoderAugmentation
import Arxiv.Arxiv2411_18291.FiniteGeneratorAssemblyThreshold

/-! # Focusing and decoding with an additive edge multiplicity bound -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_decoder_focusing_augmentation_with_cap_paper_threshold
    {I : Type*} [Fintype I] {q r n H : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ H)
    (hH : H ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    {C M : ℝ} (hgrowth : C + 1 ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 20))
    (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card)
    (σ : I → Equiv.Perm (Fin n))
    (hcount : ∀ e : Block (Fin n) (r + 1),
      ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
        (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial ≤
          (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1))))
    (F₀ : Finset (Block (Fin n) q))
    (hF₀ : IsCliqueFamilyBounded r F₀
      (C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))))
    (hM : ∀ e : Block (Fin n) (r + 1),
      ((F₀.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M) :
    ∃ D : Finset (Block (Fin n) q), F₀ ⊆ D ∧
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) / 2) ∧
      (∀ e : Block (Fin n) (r + 1),
        ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M + 1 + q.choose (r + 1)) ∧
      (∀ J : Block (Fin n) (r + 1) → ℤ,
        (∀ e, e ∉ cliqueSupport (r + 1) F₀ → J e = 0) →
        (∀ e, (((r + 1).factorial * q.choose (r + 1) : ℕ) : ℤ) ∣ J e) → GeneratedBy D J) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J →
        ∃ J' : Block (Fin n) (r + 1) → ℤ, GeneratedBy D (J - J') ∧
          (∀ e, e ∉ permutedUnion σ G → J' e = 0) ∧ IntegrallyDecomposable q J' := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hα := paperAlpha_pos hqr
  have hα1 := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  obtain ⟨F, hF, hFcap, hfocus⟩ :=
    exists_sparse_coloured_focusing_with_cap_paper_threshold hqr hn hqh hH
      K G hd hGK hloss σ hcount B hB
  have hsum : IsCliqueFamilyBounded r (F₀ ∪ F)
      ((C + 1) * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) := by
    simpa only [add_mul, one_mul] using hF₀.union hF
  have hnormalized : IsCliqueFamilyBounded r (F₀ ∪ F)
      (1 * (n : ℝ) ^ (-(13 * paperAlpha q (r + 1) / 20))) := by
    apply hsum.mono
    calc
      _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 20) *
          (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)) :=
        mul_le_mul_of_nonneg_right hgrowth (Real.rpow_nonneg hn0.le _)
      _ = _ := by rw [← Real.rpow_add hn0, one_mul]; congr 1; ring
  have hsumcap (e : Block (Fin n) (r + 1)) :
      (((F₀ ∪ F).filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M + 1 :=
    containing_union_le F₀ F hM (fun e => by exact_mod_cast hFcap e) e
  have hC24 : (1 : ℝ) ≤ (4 * q : ℝ) ^ (24 * q) :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ 4 * q by omega))
  obtain ⟨D, hsub, hDb, hcap, hdecode⟩ :=
    augment_with_local_decoders_and_cap_at_exponent hqr hn le_rfl hC24
      (by linarith only [hα] : paperAlpha q (r + 1) / 3 ≤
        13 * paperAlpha q (r + 1) / 20)
      (by linarith only [hα1] : 13 * paperAlpha q (r + 1) / 20 ≤ 1 / 2)
      (F₀ ∪ F) hnormalized hsumcap
  have hD : IsCliqueFamilyBounded r D
      ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) / 2) := by
    apply hDb.mono
    have hh := normalized_decoder_cost_paper_threshold hqr hn
    linarith only [hh]
  have hsupport : cliqueSupport (r + 1) F₀ ⊆ cliqueSupport (r + 1) (F₀ ∪ F) := by
    intro e he
    obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨Q, mem_union_left _ hQ, heQ⟩
  refine ⟨D, subset_union_left.trans hsub, hD, hcap, ?_, ?_⟩
  · intro J hs hdiv
    exact hdecode J (fun e he => hs e (fun he₀ => he (hsupport he₀))) hdiv
  · intro J hs hInt
    obtain ⟨J', hJ', hs', hInt'⟩ := hfocus J hs hInt
    exact ⟨J', hJ'.mono (subset_union_right.trans hsub), hs', hInt'⟩

end Arxiv2411_18291
